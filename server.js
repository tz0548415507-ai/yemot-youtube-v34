const express = require('express');
const ffmpeg = require('fluent-ffmpeg');
const ffmpegPath = require('ffmpeg-static');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { execFile } = require('child_process');
const ytdl = require('@distube/ytdl-core');

ffmpeg.setFfmpegPath(ffmpegPath);

const app = express();
app.use(express.urlencoded({ extended: true }));
app.use(express.json());

const TOKEN = (process.env.YEMOT_TOKEN || '').trim();
const GEMINI_KEY = (process.env.GEMINI_API_KEY || '').trim();
const YT_KEY = (process.env.YOUTUBE_API_KEY || '').trim();
const YT_KEY2 = (process.env.YOUTUBE_API_KEY2 || '').trim();
const YT_KEYS = [YT_KEY, YT_KEY2].filter(Boolean);
let activeYtKeyIndex = 0;

const YM = 'https://www.call2all.co.il/ym/api/';
const ADMIN_LOG_EXT = (process.env.ADMIN_LOG_EXT || '8').trim();
const ENV_MAIN_EXT = (process.env.MAIN_EXT || '').trim();
const RESULTS_PER_PAGE = 7;

let cachedModelName = null;
const folderCounters = {};
const userNamesCache = new Map();
const configuredPlayfileDirs = new Set();
const userSessionState = new Map();

const YTDLP_BIN_PATH = path.join(os.tmpdir(), 'yt-dlp-linux');
let ytdlpReadyPromise = null;

function normalizeMainExt(extVal) {
    const clean = String(extVal || '')
        .replace(/^ivr2:\/*/, '')
        .replace(/^\/+/, '')
        .replace(/\/+$/, '')
        .trim();
    return clean ? `/${clean}` : '/9';
}

function findDownloadedFileByPrefix(prefix) {
    try {
        const files = fs.readdirSync(os.tmpdir());
        const match = files.find(f =>
            f.startsWith(prefix + '.') &&
            !f.endsWith('.part') &&
            !f.endsWith('.ytdl') &&
            !f.endsWith('.temp')
        );
        if (match) {
            const fullPath = path.join(os.tmpdir(), match);
            const stat = fs.statSync(fullPath);
            if (stat.size > 20000) {
                return { filePath: fullPath, size: stat.size };
            }
        }
    } catch (e) {}
    return null;
}

function cleanupFilesByPrefix(prefix) {
    try {
        const files = fs.readdirSync(os.tmpdir());
        for (const f of files) {
            if (f.startsWith(prefix)) {
                fs.promises.unlink(path.join(os.tmpdir(), f)).catch(() => null);
            }
        }
    } catch (e) {}
}

async function ensureYtDlpBinary() {
    if (ytdlpReadyPromise) return ytdlpReadyPromise;

    ytdlpReadyPromise = (async () => {
        try {
            if (fs.existsSync(YTDLP_BIN_PATH) && fs.statSync(YTDLP_BIN_PATH).size > 1000000) {
                await fs.promises.chmod(YTDLP_BIN_PATH, 0o755);
                return YTDLP_BIN_PATH;
            }
            console.log('[yt-dlp] Downloading standalone yt-dlp_linux binary...');
            const binUrl = 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux';
            const res = await fetchWithTimeout(binUrl, {}, 45000);
            if (!res.ok) throw new Error(`HTTP ${res.status}`);
            const buf = Buffer.from(await res.arrayBuffer());
            await fs.promises.writeFile(YTDLP_BIN_PATH, buf);
            await fs.promises.chmod(YTDLP_BIN_PATH, 0o755);
            console.log(`[yt-dlp] Binary ready at ${YTDLP_BIN_PATH} (${buf.length} bytes)`);
            return YTDLP_BIN_PATH;
        } catch (err) {
            console.warn('[yt-dlp] Binary setup error:', err.message);
            ytdlpReadyPromise = null;
            throw err;
        }
    })();

    return ytdlpReadyPromise;
}

async function downloadWithYtDlpNoCookies(videoId, maxDurationSec = 900, perAttemptTimeoutMs = 18000) {
    const binPath = await ensureYtDlpBinary();
    const videoUrl = `https://www.youtube.com/watch?v=${videoId}`;
    
    const clientStrategies = [
        'youtube:player_client=android,web',
        'youtube:player_client=ios,mweb',
        'youtube:player_client=tv_embedded,android_vr'
    ];

    const uniquePrefix = `ytdlp_${videoId}_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    const outputTemplate = path.join(os.tmpdir(), `${uniquePrefix}.%(ext)s`);

    let lastErr = '';
    for (const extractorArg of clientStrategies) {
        cleanupFilesByPrefix(uniquePrefix);
        try {
            const args = [
                '--no-playlist',
                '--no-check-certificates',
                '--no-cache-dir',
                '--force-ipv4',
                '--extractor-args', extractorArg,
                '-f', 'bestaudio[ext=m4a]/bestaudio/worst',
                '--ffmpeg-location', ffmpegPath
            ];

            if (maxDurationSec > 0 && maxDurationSec <= 950) {
                args.push('--download-sections', `*0-${maxDurationSec}`);
            }

            args.push('-o', outputTemplate, videoUrl);

            await new Promise((resolve, reject) => {
                execFile(binPath, args, { timeout: perAttemptTimeoutMs, maxBuffer: 8 * 1024 * 1024 }, (error, stdout, stderr) => {
                    const found = findDownloadedFileByPrefix(uniquePrefix);
                    if (found) {
                        return resolve();
                    }
                    reject(new Error((stderr || (error && error.message) || 'yt-dlp failed').slice(-300)));
                });
            });

            const found = findDownloadedFileByPrefix(uniquePrefix);
            if (found) {
                console.log(`[yt-dlp Success] Downloaded ${found.size} bytes using ${extractorArg}`);
                return {
                    filePath: found.filePath,
                    size: found.size,
                    cleanup: () => cleanupFilesByPrefix(uniquePrefix)
                };
            }
        } catch (err) {
            lastErr = err.message;
            console.warn(`[yt-dlp Attempt Failed] (${extractorArg}):`, lastErr.slice(0, 180));
            cleanupFilesByPrefix(uniquePrefix);
        }
    }

    throw new Error('YTDLP_ALL_STRATEGIES_FAILED: ' + lastErr);
}

async function downloadWithYtdlFallback(videoId, targetFilePath, maxBytes, timeoutMs = 12000) {
    return new Promise((resolve, reject) => {
        let dl = 0;
        const ws = fs.createWriteStream(targetFilePath);
        const st = ytdl(`https://www.youtube.com/watch?v=${videoId}`, {
            filter: 'audioonly',
            quality: 'lowestaudio',
            playerClients: ['ANDROID', 'IOS', 'WEB']
        });
        const tm = setTimeout(() => {
            try { st.destroy(); } catch (e) {}
            ws.end(() => dl >= 20000 ? resolve(dl) : reject(new Error('ytdl fallback timeout')));
        }, timeoutMs);

        st.on('data', c => {
            dl += c.length;
            ws.write(c);
            if (dl >= maxBytes) {
                clearTimeout(tm);
                try { st.destroy(); } catch (e) {}
                ws.end(() => resolve(dl));
            }
        });
        st.on('end', () => {
            clearTimeout(tm);
            ws.end(() => dl >= 20000 ? resolve(dl) : reject(new Error('ytdl fallback empty stream')));
        });
        st.on('error', e => {
            clearTimeout(tm);
            ws.end(() => dl >= 150000 ? resolve(dl) : reject(e));
        });
    });
}

function lastVal(param) {
    if (Array.isArray(param)) {
        return String(param[param.length - 1] || '').trim();
    }
    return String(param || '').trim();
}

function sanitizeForYemotTts(str, maxLen = 55) {
    return String(str || '')
        .replace(/&quot;/g, ' ')
        .replace(/&#39;/g, ' ')
        .replace(/&amp;/g, ' ')
        .replace(/[^א-תa-zA-Z0-9\s]/g, ' ')
        .replace(/\s+/g, ' ')
        .trim()
        .slice(0, maxLen);
}

function parseIsoDurationToHebrew(isoDuration) {
    if (!isoDuration) return { seconds: 0, text: '' };
    const match = String(isoDuration).match(/PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?/);
    if (!match) return { seconds: 0, text: '' };

    const hours = parseInt(match[1] || '0', 10);
    const minutes = parseInt(match[2] || '0', 10);
    const seconds = parseInt(match[3] || '0', 10);
    const totalSeconds = (hours * 3600) + (minutes * 60) + seconds;

    const parts = [];
    if (hours === 1) parts.push('שעה');
    else if (hours === 2) parts.push('שעתיים');
    else if (hours > 2) parts.push(`${hours} שעות`);

    if (minutes === 1) parts.push('דקה אחת');
    else if (minutes > 1) parts.push(`${minutes} דקות`);

    if (hours === 0 && seconds > 0) {
        parts.push(`${seconds} שניות`);
    }

    return {
        seconds: totalSeconds,
        text: parts.join(' ו ')
    };
}

function buildPagePromptText(cleanQuery, allResults, pageIndex) {
    const startIdx = pageIndex * RESULTS_PER_PAGE;
    const pageItems = allResults.slice(startIdx, startIdx + RESULTS_PER_PAGE);
    const hasMorePages = allResults.length > (startIdx + RESULTS_PER_PAGE);

    const optionsTextParts = pageItems.map((item, idx) => `לתוצאה ${idx + 1} ${item.title} הקישו ${idx + 1}`);
    const headerText = (pageIndex === 0)
        ? `נקלט ${cleanQuery}`
        : `המשך תוצאות עבור ${cleanQuery}`;

    const moreText = hasMorePages
        ? 'לעוד תוצאות אחרות הקישו 9'
        : (allResults.length > RESULTS_PER_PAGE ? 'לחזרה לתוצאות הראשונות הקישו 9' : '');

    return `${headerText} ${optionsTextParts.join(' ')} לחיפוש מחדש הקישו 8 ${moreText} לחזרה לתפריט הקישו 0`.replace(/\s+/g, ' ').trim();
}

async function fetchWithTimeout(url, options = {}, timeout = 20000) {
    const controller = new AbortController();
    const id = setTimeout(() => controller.abort(), timeout);
    try {
        const response = await fetch(url, { ...options, signal: controller.signal });
        clearTimeout(id);
        return response;
    } catch (err) {
        clearTimeout(id);
        throw err;
    }
}

async function fetchYouTubeWithFallback(baseUrlWithoutKey, timeoutMs = 6500) {
    const keysToTry = YT_KEYS.length > 0 ? [
        YT_KEYS[activeYtKeyIndex % YT_KEYS.length],
        ...YT_KEYS.filter((_, idx) => idx !== (activeYtKeyIndex % YT_KEYS.length))
    ] : [''];

    let lastRes = null;
    let lastData = null;
    let lastErr = null;

    for (const key of keysToTry) {
        const sep = baseUrlWithoutKey.includes('?') ? '&' : '?';
        const fullUrl = `${baseUrlWithoutKey}${sep}key=${encodeURIComponent(key)}`;
        try {
            const res = await fetchWithTimeout(fullUrl, {}, timeoutMs);
            const data = await res.json();
            if (res.ok) {
                const usedIdx = YT_KEYS.indexOf(key);
                if (usedIdx !== -1 && usedIdx !== activeYtKeyIndex) {
                    activeYtKeyIndex = usedIdx;
                }
                return { res, data };
            }
            lastRes = res;
            lastData = data;
        } catch (err) {
            lastErr = err;
        }
    }

    if (lastRes) {
        return { res: lastRes, data: lastData };
    }
    throw lastErr || new Error('All YouTube API keys failed');
}

async function uploadTextToExactPath(textContent, exactTargetPath, fileNameLabel = 'file.txt') {
    const form = new FormData();
    form.append('token', TOKEN);
    form.append('path', exactTargetPath);
    form.append('convertAudio', '0');
    form.append('file', new Blob([Buffer.from(textContent, 'utf8')], { type: 'text/plain; charset=utf-8' }), fileNameLabel);
    await fetchWithTimeout(`${YM}UploadFile`, { method: 'POST', body: form }, 12000);
}

async function getUserNameIfRegistered(phone) {
    if (userNamesCache.has(phone)) {
        return userNamesCache.get(phone);
    }
    const folderPath = `ivr2:/users/${phone}`;
    try {
        const url = `${YM}GetIVR2Dir?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath)}`;
        const res = await fetchWithTimeout(url, {}, 6000);
        if (res.ok) {
            const data = await res.json();
            const files = data.files || [];
            const hasNameFile = files.some(f => {
                const fname = (typeof f === 'string') ? f : (f && (f.name || f.fileName || ''));
                const low = String(fname).toLowerCase();
                return low === 'name.txt' || low === 'name.wav';
            });
            if (hasNameFile) {
                try {
                    const dlUrl = `${YM}DownloadFile?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath + '/name.txt')}`;
                    const dlRes = await fetchWithTimeout(dlUrl, {}, 5000);
                    if (dlRes.ok) {
                        const nameTxt = (await dlRes.text()).trim();
                        if (nameTxt && !nameTxt.includes('responseStatus') && !nameTxt.includes('EXCEPTION')) {
                            userNamesCache.set(phone, nameTxt);
                            return nameTxt;
                        }
                    }
                } catch (e) {}
                userNamesCache.set(phone, 'משתמש רשום');
                return 'משתמש רשום';
            }
        }
    } catch (e) {}
    return null;
}

async function ensurePlayfileExtension(folderPathStr, returnExt) {
    const clean = String(folderPathStr).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const targetReturn = normalizeMainExt(returnExt);
    const cacheKey = `${clean}|${targetReturn}`;
    if (configuredPlayfileDirs.has(cacheKey)) return;

    try {
        const body = new URLSearchParams({
            token: TOKEN,
            path: `ivr2:/${clean}`,
            type: 'playfile'
        });
        await fetchWithTimeout(`${YM}UpdateExtension`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
            body
        }, 7000);

        const playfileIni = [
            'type=playfile',
            `playfile_end_goto=${targetReturn}`,
            `empty_goto=${targetReturn}`,
            `root_goto=${targetReturn}`,
            `control_play_return=${targetReturn}`,
            `control_play#=${targetReturn}`
        ].join('\r\n') + '\r\n';
        await uploadTextToExactPath(playfileIni, `ivr2:/${clean}/ext.ini`, 'ext.ini');

        configuredPlayfileDirs.add(cacheKey);
    } catch (e) {}
}

async function getNextFileNumberStr(folder, reserveCount = 1) {
    const cleanFolder = String(folder || '').replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');

    if (folderCounters[cleanFolder] !== undefined) {
        const startNum = folderCounters[cleanFolder] + 1;
        folderCounters[cleanFolder] += reserveCount;
        const result = [];
        for (let i = 0; i < reserveCount; i++) {
            result.push(String(startNum + i).padStart(3, '0'));
        }
        return reserveCount === 1 ? result[0] : result;
    }

    const folderPath = cleanFolder ? `ivr2:/${cleanFolder}` : `ivr2:/`;
    let maxExisting = -1;

    try {
        const url = `${YM}GetIVR2Dir?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath)}`;
        const res = await fetchWithTimeout(url, {}, 5000);
        if (res.ok) {
            const data = await res.json();
            const files = data.files || [];
            for (const f of files) {
                const fname = (typeof f === 'string') ? f : (f && (f.name || f.fileName || ''));
                const m = String(fname).match(/^(\d+)\.(wav|tts|txt|mp3)$/i);
                if (m) {
                    const num = parseInt(m[1], 10);
                    if (!isNaN(num) && num < 900 && num > maxExisting) {
                        maxExisting = num;
                    }
                }
            }
        }
    } catch (e) {}

    const baseNum = Math.max(maxExisting, 0);
    const startNum = baseNum + 1;
    folderCounters[cleanFolder] = baseNum + reserveCount;

    const result = [];
    for (let i = 0; i < reserveCount; i++) {
        result.push(String(startNum + i).padStart(3, '0'));
    }
    return reserveCount === 1 ? result[0] : result;
}

async function uploadWavBufferToExactPath(wavBuffer, exactTargetPath, fileNameLabel = 'audio.wav', timeoutMs = 45000) {
    const formData = new FormData();
    formData.append('token', TOKEN);
    formData.append('path', exactTargetPath);
    formData.append('convertAudio', '0');
    formData.append('file', new Blob([wavBuffer], { type: 'audio/wav' }), fileNameLabel);

    const upRes = await fetchWithTimeout(`${YM}UploadFile`, {
        method: 'POST',
        body: formData
    }, timeoutMs);

    return await upRes.text();
}

async function saveAdminLogToExt8(callerPhone, userName, categoryLabel, searchQuery, downloadedTitle, statusText) {
    try {
        const nextNum = await getNextFileNumberStr(ADMIN_LOG_EXT, 1);
        const nowStr = new Date().toLocaleString('he-IL', { timeZone: 'Asia/Jerusalem' });

        const ttsSummary = `משתמש ${userName} טלפון ${callerPhone} חיפש ב${categoryLabel} את ${searchQuery}. סטטוס: ${statusText}`;
        await uploadTextToExactPath(ttsSummary, `ivr2:/${ADMIN_LOG_EXT}/${nextNum}.tts`, `${nextNum}.tts`);

        const txtDetails = [
            `שם משתמש: ${userName}`,
            `מספר טלפון: ${callerPhone}`,
            `קובץ הקלטת שם: ivr2:/users/${callerPhone}/name.wav`,
            `קטגוריה: ${categoryLabel}`,
            `מילות חיפוש: ${searchQuery}`,
            `כותרת סרטון: ${downloadedTitle || 'לא הורד'}`,
            `סטטוס: ${statusText}`,
            `זמן פעולה: ${nowStr}`
        ].join('\r\n') + '\r\n';

        await uploadTextToExactPath(txtDetails, `ivr2:/${ADMIN_LOG_EXT}/${nextNum}.txt`, `${nextNum}.txt`);
    } catch (err) {}
}

async function downloadRecordingFromYemot(recordPath, apiDir) {
    const cleanPath = String(recordPath).replace(/^ivr2:\/*/, '').replace(/^\/*/, '');
    const cleanDir = String(apiDir || '').replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');

    const candidates = [
        `ivr2:/${cleanPath}`,
        `ivr2:${cleanPath}`
    ];
    if (cleanDir && !cleanPath.startsWith(cleanDir + '/')) {
        candidates.unshift(`ivr2:/${cleanDir}/${cleanPath}`);
    }
    if (!cleanPath.toLowerCase().endsWith('.wav')) {
        candidates.unshift(`ivr2:/${cleanPath}.wav`);
        if (cleanDir) candidates.unshift(`ivr2:/${cleanDir}/${cleanPath}.wav`);
    }

    const uniquePaths = [...new Set(candidates)];
    let lastYemotResponse = '';
    for (const p of uniquePaths) {
        const url = `${YM}DownloadFile?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(p)}`;
        try {
            const res = await fetchWithTimeout(url, {}, 10000);
            if (!res.ok) {
                lastYemotResponse = `HTTP_${res.status}`;
                continue;
            }
            const buf = Buffer.from(await res.arrayBuffer());
            const headStr = buf.toString('utf8', 0, Math.min(buf.length, 150));

            if (buf.length > 200 && !headStr.includes('responseStatus') && !headStr.includes('EXCEPTION')) {
                return buf;
            } else {
                lastYemotResponse = headStr;
            }
        } catch (e) {
            lastYemotResponse = e.message;
        }
    }
    throw new Error('YEMOT_DOWNLOAD_ERR: ' + lastYemotResponse);
}

async function getFastGeminiModels() {
    const defaultFastOrder = [
        'gemini-flash-lite-latest',
        'gemini-3.5-flash-lite',
        'gemini-3.5-flash',
        'gemini-flash-latest'
    ];
    if (cachedModelName) {
        return [cachedModelName, ...defaultFastOrder.filter(m => m !== cachedModelName)];
    }
    try {
        const res = await fetchWithTimeout(`https://generativelanguage.googleapis.com/v1beta/models?key=${GEMINI_KEY}`, {}, 6000);
        if (res.ok) {
            const data = await res.json();
            const available = (data.models || [])
                .filter(m => (m.supportedGenerationMethods || []).includes('generateContent'))
                .map(m => m.name.replace('models/', ''))
                .filter(m => !m.includes('tts') && !m.includes('image'));
            if (available.length > 0) {
                cachedModelName = available[0];
                return available;
            }
        }
    } catch (e) {}
    return defaultFastOrder;
}

async function transcribeAudio(audioBase64) {
    const modelsToTry = await getFastGeminiModels();
    const prompt = "תמלל את ההקלטה לעברית. החזר אך ורק את המילים שנאמרו בהקלטה ללא שום תוספת.";

    let lastErr = '';
    for (const model of modelsToTry.slice(0, 4)) {
        const url = `https://generativelanguage.googleapis.com/v1beta/models/${model}:generateContent?key=${GEMINI_KEY}`;
        try {
            const res = await fetchWithTimeout(url, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    contents: [{
                        parts: [
                            { text: prompt },
                            { inlineData: { mimeType: 'audio/wav', data: audioBase64 } }
                        ]
                    }],
                    generationConfig: { temperature: 0.1, maxOutputTokens: 60 }
                })
            }, 10000);

            if (res.ok) {
                cachedModelName = model;
                const data = await res.json();
                const text = data?.candidates?.[0]?.content?.parts?.[0]?.text || '';
                return text;
            }
            lastErr = await res.text();
        } catch (err) {
            lastErr = err.message;
        }
    }
    throw new Error('GEMINI_ERR: ' + lastErr);
}

async function convertSegmentToWavFast(inputPath, outputWavPath, startSec = 0, durationSec = 900) {
    await new Promise((resolve, reject) => {
        const ffTimer = setTimeout(() => reject(new Error('Local FFmpeg segment timeout')), 45000);
        let cmd = ffmpeg(inputPath);

        const inOpts = [];
        if (startSec > 0) {
            inOpts.push(`-ss ${startSec}`);
        }
        if (inOpts.length > 0) {
            cmd = cmd.inputOptions(inOpts);
        }

        cmd.duration(durationSec)
            .format('wav')
            .audioCodec('pcm_s16le')
            .audioChannels(1)
            .audioFrequency(8000)
            .outputOptions(['-threads 0'])
            .on('end', () => { clearTimeout(ffTimer); resolve(); })
            .on('error', (err) => { clearTimeout(ffTimer); reject(err); })
            .save(outputWavPath);
    });
}

async function downloadAndPreparePlayback(videoId, livePlayFolder, archiveUserFolder, durationSeconds = 0, returnExt = '/9') {
    const cleanLive = String(livePlayFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const cleanArchive = String(archiveUserFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');

    const tmpQuickWav = path.join(os.tmpdir(), `quick_out_${videoId}_${Date.now()}.wav`);
    const tmpFallbackIn = path.join(os.tmpdir(), `quick_fb_${videoId}_${Date.now()}.webm`);
    let quickCleanup = () => fs.promises.unlink(tmpFallbackIn).catch(() => null);

    try {
        const isLongVideo = durationSeconds > 900;
        const firstChunkDuration = isLongVideo ? 905 : 0;
        let quickInputPath = null;

        try {
            const dlRes = await downloadWithYtDlpNoCookies(videoId, firstChunkDuration, 16000);
            quickInputPath = dlRes.filePath;
            quickCleanup = dlRes.cleanup;
        } catch (ytdlpErr) {
            await downloadWithYtdlFallback(videoId, tmpFallbackIn, 5.5 * 1024 * 1024, 10000);
            quickInputPath = tmpFallbackIn;
        }

        await convertSegmentToWavFast(quickInputPath, tmpQuickWav, 0, 900);

        let quickWavBuf = await fs.promises.readFile(tmpQuickWav);
        quickCleanup();
        fs.promises.unlink(tmpQuickWav).catch(() => null);

        const isFullFifteenMin = quickWavBuf.length >= 13800000;
        const isLongStream = (durationSeconds > 900) ? true : (durationSeconds > 0 ? false : isFullFifteenMin);

        if (!isLongStream) {
            const singleNum = await getNextFileNumberStr(cleanLive, 1);
            const singlePath = `ivr2:/${cleanLive}/${singleNum}.wav`;
            await uploadWavBufferToExactPath(quickWavBuf, singlePath, `${singleNum}.wav`, 25000);

            (async () => {
                try {
                    await ensurePlayfileExtension(cleanArchive, returnExt);
                    const archNum = await getNextFileNumberStr(cleanArchive, 1);
                    const archTargetPath = `ivr2:/${cleanArchive}/${archNum}.wav`;
                    await uploadWavBufferToExactPath(quickWavBuf, archTargetPath, `${archNum}.wav`, 30000);
                } catch (e) {}
            })();

            return `f-/${cleanLive}/${singleNum}`;
        }

        const TOTAL_PARTS = durationSeconds > 900 ? Math.min(6, Math.max(2, Math.ceil((durationSeconds - 10) / 900))) : 6;
        const rawPartNums = await getNextFileNumberStr(cleanLive, TOTAL_PARTS);
        const partNums = Array.isArray(rawPartNums) ? rawPartNums : [rawPartNums];
        const partPaths = partNums.map(num => `ivr2:/${cleanLive}/${num}.wav`);
        const partCmds = partNums.map(num => `f-/${cleanLive}/${num}`);
        const chainedPlayCommand = partCmds.join('.');

        await uploadWavBufferToExactPath(quickWavBuf, partPaths[0], `${partNums[0]}.wav`, 20000);

        return chainedPlayCommand;
    } catch (e) {
        quickCleanup();
        fs.promises.unlink(tmpQuickWav).catch(() => null);
        throw e;
    }
}

const MAIN_MENU_TEXT = 'ברוכים הבאים לחיפוש ביוטיוב! לשמיעת הפלייליסט שלכם הקישו 1 לשמיעת שיעורי התורה שלכם הקישו 2 לחיפוש מוזיקה חדש הקישו 3 לחיפוש שיעור חדש הקישו 4!';

app.get('/', (req, res) => { res.send('YouTube Personal Line Server v38.0 OK'); });

app.all(['/yemot', '/yemot/:e'], async (req, res) => {
    const q = { ...req.query, ...req.body };
    res.type('text/plain; charset=utf-8');

    try {
        const callerPhone = lastVal(q.ApiPhone).replace(/[^0-9]/g, '');
        const callId = lastVal(q.ApiCallId);
        const currentMainExt = normalizeMainExt(q.main_ext || ENV_MAIN_EXT || lastVal(q.ApiExtension) || '/9');

        if (q.hangup === 'yes') {
            if (callerPhone) userSessionState.delete(callerPhone);
            return res.send('noop');
        }

        if (!callerPhone) {
            return res.send(`id_list_message=t-שגיאה בזיהוי מספר הטלפון&go_to_folder=${currentMainExt}`);
        }

        const hasMenuChoiceParam = (q.MenuChoice !== undefined);
        const menuChoice = lastVal(q.MenuChoice);
        const searchMusic = lastVal(q.SearchMusic);
        const searchTorah = lastVal(q.SearchTorah);
        const selectResult = lastVal(q.SelectResult);
        const recordName = lastVal(q.RecordName);

        const userFolder = `users/${callerPhone}`;
        const tempRecFolder = `users/${callerPhone}/temp`;
        const musicExtFolder = `1/${callerPhone}`;
        const torahExtFolder = `2/${callerPhone}`;

        let state = userSessionState.get(callerPhone);

        const hasAnyInputParams = Boolean(hasMenuChoiceParam || menuChoice || searchMusic || searchTorah || selectResult || recordName);
        if (!state || (callId && state.callId && state.callId !== callId) || !hasAnyInputParams) {
            const registeredName = await getUserNameIfRegistered(callerPhone);
            if (!registeredName) {
                userSessionState.set(callerPhone, { step: 'WAIT_NAME', callId });
                return res.send(`read=t-ברוכים הבאים אנא הקליטו את שמכם המלא ובסיום הקישו סולמית=RecordName,no,record,/${tempRecFolder},name_rec,no,7,1`);
            }
            userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'IN_PLAYLIST') {
            userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'WAIT_SELECT_RESULT' && selectResult) {
            if (selectResult === '8') {
                userSessionState.set(callerPhone, { step: 'WAIT_RECORD', isMusic: state.isMusic, callId });
                const recNum = await getNextFileNumberStr(tempRecFolder, 1);
                if (state.isMusic) {
                    return res.send(`read=t-אנא אמרו שוב את שם השיר המבוקש ובסיום הקישו סולמית=SearchMusic,no,record,/${tempRecFolder},${recNum},no,7,1`);
                } else {
                    return res.send(`read=t-אנא אמרו שוב את שם השיעור המבוקש ובסיום הקישו סולמית=SearchTorah,no,record,/${tempRecFolder},${recNum},no,7,1`);
                }
            }

            if (selectResult === '9') {
                const allResults = state.results || [];
                const currentPage = state.pageIndex || 0;
                const nextPage = ((currentPage + 1) * RESULTS_PER_PAGE < allResults.length) ? (currentPage + 1) : 0;
                const nextPromptText = buildPagePromptText(state.cleanQuery, allResults, nextPage);
                userSessionState.set(callerPhone, { ...state, pageIndex: nextPage, menuPromptText: nextPromptText, callId });
                return res.send(`read=t-${nextPromptText}=SelectResult,no,1,1,7,Digits,no`);
            }

            if (selectResult === '0' || selectResult === '*' || selectResult === '#') {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const digitNum = parseInt(selectResult, 10);
            const allResults = state.results || [];
            const currentPage = state.pageIndex || 0;
            const pageStart = currentPage * RESULTS_PER_PAGE;
            const currentPageItems = allResults.slice(pageStart, pageStart + RESULTS_PER_PAGE);

            if (isNaN(digitNum) || digitNum < 1 || digitNum > currentPageItems.length) {
                return res.send(`id_list_message=t-בחירה שגויה&read=t-${state.menuPromptText}=SelectResult,no,1,1,7,Digits,no`);
            }

            const chosenVideo = currentPageItems[digitNum - 1];
            const { cleanQuery, isMusic } = state;
            const archiveFolder = isMusic ? musicExtFolder : torahExtFolder;
            const categoryLabel = isMusic ? 'מוזיקה' : 'שיעורים';
            const registeredName = (await getUserNameIfRegistered(callerPhone)) || 'משתמש רשום';

            try {
                const playCmd = await downloadAndPreparePlayback(chosenVideo.videoId, tempRecFolder, archiveFolder, chosenVideo.durationSeconds || 0, currentMainExt);
                saveAdminLogToExt8(callerPhone, registeredName, categoryLabel, cleanQuery, chosenVideo.title, `הורד בהצלחה לשלוחה ${archiveFolder}`);
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-משמיע ${chosenVideo.title}.${playCmd}&go_to_folder=${currentMainExt}`);
            } catch (audioErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-נמצא ${chosenVideo.title} אך אירעה שגיאה בטעינת הקובץ&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }
        }

        if (state.step === 'WAIT_RECORD' && (searchMusic || searchTorah)) {
            const isMusic = Boolean(state.isMusic);
            const recordPath = isMusic ? (searchMusic || searchTorah) : (searchTorah || searchMusic);
            const categoryLabel = isMusic ? 'מוזיקה' : 'שיעורים';
            const registeredName = (await getUserNameIfRegistered(callerPhone)) || 'משתמש רשום';

            let audioBuf;
            try {
                audioBuf = await downloadRecordingFromYemot(recordPath, lastVal(q.ApiExtension));
            } catch (dlErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה בהורדת ההקלטה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            let rawText = '';
            try {
                rawText = await transcribeAudio(audioBuf.toString('base64'));
            } catch (gemErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה במנוע זיהוי הדיבור&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const cleanQuery = sanitizeForYemotTts(rawText, 55);
            if (!cleanQuery) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-לא הצלחתי לשמוע את הבקשה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const ytBaseUrl = `https://www.googleapis.com/youtube/v3/search?part=snippet&q=${encodeURIComponent(cleanQuery)}&type=video&maxResults=28`;
            let ytRes, ytData;
            try {
                const ytResult = await fetchYouTubeWithFallback(ytBaseUrl, 6500);
                ytRes = ytResult.res;
                ytData = ytResult.data;
            } catch (ytFetchErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה בתקשורת עם יוטיוב&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const validItems = (ytData.items || [])
                .filter(item => item.id && item.id.videoId)
                .map(item => ({
                    videoId: item.id.videoId,
                    title: sanitizeForYemotTts(item.snippet?.title || cleanQuery, 52) || cleanQuery,
                    durationSeconds: 0,
                    durationText: ''
                }));

            if (validItems.length === 0) {
                saveAdminLogToExt8(callerPhone, registeredName, categoryLabel, cleanQuery, '', 'לא נמצאו תוצאות');
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-לא נמצאו תוצאות&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const menuPromptText = buildPagePromptText(cleanQuery, validItems, 0);
            userSessionState.set(callerPhone, { step: 'WAIT_SELECT_RESULT', cleanQuery, isMusic, results: validItems, pageIndex: 0, menuPromptText, callId });
            return res.send(`read=t-${menuPromptText}=SelectResult,no,1,1,7,Digits,no`);
        }

        if (state.step === 'WAIT_MENU' && (hasMenuChoiceParam || menuChoice)) {
            if (menuChoice === '' || menuChoice === '#' || menuChoice === '*' || menuChoice === '0') {
                userSessionState.delete(callerPhone);
                return res.send('go_to_folder=..');
            }
            if (menuChoice === '1') {
                await ensurePlayfileExtension(musicExtFolder, currentMainExt);
                userSessionState.set(callerPhone, { step: 'IN_PLAYLIST', callId });
                return res.send(`go_to_folder=/${musicExtFolder}`);
            }
            if (menuChoice === '2') {
                await ensurePlayfileExtension(torahExtFolder, currentMainExt);
                userSessionState.set(callerPhone, { step: 'IN_PLAYLIST', callId });
                return res.send(`go_to_folder=/${torahExtFolder}`);
            }
            if (menuChoice === '3') {
                const recNum = await getNextFileNumberStr(tempRecFolder, 1);
                userSessionState.set(callerPhone, { step: 'WAIT_RECORD', isMusic: true, callId });
                return res.send(`read=t-אנא אמרו את שם השיר המבוקש ובסיום הקישו סולמית=SearchMusic,no,record,/${tempRecFolder},${recNum},no,7,1`);
            }
            if (menuChoice === '4') {
                const recNum = await getNextFileNumberStr(tempRecFolder, 1);
                userSessionState.set(callerPhone, { step: 'WAIT_RECORD', isMusic: false, callId });
                return res.send(`read=t-אנא אמרו את שם השיעור המבוקש ובסיום הקישו סולמית=SearchTorah,no,record,/${tempRecFolder},${recNum},no,7,1`);
            }
            userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'WAIT_NAME' && recordName) {
            let audioBuf;
            try {
                audioBuf = await downloadRecordingFromYemot(recordName, lastVal(q.ApiExtension));
            } catch (dlErr) {
                return res.send(`read=t-שגיאה בקליטת ההקלטה אנא הקליטו שוב את שמכם ובסיום הקישו סולמית=RecordName,no,record,/${tempRecFolder},name_rec,no,7,1`);
            }

            let rawName = '';
            try { rawName = await transcribeAudio(audioBuf.toString('base64')); } catch (e) {}
            const cleanName = sanitizeForYemotTts(rawName, 40) || 'משתמש רשום';

            await uploadWavBufferToExactPath(audioBuf, `ivr2:/${userFolder}/name.wav`, 'name.wav');
            await uploadTextToExactPath(cleanName, `ivr2:/${userFolder}/name.txt`, 'name.txt');
            userNamesCache.set(callerPhone, cleanName);

            await ensurePlayfileExtension(musicExtFolder, currentMainExt);
            await ensurePlayfileExtension(torahExtFolder, currentMainExt);
            saveAdminLogToExt8(callerPhone, cleanName, 'רישום למערכת', 'הקלטת שם משתמש', '', 'נרשם בהצלחה');

            userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`id_list_message=t-שלום ${cleanName} נרשמתם בהצלחה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
        return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);

    } catch (e) {
        if (!res.headersSent) {
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }
    }
});

const port = process.env.PORT || 3000;
app.listen(port, '0.0.0.0', () => {
    console.log(`=== Server v38.0 Ready on port ${port} ===`);
    setTimeout(async () => {
        try { await ensureYtDlpBinary(); } catch (e) {}
    }, 2000);
});
