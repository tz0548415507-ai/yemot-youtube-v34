const express = require('express');
const ffmpeg = require('fluent-ffmpeg');
const ffmpegPath = require('ffmpeg-static');
const fs = require('fs');
const path = require('path');
const os = require('os');
const net = require('net');
const { execFile } = require('child_process');

ffmpeg.setFfmpegPath(ffmpegPath);

const app = express();
app.use(express.urlencoded({ extended: true }));
app.use(express.json());

// ==================== הגדרות סביבה (100% חינמי) ====================
const TOKEN = (process.env.YEMOT_TOKEN || '').trim();
const GEMINI_KEY = (process.env.GEMINI_API_KEY || '').trim();
const YT_KEY = (process.env.YOUTUBE_API_KEY || '').trim();
const YT_KEY2 = (process.env.YOUTUBE_API_KEY2 || '').trim();
const YT_KEYS = [YT_KEY, YT_KEY2].filter(Boolean);
let activeYtKeyIndex = 0;

// אופציונלי וחינמי לגמרי: עוגיות מחשבון גוגל משני (מונע חסימת בוט לצמיתות)
const YT_COOKIES_B64 = (process.env.YT_COOKIES_B64 || '').trim();

const YM = 'https://www.call2all.co.il/ym/api/';
const ADMIN_LOG_EXT = '8';
const YOUTUBE_MAIN_EXT = '/1/0000000144';
const RESULTS_PER_PAGE = 7;

// סדר מנועי ההורדה החינמיים האוטומטיים
const ENGINE_ORDER = [
    'ytdlp_cookies',
    'innertube_direct',
    'ytdlp_direct',
    'invidious_auto',
    'piped_auto',
    'ytdlp_free_proxy'
];

let cachedModelName = null;
const folderCounters = {};
const userNamesCache = new Map();
const configuredPlayfileDirs = new Set();
const userSessionState = new Map();

// Circuit Breaker: השהיית מנוע תקול ל-10 דקות כדי לחסוך זמן בשיחה
const engineCooldown = new Map();
const COOLDOWN_MS = 10 * 60 * 1000;

const YTDLP_BIN_PATH = path.join(os.tmpdir(), 'yt-dlp-linux');
const YTDLP_MAX_AGE_MS = 24 * 60 * 60 * 1000;
const COOKIES_FILE_PATH = path.join(os.tmpdir(), 'yt_cookies.txt');
let ytdlpReadyPromise = null;
let cookiesInitialized = false;

// מטמונים אוטומטיים לשרתים חינמיים ופרוקסי חינמיים (מתרעננים ברקע)
let invidiousCache = {
    updatedAt: 0,
    list: [
        'https://inv.nadeko.net',
        'https://yewtu.be',
        'https://invidious.nerdvpn.de',
        'https://invidious.f5.si',
        'https://iv.datura.network'
    ]
};

let pipedCache = {
    updatedAt: 0,
    list: [
        'https://pipedapi.kavin.rocks',
        'https://pipedapi.adminforge.de',
        'https://api.piped.private.coffee',
        'https://pipedapi.leptons.xyz',
        'https://pipedapi.drgns.space'
    ]
};

let freeProxyCache = {
    updatedAt: 0,
    working: [],
    refreshing: null
};

const REGISTRY_TTL_MS = 30 * 60 * 1000;
const PROXY_TTL_MS = 20 * 60 * 1000;

function setEngineCooldown(engine, reason, ms = COOLDOWN_MS) {
    engineCooldown.set(engine, { until: Date.now() + ms, reason: String(reason).slice(0, 140) });
    console.warn(`[CircuitBreaker] Pausing ${engine} for ${Math.round(ms / 1000)}s: ${reason}`);
}

function isEngineCoolingDown(engine) {
    const entry = engineCooldown.get(engine);
    if (!entry) return false;
    if (Date.now() > entry.until) {
        engineCooldown.delete(engine);
        return false;
    }
    return true;
}

function getCookiesFilePath() {
    if (!YT_COOKIES_B64) return null;
    if (cookiesInitialized && fs.existsSync(COOKIES_FILE_PATH)) return COOKIES_FILE_PATH;
    try {
        let content = YT_COOKIES_B64;
        if (!content.includes('\t') && !content.includes('Netscape')) {
            const decoded = Buffer.from(content, 'base64').toString('utf8');
            if (decoded.includes('youtube.com') || decoded.includes('\t') || decoded.includes('Netscape')) {
                content = decoded;
            }
        }
        if (content.trim().length > 20) {
            fs.writeFileSync(COOKIES_FILE_PATH, content, 'utf8');
            cookiesInitialized = true;
            return COOKIES_FILE_PATH;
        }
    } catch (e) {}
    return null;
}

function lastVal(param) {
    if (Array.isArray(param)) return String(param[param.length - 1] || '').trim();
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

    if (hours === 0 && seconds > 0) parts.push(`${seconds} שניות`);

    return { seconds: totalSeconds, text: parts.join(' ו ') };
}

function buildPagePromptText(cleanQuery, allResults, pageIndex) {
    const startIdx = pageIndex * RESULTS_PER_PAGE;
    const pageItems = allResults.slice(startIdx, startIdx + RESULTS_PER_PAGE);
    const hasMorePages = allResults.length > (startIdx + RESULTS_PER_PAGE);

    const optionsTextParts = pageItems.map((item, idx) => `לתוצאה ${idx + 1} ${item.title} הקישו ${idx + 1}`);
    const headerText = (pageIndex === 0) ? `נקלט ${cleanQuery}` : `המשך תוצאות עבור ${cleanQuery}`;
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

async function fetchYouTubeWithFallback(baseUrlWithoutKey, timeoutMs = 6000) {
    const keysToTry = YT_KEYS.length > 0 ? [
        YT_KEYS[activeYtKeyIndex % YT_KEYS.length],
        ...YT_KEYS.filter((_, idx) => idx !== (activeYtKeyIndex % YT_KEYS.length))
    ] : [''];

    let lastRes = null, lastData = null, lastErr = null;
    for (const key of keysToTry) {
        const sep = baseUrlWithoutKey.includes('?') ? '&' : '?';
        const fullUrl = `${baseUrlWithoutKey}${sep}key=${encodeURIComponent(key)}`;
        try {
            const res = await fetchWithTimeout(fullUrl, {}, timeoutMs);
            const data = await res.json();
            if (res.ok) {
                const usedIdx = YT_KEYS.indexOf(key);
                if (usedIdx !== -1 && usedIdx !== activeYtKeyIndex) activeYtKeyIndex = usedIdx;
                return { res, data };
            }
            lastRes = res; lastData = data;
        } catch (err) { lastErr = err; }
    }
    if (lastRes) return { res: lastRes, data: lastData };
    throw lastErr || new Error('All YouTube API keys failed');
}

// ==================== רענון אוטומטי של רשימות חינמיות ====================

async function refreshInvidiousList(force = false) {
    if (!force && (Date.now() - invidiousCache.updatedAt) < REGISTRY_TTL_MS) {
        return invidiousCache.list;
    }
    try {
        const res = await fetchWithTimeout('https://api.invidious.io/instances.json?sort_by=health', {
            headers: { 'User-Agent': 'Mozilla/5.0' }
        }, 7000);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => Array.isArray(item) && item[1] && item[1].type === 'https' && item[1].api === true && item[1].uri)
                    .map(item => String(item[1].uri).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    invidiousCache.list = [...new Set([...fresh, ...invidiousCache.list])].slice(0, 15);
                    invidiousCache.updatedAt = Date.now();
                    console.log(`[Invidious Auto] Loaded ${invidiousCache.list.length} live instances`);
                }
            }
        }
    } catch (e) {}
    return invidiousCache.list;
}

async function refreshPipedList(force = false) {
    if (!force && (Date.now() - pipedCache.updatedAt) < REGISTRY_TTL_MS) {
        return pipedCache.list;
    }
    try {
        const res = await fetchWithTimeout('https://piped-instances.kavin.rocks/', {
            headers: { 'User-Agent': 'Mozilla/5.0' }
        }, 7000);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => item && item.api_url && item.up_to_date !== false)
                    .map(item => String(item.api_url).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    pipedCache.list = [...new Set([...fresh, ...pipedCache.list])].slice(0, 15);
                    pipedCache.updatedAt = Date.now();
                    console.log(`[Piped Auto] Loaded ${pipedCache.list.length} live instances`);
                }
            }
        }
    } catch (e) {}
    return pipedCache.list;
}

function testTcpConnect(host, port, timeoutMs = 2200) {
    return new Promise(resolve => {
        const sock = new net.Socket();
        let done = false;
        const finish = ok => {
            if (done) return;
            done = true;
            sock.destroy();
            resolve(ok);
        };
        sock.setTimeout(timeoutMs);
        sock.once('connect', () => finish(true));
        sock.once('timeout', () => finish(false));
        sock.once('error', () => finish(false));
        sock.connect(port, host);
    });
}

async function refreshFreeProxyPool(force = false) {
    if (!force && freeProxyCache.working.length >= 3 && (Date.now() - freeProxyCache.updatedAt) < PROXY_TTL_MS) {
        return freeProxyCache.working;
    }
    if (freeProxyCache.refreshing) return freeProxyCache.refreshing;

    freeProxyCache.refreshing = (async () => {
        const sources = [
            { proto: 'http', url: 'https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=3000&country=all&ssl=yes&anonymity=elite' },
            { proto: 'socks5', url: 'https://api.proxyscrape.com/v2/?request=displayproxies&protocol=socks5&timeout=3000&country=all' },
            { proto: 'http', url: 'https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt' },
            { proto: 'socks5', url: 'https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/socks5.txt' }
        ];

        const candidates = [];
        await Promise.all(sources.map(async src => {
            try {
                const res = await fetchWithTimeout(src.url, {}, 5500);
                if (!res.ok) return;
                const txt = await res.text();
                const lines = txt.split(/\r?\n/).map(s => s.trim()).filter(l => /^\d+\.\d+\.\d+\.\d+:\d+$/.test(l));
                // ערבוב קל ובחירת עד 18 מועמדים מכל מקור
                for (let i = lines.length - 1; i > 0; i--) {
                    const j = Math.floor(Math.random() * (i + 1));
                    [lines[i], lines[j]] = [lines[j], lines[i]];
                }
                for (const hp of lines.slice(0, 18)) {
                    candidates.push({ proto: src.proto, hp });
                }
            } catch (e) {}
        }));

        const verified = [];
        const batchSize = 16;
        for (let i = 0; i < candidates.length && verified.length < 8; i += batchSize) {
            const batch = candidates.slice(i, i + batchSize);
            const results = await Promise.all(batch.map(async c => {
                const [host, portStr] = c.hp.split(':');
                const ok = await testTcpConnect(host, parseInt(portStr, 10), 2000);
                return ok ? `${c.proto}://${c.hp}` : null;
            }));
            for (const p of results) {
                if (p && !verified.includes(p)) verified.push(p);
            }
        }

        if (verified.length > 0) {
            freeProxyCache.working = verified;
            freeProxyCache.updatedAt = Date.now();
            console.log(`[FreeProxy Auto] Verified ${verified.length} reachable free proxies`);
        }
        return freeProxyCache.working;
    })().finally(() => {
        freeProxyCache.refreshing = null;
    });

    return freeProxyCache.refreshing;
}

// ==================== פונקציות ימות המשיח ו-Gemini ====================

async function uploadTextToExactPath(textContent, exactTargetPath, fileNameLabel = 'file.txt') {
    const form = new FormData();
    form.append('token', TOKEN);
    form.append('path', exactTargetPath);
    form.append('convertAudio', '0');
    form.append('file', new Blob([Buffer.from(textContent, 'utf8')], { type: 'text/plain; charset=utf-8' }), fileNameLabel);
    await fetchWithTimeout(`${YM}UploadFile`, { method: 'POST', body: form }, 12000);
}

async function getUserNameIfRegistered(phone) {
    if (userNamesCache.has(phone)) return userNamesCache.get(phone);
    const folderPath = `ivr2:/users/${phone}`;
    try {
        const url = `${YM}GetIVR2Dir?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath)}`;
        const res = await fetchWithTimeout(url, {}, 5000);
        if (res.ok) {
            const data = await res.json();
            const hasNameFile = (data.files || []).some(f => {
                const fname = (typeof f === 'string') ? f : (f && (f.name || f.fileName || ''));
                const low = String(fname).toLowerCase();
                return low === 'name.txt' || low === 'name.wav';
            });
            if (hasNameFile) {
                try {
                    const dlUrl = `${YM}DownloadFile?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath + '/name.txt')}`;
                    const dlRes = await fetchWithTimeout(dlUrl, {}, 4000);
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

async function ensurePlayfileExtension(folderPathStr) {
    const clean = String(folderPathStr).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    if (configuredPlayfileDirs.has(clean)) return;
    try {
        const body = new URLSearchParams({ token: TOKEN, path: `ivr2:/${clean}`, type: 'playfile' });
        const playfileIni = [
            'type=playfile',
            `playfile_end_goto=${YOUTUBE_MAIN_EXT}`,
            `empty_goto=${YOUTUBE_MAIN_EXT}`,
            `root_goto=${YOUTUBE_MAIN_EXT}`,
            `control_play_return=${YOUTUBE_MAIN_EXT}`,
            `control_play#=${YOUTUBE_MAIN_EXT}`
        ].join('\r\n') + '\r\n';

        await Promise.all([
            fetchWithTimeout(`${YM}UpdateExtension`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
                body
            }, 6000),
            uploadTextToExactPath(playfileIni, `ivr2:/${clean}/ext.ini`, 'ext.ini')
        ]);
        configuredPlayfileDirs.add(clean);
    } catch (e) {}
}

async function getNextFileNumberStr(folder, reserveCount = 1) {
    const cleanFolder = String(folder || '').replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    if (folderCounters[cleanFolder] !== undefined) {
        const startNum = folderCounters[cleanFolder] + 1;
        folderCounters[cleanFolder] += reserveCount;
        const result = [];
        for (let i = 0; i < reserveCount; i++) result.push(String(startNum + i).padStart(3, '0'));
        return reserveCount === 1 ? result[0] : result;
    }

    const folderPath = cleanFolder ? `ivr2:/${cleanFolder}` : `ivr2:/`;
    let maxExisting = -1;
    try {
        const url = `${YM}GetIVR2Dir?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(folderPath)}`;
        const res = await fetchWithTimeout(url, {}, 4500);
        if (res.ok) {
            const data = await res.json();
            for (const f of (data.files || [])) {
                const fname = (typeof f === 'string') ? f : (f && (f.name || f.fileName || ''));
                const m = String(fname).match(/^(\d+)\.(wav|tts|txt|mp3)$/i);
                if (m) {
                    const num = parseInt(m[1], 10);
                    if (!isNaN(num) && num < 900 && num > maxExisting) maxExisting = num;
                }
            }
        }
    } catch (e) {}

    const baseNum = Math.max(maxExisting, 0);
    const startNum = baseNum + 1;
    folderCounters[cleanFolder] = baseNum + reserveCount;
    const result = [];
    for (let i = 0; i < reserveCount; i++) result.push(String(startNum + i).padStart(3, '0'));
    return reserveCount === 1 ? result[0] : result;
}

async function uploadAudioBufferToExactPath(audioBuffer, exactTargetPath, fileNameLabel = 'audio.mp3', convertAudio = '1', timeoutMs = 45000) {
    const formData = new FormData();
    formData.append('token', TOKEN);
    formData.append('path', exactTargetPath);
    formData.append('convertAudio', String(convertAudio));
    formData.append('file', new Blob([audioBuffer], { type: 'audio/mpeg' }), fileNameLabel);

    const upRes = await fetchWithTimeout(`${YM}UploadFile`, { method: 'POST', body: formData }, timeoutMs);
    const upText = await upRes.text();
    console.log(`[Yemot Upload -> ${exactTargetPath}] (${audioBuffer.length} bytes) Response:`, upText.slice(0, 150));
    return upText;
}

async function saveAdminLogToExt8(callerPhone, userName, categoryLabel, searchQuery, downloadedTitle, statusText) {
    try {
        const nextNum = await getNextFileNumberStr(ADMIN_LOG_EXT, 1);
        const nowStr = new Date().toLocaleString('he-IL', { timeZone: 'Asia/Jerusalem' });
        const ttsSummary = `משתמש ${userName} טלפון ${callerPhone} חיפש ב${categoryLabel} את ${searchQuery}. סטטוס: ${statusText}`;
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

        await Promise.all([
            uploadTextToExactPath(ttsSummary, `ivr2:/${ADMIN_LOG_EXT}/${nextNum}.tts`, `${nextNum}.tts`),
            uploadTextToExactPath(txtDetails, `ivr2:/${ADMIN_LOG_EXT}/${nextNum}.txt`, `${nextNum}.txt`)
        ]);
    } catch (err) {}
}

async function downloadRecordingFromYemot(recordPath, apiDir) {
    const cleanPath = String(recordPath).replace(/^ivr2:\/*/, '').replace(/^\/*/, '');
    const cleanDir = String(apiDir || '').replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const candidates = [`ivr2:/${cleanPath}`, `ivr2:${cleanPath}`];
    if (cleanDir && !cleanPath.startsWith(cleanDir + '/')) candidates.unshift(`ivr2:/${cleanDir}/${cleanPath}`);
    if (!cleanPath.toLowerCase().endsWith('.wav')) {
        candidates.unshift(`ivr2:/${cleanPath}.wav`);
        if (cleanDir) candidates.unshift(`ivr2:/${cleanDir}/${cleanPath}.wav`);
    }

    let lastYemotResponse = '';
    for (const p of [...new Set(candidates)]) {
        const url = `${YM}DownloadFile?token=${encodeURIComponent(TOKEN)}&path=${encodeURIComponent(p)}`;
        try {
            const res = await fetchWithTimeout(url, {}, 8000);
            if (!res.ok) { lastYemotResponse = `HTTP_${res.status}`; continue; }
            const buf = Buffer.from(await res.arrayBuffer());
            const headStr = buf.toString('utf8', 0, Math.min(buf.length, 150));
            if (buf.length > 200 && !headStr.includes('responseStatus') && !headStr.includes('EXCEPTION')) return buf;
            lastYemotResponse = headStr;
        } catch (e) { lastYemotResponse = e.message; }
    }
    throw new Error('YEMOT_DOWNLOAD_ERR: ' + lastYemotResponse);
}

async function getFastGeminiModels() {
    const defaultFastOrder = [
        'gemini-flash-lite-latest',
        'gemini-flash-latest',
        'gemini-2.5-flash-lite',
        'gemini-2.5-flash'
    ];
    if (cachedModelName) return [cachedModelName, ...defaultFastOrder.filter(m => m !== cachedModelName)];
    try {
        const res = await fetchWithTimeout(`https://generativelanguage.googleapis.com/v1beta/models?key=${GEMINI_KEY}`, {}, 5000);
        if (res.ok) {
            const data = await res.json();
            const available = (data.models || [])
                .filter(m => (m.supportedGenerationMethods || []).includes('generateContent'))
                .map(m => m.name.replace('models/', ''))
                .filter(m => m.includes('flash') && !m.includes('tts') && !m.includes('image') && !m.includes('thinking'));
            if (available.length > 0) {
                const prioritized = [...defaultFastOrder.filter(m => available.includes(m)), ...available];
                const unique = [...new Set(prioritized)];
                cachedModelName = unique[0];
                return unique;
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
                    contents: [{ parts: [{ text: prompt }, { inlineData: { mimeType: 'audio/wav', data: audioBase64 } }] }],
                    generationConfig: { temperature: 0.1, maxOutputTokens: 60 }
                })
            }, 9000);
            if (res.ok) {
                cachedModelName = model;
                const data = await res.json();
                return data?.candidates?.[0]?.content?.parts?.[0]?.text || '';
            }
            lastErr = await res.text();
        } catch (err) { lastErr = err.message; }
    }
    throw new Error('GEMINI_ERR: ' + lastErr);
}

// ==================== 6 מנועי ההורדה החינמיים האוטומטיים ====================

function isHtmlBuffer(buf) {
    if (!buf || buf.length < 16) return true;
    const head = buf.toString('utf8', 0, Math.min(buf.length, 64)).trim().toLowerCase();
    return head.startsWith('<!doctype') || head.startsWith('<html') || head.startsWith('{"error');
}

function isValidMp3Header(buf) {
    if (!buf || buf.length < 1024) return false;
    if (buf[0] === 0x49 && buf[1] === 0x44 && buf[2] === 0x33) return true;
    if (buf[0] === 0xFF && (buf[1] & 0xE0) === 0xE0) return true;
    return false;
}

// מנוע א': InnerTube API ישיר (מהיר מאוד — ללא הפעלת תהליך חיצוני)
async function tryInnerTubeDirect(videoId) {
    const clients = [
        {
            name: 'ANDROID_VR',
            ua: 'com.google.android.apps.youtube.vr.oculus/1.60.19 (Linux; U; Android 12L; eureka-user Build/SQ3A.220605.009.A1) gzip',
            context: { client: { clientName: 'ANDROID_VR', clientVersion: '1.60.19', deviceMake: 'Oculus', deviceModel: 'Quest 3', androidSdkVersion: 32, hl: 'en', gl: 'US' } }
        },
        {
            name: 'IOS',
            ua: 'com.google.ios.youtube/19.45.4 (iPhone16,2; U; CPU iOS 18_1_0 like Mac OS X;)',
            context: { client: { clientName: 'IOS', clientVersion: '19.45.4', deviceMake: 'Apple', deviceModel: 'iPhone16,2', osName: 'iPhone', osVersion: '18.1.0.22B83', hl: 'en', gl: 'US' } }
        },
        {
            name: 'TVHTML5_SIMPLY_EMBEDDED_PLAYER',
            ua: 'Mozilla/5.0 (SMART-TV; LINUX; Tizen 6.0) AppleWebKit/537.36',
            context: {
                client: { clientName: 'TVHTML5_SIMPLY_EMBEDDED_PLAYER', clientVersion: '2.0', hl: 'en', gl: 'US' },
                thirdParty: { embedUrl: 'https://www.youtube.com/' }
            }
        }
    ];

    let lastErr = null;
    for (const c of clients) {
        try {
            const res = await fetchWithTimeout('https://www.youtube.com/youtubei/v1/player?prettyPrint=false', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'User-Agent': c.ua
                },
                body: JSON.stringify({
                    videoId,
                    context: c.context,
                    contentCheckOk: true,
                    racyCheckOk: true
                })
            }, 6500);

            if (!res.ok) { lastErr = new Error(`${c.name}: HTTP_${res.status}`); continue; }
            const data = await res.json();
            const status = data?.playabilityStatus?.status;
            if (status !== 'OK') {
                lastErr = new Error(`${c.name}: ${status || 'NOT_OK'} (${data?.playabilityStatus?.reason || ''})`);
                continue;
            }

            const formats = (data?.streamingData?.adaptiveFormats || [])
                .filter(f => f && f.url && String(f.mimeType || '').includes('audio/'));
            if (formats.length === 0) {
                lastErr = new Error(`${c.name}: no direct audio url`);
                continue;
            }

            // בוחרים את פורמט האודיו הקל ביותר (חיסכון בתעבורה ומהירות מקסימלית)
            formats.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
            const audioUrl = formats[0].url;

            const dlRes = await fetchWithTimeout(audioUrl, { headers: { 'User-Agent': c.ua } }, 25000);
            if (!dlRes.ok) { lastErr = new Error(`${c.name}_DL: HTTP_${dlRes.status}`); continue; }
            const buf = Buffer.from(await dlRes.arrayBuffer());
            if (buf.length > 8000 && !isHtmlBuffer(buf)) {
                return { buffer: buf, alreadyTrimmed: false };
            }
            lastErr = new Error(`${c.name}: empty/html audio`);
        } catch (err) {
            lastErr = err;
        }
    }
    throw lastErr || new Error('InnerTube failed');
}

// מנוע ב': yt-dlp מתעדכן אוטומטית כל 24 שעות (ישיר / עם עוגיות חינמיות / עם פרוקסי חינמי אוטומטי)
async function ensureYtDlpBinary(forceRefresh = false) {
    if (!forceRefresh && fs.existsSync(YTDLP_BIN_PATH)) {
        const stat = fs.statSync(YTDLP_BIN_PATH);
        if (stat.size > 1000000 && (Date.now() - stat.mtimeMs) < YTDLP_MAX_AGE_MS) {
            return YTDLP_BIN_PATH;
        }
    }
    if (ytdlpReadyPromise && !forceRefresh) return ytdlpReadyPromise;

    ytdlpReadyPromise = (async () => {
        const binUrl = 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux';
        console.log('[yt-dlp] Downloading latest yt-dlp_linux...');
        const res = await fetchWithTimeout(binUrl, {}, 45000);
        if (!res.ok) throw new Error(`yt-dlp download HTTP ${res.status}`);
        const buf = Buffer.from(await res.arrayBuffer());
        const tmpBin = YTDLP_BIN_PATH + '.tmp';
        await fs.promises.writeFile(tmpBin, buf);
        await fs.promises.chmod(tmpBin, 0o755);
        await fs.promises.rename(tmpBin, YTDLP_BIN_PATH);
        return YTDLP_BIN_PATH;
    })().catch(err => {
        ytdlpReadyPromise = null;
        throw err;
    });
    return ytdlpReadyPromise;
}

function runYtDlpOnce(binPath, videoId, startSec, durationSec, opts = {}) {
    return new Promise((resolve, reject) => {
        const prefix = `yt_${videoId}_${startSec}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
        const tmpl = path.join(os.tmpdir(), `${prefix}.%(ext)s`);
        const args = [
            '--no-playlist',
            '--no-check-certificates',
            '--no-cache-dir',
            '--force-ipv4',
            '--socket-timeout', String(opts.socketTimeout || 12),
            '--retries', '1',
            '-f', 'bestaudio[ext=m4a]/bestaudio[ext=webm]/bestaudio/worst',
            '--ffmpeg-location', ffmpegPath
        ];

        if (!opts.skipJsRuntime) args.push('--js-runtimes', 'node');
        if (opts.playerClients) args.push('--extractor-args', `youtube:player_client=${opts.playerClients}`);
        if (opts.proxyUrl) args.push('--proxy', opts.proxyUrl);
        if (opts.cookiesPath) args.push('--cookies', opts.cookiesPath);
        if (durationSec > 0) args.push('--download-sections', `*${startSec}-${startSec + durationSec}`);
        args.push('-o', tmpl, `https://www.youtube.com/watch?v=${videoId}`);

        execFile(binPath, args, { timeout: opts.execTimeout || 24000, maxBuffer: 6 * 1024 * 1024 }, (err, stdout, stderr) => {
            const files = fs.readdirSync(os.tmpdir()).filter(f => f.startsWith(prefix + '.') && !f.endsWith('.part'));
            if (files.length > 0) {
                const fullPath = path.join(os.tmpdir(), files[0]);
                if (fs.statSync(fullPath).size > 5000) {
                    return resolve({ filePath: fullPath, alreadyTrimmed: durationSec > 0 });
                }
                fs.promises.unlink(fullPath).catch(() => null);
            }
            const cleanErr = String(stderr || err?.message || 'yt-dlp failed')
                .split('\n')
                .filter(l => l.includes('ERROR:'))
                .slice(-2)
                .join(' | ') || String(err?.message || 'yt-dlp failed').slice(0, 160);
            reject(new Error(cleanErr));
        });
    });
}

async function tryYtDlpMode(mode, videoId, startSec, durationSec) {
    const binPath = await ensureYtDlpBinary(false);
    const cookiesPath = getCookiesFilePath();
    const attempts = [];

    if (mode === 'ytdlp_cookies') {
        if (!cookiesPath) throw new Error('SKIP: YT_COOKIES_B64 not set (optional)');
        attempts.push({ cookiesPath, playerClients: 'tv,web,mweb' });
        attempts.push({ cookiesPath, playerClients: 'web_safari,mweb' });
    } else if (mode === 'ytdlp_direct') {
        attempts.push({ playerClients: 'android_vr,tv_simply,ios' });
        attempts.push({ playerClients: 'mweb,web_embedded' });
    } else if (mode === 'ytdlp_free_proxy') {
        const proxies = await refreshFreeProxyPool(false);
        if (!proxies || proxies.length === 0) throw new Error('No reachable free proxies found');
        for (const p of proxies.slice(0, 3)) {
            attempts.push({
                proxyUrl: p,
                cookiesPath: cookiesPath || undefined,
                playerClients: 'android_vr,tv_simply,ios',
                socketTimeout: 9,
                execTimeout: 18000
            });
        }
    }

    let lastErr = null;
    for (const cfg of attempts) {
        try {
            return await runYtDlpOnce(binPath, videoId, startSec, durationSec, cfg);
        } catch (err) {
            lastErr = err;
            if (String(err.message).includes('no such option: --js-runtimes')) {
                try {
                    return await runYtDlpOnce(binPath, videoId, startSec, durationSec, { ...cfg, skipJsRuntime: true });
                } catch (e2) { lastErr = e2; }
            }
        }
    }

    if (mode === 'ytdlp_direct' && lastErr && String(lastErr.message).toLowerCase().includes('not a bot')) {
        setEngineCooldown('ytdlp_direct', 'YouTube bot check on datacenter IP');
    }
    throw lastErr || new Error(`${mode} failed`);
}

// מנוע ג': Invidious אוטומטי (עם הזרמה דרך השרת שלהם — עוקף חסימת IP של Render)
async function tryInvidiousAuto(videoId) {
    const instances = await refreshInvidiousList(false);
    let lastErr = null;

    for (const base of instances.slice(0, 5)) {
        try {
            const apiUrl = `${base}/api/v1/videos/${encodeURIComponent(videoId)}?fields=adaptiveFormats`;
            const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 5500);
            if (!res.ok) { lastErr = new Error(`${base}: HTTP_${res.status}`); continue; }
            const data = await res.json();

            const audioStreams = (data.adaptiveFormats || [])
                .filter(f => f && f.url && String(f.type || '').includes('audio/'));
            if (audioStreams.length === 0) { lastErr = new Error(`${base}: no audio`); continue; }

            audioStreams.sort((a, b) => (parseInt(a.bitrate, 10) || 999999) - (parseInt(b.bitrate, 10) || 999999));
            let streamUrl = audioStreams[0].url;
            if (streamUrl.startsWith('/')) streamUrl = base + streamUrl;

            // מעדיפים הזרמה דרך הפרוקסי הפנימי של Invidious (local=true) כדי שיוטיוב לא תראה את ה-IP של Render
            const proxiedUrl = streamUrl.includes(base)
                ? streamUrl
                : `${base}/latest_version?id=${encodeURIComponent(videoId)}&itag=${encodeURIComponent(audioStreams[0].itag || '140')}&local=true`;

            for (const tryUrl of [proxiedUrl, streamUrl]) {
                try {
                    const dlRes = await fetchWithTimeout(tryUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 22000);
                    if (!dlRes.ok) continue;
                    const buf = Buffer.from(await dlRes.arrayBuffer());
                    if (buf.length > 8000 && !isHtmlBuffer(buf)) {
                        return { buffer: buf, alreadyTrimmed: false };
                    }
                } catch (e) {}
            }
            lastErr = new Error(`${base}: stream download failed`);
        } catch (err) {
            lastErr = err;
        }
    }
    throw lastErr || new Error('All live Invidious instances failed');
}

// מנוע ד': Piped אוטומטי (מושך רשימת שרתים פעילים ומחליף אוטומטית)
async function tryPipedAuto(videoId) {
    const instances = await refreshPipedList(false);
    let lastErr = null;

    for (const base of instances.slice(0, 5)) {
        try {
            const apiUrl = `${base}/streams/${encodeURIComponent(videoId)}`;
            const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 5500);
            if (!res.ok) { lastErr = new Error(`${base}: HTTP_${res.status}`); continue; }
            const data = await res.json();

            const audioStreams = (data.audioStreams || []).filter(s => s && s.url);
            if (audioStreams.length === 0) { lastErr = new Error(`${base}: no audioStreams`); continue; }

            audioStreams.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
            const dlRes = await fetchWithTimeout(audioStreams[0].url, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 22000);
            if (!dlRes.ok) { lastErr = new Error(`${base}_DL: HTTP_${dlRes.status}`); continue; }

            const buf = Buffer.from(await dlRes.arrayBuffer());
            if (buf.length > 8000 && !isHtmlBuffer(buf)) {
                return { buffer: buf, alreadyTrimmed: false };
            }
            lastErr = new Error(`${base}: invalid audio`);
        } catch (err) {
            lastErr = err;
        }
    }
    throw lastErr || new Error('All live Piped instances failed');
}

// המרה וחיתוך חסכוני (32kbps מונו 16kHz — איכות טלפונית מצוינת + חיסכון מקסימלי בתעבורת Render)
async function finalizeToCompactMp3(rawResult, videoId, startSec, durationSec) {
    const { buffer, filePath, alreadyTrimmed } = rawResult;

    if (buffer && startSec === 0 && durationSec === 0 && isValidMp3Header(buffer) && buffer.length < 8 * 1024 * 1024) {
        return buffer;
    }

    const tmpIn = filePath || path.join(os.tmpdir(), `in_${videoId}_${startSec}_${Date.now()}.bin`);
    const tmpOut = path.join(os.tmpdir(), `out_${videoId}_${startSec}_${Date.now()}.mp3`);
    try {
        if (!filePath && buffer) {
            await fs.promises.writeFile(tmpIn, buffer);
        }

        try {
            await new Promise((resolve, reject) => {
                const ffTimer = setTimeout(() => reject(new Error('FFmpeg copy timeout')), 15000);
                let cmd = ffmpeg(tmpIn);
                if (!alreadyTrimmed && startSec > 0) cmd = cmd.setStartTime(startSec);
                if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
                cmd.format('mp3')
                    .audioCodec('copy')
                    .on('end', () => { clearTimeout(ffTimer); resolve(); })
                    .on('error', err => { clearTimeout(ffTimer); reject(err); })
                    .save(tmpOut);
            });
            const copiedBuf = await fs.promises.readFile(tmpOut);
            if (copiedBuf.length > 5000 && copiedBuf.length < 8 * 1024 * 1024) {
                return copiedBuf;
            }
        } catch (copyErr) {
            await new Promise((resolve, reject) => {
                const ffTimer = setTimeout(() => reject(new Error('FFmpeg encode timeout')), 45000);
                let cmd = ffmpeg(tmpIn);
                if (!alreadyTrimmed && startSec > 0) cmd = cmd.setStartTime(startSec);
                if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
                cmd.format('mp3')
                    .audioCodec('libmp3lame')
                    .audioBitrate('32k')
                    .audioChannels(1)
                    .audioFrequency(16000)
                    .outputOptions(['-q:a 9', '-threads 0'])
                    .on('end', () => { clearTimeout(ffTimer); resolve(); })
                    .on('error', err => { clearTimeout(ffTimer); reject(err); })
                    .save(tmpOut);
            });
            return await fs.promises.readFile(tmpOut);
        }
    } finally {
        fs.promises.unlink(tmpIn).catch(() => null);
        fs.promises.unlink(tmpOut).catch(() => null);
    }
}

async function runSingleEngine(engine, videoId, startSec, durationSec) {
    if (engine === 'ytdlp_cookies' || engine === 'ytdlp_direct' || engine === 'ytdlp_free_proxy') {
        return await tryYtDlpMode(engine, videoId, startSec, durationSec);
    }
    if (engine === 'innertube_direct') return await tryInnerTubeDirect(videoId);
    if (engine === 'invidious_auto') return await tryInvidiousAuto(videoId);
    if (engine === 'piped_auto') return await tryPipedAuto(videoId);
    throw new Error(`Unknown engine: ${engine}`);
}

async function downloadSegmentBufferFree(videoId, startSec = 0, durationSec = 900) {
    const errors = [];
    for (const engine of ENGINE_ORDER) {
        if (isEngineCoolingDown(engine)) {
            errors.push(`${engine}: paused (${engineCooldown.get(engine)?.reason})`);
            continue;
        }
        try {
            const t0 = Date.now();
            const rawRes = await runSingleEngine(engine, videoId, startSec, durationSec);
            const mp3Buf = await finalizeToCompactMp3(rawRes, videoId, startSec, durationSec);
            console.log(`[Download OK] engine=${engine} video=${videoId} bytes=${mp3Buf.length} ms=${Date.now() - t0}`);
            return mp3Buf;
        } catch (err) {
            const msg = err.message || String(err);
            if (!msg.startsWith('SKIP:')) console.warn(`[Engine Fail] ${engine}:`, msg);
            errors.push(`${engine}: ${msg}`);
        }
    }
    throw new Error(`ALL_FREE_ENGINES_FAILED -> ${errors.join(' ; ')}`);
}

async function downloadAndPreparePlayback(videoId, livePlayFolder, archiveUserFolder, durationSeconds = 0) {
    const cleanLive = String(livePlayFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const cleanArchive = String(archiveUserFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');

    const isLongVideo = durationSeconds > 900;
    const firstChunkSec = isLongVideo ? 900 : 0;

    const [firstMp3Buf, , archNum] = await Promise.all([
        downloadSegmentBufferFree(videoId, 0, firstChunkSec),
        ensurePlayfileExtension(cleanArchive),
        getNextFileNumberStr(cleanArchive, 1)
    ]);

    const archPath = `ivr2:/${cleanArchive}/${archNum}.mp3`;
    await uploadAudioBufferToExactPath(firstMp3Buf, archPath, `${archNum}.mp3`, '1', 35000);

    if (!isLongVideo) return `f-/${cleanArchive}/${archNum}`;

    const TOTAL_PARTS = Math.min(6, Math.max(2, Math.ceil((durationSeconds - 10) / 900)));
    const rawPartNums = await getNextFileNumberStr(cleanLive, TOTAL_PARTS - 1);
    const extraNums = Array.isArray(rawPartNums) ? rawPartNums : [rawPartNums];
    const chainedPlayCommand = [`f-/${cleanArchive}/${archNum}`, ...extraNums.map(n => `f-/${cleanLive}/${n}`)].join('.');

    (async () => {
        for (let i = 1; i < TOTAL_PARTS; i++) {
            const startSec = i * 900;
            try {
                const partBuf = await downloadSegmentBufferFree(videoId, startSec, 900);
                if (partBuf && partBuf.length > 5000) {
                    const liveNum = extraNums[i - 1];
                    await uploadAudioBufferToExactPath(partBuf, `ivr2:/${cleanLive}/${liveNum}.mp3`, `${liveNum}.mp3`, '1', 45000);
                }
            } catch (e) {
                console.warn(`[Part ${i + 1} Error]`, e.message);
            }
        }
    })();

    return chainedPlayCommand;
}

// ==================== נתיבי בדיקה ואבחון ====================
function setCors(res) {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
}

app.get('/', (req, res) => {
    res.send('YouTube Personal Line Server v4.1 (100% Free Auto-Resilient Multi-Engine) OK');
});

app.get('/health', async (req, res) => {
    setCors(res);
    const cooldowns = {};
    for (const [k, v] of engineCooldown.entries()) {
        if (Date.now() < v.until) cooldowns[k] = { reason: v.reason, remainingSec: Math.round((v.until - Date.now()) / 1000) };
    }
    res.json({
        version: '4.1.0 (100% Free)',
        engineOrder: ENGINE_ORDER,
        autoPools: {
            invidiousInstances: invidiousCache.list.length,
            pipedInstances: pipedCache.list.length,
            verifiedFreeProxies: freeProxyCache.working.length
        },
        configured: {
            cookies_optional: Boolean(YT_COOKIES_B64),
            youtube_api_keys: YT_KEYS.length,
            gemini_key: Boolean(GEMINI_KEY),
            yemot_token: Boolean(TOKEN)
        },
        cooldowns
    });
});

app.get('/test', async (req, res) => {
    setCors(res);
    if (req.query.reset === '1') engineCooldown.clear();
    const videoId = String(req.query.v || 'jNQXAC9IVRw').replace(/[^a-zA-Z0-9_-]/g, '');
    const results = [];

    for (const engine of ENGINE_ORDER) {
        const t0 = Date.now();
        try {
            const rawRes = await runSingleEngine(engine, videoId, 0, 10);
            const mp3Buf = await finalizeToCompactMp3(rawRes, videoId, 0, 10);
            results.push({ engine, status: 'OK', bytes: mp3Buf.length, ms: Date.now() - t0 });
        } catch (err) {
            const msg = err.message || String(err);
            results.push({
                engine,
                status: msg.startsWith('SKIP:') ? 'SKIPPED' : 'FAIL',
                error: msg,
                ms: Date.now() - t0
            });
        }
    }
    res.json({ version: '4.1.0', videoId, results });
});

// ==================== מנוע ימות המשיח ====================
const MAIN_MENU_TEXT = 'ברוכים הבאים לחיפוש ביוטיוב! לשמיעת הפלייליסט שלכם הקישו 1 לשמיעת שיעורי התורה שלכם הקישו 2 לחיפוש מוזיקה חדש הקישו 3 לחיפוש שיעור חדש הקישו 4! שימו לב אם הסרטון ארוך מ 15 דקות הוא עולה בחלקים לשלוחת הפלייליסט או לשלוחת השיעורי תורה ! לחזרה לשלוחה הקודמת הקישו כוכבית! הקו מנוטר משתמש שיחפש תוכן לא ראוי יחסם ';

app.all(['/yemot', '/yemot/:e'], async (req, res) => {
    const q = { ...req.query, ...req.body };
    res.type('text/plain; charset=utf-8');

    try {
        const callerPhone = lastVal(q.ApiPhone).replace(/[^0-9]/g, '');
        const callId = lastVal(q.ApiCallId);

        if (q.hangup === 'yes') {
            if (callerPhone) userSessionState.delete(callerPhone);
            return res.send('noop');
        }

        if (!callerPhone) {
            return res.send(`id_list_message=t-שגיאה בזיהוי מספר הטלפון&go_to_folder=${YOUTUBE_MAIN_EXT}`);
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
                return state.isMusic
                    ? res.send(`read=t-אנא אמרו שוב את שם השיר המבוקש ובסיום הקישו סולמית=SearchMusic,no,record,/${tempRecFolder},${recNum},no,7,1`)
                    : res.send(`read=t-אנא אמרו שוב את שם השיעור המבוקש ובסיום הקישו סולמית=SearchTorah,no,record,/${tempRecFolder},${recNum},no,7,1`);
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
            const pageStart = (state.pageIndex || 0) * RESULTS_PER_PAGE;
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
                const playCmd = await downloadAndPreparePlayback(chosenVideo.videoId, tempRecFolder, archiveFolder, chosenVideo.durationSeconds || 0);
                saveAdminLogToExt8(callerPhone, registeredName, categoryLabel, cleanQuery, chosenVideo.title, `הורד בהצלחה לשלוחה ${archiveFolder}`);
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                const durationPart = chosenVideo.durationText ? ` באורך ${chosenVideo.durationText}` : '';
                return res.send(`id_list_message=t-משמיע ${chosenVideo.title}${durationPart}.${playCmd}&go_to_folder=${YOUTUBE_MAIN_EXT}`);
            } catch (audioErr) {
                console.error('[Download Error]', audioErr.message);
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
            try { audioBuf = await downloadRecordingFromYemot(recordPath, lastVal(q.ApiExtension)); }
            catch (dlErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה בהורדת ההקלטה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            let rawText = '';
            try { rawText = await transcribeAudio(audioBuf.toString('base64')); }
            catch (gemErr) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה במנוע זיהוי הדיבור&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const cleanQuery = sanitizeForYemotTts(rawText, 55);
            if (!cleanQuery) {
                userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-לא הצלחתי לשמוע את הבקשה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const ytBaseUrl = `https://www.googleapis.com/youtube/v3/search?part=snippet&q=${encodeURIComponent(cleanQuery)}&type=video&maxResults=28`;
            let ytData;
            try {
                const ytResult = await fetchYouTubeWithFallback(ytBaseUrl, 6000);
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

            try {
                const idsList = validItems.map(v => v.videoId).join(',');
                const durBaseUrl = `https://www.googleapis.com/youtube/v3/videos?part=contentDetails&id=${encodeURIComponent(idsList)}`;
                const { res: durRes, data: durData } = await fetchYouTubeWithFallback(durBaseUrl, 4500);
                if (durRes && durRes.ok) {
                    const durMap = new Map();
                    for (const vItem of (durData.items || [])) {
                        if (vItem.id && vItem.contentDetails?.duration) {
                            durMap.set(vItem.id, parseIsoDurationToHebrew(vItem.contentDetails.duration));
                        }
                    }
                    for (const item of validItems) {
                        const dInfo = durMap.get(item.videoId);
                        if (dInfo) { item.durationSeconds = dInfo.seconds; item.durationText = dInfo.text; }
                    }
                }
            } catch (e) {}

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
                await ensurePlayfileExtension(musicExtFolder);
                userSessionState.set(callerPhone, { step: 'IN_PLAYLIST', callId });
                return res.send(`go_to_folder=/${musicExtFolder}`);
            }
            if (menuChoice === '2') {
                await ensurePlayfileExtension(torahExtFolder);
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
            try { audioBuf = await downloadRecordingFromYemot(recordName, lastVal(q.ApiExtension)); }
            catch (dlErr) {
                return res.send(`read=t-שגיאה בקליטת ההקלטה אנא הקליטו שוב את שמכם ובסיום הקישו סולמית=RecordName,no,record,/${tempRecFolder},name_rec,no,7,1`);
            }

            let rawName = '';
            try { rawName = await transcribeAudio(audioBuf.toString('base64')); } catch (e) {}
            const cleanName = sanitizeForYemotTts(rawName, 40) || 'משתמש רשום';

            await Promise.all([
                uploadAudioBufferToExactPath(audioBuf, `ivr2:/${userFolder}/name.wav`, 'name.wav', '0'),
                uploadTextToExactPath(cleanName, `ivr2:/${userFolder}/name.txt`, 'name.txt'),
                ensurePlayfileExtension(musicExtFolder),
                ensurePlayfileExtension(torahExtFolder)
            ]);
            userNamesCache.set(callerPhone, cleanName);
            saveAdminLogToExt8(callerPhone, cleanName, 'רישום למערכת', 'הקלטת שם משתמש', '', 'נרשם בהצלחה');

            userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`id_list_message=t-שלום ${cleanName} נרשמתם בהצלחה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        userSessionState.set(callerPhone, { step: 'WAIT_MENU', callId });
        return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
    } catch (e) {
        console.error('[Yemot Route Error]', e.message);
        if (!res.headersSent) {
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }
    }
});

const port = process.env.PORT || 3000;
app.listen(port, '0.0.0.0', () => {
    console.log(`=== Server v4.1 (100% Free Auto-Resilient) Ready on port ${port} ===`);
    console.log(`[Engine Order] ${ENGINE_ORDER.join(' -> ')}`);
    // חימום אוטומטי ברקע מיד בעליית השרת
    ensureYtDlpBinary(false).catch(() => null);
    refreshInvidiousList(true).catch(() => null);
    refreshPipedList(true).catch(() => null);
    refreshFreeProxyPool(true).catch(() => null);
});
