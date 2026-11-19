const express = require('express');
const ffmpeg = require('fluent-ffmpeg');
const ffmpegPath = require('ffmpeg-static');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { execFile } = require('child_process');

ffmpeg.setFfmpegPath(ffmpegPath);

const app = express();
app.use(express.urlencoded({ extended: true }));
app.use(express.json());

// ==================== הגדרות סביבה ====================
const TOKEN = (process.env.YEMOT_TOKEN || '').trim();
const GEMINI_KEY = (process.env.GEMINI_API_KEY || '').trim();
const YT_KEY = (process.env.YOUTUBE_API_KEY || '').trim();
const YT_KEY2 = (process.env.YOUTUBE_API_KEY2 || '').trim();
const YT_KEYS = [YT_KEY, YT_KEY2].filter(Boolean);
let activeYtKeyIndex = 0;

const RAPID_CONFIGS = [
    {
        id: 'rapidapi1',
        key: (process.env.RAPIDAPI_KEY || '').trim(),
        host: (process.env.RAPIDAPI_HOST || 'youtube-info-download-api.p.rapidapi.com').trim(),
        endpoint: (process.env.RAPIDAPI_ENDPOINT || 'auto').trim()
    },
    {
        id: 'rapidapi2',
        key: (process.env.RAPIDAPI_KEY2 || '').trim(),
        host: (process.env.RAPIDAPI_HOST2 || '').trim(),
        endpoint: (process.env.RAPIDAPI_ENDPOINT2 || 'auto').trim()
    }
];

const YT_COOKIES_B64 = (process.env.YT_COOKIES_B64 || '').trim();
const COBALT_API_URL = (process.env.COBALT_API_URL || '').trim().replace(/\/+$/, '');
const PROXY_URL = (process.env.PROXY_URL || '').trim();

const YM = 'https://www.call2all.co.il/ym/api/';
const ADMIN_LOG_EXT = '8';
const YOUTUBE_MAIN_EXT = '/1/0000000144';
const RESULTS_PER_PAGE = 7;

// איזון מהירות ותעבורה (מכסת 5GB של Render): קבצי MP3 עד 10MB עולים ישירות; מעל זה מקודד ל-32k מונו (~3.5MB ל-15 דק')
const DIRECT_MP3_MAX_BYTES = 10 * 1024 * 1024;

const BASE_ENGINE_ORDER = [
    'rapidapi1',
    'ytdlp_cookies',
    'rapidapi2',
    'cobalt',
    'invidious_parallel',
    'piped_parallel',
    'innertube_direct',
    'ytdlp_direct'
];
let lastWinningEngine = null;

let cachedModelName = null;
const folderCounters = {};
const userNamesCache = new Map();
const configuredPlayfileDirs = new Set();
const userSessionState = new Map();

// מטמון השמעה חוזרת (שעתיים) — חוסך 100% זמן, תעבורת Render ומכסות API
const recentPlaybackCache = new Map();
const PLAYBACK_CACHE_TTL_MS = 2 * 60 * 60 * 1000;

const workingRapidTemplate = new Map();
const engineCooldown = new Map();
const COOLDOWN_MS = 10 * 60 * 1000;

const YTDLP_BIN_PATH = path.join(os.tmpdir(), 'yt-dlp-linux');
const YTDLP_CACHE_DIR = path.join(os.tmpdir(), 'ytdlp-cache');
const YTDLP_MAX_AGE_MS = 24 * 60 * 60 * 1000;
const COOKIES_FILE_PATH = path.join(os.tmpdir(), 'yt_cookies.txt');
let ytdlpReadyPromise = null;
let cookiesStatus = { initialized: false, format: 'none', count: 0 };

try { fs.mkdirSync(YTDLP_CACHE_DIR, { recursive: true }); } catch (e) {}

let invidiousCache = {
    updatedAt: 0,
    list: [
        'https://inv.nadeko.net',
        'https://yewtu.be',
        'https://invidious.nerdvpn.de',
        'https://inv.tux.pizza',
        'https://iv.ggtyler.dev'
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
const REGISTRY_TTL_MS = 30 * 60 * 1000;

function getDynamicEngineOrder() {
    if (lastWinningEngine && BASE_ENGINE_ORDER.includes(lastWinningEngine) && !isEngineCoolingDown(lastWinningEngine)) {
        return [lastWinningEngine, ...BASE_ENGINE_ORDER.filter(e => e !== lastWinningEngine)];
    }
    return BASE_ENGINE_ORDER;
}

function setEngineCooldown(engine, reason, ms = COOLDOWN_MS) {
    engineCooldown.set(engine, { until: Date.now() + ms, reason: String(reason).slice(0, 180) });
    if (lastWinningEngine === engine) lastWinningEngine = null;
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

// ==================== ממיר עוגיות אוטומטי (JSON / Base64 -> Netscape) ====================
function convertJsonCookiesToNetscape(jsonText) {
    const parsed = JSON.parse(jsonText);
    const arr = Array.isArray(parsed) ? parsed : (parsed.cookies || parsed.data || []);
    if (!Array.isArray(arr) || arr.length === 0) return null;

    const lines = ['# Netscape HTTP Cookie File', '# Auto-converted from JSON by Server v4.5'];
    let count = 0;

    for (const c of arr) {
        if (!c || typeof c !== 'object' || !c.name) continue;
        let domain = String(c.domain || '.youtube.com').trim();
        let includeSub;
        if (c.hostOnly === true) {
            includeSub = 'FALSE';
        } else if (c.hostOnly === false) {
            includeSub = 'TRUE';
            if (!domain.startsWith('.')) domain = '.' + domain;
        } else {
            includeSub = domain.startsWith('.') ? 'TRUE' : 'FALSE';
        }
        const cookiePath = String(c.path || '/').trim() || '/';
        const secure = c.secure ? 'TRUE' : 'FALSE';

        let rawExp = c.expirationDate ?? c.expires ?? c.expiry ?? 0;
        let expInt = 0;
        if (typeof rawExp === 'number' && isFinite(rawExp) && rawExp > 0) {
            expInt = Math.floor(rawExp > 1e12 ? rawExp / 1000 : rawExp);
        } else if (typeof rawExp === 'string' && rawExp.trim()) {
            const num = Number(rawExp);
            if (!isNaN(num) && num > 0) expInt = Math.floor(num > 1e12 ? num / 1000 : num);
            else {
                const dt = Date.parse(rawExp);
                if (!isNaN(dt) && dt > 0) expInt = Math.floor(dt / 1000);
            }
        }

        const name = String(c.name).replace(/[\t\r\n]/g, ' ');
        const value = String(c.value ?? '').replace(/[\t\r\n]/g, ' ');
        lines.push(`${domain}\t${includeSub}\t${cookiePath}\t${secure}\t${expInt}\t${name}\t${value}`);
        count++;
    }

    if (count === 0) return null;
    return { text: lines.join('\n') + '\n', count };
}

function getCookiesFilePath() {
    if (!YT_COOKIES_B64) return null;
    if (cookiesStatus.initialized && fs.existsSync(COOKIES_FILE_PATH)) return COOKIES_FILE_PATH;

    try {
        let content = YT_COOKIES_B64.trim();
        if (!content.startsWith('[') && !content.startsWith('{') && !content.includes('\t') && !content.includes('Netscape')) {
            try {
                const decoded = Buffer.from(content, 'base64').toString('utf8').trim();
                if (decoded.startsWith('[') || decoded.startsWith('{') || decoded.includes('\t') || decoded.includes('youtube.com')) {
                    content = decoded;
                }
            } catch (e) {}
        }

        if (content.startsWith('[') || content.startsWith('{')) {
            const converted = convertJsonCookiesToNetscape(content);
            if (converted) {
                fs.writeFileSync(COOKIES_FILE_PATH, converted.text, 'utf8');
                cookiesStatus = { initialized: true, format: 'json_auto_converted_to_netscape', count: converted.count };
                console.log(`[Cookies] Auto-converted ${converted.count} JSON cookies -> Netscape cookies.txt`);
                return COOKIES_FILE_PATH;
            }
        }

        if (content.includes('\t') && content.length > 20) {
            if (!content.startsWith('# Netscape') && !content.startsWith('# HTTP Cookie File')) {
                content = '# Netscape HTTP Cookie File\n' + content;
            }
            const cookieLines = content.split(/\r?\n/).filter(l => l.trim() && !l.startsWith('#') && l.includes('\t')).length;
            fs.writeFileSync(COOKIES_FILE_PATH, content, 'utf8');
            cookiesStatus = { initialized: true, format: 'netscape', count: cookieLines };
            return COOKIES_FILE_PATH;
        }
    } catch (e) {
        console.warn('[Cookies Init Error]', e.message);
    }
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

async function fetchWithTimeout(url, options = {}, timeout = 15000) {
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

async function refreshInvidiousList(force = false) {
    if (!force && (Date.now() - invidiousCache.updatedAt) < REGISTRY_TTL_MS) return invidiousCache.list;
    try {
        const res = await fetchWithTimeout('https://api.invidious.io/instances.json?sort_by=health', {
            headers: { 'User-Agent': 'Mozilla/5.0' }
        }, 6500);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => Array.isArray(item) && item[1] && item[1].type === 'https' && item[1].api === true && item[1].uri)
                    .map(item => String(item[1].uri).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    invidiousCache.list = [...new Set([...fresh, ...invidiousCache.list])].slice(0, 14);
                    invidiousCache.updatedAt = Date.now();
                }
            }
        }
    } catch (e) {}
    return invidiousCache.list;
}

async function refreshPipedList(force = false) {
    if (!force && (Date.now() - pipedCache.updatedAt) < REGISTRY_TTL_MS) return pipedCache.list;
    try {
        const res = await fetchWithTimeout('https://piped-instances.kavin.rocks/', {
            headers: { 'User-Agent': 'Mozilla/5.0' }
        }, 6500);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => item && item.api_url && item.up_to_date !== false)
                    .map(item => String(item.api_url).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    pipedCache.list = [...new Set([...fresh, ...pipedCache.list])].slice(0, 14);
                    pipedCache.updatedAt = Date.now();
                }
            }
        }
    } catch (e) {}
    return pipedCache.list;
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

// ==================== מנועי ההורדה (גרסה 4.5 — תיקון EJS + RapidAPI) ====================

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

function extractAudioUrlFromRapidPayload(payload, depth = 0) {
    if (!payload || typeof payload !== 'object' || depth > 5) return null;

    const directCandidates = [
        payload.link, payload.download_url, payload.downloadUrl,
        payload.audio_url, payload.audioUrl, payload.dlink,
        payload.mp3, payload.file, payload.url
    ];
    for (const c of directCandidates) {
        if (typeof c === 'string' && /^https?:\/\//i.test(c) && !c.includes('youtube.com/watch') && !c.includes('youtu.be/')) {
            return c;
        }
    }

    if (payload.audios && Array.isArray(payload.audios.items)) {
        const sorted = [...payload.audios.items].sort((a, b) => (a.size || 9e9) - (b.size || 9e9));
        for (const it of sorted) {
            if (it && typeof it.url === 'string' && it.url.startsWith('http')) return it.url;
        }
    }
    if (Array.isArray(payload.adaptiveFormats)) {
        const audioOnly = payload.adaptiveFormats
            .filter(f => String(f.mimeType || '').includes('audio') && f.url)
            .sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
        if (audioOnly.length > 0) return audioOnly[0].url;
    }

    const lists = [payload.audios, payload.audio_formats, payload.formats, payload.items, payload.data, payload.result];
    for (const lst of lists) {
        if (Array.isArray(lst)) {
            for (const item of lst) {
                if (!item || typeof item !== 'object') continue;
                const u = item.download_url || item.url || item.link;
                if (typeof u === 'string' && /^https?:\/\//i.test(u)) return u;
            }
        }
    }
    if (payload.data && typeof payload.data === 'object') {
        const nested = extractAudioUrlFromRapidPayload(payload.data, depth + 1);
        if (nested) return nested;
    }
    if (payload.result && typeof payload.result === 'object') {
        return extractAudioUrlFromRapidPayload(payload.result, depth + 1);
    }
    return null;
}

function getRapidCandidateTemplates(cfg) {
    if (cfg.endpoint && cfg.endpoint.toLowerCase() !== 'auto') {
        return [cfg.endpoint];
    }
    const remembered = workingRapidTemplate.get(cfg.host);
    const h = cfg.host.toLowerCase();
    let list = [];
    if (h.includes('youtube-info-download-api')) {
        // קודם MP3 64kbps (ישיר ללא FFmpeg), ואם נתקע ב-Initialising עובר ל-m4a (ללא המרה בשרת המרוחק)
        list = [
            '/ajax/download.php?url={url}&format=mp3&audio_quality=64',
            '/ajax/download.php?url={url}&format=m4a'
        ];
    } else if (h.includes('youtube-mp36') || h.includes('yt-api')) {
        list = ['/dl?id={id}', '/dl?url={url}'];
    } else if (h.includes('youtube-media-downloader')) {
        list = ['/v2/video/details?videoId={id}', '/v2/video/details?videoId={id}&audios=true'];
    } else if (h.includes('youtube-mp3')) {
        list = ['/v1/social/youtube/audio?id={id}', '/dl?id={id}', '/download?id={id}'];
    } else {
        list = ['/dl?id={id}', '/ajax/download.php?url={url}&format=mp3&audio_quality=64', '/v2/video/details?videoId={id}'];
    }
    return remembered ? [remembered, ...list.filter(t => t !== remembered)] : list;
}

function renderRapidTemplate(tpl, host, videoId, startSec, durationSec) {
    const ytUrl = `https://www.youtube.com/watch?v=${videoId}`;
    const endSec = durationSec > 0 ? (startSec + durationSec) : 0;
    let ep = tpl
        .replace(/\{id\}/g, encodeURIComponent(videoId))
        .replace(/\{url\}/g, encodeURIComponent(ytUrl))
        .replace(/\{start\}/g, String(startSec))
        .replace(/\{end\}/g, String(endSec));
    if (!ep.startsWith('/')) ep = '/' + ep;
    if (ep.includes('/ajax/download.php') && durationSec > 0) {
        if (startSec > 0 && !ep.includes('start_time=')) ep += `&start_time=${startSec}`;
        if (endSec > 0 && !ep.includes('end_time=')) ep += `&end_time=${endSec}`;
    }
    return { url: `https://${host}${ep}`, supportsTrim: ep.includes('end_time=') };
}

async function tryRapidApiEngine(cfg, videoId, startSec, durationSec) {
    if (!cfg.key || !cfg.host) throw new Error(`SKIP: ${cfg.id} not configured`);

    const headers = { 'x-rapidapi-key': cfg.key, 'x-rapidapi-host': cfg.host };
    const templates = getRapidCandidateTemplates(cfg);
    let lastErr = null;
    let all404 = true;

    for (const tpl of templates) {
        const { url: endpointUrl, supportsTrim } = renderRapidTemplate(tpl, cfg.host, videoId, startSec, durationSec);
        try {
            const res = await fetchWithTimeout(endpointUrl, { headers }, 22000);
            if (res.status === 404) {
                lastErr = new Error(`${cfg.id}: HTTP_404 on ${tpl}`);
                continue;
            }
            all404 = false;
            if (!res.ok) {
                if ([401, 403, 429].includes(res.status)) {
                    setEngineCooldown(cfg.id, `HTTP_${res.status} on ${cfg.host}`);
                }
                throw new Error(`${cfg.id}: HTTP_${res.status}`);
            }

            const json = await res.json();
            let resolvedUrl = extractAudioUrlFromRapidPayload(json);

            // דגימה תקינה לפי התיעוד הרשמי: כל 1.2 שניות (אפס rate-limit, אפס מכסה על progress_url)
            if (!resolvedUrl && (json.progress_url || json.id || String(json.status || '').toLowerCase() === 'processing')) {
                const jobUrl = json.progress_url || (json.id ? `https://${cfg.host}/api/progress?id=${encodeURIComponent(json.id)}` : endpointUrl);
                const isRapidHostJob = jobUrl.includes(cfg.host);
                const pollIntervalMs = 1200;
                const maxAttempts = 50; // עד 60 שניות אם ההתקדמות זזה
                let lastProgressNum = -1;
                let lastProgressStr = '';
                let stalledAtInitSince = Date.now();
                let stalledInit = false;

                for (let i = 0; i < maxAttempts; i++) {
                    await new Promise(r => setTimeout(r, pollIntervalMs));
                    const pHeaders = isRapidHostJob ? headers : {};
                    const pRes = await fetchWithTimeout(jobUrl, { headers: pHeaders }, 10000);
                    if (!pRes.ok) continue;
                    const pJson = await pRes.json();

                    const pNum = Number(pJson.progress);
                    const pTxt = String(pJson.text || pJson.status || '');
                    lastProgressStr = `${pJson.progress ?? ''}/${pTxt}`;

                    resolvedUrl = extractAudioUrlFromRapidPayload(pJson);
                    if (resolvedUrl) break;

                    const st = pTxt.toLowerCase();
                    if (st === 'failed' || st === 'error' || st === 'fail' || st === 'expired') {
                        throw new Error(`${cfg.id}_JOB_FAILED: ${pJson.msg || pJson.message || st}`);
                    }

                    // זיהוי תקיעה ב-Initialising (כמו progress=21 שלא זז 22 שניות) -> עובר מיד לניסיון m4a
                    if (!isNaN(pNum) && pNum > lastProgressNum) {
                        lastProgressNum = pNum;
                        stalledAtInitSince = Date.now();
                    } else if ((isNaN(pNum) || pNum < 100) && (Date.now() - stalledAtInitSince) > 22000) {
                        stalledInit = true;
                        break;
                    }
                }

                if (!resolvedUrl) {
                    const reason = stalledInit
                        ? `${cfg.id}: Stalled at ${lastProgressStr} for 22s (${tpl})`
                        : `${cfg.id}: Conversion timeout after 60s (progress=${lastProgressStr})`;
                    lastErr = new Error(reason);
                    // אם נתקע ב-mp3 ויש נתיב m4a בתור — מנסים m4a!
                    if (stalledInit && tpl.includes('format=mp3')) {
                        console.warn(`[RapidAPI] ${reason} -> retrying with m4a...`);
                        continue;
                    }
                    throw lastErr;
                }
            }

            if (!resolvedUrl) {
                lastErr = new Error(`${cfg.id}: No download_url returned on ${tpl}`);
                continue;
            }

            const dlRes = await fetchWithTimeout(resolvedUrl, {}, 45000);
            if (!dlRes.ok) throw new Error(`${cfg.id}_DL: HTTP_${dlRes.status}`);
            const buf = Buffer.from(await dlRes.arrayBuffer());
            if (buf.length < 8000 || isHtmlBuffer(buf)) {
                throw new Error(`${cfg.id}: Invalid audio bytes (${buf.length})`);
            }

            workingRapidTemplate.set(cfg.host, tpl);
            return { buffer: buf, alreadyTrimmed: supportsTrim, detail: tpl };
        } catch (err) {
            lastErr = err;
            if (!String(err.message).includes('HTTP_404') && !String(err.message).includes('Stalled at')) {
                all404 = false;
                break;
            }
        }
    }

    if (all404) {
        setEngineCooldown(cfg.id, `All endpoints returned 404 on ${cfg.host}`);
    }
    throw lastErr || new Error(`${cfg.id} failed`);
}

async function tryCobaltEngine(videoId) {
    if (!COBALT_API_URL) throw new Error('SKIP: COBALT_API_URL not set');
    const res = await fetchWithTimeout(COBALT_API_URL, {
        method: 'POST',
        headers: { 'Accept': 'application/json', 'Content-Type': 'application/json' },
        body: JSON.stringify({
            url: `https://www.youtube.com/watch?v=${videoId}`,
            downloadMode: 'audio',
            audioFormat: 'mp3',
            audioBitrate: '64'
        })
    }, 15000);
    if (!res.ok) {
        if ([401, 403, 404].includes(res.status)) setEngineCooldown('cobalt', `HTTP_${res.status}`);
        throw new Error(`COBALT HTTP_${res.status}`);
    }
    const json = await res.json();
    const audioUrl = json.url || (Array.isArray(json.picker) && json.picker[0]?.url);
    if (!audioUrl) throw new Error('COBALT no url');
    const dlRes = await fetchWithTimeout(audioUrl, {}, 35000);
    if (!dlRes.ok) throw new Error(`COBALT_DL HTTP_${dlRes.status}`);
    const buf = Buffer.from(await dlRes.arrayBuffer());
    if (buf.length < 8000 || isHtmlBuffer(buf)) throw new Error('COBALT invalid audio');
    return { buffer: buf, alreadyTrimmed: false };
}

async function tryInvidiousParallel(videoId) {
    const instances = await refreshInvidiousList(false);
    const batch = instances.slice(0, 5);

    const fetchOne = async (base) => {
        const apiUrl = `${base}/api/v1/videos/${encodeURIComponent(videoId)}?fields=adaptiveFormats`;
        const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 5000);
        if (!res.ok) throw new Error(`${base}: HTTP_${res.status}`);
        const data = await res.json();
        const audioStreams = (data.adaptiveFormats || []).filter(f => f && f.url && String(f.type || '').includes('audio/'));
        if (audioStreams.length === 0) throw new Error(`${base}: no audio`);

        audioStreams.sort((a, b) => (parseInt(a.bitrate, 10) || 999999) - (parseInt(b.bitrate, 10) || 999999));
        let streamUrl = audioStreams[0].url;
        if (streamUrl.startsWith('/')) streamUrl = base + streamUrl;
        const proxiedUrl = streamUrl.includes(base)
            ? streamUrl
            : `${base}/latest_version?id=${encodeURIComponent(videoId)}&itag=${encodeURIComponent(audioStreams[0].itag || '140')}&local=true`;

        for (const tryUrl of [proxiedUrl, streamUrl]) {
            try {
                const dlRes = await fetchWithTimeout(tryUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 18000);
                if (!dlRes.ok) continue;
                const buf = Buffer.from(await dlRes.arrayBuffer());
                if (buf.length > 8000 && !isHtmlBuffer(buf)) {
                    return { buffer: buf, alreadyTrimmed: false, detail: base };
                }
            } catch (e) {}
        }
        throw new Error(`${base}: stream failed`);
    };

    try {
        return await Promise.any(batch.map(fetchOne));
    } catch (agg) {
        throw new Error(`Invidious(${batch.length}): ${agg?.errors?.[0]?.message || 'failed'}`);
    }
}

async function tryPipedParallel(videoId) {
    const instances = await refreshPipedList(false);
    const batch = instances.slice(0, 5);

    const fetchOne = async (base) => {
        const apiUrl = `${base}/streams/${encodeURIComponent(videoId)}`;
        const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 5000);
        if (!res.ok) throw new Error(`${base}: HTTP_${res.status}`);
        const data = await res.json();
        const audioStreams = (data.audioStreams || []).filter(s => s && s.url);
        if (audioStreams.length === 0) throw new Error(`${base}: no audioStreams`);

        audioStreams.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
        const dlRes = await fetchWithTimeout(audioStreams[0].url, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 18000);
        if (!dlRes.ok) throw new Error(`${base}_DL: HTTP_${dlRes.status}`);
        const buf = Buffer.from(await dlRes.arrayBuffer());
        if (buf.length > 8000 && !isHtmlBuffer(buf)) {
            return { buffer: buf, alreadyTrimmed: false, detail: base };
        }
        throw new Error(`${base}: invalid audio`);
    };

    try {
        return await Promise.any(batch.map(fetchOne));
    } catch (agg) {
        throw new Error(`Piped(${batch.length}): ${agg?.errors?.[0]?.message || 'failed'}`);
    }
}

async function tryInnerTubeDirect(videoId) {
    const clients = [
        {
            name: 'ANDROID_VR',
            ua: 'com.google.android.apps.youtube.vr.oculus/1.60.19 (Linux; U; Android 12L; eureka-user Build/SQ3A.220605.009.A1) gzip',
            context: { client: { clientName: 'ANDROID_VR', clientVersion: '1.60.19', deviceMake: 'Oculus', deviceModel: 'Quest 3', androidSdkVersion: 32, hl: 'en', gl: 'US' } }
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
                headers: { 'Content-Type': 'application/json', 'User-Agent': c.ua },
                body: JSON.stringify({ videoId, context: c.context, contentCheckOk: true, racyCheckOk: true })
            }, 6000);
            if (!res.ok) { lastErr = new Error(`${c.name}: HTTP_${res.status}`); continue; }
            const data = await res.json();
            if (data?.playabilityStatus?.status !== 'OK') {
                lastErr = new Error(`${c.name}: ${data?.playabilityStatus?.status || 'NOT_OK'}`);
                continue;
            }
            const formats = (data?.streamingData?.adaptiveFormats || [])
                .filter(f => f && f.url && String(f.mimeType || '').includes('audio/'));
            if (formats.length === 0) { lastErr = new Error(`${c.name}: no direct url`); continue; }
            formats.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
            const dlRes = await fetchWithTimeout(formats[0].url, { headers: { 'User-Agent': c.ua } }, 18000);
            if (!dlRes.ok) { lastErr = new Error(`${c.name}_DL: HTTP_${dlRes.status}`); continue; }
            const buf = Buffer.from(await dlRes.arrayBuffer());
            if (buf.length > 8000 && !isHtmlBuffer(buf)) return { buffer: buf, alreadyTrimmed: false, detail: c.name };
        } catch (err) { lastErr = err; }
    }
    throw lastErr || new Error('InnerTube failed');
}

// ==================== yt-dlp 2026 (עם EJS + Node path + שגיאות מלאות) ====================
async function ensureYtDlpBinary(forceRefresh = false) {
    if (!forceRefresh && fs.existsSync(YTDLP_BIN_PATH)) {
        const stat = fs.statSync(YTDLP_BIN_PATH);
        if (stat.size > 1000000 && (Date.now() - stat.mtimeMs) < YTDLP_MAX_AGE_MS) return YTDLP_BIN_PATH;
    }
    if (ytdlpReadyPromise && !forceRefresh) return ytdlpReadyPromise;

    ytdlpReadyPromise = (async () => {
        const binUrl = 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux';
        const res = await fetchWithTimeout(binUrl, {}, 40000);
        if (!res.ok) throw new Error(`yt-dlp download HTTP ${res.status}`);
        const buf = Buffer.from(await res.arrayBuffer());
        const tmpBin = YTDLP_BIN_PATH + '.tmp';
        await fs.promises.writeFile(tmpBin, buf);
        await fs.promises.chmod(tmpBin, 0o755);
        await fs.promises.rename(tmpBin, YTDLP_BIN_PATH);
        return YTDLP_BIN_PATH;
    })().catch(err => { ytdlpReadyPromise = null; throw err; });
    return ytdlpReadyPromise;
}

function extractRealYtDlpError(stderr, err) {
    const lines = String(stderr || '').split(/\r?\n/).map(l => l.trim()).filter(Boolean);
    const errLines = lines.filter(l => /error:/i.test(l));
    if (err && err.killed) {
        const tail = (errLines.length > 0 ? errLines : lines).slice(-2).join(' | ');
        return `TIMEOUT (${err.signal || 'killed'})${tail ? ': ' + tail : ''}`.slice(0, 260);
    }
    if (errLines.length > 0) return errLines.slice(-2).join(' | ').slice(0, 260);
    if (lines.length > 0) return lines.slice(-3).join(' | ').slice(0, 260);
    return String(err?.message || 'yt-dlp failed').slice(0, 220);
}

function runYtDlpOnce(binPath, videoId, startSec, durationSec, opts = {}) {
    return new Promise((resolve, reject) => {
        const prefix = `yt_${videoId}_${startSec}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
        const tmpl = path.join(os.tmpdir(), `${prefix}.%(ext)s`);
        const args = [
            '--no-playlist',
            '--no-check-certificates',
            '--cache-dir', YTDLP_CACHE_DIR,
            '--force-ipv4',
            '--socket-timeout', '15',
            '--retries', '2',
            '-f', 'worstaudio[abr>=32]/bestaudio[abr<=96]/bestaudio[ext=m4a]/bestaudio/worst',
            '--ffmpeg-location', ffmpegPath
        ];

        // חובה ב-yt-dlp 2026: מפעיל את Node המדויק של השרת + סקריפט EJS מ-GitHub (נשמר במטמון)
        if (!opts.skipEjs) {
            args.push('--js-runtimes', `node:${process.execPath}`);
            args.push('--remote-components', 'ejs:github');
        }
        if (opts.playerClients) args.push('--extractor-args', `youtube:player_client=${opts.playerClients}`);
        if (opts.proxyUrl) args.push('--proxy', opts.proxyUrl);
        if (opts.cookiesPath) args.push('--cookies', opts.cookiesPath);
        if (durationSec > 0) args.push('--download-sections', `*${startSec}-${startSec + durationSec}`);
        args.push('-o', tmpl, `https://www.youtube.com/watch?v=${videoId}`);

        const execTimeout = durationSec > 0 ? 48000 : 35000;
        execFile(binPath, args, { timeout: execTimeout, maxBuffer: 6 * 1024 * 1024 }, (err, stdout, stderr) => {
            const files = fs.readdirSync(os.tmpdir()).filter(f => f.startsWith(prefix + '.') && !f.endsWith('.part'));
            if (files.length > 0) {
                const fullPath = path.join(os.tmpdir(), files[0]);
                if (fs.statSync(fullPath).size > 5000) {
                    return resolve({ filePath: fullPath, alreadyTrimmed: durationSec > 0, detail: opts.playerClients || 'default+ejs' });
                }
                fs.promises.unlink(fullPath).catch(() => null);
            }
            reject(new Error(extractRealYtDlpError(stderr, err)));
        });
    });
}

async function tryYtDlpMode(mode, videoId, startSec, durationSec) {
    const binPath = await ensureYtDlpBinary(false);
    const cookiesPath = getCookiesFilePath();
    const attempts = [];

    if (mode === 'ytdlp_cookies') {
        if (!cookiesPath && !PROXY_URL) throw new Error('SKIP: YT_COOKIES_B64 / PROXY_URL not set');
        // ברירת המחדל הרשמית של yt-dlp 2026 עם עוגיות + EJS, ואחריה tv/mweb
        attempts.push({ cookiesPath: cookiesPath || undefined, proxyUrl: PROXY_URL || undefined });
        attempts.push({ cookiesPath: cookiesPath || undefined, proxyUrl: PROXY_URL || undefined, playerClients: 'tv,mweb,web' });
    } else if (mode === 'ytdlp_direct') {
        attempts.push({ playerClients: 'android_vr,tv_simply' });
        attempts.push({});
    }

    let lastErr = null;
    for (const cfg of attempts) {
        try {
            return await runYtDlpOnce(binPath, videoId, startSec, durationSec, cfg);
        } catch (err) {
            lastErr = err;
            const msg = String(err.message || '');
            if (msg.includes('no such option')) {
                try {
                    return await runYtDlpOnce(binPath, videoId, startSec, durationSec, { ...cfg, skipEjs: true });
                } catch (e2) { lastErr = e2; }
            }
        }
    }
    if (lastErr) {
        const low = String(lastErr.message).toLowerCase();
        // משהה רק על חסימה קשיחה אמיתית — לא על Timeout חד-פעמי!
        if (low.includes('not a bot') || low.includes('sign in') || low.includes('http error 403')) {
            setEngineCooldown(mode, lastErr.message);
        }
    }
    throw lastErr || new Error(`${mode} failed`);
}

// חימום מוקדם של EJS Solver בעליית השרת (חוסך זמן בשיחה הראשונה)
async function prewarmYtDlpEjs() {
    try {
        const binPath = await ensureYtDlpBinary(false);
        const args = [
            '--simulate', '--skip-download', '--no-playlist',
            '--cache-dir', YTDLP_CACHE_DIR,
            '--js-runtimes', `node:${process.execPath}`,
            '--remote-components', 'ejs:github',
            'https://www.youtube.com/watch?v=jNQXAC9IVRw'
        ];
        const cookiesPath = getCookiesFilePath();
        if (cookiesPath) args.splice(args.length - 1, 0, '--cookies', cookiesPath);
        execFile(binPath, args, { timeout: 25000 }, (err, stdout, stderr) => {
            if (!err) console.log('[yt-dlp EJS] Prewarmed & cached successfully');
            else console.log('[yt-dlp EJS] Prewarm info:', extractRealYtDlpError(stderr, err));
        });
    } catch (e) {}
}

// מעבר ישיר ללא קידוד מחדש לכל MP3 מוכן עד 10MB, וקידוד מהיר 32k מונו כשצריך
async function finalizeToCompactMp3(rawResult, videoId, startSec, durationSec) {
    const { buffer, filePath, alreadyTrimmed } = rawResult;

    if (buffer && isValidMp3Header(buffer) && buffer.length < DIRECT_MP3_MAX_BYTES && (alreadyTrimmed || (startSec === 0 && durationSec === 0))) {
        return buffer;
    }

    const tmpIn = filePath || path.join(os.tmpdir(), `in_${videoId}_${startSec}_${Date.now()}.bin`);
    const tmpOut = path.join(os.tmpdir(), `out_${videoId}_${startSec}_${Date.now()}.mp3`);
    try {
        if (!filePath && buffer) await fs.promises.writeFile(tmpIn, buffer);

        let copySucceeded = false;
        try {
            await new Promise((resolve, reject) => {
                const ffTimer = setTimeout(() => reject(new Error('FFmpeg copy timeout')), 12000);
                let cmd = ffmpeg(tmpIn);
                if (!alreadyTrimmed && startSec > 0) cmd = cmd.setStartTime(startSec);
                if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
                cmd.format('mp3').audioCodec('copy')
                    .on('end', () => { clearTimeout(ffTimer); resolve(); })
                    .on('error', err => { clearTimeout(ffTimer); reject(err); })
                    .save(tmpOut);
            });
            const copiedBuf = await fs.promises.readFile(tmpOut);
            if (copiedBuf.length > 5000 && copiedBuf.length < DIRECT_MP3_MAX_BYTES) {
                copySucceeded = true;
                return copiedBuf;
            }
        } catch (copyErr) {}

        if (!copySucceeded) {
            await fs.promises.unlink(tmpOut).catch(() => null);
            await new Promise((resolve, reject) => {
                const ffTimer = setTimeout(() => reject(new Error('FFmpeg encode timeout')), 55000);
                let cmd = ffmpeg(tmpIn);
                if (!alreadyTrimmed && startSec > 0) cmd = cmd.setStartTime(startSec);
                if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
                cmd.format('mp3')
                    .audioCodec('libmp3lame')
                    .audioBitrate('32k')
                    .audioChannels(1)
                    .audioFrequency(16000)
                    .outputOptions(['-compression_level 9', '-threads 0'])
                    .on('end', () => { clearTimeout(ffTimer); resolve(); })
                    .on('error', err => { clearTimeout(ffTimer); reject(err); })
                    .save(tmpOut);
            });
            const encBuf = await fs.promises.readFile(tmpOut);
            if (encBuf.length < 2000) throw new Error('Encoded MP3 empty');
            return encBuf;
        }
    } finally {
        fs.promises.unlink(tmpIn).catch(() => null);
        fs.promises.unlink(tmpOut).catch(() => null);
    }
}

async function runSingleEngine(engine, videoId, startSec, durationSec) {
    if (engine === 'rapidapi1') return await tryRapidApiEngine(RAPID_CONFIGS[0], videoId, startSec, durationSec);
    if (engine === 'rapidapi2') return await tryRapidApiEngine(RAPID_CONFIGS[1], videoId, startSec, durationSec);
    if (engine === 'ytdlp_cookies' || engine === 'ytdlp_direct') return await tryYtDlpMode(engine, videoId, startSec, durationSec);
    if (engine === 'cobalt') return await tryCobaltEngine(videoId);
    if (engine === 'invidious_parallel') return await tryInvidiousParallel(videoId);
    if (engine === 'piped_parallel') return await tryPipedParallel(videoId);
    if (engine === 'innertube_direct') return await tryInnerTubeDirect(videoId);
    throw new Error(`Unknown engine: ${engine}`);
}

async function downloadSegmentBufferHybrid(videoId, startSec = 0, durationSec = 900) {
    const errors = [];
    const order = getDynamicEngineOrder();
    for (const engine of order) {
        if (isEngineCoolingDown(engine)) {
            errors.push(`${engine}: paused (${engineCooldown.get(engine)?.reason})`);
            continue;
        }
        try {
            const t0 = Date.now();
            const rawRes = await runSingleEngine(engine, videoId, startSec, durationSec);
            const mp3Buf = await finalizeToCompactMp3(rawRes, videoId, startSec, durationSec);
            lastWinningEngine = engine;
            console.log(`[Download OK] engine=${engine} (${rawRes.detail || 'ok'}) video=${videoId} seg=${startSec}-${startSec + durationSec} bytes=${mp3Buf.length} ms=${Date.now() - t0}`);
            return mp3Buf;
        } catch (err) {
            const msg = err.message || String(err);
            if (!msg.startsWith('SKIP:')) console.warn(`[Engine Fail] ${engine}:`, msg);
            errors.push(`${engine}: ${msg}`);
        }
    }
    throw new Error(`ALL_ENGINES_FAILED -> ${errors.join(' ; ')}`);
}

async function downloadAndPreparePlayback(videoId, livePlayFolder, archiveUserFolder, durationSeconds = 0) {
    const cleanLive = String(livePlayFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const cleanArchive = String(archiveUserFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');

    const cacheKey = `${cleanArchive}:${videoId}`;
    const cached = recentPlaybackCache.get(cacheKey);
    if (cached && (Date.now() - cached.ts) < PLAYBACK_CACHE_TTL_MS) {
        console.log(`[Cache Hit] Instant replay for ${cacheKey} -> ${cached.playCmd}`);
        return cached.playCmd;
    }

    const isLongVideo = durationSeconds > 900;
    const firstChunkSec = isLongVideo ? 900 : 0;

    const [firstMp3Buf, , archNum] = await Promise.all([
        downloadSegmentBufferHybrid(videoId, 0, firstChunkSec),
        ensurePlayfileExtension(cleanArchive),
        getNextFileNumberStr(cleanArchive, 1)
    ]);

    const archPath = `ivr2:/${cleanArchive}/${archNum}.mp3`;
    await uploadAudioBufferToExactPath(firstMp3Buf, archPath, `${archNum}.mp3`, '1', 35000);

    if (!isLongVideo) {
        const playCmd = `f-/${cleanArchive}/${archNum}`;
        recentPlaybackCache.set(cacheKey, { playCmd, ts: Date.now() });
        return playCmd;
    }

    const TOTAL_PARTS = Math.min(8, Math.max(2, Math.ceil((durationSeconds - 10) / 900)));
    const rawPartNums = await getNextFileNumberStr(cleanLive, TOTAL_PARTS - 1);
    const extraNums = Array.isArray(rawPartNums) ? rawPartNums : [rawPartNums];
    const chainedPlayCommand = [`f-/${cleanArchive}/${archNum}`, ...extraNums.map(n => `f-/${cleanLive}/${n}`)].join('.');

    recentPlaybackCache.set(cacheKey, { playCmd: chainedPlayCommand, ts: Date.now() });

    (async () => {
        for (let i = 1; i < TOTAL_PARTS; i++) {
            const startSec = i * 900;
            try {
                const partBuf = await downloadSegmentBufferHybrid(videoId, startSec, 900);
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
    res.send('YouTube Personal Line Server v4.5 (yt-dlp EJS 2026 + Smart RapidAPI Stall Recovery) OK');
});

app.get('/health', (req, res) => {
    setCors(res);
    getCookiesFilePath();
    const cooldowns = {};
    for (const [k, v] of engineCooldown.entries()) {
        if (Date.now() < v.until) cooldowns[k] = { reason: v.reason, remainingSec: Math.round((v.until - Date.now()) / 1000) };
    }
    res.json({
        version: '4.5.0',
        nodePath: process.execPath,
        activeEngineOrder: getDynamicEngineOrder(),
        lastWinningEngine,
        cookies: cookiesStatus,
        configured: {
            rapidapi1: Boolean(RAPID_CONFIGS[0].key && RAPID_CONFIGS[0].host),
            rapidapi1_host: RAPID_CONFIGS[0].host || null,
            rapidapi2: Boolean(RAPID_CONFIGS[1].key && RAPID_CONFIGS[1].host),
            ytdlp_cookies: Boolean(YT_COOKIES_B64),
            cobalt: Boolean(COBALT_API_URL),
            proxy: Boolean(PROXY_URL),
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
    const dur = parseInt(req.query.dur || '15', 10) || 15;
    const results = [];

    for (const engine of getDynamicEngineOrder()) {
        const t0 = Date.now();
        try {
            const rawRes = await runSingleEngine(engine, videoId, 0, dur);
            const mp3Buf = await finalizeToCompactMp3(rawRes, videoId, 0, dur);
            results.push({ engine, status: 'OK', detail: rawRes.detail || '', bytes: mp3Buf.length, ms: Date.now() - t0 });
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
    res.json({ version: '4.5.0', cookies: cookiesStatus, videoId, results });
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

            try {
                const [playCmd, regName] = await Promise.all([
                    downloadAndPreparePlayback(chosenVideo.videoId, tempRecFolder, archiveFolder, chosenVideo.durationSeconds || 0),
                    getUserNameIfRegistered(callerPhone).catch(() => null)
                ]);
                saveAdminLogToExt8(callerPhone, regName || 'משתמש רשום', categoryLabel, cleanQuery, chosenVideo.title, `הורד בהצלחה לשלוחה ${archiveFolder}`);
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

            let audioBuf, registeredName;
            try {
                const [dlBuf, rName] = await Promise.all([
                    downloadRecordingFromYemot(recordPath, lastVal(q.ApiExtension)),
                    getUserNameIfRegistered(callerPhone).catch(() => null)
                ]);
                audioBuf = dlBuf;
                registeredName = rName || 'משתמש רשום';
            } catch (dlErr) {
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
    console.log(`=== Server v4.5 (yt-dlp EJS 2026 + Smart RapidAPI) Ready on port ${port} ===`);
    getCookiesFilePath();
    console.log(`[Engine Order] ${getDynamicEngineOrder().join(' -> ')}`);
    prewarmYtDlpEjs().catch(() => null);
    refreshInvidiousList(true).catch(() => null);
    refreshPipedList(true).catch(() => null);
});
