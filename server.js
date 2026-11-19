const express = require('express');
const ffmpeg = require('fluent-ffmpeg');
const ffmpegPath = require('ffmpeg-static');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { Readable } = require('stream');
const { pipeline } = require('stream/promises');
const { spawn } = require('child_process');

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

const APIFY_TOKEN = (process.env.APIFY_TOKEN || '').trim();
const APIFY_ACTOR = (process.env.APIFY_ACTOR || 'johnvc~youtube-download-api').trim();

const PRIMARY_RAPID_KEY = (process.env.RAPIDAPI_KEY || '').trim();
const RAPID_CONFIGS = [
    {
        id: 'rapidapi1',
        key: PRIMARY_RAPID_KEY,
        host: (process.env.RAPIDAPI_HOST || 'youtube-info-download-api.p.rapidapi.com').trim(),
        endpoint: (process.env.RAPIDAPI_ENDPOINT || 'auto').trim()
    },
    {
        id: 'rapidapi2',
        key: (process.env.RAPIDAPI_KEY2 || PRIMARY_RAPID_KEY).trim(),
        host: (process.env.RAPIDAPI_HOST2 || '').trim(),
        endpoint: (process.env.RAPIDAPI_ENDPOINT2 || 'auto').trim()
    }
];

const YT_COOKIES_B64 = (process.env.YT_COOKIES_B64 || '').trim();
const COBALT_API_URL = (process.env.COBALT_API_URL || '').trim().replace(/\/+$/, '');
const PROXY_URL = (process.env.PROXY_URL || '').trim();

const AUDIO_MODE = (process.env.AUDIO_MODE || 'fast').trim().toLowerCase();
const DIRECT_MP3_MAX_BYTES = AUDIO_MODE === 'saver' ? (3.2 * 1024 * 1024) : (10.5 * 1024 * 1024);
const MAX_DOWNLOAD_DISK_BYTES = 180 * 1024 * 1024; // מגן דיסק לשיעורים ארוכים במיוחד

const YM = 'https://www.call2all.co.il/ym/api/';
const ADMIN_LOG_EXT = (process.env.ADMIN_LOG_EXT || '8').replace(/^\/+|\/+$/g, '') || '8';

// שלוחת חזרה דינמית (תיקון #4): נלקחת מ-MAIN_EXT או מזוהה אוטומטית מהשיחה (ApiExtension)
function normalizeExtPath(raw, fallback = '/9') {
    const cleaned = String(raw || '').replace(/^ivr2:/i, '').replace(/\/+/g, '/').replace(/\/$/, '').trim();
    if (!cleaned || cleaned === '/') return fallback;
    return cleaned.startsWith('/') ? cleaned : '/' + cleaned;
}
const CONFIGURED_MAIN_EXT = process.env.MAIN_EXT ? normalizeExtPath(process.env.MAIN_EXT, '/9') : '';
let detectedMainExt = CONFIGURED_MAIN_EXT || '/9';
function getReturnMainExt(apiExtensionParam) {
    if (CONFIGURED_MAIN_EXT) return CONFIGURED_MAIN_EXT;
    if (apiExtensionParam) {
        const norm = normalizeExtPath(apiExtensionParam, '');
        if (norm && !norm.startsWith('/1/') && !norm.startsWith('/2/')) {
            detectedMainExt = norm;
        }
    }
    return detectedMainExt;
}

const RESULTS_PER_PAGE = 7;
const CHUNK_SEC = 900;
const MAX_PARTS = 12;

const BASE_ENGINE_ORDER = [
    'rapidapi1',
    'rapidapi2',
    'apify',
    'ytdlp_proxy_nocookies',
    'cobalt',
    'ytdlp_cookies',
    'ytdlp_direct',
    'invidious_parallel',
    'piped_parallel',
    'innertube_direct'
];
let lastWinningEngine = null;

let cachedModelName = null;
const folderCounters = {};
const userNamesCache = new Map();
const configuredPlayfileDirs = new Set();
const userSessionState = new Map(); // phone -> { ..., updatedAt }

// מטמון השמעה בטוח (תיקון #5): שומר סטטוס מלא ('uploading' | 'ready') כדי לא לנגן חלקים חסרים
const recentPlaybackCache = new Map(); // key -> { playCmd, status, ts, totalParts, uploadedCount }
const PLAYBACK_CACHE_TTL_MS = 2 * 60 * 60 * 1000;
const SESSION_TTL_MS = 45 * 60 * 1000;

const workingRapidTemplate = new Map();
const engineCooldown = new Map();
const engineConsecutiveTimeouts = new Map();
const COOLDOWN_MS = 25 * 60 * 1000;
const SHORT_TIMEOUT_COOLDOWN_MS = 3 * 60 * 1000;

const STATE_FILE_PATH = path.join(os.tmpdir(), 'engine_state_v5.json');
const YTDLP_BIN_PATH = path.join(os.tmpdir(), 'yt-dlp-linux');
const YTDLP_CACHE_DIR = path.join(os.tmpdir(), 'ytdlp-cache');
const YTDLP_MAX_AGE_MS = 24 * 60 * 60 * 1000;
const COOKIES_FILE_PATH = path.join(os.tmpdir(), 'yt_cookies.txt');
let ytdlpReadyPromise = null;
let cookiesStatus = { initialized: false, format: 'none', count: 0 };
let activeBackgroundJobs = 0;

try { fs.mkdirSync(YTDLP_CACHE_DIR, { recursive: true }); } catch (e) {}

// שמירה וטעינה של מצב מנועים לדיסק (תיקון #8)
function persistEngineState() {
    try {
        const now = Date.now();
        const cooldowns = {};
        for (const [k, v] of engineCooldown.entries()) {
            if (v.until > now) cooldowns[k] = v;
        }
        const templates = {};
        for (const [k, v] of workingRapidTemplate.entries()) templates[k] = v;
        fs.writeFileSync(STATE_FILE_PATH, JSON.stringify({ lastWinningEngine, cooldowns, templates }), 'utf8');
    } catch (e) {}
}

function loadEngineState() {
    try {
        if (!fs.existsSync(STATE_FILE_PATH)) return;
        const raw = JSON.parse(fs.readFileSync(STATE_FILE_PATH, 'utf8'));
        const now = Date.now();
        if (raw.lastWinningEngine && BASE_ENGINE_ORDER.includes(raw.lastWinningEngine)) {
            lastWinningEngine = raw.lastWinningEngine;
        }
        for (const [k, v] of Object.entries(raw.cooldowns || {})) {
            if (v && v.until > now) engineCooldown.set(k, v);
        }
        for (const [k, v] of Object.entries(raw.templates || {})) {
            if (typeof v === 'string' && !v.includes('format=m4a')) workingRapidTemplate.set(k, v);
        }
    } catch (e) {}
}
loadEngineState();

// ניקוי תקופתי של זיכרון ומטמונים ישנים (מונע זליגות RAM)
setInterval(() => {
    const now = Date.now();
    for (const [phone, st] of userSessionState.entries()) {
        if (!st || (now - (st.updatedAt || 0)) > SESSION_TTL_MS) userSessionState.delete(phone);
    }
    for (const [k, v] of recentPlaybackCache.entries()) {
        if (!v || (now - v.ts) > PLAYBACK_CACHE_TTL_MS) recentPlaybackCache.delete(k);
    }
    for (const [k, v] of engineCooldown.entries()) {
        if (now > v.until) engineCooldown.delete(k);
    }
}, 10 * 60 * 1000).unref();

let invidiousCache = {
    updatedAt: 0,
    list: [
        'https://inv.nadeko.net',
        'https://yewtu.be',
        'https://invidious.nerdvpn.de',
        'https://inv.tux.pizza'
    ]
};

let pipedCache = {
    updatedAt: 0,
    list: [
        'https://pipedapi.kavin.rocks',
        'https://pipedapi.adminforge.de',
        'https://api.piped.private.coffee',
        'https://pipedapi.leptons.xyz'
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
    persistEngineState();
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

// ==================== ממיר עוגיות אופציונלי ====================
function convertJsonCookiesToNetscape(jsonText) {
    const parsed = JSON.parse(jsonText);
    const arr = Array.isArray(parsed) ? parsed : (parsed.cookies || parsed.data || []);
    if (!Array.isArray(arr) || arr.length === 0) return null;

    const lines = ['# Netscape HTTP Cookie File', '# Auto-converted from JSON by Server v5.0'];
    let count = 0;

    for (const c of arr) {
        if (!c || typeof c !== 'object' || !c.name) continue;
        let domain = String(c.domain || '.youtube.com').trim();
        let includeSub;
        if (c.hostOnly === true) includeSub = 'FALSE';
        else if (c.hostOnly === false) {
            includeSub = 'TRUE';
            if (!domain.startsWith('.')) domain = '.' + domain;
        } else includeSub = domain.startsWith('.') ? 'TRUE' : 'FALSE';

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

// ==================== הזרמת הורדות ישירות לדיסק (תיקון #3 — מניעת OOM ב-512MB RAM!) ====================
async function readFileHead(filePath, maxBytes = 64) {
    const fh = await fs.promises.open(filePath, 'r');
    try {
        const buf = Buffer.alloc(maxBytes);
        const { bytesRead } = await fh.read(buf, 0, maxBytes, 0);
        return buf.subarray(0, bytesRead);
    } finally {
        await fh.close();
    }
}

function isHtmlHead(buf) {
    if (!buf || buf.length < 8) return true;
    const head = buf.toString('utf8', 0, Math.min(buf.length, 64)).trim().toLowerCase();
    return head.startsWith('<!doctype') || head.startsWith('<html') || head.startsWith('{"error') || head.startsWith('<?xml');
}

function isMp3Head(buf) {
    if (!buf || buf.length < 4) return false;
    if (buf[0] === 0x49 && buf[1] === 0x44 && buf[2] === 0x33) return true;
    if (buf[0] === 0xFF && (buf[1] & 0xE0) === 0xE0) return true;
    return false;
}

async function downloadUrlToTempFile(url, headers = {}, timeoutMs = 45000, tag = 'dl') {
    const tmpBase = path.join(os.tmpdir(), `${tag}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`);
    const tmpBin = `${tmpBase}.bin`;

    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeoutMs);

    try {
        const res = await fetch(url, { headers, signal: controller.signal });
        if (!res.ok) throw new Error(`HTTP_${res.status}`);

        const contentLen = parseInt(res.headers.get('content-length') || '0', 10);
        if (contentLen > MAX_DOWNLOAD_DISK_BYTES) {
            throw new Error(`FILE_TOO_LARGE (${Math.round(contentLen / (1024 * 1024))}MB)`);
        }

        if (!res.body) throw new Error('EMPTY_BODY');

        let downloadedBytes = 0;
        const ws = fs.createWriteStream(tmpBin);
        const nodeStream = Readable.fromWeb(res.body);

        nodeStream.on('data', chunk => {
            downloadedBytes += chunk.length;
            if (downloadedBytes > MAX_DOWNLOAD_DISK_BYTES) {
                controller.abort();
                nodeStream.destroy(new Error('FILE_TOO_LARGE_STREAM'));
            }
        });

        await pipeline(nodeStream, ws);
        clearTimeout(timer);

        const stat = await fs.promises.stat(tmpBin);
        if (stat.size < 8000) throw new Error(`AUDIO_TOO_SMALL (${stat.size} bytes)`);

        const head = await readFileHead(tmpBin, 64);
        if (isHtmlHead(head)) throw new Error('INVALID_AUDIO_HTML_RESPONSE');

        const isMp3 = isMp3Head(head);
        let finalPath = tmpBin;
        if (isMp3) {
            finalPath = `${tmpBase}.mp3`;
            await fs.promises.rename(tmpBin, finalPath);
        }

        return { filePath: finalPath, size: stat.size, isMp3 };
    } catch (err) {
        clearTimeout(timer);
        fs.promises.unlink(tmpBin).catch(() => null);
        throw err;
    }
}

// פירוק גדלי מחרוזות ומספרים (תיקון #7)
function parseSizeBytes(val) {
    if (typeof val === 'number' && isFinite(val) && val > 0) return val;
    if (typeof val !== 'string') return 9e12;
    const s = val.trim().toUpperCase();
    const m = s.match(/^([\d.]+)\s*(B|KB|KIB|MB|MIB|GB|GIB)?$/);
    if (!m) return 9e12;
    const n = parseFloat(m[1]);
    if (isNaN(n)) return 9e12;
    const unit = m[2] || 'B';
    if (unit.startsWith('G')) return n * 1024 * 1024 * 1024;
    if (unit.startsWith('M')) return n * 1024 * 1024;
    if (unit.startsWith('K')) return n * 1024;
    return n;
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
        }, 4500);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => Array.isArray(item) && item[1] && item[1].type === 'https' && item[1].api === true && item[1].uri)
                    .map(item => String(item[1].uri).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    invidiousCache.list = [...new Set([...fresh, ...invidiousCache.list])].slice(0, 10);
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
        }, 4500);
        if (res.ok) {
            const arr = await res.json();
            if (Array.isArray(arr)) {
                const fresh = arr
                    .filter(item => item && item.api_url && item.up_to_date !== false)
                    .map(item => String(item.api_url).replace(/\/+$/, ''));
                if (fresh.length > 0) {
                    pipedCache.list = [...new Set([...fresh, ...pipedCache.list])].slice(0, 10);
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

// מחיקה אוטומטית של הקלטות חיפוש זמניות (תיקון #6)
async function deleteYemotFileSilently(yemotPath) {
    if (!yemotPath || !TOKEN) return;
    try {
        const body = new URLSearchParams({
            token: TOKEN,
            what: yemotPath,
            action: 'delete'
        });
        await fetchWithTimeout(`${YM}FileAction`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
            body
        }, 6000);
    } catch (e) {}
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

async function ensurePlayfileExtension(folderPathStr, returnExtOverride = '') {
    const clean = String(folderPathStr).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const retExt = returnExtOverride || getReturnMainExt();
    const dirKey = `${clean}::${retExt}`;
    if (configuredPlayfileDirs.has(dirKey)) return;
    try {
        const body = new URLSearchParams({ token: TOKEN, path: `ivr2:/${clean}`, type: 'playfile' });
        const playfileIni = [
            'type=playfile',
            `playfile_end_goto=${retExt}`,
            `empty_goto=${retExt}`,
            `root_goto=${retExt}`,
            `control_play_return=${retExt}`,
            `control_play#=${retExt}`
        ].join('\r\n') + '\r\n';

        await Promise.all([
            fetchWithTimeout(`${YM}UpdateExtension`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
                body
            }, 6000),
            uploadTextToExactPath(playfileIni, `ivr2:/${clean}/ext.ini`, 'ext.ini')
        ]);
        configuredPlayfileDirs.add(dirKey);
    } catch (e) {}
}

// תיקון #6: הוסרה תקרת 900 השרירותית (תומך עד 99,999 קבצים!)
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
                    if (!isNaN(num) && num < 99999 && num > maxExisting) maxExisting = num;
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

// הקלטות חיפוש זמניות בתיקיית temp ממחזרות סלוטים 001..020 (למניעת הצטברות אינסופית)
const tempRecRolling = new Map();
function getRollingTempSlot(phone) {
    const next = ((tempRecRolling.get(phone) || 0) % 20) + 1;
    tempRecRolling.set(phone, next);
    return `rec_${String(next).padStart(2, '0')}`;
}

async function uploadAudioFileToExactPath(localAudioPath, exactTargetPath, fileNameLabel = 'audio.mp3', convertAudio = '1', timeoutMs = 45000) {
    const audioBuffer = await fs.promises.readFile(localAudioPath);
    const formData = new FormData();
    formData.append('token', TOKEN);
    formData.append('path', exactTargetPath);
    formData.append('convertAudio', String(convertAudio));
    formData.append('file', new Blob([audioBuffer], { type: 'audio/mpeg' }), fileNameLabel);

    const upRes = await fetchWithTimeout(`${YM}UploadFile`, { method: 'POST', body: formData }, timeoutMs);
    const upText = await upRes.text();
    console.log(`[Yemot Upload -> ${exactTargetPath}] (${audioBuffer.length} bytes) Response:`, upText.slice(0, 150));
    if (!upRes.ok || upText.includes('EXCEPTION')) {
        throw new Error(`YEMOT_UPLOAD_ERR: ${upText.slice(0, 120)}`);
    }
    return upText;
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
            if (buf.length > 200 && !headStr.includes('responseStatus') && !headStr.includes('EXCEPTION')) {
                return { buf, resolvedPath: p };
            }
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

// ==================== מנועי ההורדה (Streaming לדיסק — אפס לחץ RAM) ====================

async function tryApifyEngine(videoId, maxWaitMs = 45000, preferMp3 = false) {
    if (!APIFY_TOKEN) throw new Error('SKIP: APIFY_TOKEN not configured');

    const ytUrl = `https://www.youtube.com/watch?v=${videoId}`;
    const cleanActor = APIFY_ACTOR.replace('/', '~');
    const chosenFmt = preferMp3 ? 'mp3' : 'm4a';
    const payload = cleanActor.includes('hipersoft')
        ? { videoUrls: [ytUrl], format: chosenFmt, maxItems: 1 }
        : { videoUrls: [ytUrl], format: 'audio', audioFormat: chosenFmt, audioQuality: 'standard' };

    const startUrl = `https://api.apify.com/v2/acts/${cleanActor}/runs?token=${encodeURIComponent(APIFY_TOKEN)}`;
    const startRes = await fetchWithTimeout(startUrl, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload)
    }, 12000);

    if (!startRes.ok) {
        const errBody = (await startRes.text().catch(() => '')).replace(/\s+/g, ' ').slice(0, 180);
        if ([400, 401, 402, 403, 404, 429].includes(startRes.status)) {
            setEngineCooldown('apify', `HTTP_${startRes.status}: ${errBody}`);
        }
        throw new Error(`APIFY_START(${cleanActor}) HTTP_${startRes.status}: ${errBody}`);
    }

    const startJson = await startRes.json();
    const runId = startJson?.data?.id;
    let finalDatasetId = startJson?.data?.defaultDatasetId;
    if (!runId) throw new Error('APIFY_START: missing runId');

    const deadline = Date.now() + Math.max(20000, maxWaitMs);
    let lastStatus = startJson?.data?.status || 'READY';

    while (Date.now() < deadline) {
        await new Promise(r => setTimeout(r, 1500));
        const pollUrl = `https://api.apify.com/v2/actor-runs/${runId}?token=${encodeURIComponent(APIFY_TOKEN)}`;
        const pRes = await fetchWithTimeout(pollUrl, {}, 8000);
        if (!pRes.ok) continue;
        const pJson = await pRes.json();
        lastStatus = pJson?.data?.status || lastStatus;
        finalDatasetId = pJson?.data?.defaultDatasetId || finalDatasetId;

        if (lastStatus === 'SUCCEEDED') break;
        if (['FAILED', 'ABORTED', 'TIMED-OUT'].includes(lastStatus)) {
            throw new Error(`APIFY_RUN_${lastStatus}(${cleanActor}): ${pJson?.data?.statusMessage || lastStatus}`);
        }
    }

    if (lastStatus !== 'SUCCEEDED') {
        fetch(`https://api.apify.com/v2/actor-runs/${runId}/abort?token=${encodeURIComponent(APIFY_TOKEN)}`, { method: 'POST' }).catch(() => null);
        throw new Error(`APIFY_TIMEOUT(${cleanActor}): still ${lastStatus} after ${Math.round(maxWaitMs / 1000)}s`);
    }

    const dsUrl = `https://api.apify.com/v2/datasets/${finalDatasetId}/items?token=${encodeURIComponent(APIFY_TOKEN)}`;
    const dsRes = await fetchWithTimeout(dsUrl, {}, 10000);
    if (!dsRes.ok) throw new Error(`APIFY_DATASET HTTP_${dsRes.status}`);
    const items = await dsRes.json();
    const row = Array.isArray(items) ? items[0] : items;
    if (!row || typeof row !== 'object') throw new Error(`APIFY(${cleanActor}) empty dataset`);

    const audioUrl = row.fileUrl || row.downloadUrl || row.download_url || row.audioUrl || row.mediaUrl || row.url || row.link;
    if (!audioUrl || !String(audioUrl).startsWith('http') || String(audioUrl).includes('youtube.com/watch')) {
        throw new Error(`APIFY(${cleanActor}) no fileUrl: ${row.error || row.status || JSON.stringify(row).slice(0, 140)}`);
    }

    const dl = await downloadUrlToTempFile(audioUrl, { 'User-Agent': 'Mozilla/5.0' }, 50000, 'apify');
    return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: false, detail: `${cleanActor}/${chosenFmt} (${Math.round(dl.size / 1024)}KB)` };
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

    // תיקון #7: מיון מספרי תקין גם כאשר size מגיע כמחרוזת ("4.2 MB")
    if (payload.audios && Array.isArray(payload.audios.items)) {
        const sorted = [...payload.audios.items]
            .filter(it => it && typeof it.url === 'string' && it.url.startsWith('http'))
            .sort((a, b) => parseSizeBytes(a.size) - parseSizeBytes(b.size));
        if (sorted.length > 0) return sorted[0].url;
    }
    if (Array.isArray(payload.adaptiveFormats)) {
        const audioOnly = payload.adaptiveFormats
            .filter(f => String(f.mimeType || '').includes('audio') && f.url)
            .sort((a, b) => (parseInt(a.bitrate, 10) || 999999) - (parseInt(b.bitrate, 10) || 999999));
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
    if (cfg.endpoint && cfg.endpoint.toLowerCase() !== 'auto') return [cfg.endpoint];
    const remembered = workingRapidTemplate.get(cfg.host);
    const h = cfg.host.toLowerCase();
    let list = [];
    if (h.includes('youtube-info-download-api')) {
        // תיקון #1: MP3 תמיד נשאר ראשון, m4a משמש רק כגיבוי נקודתי לבקשה הנוכחית
        return [
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

async function tryRapidApiEngine(cfg, videoId, startSec, durationSec, isBackground = false) {
    if (!cfg.key || !cfg.host) throw new Error(`SKIP: ${cfg.id} not configured`);

    const headers = { 'x-rapidapi-key': cfg.key, 'x-rapidapi-host': cfg.host };
    const templates = getRapidCandidateTemplates(cfg);
    let lastErr = null;
    let all404 = true;

    for (const tpl of templates) {
        const { url: endpointUrl, supportsTrim } = renderRapidTemplate(tpl, cfg.host, videoId, startSec, durationSec);
        try {
            const res = await fetchWithTimeout(endpointUrl, { headers }, 14000);
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

            if (!resolvedUrl && (json.progress_url || json.id || String(json.status || '').toLowerCase() === 'processing')) {
                const jobUrl = json.progress_url || (json.id ? `https://${cfg.host}/api/progress?id=${encodeURIComponent(json.id)}` : endpointUrl);
                const isRapidHostJob = jobUrl.includes(cfg.host);
                const pollIntervalMs = 1200;
                const maxAttempts = isBackground ? 55 : 20; // קדמי ~24 שנ' מקסימום (משאיר זמן מלא ל-rapidapi2/apify!), רקע ~66 שנ'
                let lastProgressStr = '';
                let initStuckSince = Date.now();
                let stuckAtInit = false;

                for (let i = 0; i < maxAttempts; i++) {
                    await new Promise(r => setTimeout(r, pollIntervalMs));
                    const pHeaders = isRapidHostJob ? headers : {};
                    const pRes = await fetchWithTimeout(jobUrl, { headers: pHeaders }, 7000);
                    if (!pRes.ok) continue;
                    const pJson = await pRes.json();

                    const pTxt = String(pJson.text || pJson.status || '');
                    lastProgressStr = `${pJson.progress ?? ''}/${pTxt}`;

                    resolvedUrl = extractAudioUrlFromRapidPayload(pJson);
                    if (resolvedUrl) break;

                    const st = pTxt.toLowerCase();
                    if (st === 'failed' || st === 'error' || st === 'fail' || st === 'expired') {
                        throw new Error(`${cfg.id}_JOB_FAILED: ${pJson.msg || pJson.message || st}`);
                    }

                    if (st.includes('initialis') || st.includes('initializ') || st === 'queued') {
                        if (!isBackground && (Date.now() - initStuckSince) > 12000) {
                            stuckAtInit = true;
                            break;
                        }
                    } else {
                        initStuckSince = Date.now();
                    }
                }

                if (!resolvedUrl) {
                    const reason = stuckAtInit
                        ? `${cfg.id}: Stuck at ${lastProgressStr} >12s`
                        : `${cfg.id}: Timeout (last=${lastProgressStr})`;
                    lastErr = new Error(reason);
                    if (tpl.includes('format=mp3')) {
                        console.warn(`[RapidAPI] ${reason} -> trying m4a fallback for this request...`);
                        continue;
                    }
                    throw lastErr;
                }
            }

            if (!resolvedUrl) {
                lastErr = new Error(`${cfg.id}: No download_url returned on ${tpl}`);
                continue;
            }

            // תיקון #7: הוספת כותרות דפדפן לקישורי googlevideo וזיהוי ברור של קישור חסום-IP
            const dlHeaders = resolvedUrl.includes('googlevideo.com')
                ? { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36', 'Referer': 'https://www.youtube.com/' }
                : { 'User-Agent': 'Mozilla/5.0' };

            let dl;
            try {
                dl = await downloadUrlToTempFile(resolvedUrl, dlHeaders, 40000, cfg.id);
            } catch (dlErr) {
                if (String(dlErr.message).includes('HTTP_403') && resolvedUrl.includes('googlevideo.com')) {
                    setEngineCooldown(cfg.id, `IP-locked googlevideo 403 from ${cfg.host}`, 15 * 60 * 1000);
                    throw new Error(`${cfg.id}: IP-locked googlevideo URL returned 403`);
                }
                throw new Error(`${cfg.id}_DL: ${dlErr.message}`);
            }

            // תיקון #1: לא שומרים m4a כברירת מחדל קבועה כדי לא לתקוע שיחות עתידיות על FFmpeg!
            if (!tpl.includes('format=m4a')) {
                workingRapidTemplate.set(cfg.host, tpl);
            }
            engineConsecutiveTimeouts.set(cfg.id, 0);
            return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: supportsTrim, detail: tpl };
        } catch (err) {
            lastErr = err;
            if (!String(err.message).includes('HTTP_404') && !String(err.message).includes('Stuck at')) {
                all404 = false;
                break;
            }
        }
    }

    if (all404) {
        setEngineCooldown(cfg.id, `All endpoints returned 404 on ${cfg.host}`);
    } else if (lastErr && (String(lastErr.message).includes('Timeout') || String(lastErr.message).includes('Stuck at'))) {
        // 2 תקיעות רצופות -> השהיה קצרה של 3 דקות כדי לעבור מיד ל-rapidapi2 / apify
        const count = (engineConsecutiveTimeouts.get(cfg.id) || 0) + 1;
        engineConsecutiveTimeouts.set(cfg.id, count);
        if (count >= 2) {
            setEngineCooldown(cfg.id, lastErr.message, SHORT_TIMEOUT_COOLDOWN_MS);
            engineConsecutiveTimeouts.set(cfg.id, 0);
        }
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
    }, 10000);
    if (!res.ok) {
        if ([401, 403, 404].includes(res.status)) setEngineCooldown('cobalt', `HTTP_${res.status}`);
        throw new Error(`COBALT HTTP_${res.status}`);
    }
    const json = await res.json();
    const audioUrl = json.url || (Array.isArray(json.picker) && json.picker[0]?.url);
    if (!audioUrl) throw new Error('COBALT no url');
    const dl = await downloadUrlToTempFile(audioUrl, { 'User-Agent': 'Mozilla/5.0' }, 35000, 'cobalt');
    return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: false };
}

async function tryInvidiousParallel(videoId) {
    const instances = await refreshInvidiousList(false);
    const batch = instances.slice(0, 4);

    const fetchOne = async (base) => {
        const apiUrl = `${base}/api/v1/videos/${encodeURIComponent(videoId)}?fields=adaptiveFormats`;
        const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 3500);
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

        const dl = await downloadUrlToTempFile(proxiedUrl, { 'User-Agent': 'Mozilla/5.0' }, 12000, 'inv');
        return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: false, detail: base };
    };

    try {
        return await Promise.any(batch.map(fetchOne));
    } catch (agg) {
        const msg = `Invidious(${batch.length}): ${agg?.errors?.[0]?.message || 'failed'}`;
        setEngineCooldown('invidious_parallel', msg);
        throw new Error(msg);
    }
}

async function tryPipedParallel(videoId) {
    const instances = await refreshPipedList(false);
    const batch = instances.slice(0, 4);

    const fetchOne = async (base) => {
        const apiUrl = `${base}/streams/${encodeURIComponent(videoId)}`;
        const res = await fetchWithTimeout(apiUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } }, 3500);
        if (!res.ok) throw new Error(`${base}: HTTP_${res.status}`);
        const data = await res.json();
        const audioStreams = (data.audioStreams || []).filter(s => s && s.url);
        if (audioStreams.length === 0) throw new Error(`${base}: no audioStreams`);

        audioStreams.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
        const dl = await downloadUrlToTempFile(audioStreams[0].url, { 'User-Agent': 'Mozilla/5.0' }, 12000, 'piped');
        return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: false, detail: base };
    };

    try {
        return await Promise.any(batch.map(fetchOne));
    } catch (agg) {
        const msg = `Piped(${batch.length}): ${agg?.errors?.[0]?.message || 'failed'}`;
        setEngineCooldown('piped_parallel', msg);
        throw new Error(msg);
    }
}

async function tryInnerTubeDirect(videoId) {
    const c = {
        name: 'TVHTML5_SIMPLY_EMBEDDED_PLAYER',
        ua: 'Mozilla/5.0 (SMART-TV; LINUX; Tizen 6.0) AppleWebKit/537.36',
        context: {
            client: { clientName: 'TVHTML5_SIMPLY_EMBEDDED_PLAYER', clientVersion: '2.0', hl: 'en', gl: 'US' },
            thirdParty: { embedUrl: 'https://www.youtube.com/' }
        }
    };
    try {
        const res = await fetchWithTimeout('https://www.youtube.com/youtubei/v1/player?prettyPrint=false', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json', 'User-Agent': c.ua },
            body: JSON.stringify({ videoId, context: c.context, contentCheckOk: true, racyCheckOk: true })
        }, 4000);
        if (!res.ok) throw new Error(`${c.name}: HTTP_${res.status}`);
        const data = await res.json();
        if (data?.playabilityStatus?.status !== 'OK') throw new Error(`${c.name}: ${data?.playabilityStatus?.status || 'NOT_OK'}`);
        const formats = (data?.streamingData?.adaptiveFormats || [])
            .filter(f => f && f.url && String(f.mimeType || '').includes('audio/'));
        if (formats.length === 0) throw new Error(`${c.name}: no direct url`);
        formats.sort((a, b) => (a.bitrate || 999999) - (b.bitrate || 999999));
        const dl = await downloadUrlToTempFile(formats[0].url, { 'User-Agent': c.ua }, 12000, 'itube');
        return { filePath: dl.filePath, size: dl.size, isMp3: dl.isMp3, alreadyTrimmed: false, detail: c.name };
    } catch (err) {
        setEngineCooldown('innertube_direct', err.message);
        throw err;
    }
}

// ==================== yt-dlp עם עצירה מהירה על 403/Bot ====================
async function ensureYtDlpBinary(forceRefresh = false) {
    if (!forceRefresh && fs.existsSync(YTDLP_BIN_PATH)) {
        const stat = fs.statSync(YTDLP_BIN_PATH);
        if (stat.size > 1000000 && (Date.now() - stat.mtimeMs) < YTDLP_MAX_AGE_MS) return YTDLP_BIN_PATH;
    }
    if (ytdlpReadyPromise && !forceRefresh) return ytdlpReadyPromise;

    ytdlpReadyPromise = (async () => {
        const binUrl = 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux';
        const res = await fetchWithTimeout(binUrl, {}, 35000);
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

function runYtDlpFastFail(binPath, videoId, opts = {}) {
    return new Promise((resolve, reject) => {
        const prefix = `ytfull_${videoId}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
        const tmpl = path.join(os.tmpdir(), `${prefix}.%(ext)s`);
        const args = [
            '--no-playlist', '--no-check-certificates', '--cache-dir', YTDLP_CACHE_DIR,
            '--force-ipv4', '--socket-timeout', '10', '--retries', '1',
            '-S', 'proto:https,+abr',
            '-f', 'worstaudio[protocol^=http][abr>=32]/bestaudio[protocol^=http][abr<=96]/bestaudio[protocol^=http]/bestaudio/worst',
            '--js-runtimes', `node:${process.execPath}`,
            '--remote-components', 'ejs:github'
        ];
        if (opts.proxyUrl) args.push('--proxy', opts.proxyUrl);
        if (opts.cookiesPath) args.push('--cookies', opts.cookiesPath);
        args.push('-o', tmpl, `https://www.youtube.com/watch?v=${videoId}`);

        const child = spawn(binPath, args, { stdio: ['ignore', 'ignore', 'pipe'] });
        let stderr = '';
        let abortedReason = '';
        let finished = false;

        const timer = setTimeout(() => {
            if (!finished) {
                abortedReason = 'TIMEOUT (18s)';
                child.kill('SIGKILL');
            }
        }, 18000);

        child.stderr.on('data', chunk => {
            stderr += chunk.toString('utf8');
            if (stderr.length > 4000) stderr = stderr.slice(-4000);
            const low = stderr.toLowerCase();
            if (!abortedReason && (low.includes('http error 403') || low.includes('not a bot') || low.includes('sign in to confirm'))) {
                abortedReason = low.includes('403') ? 'HTTP 403 Forbidden (Render IP blocked)' : 'YouTube bot check (Render IP blocked)';
                child.kill('SIGKILL');
            }
        });

        child.on('close', () => {
            if (finished) return;
            finished = true;
            clearTimeout(timer);

            const files = fs.readdirSync(os.tmpdir()).filter(f => f.startsWith(prefix + '.') && !f.endsWith('.part'));
            if (files.length > 0) {
                const fullPath = path.join(os.tmpdir(), files[0]);
                const sz = fs.statSync(fullPath).size;
                if (sz > 5000) {
                    return resolve({ filePath: fullPath, size: sz, isMp3: fullPath.endsWith('.mp3'), alreadyTrimmed: false, detail: `yt-dlp (${Math.round(sz / 1024)}KB)` });
                }
                fs.promises.unlink(fullPath).catch(() => null);
            }
            const errLine = stderr.split(/\r?\n/).filter(l => /error:|warning:/i.test(l)).slice(-1)[0] || '';
            reject(new Error(abortedReason || errLine.slice(0, 200) || 'yt-dlp failed'));
        });

        child.on('error', err => {
            if (finished) return;
            finished = true;
            clearTimeout(timer);
            reject(err);
        });
    });
}

async function tryYtDlpMode(mode, videoId) {
    const binPath = await ensureYtDlpBinary(false);
    const cookiesPath = getCookiesFilePath();
    let cfg = null;

    if (mode === 'ytdlp_proxy_nocookies') {
        if (!PROXY_URL) throw new Error('SKIP: PROXY_URL not set');
        cfg = { proxyUrl: PROXY_URL };
    } else if (mode === 'ytdlp_cookies') {
        if (!cookiesPath) throw new Error('SKIP: YT_COOKIES_B64 not set');
        cfg = { cookiesPath, proxyUrl: PROXY_URL || undefined };
    } else if (mode === 'ytdlp_direct') {
        cfg = {};
    }

    try {
        return await runYtDlpFastFail(binPath, videoId, cfg);
    } catch (err) {
        const low = String(err.message || '').toLowerCase();
        if (low.includes('403') || low.includes('bot') || low.includes('sign in') || low.includes('timeout')) {
            setEngineCooldown(mode, err.message);
        }
        throw err;
    }
}

// ==================== חיתוך מקומי מהיר בדיסק עם Input Seeking (-ss לפני -i!) ====================
async function sliceLocalAudioToFile(inputPath, startSec = 0, durationSec = 0, alreadyTrimmed = false, isInputMp3 = false) {
    const tmpOut = path.join(os.tmpdir(), `slice_${startSec}_${Date.now()}_${Math.random().toString(36).slice(2, 5)}.mp3`);

    // ניסיון 1 (אולטרה-מהיר ~0.2 שנ'): Stream Copy ישיר אם המקור MP3 והתוצאה בטווח המותר
    if (AUDIO_MODE !== 'saver' && (isInputMp3 || inputPath.toLowerCase().endsWith('.mp3'))) {
        try {
            await new Promise((resolve, reject) => {
                const ffTimer = setTimeout(() => reject(new Error('FFmpeg copy timeout')), 10000);
                let cmd = ffmpeg(inputPath);
                if (!alreadyTrimmed && startSec > 0) cmd = cmd.inputOptions([`-ss ${startSec}`]);
                if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
                cmd.format('mp3').audioCodec('copy')
                    .on('end', () => { clearTimeout(ffTimer); resolve(); })
                    .on('error', err => { clearTimeout(ffTimer); reject(err); })
                    .save(tmpOut);
            });
            const stat = await fs.promises.stat(tmpOut);
            if (stat.size > 4000 && stat.size <= DIRECT_MP3_MAX_BYTES) {
                return { outPath: tmpOut, size: stat.size };
            }
            await fs.promises.unlink(tmpOut).catch(() => null);
        } catch (copyErr) {
            await fs.promises.unlink(tmpOut).catch(() => null);
        }
    }

    // ניסיון 2: קידוד מהיר עם קפיצת קלט מיידית (-ss לפני -i חוסך פענוח של שעות קודמות!)
    try {
        await new Promise((resolve, reject) => {
            const ffTimer = setTimeout(() => reject(new Error('FFmpeg encode timeout')), 65000);
            let cmd = ffmpeg(inputPath);
            if (!alreadyTrimmed && startSec > 0) cmd = cmd.inputOptions([`-ss ${startSec}`]);
            if (!alreadyTrimmed && durationSec > 0) cmd = cmd.duration(durationSec);
            cmd.format('mp3')
                .audioCodec('libmp3lame')
                .audioBitrate(AUDIO_MODE === 'saver' ? '24k' : '32k')
                .audioChannels(1)
                .audioFrequency(16000)
                .outputOptions(['-compression_level 9', '-threads 0'])
                .on('end', () => { clearTimeout(ffTimer); resolve(); })
                .on('error', err => { clearTimeout(ffTimer); reject(err); })
                .save(tmpOut);
        });
        const stat = await fs.promises.stat(tmpOut);
        if (stat.size < 1500) {
            await fs.promises.unlink(tmpOut).catch(() => null);
            throw new Error('EMPTY_SLICE');
        }
        return { outPath: tmpOut, size: stat.size };
    } catch (err) {
        await fs.promises.unlink(tmpOut).catch(() => null);
        throw err;
    }
}

async function finalizeRawFileToMp3File(rawResult, startSec, durationSec, keepReusableFull = false) {
    const { filePath, size, isMp3, alreadyTrimmed } = rawResult;

    // מסלול 0 שניות FFmpeg: קובץ MP3 מוכן וחתוך (או שיר קצר שלם) קטן מהתקרה -> מעלים ישירות!
    if (!keepReusableFull && isMp3 && size <= DIRECT_MP3_MAX_BYTES && (alreadyTrimmed || (startSec === 0 && durationSec === 0))) {
        return { outPath: filePath, size, reusableFilePath: null, ownsOutPath: true };
    }

    try {
        const sliced = await sliceLocalAudioToFile(filePath, startSec, durationSec, alreadyTrimmed, isMp3);
        if (keepReusableFull && !alreadyTrimmed) {
            return { outPath: sliced.outPath, size: sliced.size, reusableFilePath: filePath, reusableIsMp3: isMp3, ownsOutPath: true };
        }
        fs.promises.unlink(filePath).catch(() => null);
        return { outPath: sliced.outPath, size: sliced.size, reusableFilePath: null, ownsOutPath: true };
    } catch (err) {
        fs.promises.unlink(filePath).catch(() => null);
        throw err;
    }
}

async function runSingleEngine(engine, videoId, startSec, durationSec, isBackground = false, customTimeoutMs = 0, durationSecondsHint = 0) {
    if (engine === 'rapidapi1') return await tryRapidApiEngine(RAPID_CONFIGS[0], videoId, startSec, durationSec, isBackground);
    if (engine === 'rapidapi2') return await tryRapidApiEngine(RAPID_CONFIGS[1], videoId, startSec, durationSec, isBackground);
    if (engine === 'apify') {
        // לסרטון קצר (< 12 דק') מבקשים MP3 ישיר מ-Apify (אפס FFmpeg אצלנו!); לשיעור ארוך m4a (מהיר יותר ב-Apify)
        const preferMp3 = durationSecondsHint > 0 && durationSecondsHint <= 720;
        return await tryApifyEngine(videoId, customTimeoutMs || (isBackground ? 85000 : 45000), preferMp3);
    }
    if (engine === 'ytdlp_proxy_nocookies' || engine === 'ytdlp_cookies' || engine === 'ytdlp_direct') return await tryYtDlpMode(engine, videoId);
    if (engine === 'cobalt') return await tryCobaltEngine(videoId);
    if (engine === 'invidious_parallel') return await tryInvidiousParallel(videoId);
    if (engine === 'piped_parallel') return await tryPipedParallel(videoId);
    if (engine === 'innertube_direct') return await tryInnerTubeDirect(videoId);
    throw new Error(`Unknown engine: ${engine}`);
}

async function downloadSegmentOrFull(videoId, startSec = 0, durationSec = CHUNK_SEC, keepReusableFull = false, isBackground = false, durationSecondsHint = 0) {
    const errors = [];
    const order = getDynamicEngineOrder();
    // תיקון #2: תקציב קדמי 75 שנ' עם חלון מובטח של 42 שנ' ל-Apify כדי שלא ייחתך באמצע!
    const overallDeadline = Date.now() + (isBackground ? 170000 : 75000);

    for (const engine of order) {
        if (isEngineCoolingDown(engine)) {
            errors.push(`${engine}: paused (${engineCooldown.get(engine)?.reason})`);
            continue;
        }
        const remainingMs = overallDeadline - Date.now();
        if (!isBackground && remainingMs < 6000 && errors.length > 0) {
            errors.push(`${engine}: skipped (time budget reached)`);
            break;
        }
        try {
            const t0 = Date.now();
            const apifyBudget = engine === 'apify'
                ? Math.max(42000, Math.min(remainingMs, isBackground ? 90000 : 52000))
                : remainingMs;
            const rawRes = await runSingleEngine(engine, videoId, startSec, durationSec, isBackground, apifyBudget, durationSecondsHint);
            const fin = await finalizeRawFileToMp3File(rawRes, startSec, durationSec, keepReusableFull);
            lastWinningEngine = engine;
            persistEngineState();
            console.log(`[Download OK] engine=${engine} (${rawRes.detail || 'ok'}) video=${videoId} seg=${startSec}-${startSec + durationSec} bytes=${fin.size} reusable=${Boolean(fin.reusableFilePath)} ms=${Date.now() - t0}`);
            return fin;
        } catch (err) {
            const msg = err.message || String(err);
            if (!msg.startsWith('SKIP:')) console.warn(`[Engine Fail] ${engine}:`, msg);
            errors.push(`${engine}: ${msg}`);
        }
    }
    throw new Error(`ALL_ENGINES_FAILED -> ${errors.join(' ; ')}`);
}

// ==================== הורדה והשמעה עם מטמון חלקים בטוח (תיקון #5) ====================
async function downloadAndPreparePlayback(videoId, archiveUserFolder, durationSeconds = 0, returnExt = '') {
    const cleanArchive = String(archiveUserFolder).replace(/^ivr2:\/*/, '').replace(/^\/*/, '').replace(/\/*$/, '');
    const cacheKey = `${cleanArchive}:${videoId}`;
    const cached = recentPlaybackCache.get(cacheKey);

    if (cached && (Date.now() - cached.ts) < PLAYBACK_CACHE_TTL_MS) {
        if (cached.status === 'ready' || (cached.status === 'uploading' && (Date.now() - cached.ts) < 15 * 60 * 1000)) {
            console.log(`[Cache Hit] (${cached.status}) Instant replay for ${cacheKey} -> ${cached.playCmd}`);
            return cached.playCmd;
        }
        // אם היה כשל בחלקי רקע, מוחקים את המטמון כדי שיורד נקי מחדש
        recentPlaybackCache.delete(cacheKey);
    }

    const isLongVideo = durationSeconds > CHUNK_SEC;
    const totalParts = isLongVideo
        ? Math.min(MAX_PARTS, Math.max(2, Math.ceil((durationSeconds - 10) / CHUNK_SEC)))
        : 1;

    const [firstResult, , rawPartNums] = await Promise.all([
        downloadSegmentOrFull(videoId, 0, isLongVideo ? CHUNK_SEC : 0, isLongVideo, false, durationSeconds),
        ensurePlayfileExtension(cleanArchive, returnExt),
        getNextFileNumberStr(cleanArchive, totalParts)
    ]);

    const partNums = Array.isArray(rawPartNums) ? rawPartNums : [rawPartNums];
    const firstPath = `ivr2:/${cleanArchive}/${partNums[0]}.mp3`;
    try {
        await uploadAudioFileToExactPath(firstResult.outPath, firstPath, `${partNums[0]}.mp3`, '1', 45000);
    } finally {
        fs.promises.unlink(firstResult.outPath).catch(() => null);
    }

    const chainedPlayCommand = partNums.map(n => `f-/${cleanArchive}/${n}`).join('.');

    if (!isLongVideo) {
        if (firstResult.reusableFilePath) fs.promises.unlink(firstResult.reusableFilePath).catch(() => null);
        recentPlaybackCache.set(cacheKey, { playCmd: chainedPlayCommand, status: 'ready', ts: Date.now(), totalParts: 1, uploadedCount: 1 });
        return chainedPlayCommand;
    }

    const cacheEntry = { playCmd: chainedPlayCommand, status: 'uploading', ts: Date.now(), totalParts, uploadedCount: 1 };
    recentPlaybackCache.set(cacheKey, cacheEntry);

    activeBackgroundJobs++;
    (async () => {
        let localFullFile = firstResult.reusableFilePath;
        let localIsMp3 = Boolean(firstResult.reusableIsMp3);
        let allSucceeded = true;

        try {
            for (let i = 1; i < totalParts; i++) {
                const startSec = i * CHUNK_SEC;
                const targetNum = partNums[i];
                const targetPath = `ivr2:/${cleanArchive}/${targetNum}.mp3`;
                let sliceFile = null;

                if (localFullFile && fs.existsSync(localFullFile)) {
                    try {
                        const t0 = Date.now();
                        const s = await sliceLocalAudioToFile(localFullFile, startSec, CHUNK_SEC, false, localIsMp3);
                        sliceFile = s.outPath;
                        console.log(`[Local Split OK] Part ${i + 1}/${totalParts} bytes=${s.size} ms=${Date.now() - t0}`);
                    } catch (sliceErr) {
                        if (String(sliceErr.message).includes('EMPTY_SLICE')) {
                            console.log(`[Local Split] Reached end of audio at Part ${i + 1}`);
                            break;
                        }
                        console.warn(`[Local Split Part ${i + 1} Error]`, sliceErr.message);
                    }
                }

                if (!sliceFile) {
                    for (let retry = 0; retry < 2 && !sliceFile; retry++) {
                        try {
                            if (retry > 0) await new Promise(r => setTimeout(r, 3000));
                            const resPart = await downloadSegmentOrFull(videoId, startSec, CHUNK_SEC, true, true, durationSeconds);
                            sliceFile = resPart.outPath;
                            if (resPart.reusableFilePath && !localFullFile) {
                                localFullFile = resPart.reusableFilePath;
                                localIsMp3 = Boolean(resPart.reusableIsMp3);
                            }
                        } catch (e) {
                            console.warn(`[Part ${i + 1}/${totalParts} Attempt ${retry + 1} Error]`, e.message);
                        }
                    }
                }

                if (sliceFile) {
                    try {
                        await uploadAudioFileToExactPath(sliceFile, targetPath, `${targetNum}.mp3`, '1', 55000);
                        cacheEntry.uploadedCount++;
                        console.log(`[Part ${i + 1}/${totalParts} Uploaded] -> ${targetPath}`);
                    } catch (upErr) {
                        allSucceeded = false;
                        console.error(`[Part ${i + 1}/${totalParts} Upload Error]`, upErr.message);
                    } finally {
                        fs.promises.unlink(sliceFile).catch(() => null);
                    }
                } else {
                    allSucceeded = false;
                    console.error(`[Part ${i + 1}/${totalParts} Failed permanently]`);
                }
            }

            if (allSucceeded) {
                cacheEntry.status = 'ready';
                cacheEntry.ts = Date.now();
            } else {
                // תיקון #5: לא משאירים במטמון שיעור שחסרים לו חלקים!
                recentPlaybackCache.delete(cacheKey);
                console.warn(`[Cache Invalidated] Removed incomplete playback ${cacheKey}`);
            }
        } finally {
            activeBackgroundJobs = Math.max(0, activeBackgroundJobs - 1);
            if (localFullFile) fs.promises.unlink(localFullFile).catch(() => null);
        }
    })();

    return chainedPlayCommand;
}

// ==================== נתיבי בדיקה, Ping ואבחון ====================
function setCors(res) {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
}

// תיקון #8: נתיב /ping זעיר (2 בייטים!) לשמירה על השרת ער מ-cron-job.org בלי לבזבז תעבורה
app.get('/ping', (req, res) => {
    res.type('text/plain').send('ok');
});

app.get('/', (req, res) => {
    res.send('YouTube Personal Line Server v5.0 (Disk-Streaming + Fast Seek + Safe Cache + Dynamic Ext) OK');
});

app.get('/health', (req, res) => {
    setCors(res);
    getCookiesFilePath();
    const cooldowns = {};
    for (const [k, v] of engineCooldown.entries()) {
        if (Date.now() < v.until) cooldowns[k] = { reason: v.reason, remainingSec: Math.round((v.until - Date.now()) / 1000) };
    }
    const mem = process.memoryUsage();
    res.json({
        version: '5.0.0',
        uptimeSec: Math.round(process.uptime()),
        memoryMB: { rss: Math.round(mem.rss / 1048576), heapUsed: Math.round(mem.heapUsed / 1048576) },
        audioMode: AUDIO_MODE,
        mainReturnExt: getReturnMainExt(),
        adminLogExt: ADMIN_LOG_EXT,
        activeBackgroundJobs,
        cachedPlaybacks: recentPlaybackCache.size,
        activeEngineOrder: getDynamicEngineOrder(),
        lastWinningEngine,
        configured: {
            rapidapi1: Boolean(RAPID_CONFIGS[0].key && RAPID_CONFIGS[0].host),
            rapidapi1_host: RAPID_CONFIGS[0].host || null,
            rapidapi2: Boolean(RAPID_CONFIGS[1].key && RAPID_CONFIGS[1].host),
            rapidapi2_host: RAPID_CONFIGS[1].host || null,
            apify: Boolean(APIFY_TOKEN),
            apify_actor: APIFY_ACTOR,
            proxy: Boolean(PROXY_URL),
            ytdlp_cookies: Boolean(YT_COOKIES_B64),
            cobalt: Boolean(COBALT_API_URL),
            youtube_api_keys: YT_KEYS.length,
            gemini_key: Boolean(GEMINI_KEY),
            yemot_token: Boolean(TOKEN)
        },
        cooldowns
    });
});

app.get('/test', async (req, res) => {
    setCors(res);
    if (req.query.reset === '1') {
        engineCooldown.clear();
        engineConsecutiveTimeouts.clear();
        persistEngineState();
    }
    const videoId = String(req.query.v || 'jNQXAC9IVRw').replace(/[^a-zA-Z0-9_-]/g, '');
    const onlyParam = String(req.query.only || '').trim();
    const enginesToTest = onlyParam
        ? onlyParam.split(',').map(s => s.trim()).filter(Boolean)
        : getDynamicEngineOrder();
    const results = [];

    for (const engine of enginesToTest) {
        const t0 = Date.now();
        let outPath = null;
        let reusable = null;
        try {
            const customWait = engine === 'apify' ? 75000 : 0;
            const rawRes = await runSingleEngine(engine, videoId, 0, 8, false, customWait, 19);
            const fin = await finalizeRawFileToMp3File(rawRes, 0, 8, true);
            outPath = fin.outPath;
            reusable = fin.reusableFilePath;
            let part2Bytes = 0;
            if (reusable && fs.existsSync(reusable)) {
                const p2 = await sliceLocalAudioToFile(reusable, 8, 8, false, Boolean(fin.reusableIsMp3));
                part2Bytes = p2.size;
                fs.promises.unlink(p2.outPath).catch(() => null);
            }
            results.push({
                engine,
                status: 'OK',
                detail: rawRes.detail || '',
                part1Bytes: fin.size,
                part2LocalSplitBytes: part2Bytes,
                ms: Date.now() - t0
            });
        } catch (err) {
            const msg = err.message || String(err);
            results.push({
                engine,
                status: msg.startsWith('SKIP:') ? 'SKIPPED' : 'FAIL',
                error: msg,
                ms: Date.now() - t0
            });
        } finally {
            if (outPath) fs.promises.unlink(outPath).catch(() => null);
            if (reusable) fs.promises.unlink(reusable).catch(() => null);
        }
    }
    res.json({ version: '5.0.0', audioMode: AUDIO_MODE, videoId, results });
});

// ==================== מנוע ימות המשיח ====================
const MAIN_MENU_TEXT = 'ברוכים הבאים לחיפוש ביוטיוב! לשמיעת הפלייליסט שלכם הקישו 1 לשמיעת שיעורי התורה שלכם הקישו 2 לחיפוש מוזיקה חדש הקישו 3 לחיפוש שיעור חדש הקישו 4! שימו לב אם הסרטון ארוך מ 15 דקות הוא עולה בחלקים לשלוחת הפלייליסט או לשלוחת השיעורי תורה ! לחזרה לשלוחה הקודמת הקישו כוכבית! הקו מנוטר משתמש שיחפש תוכן לא ראוי יחסם ';

function setSession(phone, obj) {
    userSessionState.set(phone, { ...obj, updatedAt: Date.now() });
}

app.all(['/yemot', '/yemot/:e'], async (req, res) => {
    const q = { ...req.query, ...req.body };
    res.type('text/plain; charset=utf-8');

    try {
        const callerPhone = lastVal(q.ApiPhone).replace(/[^0-9]/g, '');
        const callId = lastVal(q.ApiCallId);
        const returnMainExt = getReturnMainExt(lastVal(q.ApiExtension));

        if (q.hangup === 'yes') {
            if (callerPhone) userSessionState.delete(callerPhone);
            return res.send('noop');
        }

        if (!callerPhone) {
            return res.send(`id_list_message=t-שגיאה בזיהוי מספר הטלפון&go_to_folder=${returnMainExt}`);
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
                setSession(callerPhone, { step: 'WAIT_NAME', callId });
                return res.send(`read=t-ברוכים הבאים אנא הקליטו את שמכם המלא ובסיום הקישו סולמית=RecordName,no,record,/${tempRecFolder},name_rec,no,7,1`);
            }
            setSession(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'IN_PLAYLIST') {
            setSession(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'WAIT_SELECT_RESULT' && selectResult) {
            if (selectResult === '8') {
                setSession(callerPhone, { step: 'WAIT_RECORD', isMusic: state.isMusic, callId });
                const recSlot = getRollingTempSlot(callerPhone);
                return state.isMusic
                    ? res.send(`read=t-אנא אמרו שוב את שם השיר המבוקש ובסיום הקישו סולמית=SearchMusic,no,record,/${tempRecFolder},${recSlot},no,7,1`)
                    : res.send(`read=t-אנא אמרו שוב את שם השיעור המבוקש ובסיום הקישו סולמית=SearchTorah,no,record,/${tempRecFolder},${recSlot},no,7,1`);
            }
            if (selectResult === '9') {
                const allResults = state.results || [];
                const currentPage = state.pageIndex || 0;
                const nextPage = ((currentPage + 1) * RESULTS_PER_PAGE < allResults.length) ? (currentPage + 1) : 0;
                const nextPromptText = buildPagePromptText(state.cleanQuery, allResults, nextPage);
                setSession(callerPhone, { ...state, pageIndex: nextPage, menuPromptText: nextPromptText, callId });
                return res.send(`read=t-${nextPromptText}=SelectResult,no,1,1,7,Digits,no`);
            }
            if (selectResult === '0' || selectResult === '*' || selectResult === '#') {
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
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
                    downloadAndPreparePlayback(chosenVideo.videoId, archiveFolder, chosenVideo.durationSeconds || 0, returnMainExt),
                    getUserNameIfRegistered(callerPhone).catch(() => null)
                ]);
                saveAdminLogToExt8(callerPhone, regName || 'משתמש רשום', categoryLabel, cleanQuery, chosenVideo.title, `הורד בהצלחה לשלוחה ${archiveFolder}`);
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
                const durationPart = chosenVideo.durationText ? ` באורך ${chosenVideo.durationText}` : '';
                return res.send(`id_list_message=t-משמיע ${chosenVideo.title}${durationPart}.${playCmd}&go_to_folder=${returnMainExt}`);
            } catch (audioErr) {
                console.error('[Download Error]', audioErr.message);
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-נמצא ${chosenVideo.title} אך אירעה שגיאה בטעינת הקובץ&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }
        }

        if (state.step === 'WAIT_RECORD' && (searchMusic || searchTorah)) {
            const isMusic = Boolean(state.isMusic);
            const recordPath = isMusic ? (searchMusic || searchTorah) : (searchTorah || searchMusic);
            const categoryLabel = isMusic ? 'מוזיקה' : 'שיעורים';

            let audioBuf, resolvedRecPath, registeredName;
            try {
                const [dlRes, rName] = await Promise.all([
                    downloadRecordingFromYemot(recordPath, lastVal(q.ApiExtension)),
                    getUserNameIfRegistered(callerPhone).catch(() => null)
                ]);
                audioBuf = dlRes.buf;
                resolvedRecPath = dlRes.resolvedPath;
                registeredName = rName || 'משתמש רשום';
                // תיקון #6: מחיקת הקלטת החיפוש הזמנית ברקע כדי שלא תצטבר ב-temp
                deleteYemotFileSilently(resolvedRecPath);
            } catch (dlErr) {
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה בהורדת ההקלטה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            let rawText = '';
            try { rawText = await transcribeAudio(audioBuf.toString('base64')); }
            catch (gemErr) {
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-שגיאה במנוע זיהוי הדיבור&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const cleanQuery = sanitizeForYemotTts(rawText, 55);
            if (!cleanQuery) {
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
                return res.send(`id_list_message=t-לא הצלחתי לשמוע את הבקשה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
            }

            const ytBaseUrl = `https://www.googleapis.com/youtube/v3/search?part=snippet&q=${encodeURIComponent(cleanQuery)}&type=video&maxResults=28`;
            let ytData;
            try {
                const ytResult = await fetchYouTubeWithFallback(ytBaseUrl, 6000);
                ytData = ytResult.data;
            } catch (ytFetchErr) {
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
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
                setSession(callerPhone, { step: 'WAIT_MENU', callId });
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
            setSession(callerPhone, { step: 'WAIT_SELECT_RESULT', cleanQuery, isMusic, results: validItems, pageIndex: 0, menuPromptText, callId });
            return res.send(`read=t-${menuPromptText}=SelectResult,no,1,1,7,Digits,no`);
        }

        if (state.step === 'WAIT_MENU' && (hasMenuChoiceParam || menuChoice)) {
            if (menuChoice === '' || menuChoice === '#' || menuChoice === '*' || menuChoice === '0') {
                userSessionState.delete(callerPhone);
                return res.send('go_to_folder=..');
            }
            if (menuChoice === '1') {
                await ensurePlayfileExtension(musicExtFolder, returnMainExt);
                setSession(callerPhone, { step: 'IN_PLAYLIST', callId });
                return res.send(`go_to_folder=/${musicExtFolder}`);
            }
            if (menuChoice === '2') {
                await ensurePlayfileExtension(torahExtFolder, returnMainExt);
                setSession(callerPhone, { step: 'IN_PLAYLIST', callId });
                return res.send(`go_to_folder=/${torahExtFolder}`);
            }
            if (menuChoice === '3') {
                const recSlot = getRollingTempSlot(callerPhone);
                setSession(callerPhone, { step: 'WAIT_RECORD', isMusic: true, callId });
                return res.send(`read=t-אנא אמרו את שם השיר המבוקש ובסיום הקישו סולמית=SearchMusic,no,record,/${tempRecFolder},${recSlot},no,7,1`);
            }
            if (menuChoice === '4') {
                const recSlot = getRollingTempSlot(callerPhone);
                setSession(callerPhone, { step: 'WAIT_RECORD', isMusic: false, callId });
                return res.send(`read=t-אנא אמרו את שם השיעור המבוקש ובסיום הקישו סולמית=SearchTorah,no,record,/${tempRecFolder},${recSlot},no,7,1`);
            }
            setSession(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        if (state.step === 'WAIT_NAME' && recordName) {
            let audioBuf, resolvedNameRec;
            try {
                const dlRes = await downloadRecordingFromYemot(recordName, lastVal(q.ApiExtension));
                audioBuf = dlRes.buf;
                resolvedNameRec = dlRes.resolvedPath;
                deleteYemotFileSilently(resolvedNameRec);
            } catch (dlErr) {
                return res.send(`read=t-שגיאה בקליטת ההקלטה אנא הקליטו שוב את שמכם ובסיום הקישו סולמית=RecordName,no,record,/${tempRecFolder},name_rec,no,7,1`);
            }

            let rawName = '';
            try { rawName = await transcribeAudio(audioBuf.toString('base64')); } catch (e) {}
            const cleanName = sanitizeForYemotTts(rawName, 40) || 'משתמש רשום';

            await Promise.all([
                uploadAudioBufferToExactPath(audioBuf, `ivr2:/${userFolder}/name.wav`, 'name.wav', '0'),
                uploadTextToExactPath(cleanName, `ivr2:/${userFolder}/name.txt`, 'name.txt'),
                ensurePlayfileExtension(musicExtFolder, returnMainExt),
                ensurePlayfileExtension(torahExtFolder, returnMainExt)
            ]);
            userNamesCache.set(callerPhone, cleanName);
            saveAdminLogToExt8(callerPhone, cleanName, 'רישום למערכת', 'הקלטת שם משתמש', '', 'נרשם בהצלחה');

            setSession(callerPhone, { step: 'WAIT_MENU', callId });
            return res.send(`id_list_message=t-שלום ${cleanName} נרשמתם בהצלחה&read=t-${MAIN_MENU_TEXT}=MenuChoice,no,1,0,7,Digits,no`);
        }

        setSession(callerPhone, { step: 'WAIT_MENU', callId });
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
    console.log(`=== Server v5.0 (Disk-Streaming + Fast Seek + Safe Cache + Dynamic Ext) Ready on port ${port} ===`);
    getCookiesFilePath();
    console.log(`[Config] audioMode=${AUDIO_MODE} mainExt=${getReturnMainExt()} adminLogExt=${ADMIN_LOG_EXT}`);
    console.log(`[Engine Order] ${getDynamicEngineOrder().join(' -> ')}`);
});
