'use strict';

const express = require('express');
const { spawn } = require('child_process');

const app = express();
const PORT = Number(process.env.PORT || 10000);
app.use(express.json({ limit: '32kb' }));

// ---------------- CONFIG ----------------
const M3U_URLS = [
  'https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u',
  'https://iptv-org.github.io/iptv/countries/vn.m3u'
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 240;
const VIDEO_FPS = 12;
const DEFAULT_CLIENT_FPS = 12;
const MIN_CLIENT_FPS = 1;
const MAX_CLIENT_FPS = 30;

const QUALITY_PRESETS = [
  { id: '1080p', label: '1080p', jpegQuality: 10 },
  { id: '720p', label: '720p', jpegQuality: 15 },
  { id: '540p', label: '540p', jpegQuality: 20 },
  { id: '340p', label: '340p', jpegQuality: 25 }
];
let currentQualityId = '1080p';

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_FRAME_MS = 20; // 20 ms PCM packets reduce latency and smooth client playback
const AUDIO_FRAME_BYTES = AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * 2 * AUDIO_FRAME_MS / 1000;
const AUDIO_BUFFER_MAX_MS = 1200;
const AUDIO_BUFFER_MAX_BYTES = AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * 2 * AUDIO_BUFFER_MAX_MS / 1000;
const AUDIO_START_BUFFER_MS = 400;

const VIDEO_QUEUE_TARGET = 3; // 250 ms at 12 fps
const VIDEO_QUEUE_MAX = 8;
const VIDEO_INTERVAL = 1000 / VIDEO_FPS;
const MASTER_TICK_MS = 10;

// Start video once it is primed. Give audio a short chance to prime so A/V
// starts together, but never let a missing/late audio track hold video forever.
const AUDIO_START_GRACE_MS = 1400;
const STREAM_READY_GRACE_MS = 100;
const STREAM_READY_TIMEOUT_MS = 8000;

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;
const MAX_JPEG_FRAME_BYTES = 512 * 1024;
const MAX_VIDEO_PENDING_BYTES = 1024 * 1024;
const CLIENT_SKIP_THRESHOLD_MS = 300;
const MAX_CLIENT_BLOCK_MS = 3000;
const MAX_AUDIO_BLOCK_MS = 1500;

const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;

const RENDER_API_KEY = process.env.RENDER_API_KEY || '';
const RENDER_SERVICE_IDS = (process.env.RENDER_SERVICE_IDS || 'srv-dbs5vb8n74is738ut5e0')
  .split(',').map(s => s.trim()).filter(Boolean);
const BANDWIDTH_LIMIT_GB = Number(process.env.BANDWIDTH_LIMIT_GB || 5);

const SOI = Buffer.from([0xff, 0xd8]);
const EOI = Buffer.from([0xff, 0xd9]);

// ---------------- STATE ----------------
let channels = [];
let currentChannel = null;
let ffmpeg = null;
let generation = 0;
let manuallyStopped = true;
let restarting = false;
let restartTimer = null;
let watchdogTimer = null;

let jpegPending = Buffer.alloc(0);
let videoQueue = [];
let latestFrame = null;
let frameSequence = 0;
let lastVideoFrameReceived = 0;
let lastVideoFrameTime = 0;
let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let videoSentFrames = 0;

const videoClients = new Map();
const audioClients = new Map();

let audioBuffer = Buffer.alloc(0);
let audioPrimed = false;
let audioUnderflows = 0;
let audioOverflowBytes = 0;
let audioFramesSent = 0;
let audioSilenceSent = 0;
let audioMaxObservedBytes = 0;

let streamReady = false;
let streamReadyAt = 0;
let readyWaiters = [];

let masterTimer = null;
let syncEpoch = 0;
let videoFramesSinceSync = 0;
let audioFramesSinceSync = 0;
let audioStartDeadline = 0;
let audioTrackAvailable = false;
let audioTrackTimedOut = false;

// ---------------- HELPERS ----------------
function currentPreset() {
  return QUALITY_PRESETS.find(p => p.id === currentQualityId) || QUALITY_PRESETS[0];
}
function normalizeQuality(value) {
  let v = String(value || '').trim().toLowerCase().replace(/\s+/g, '');
  if (!v) return null;
  if (!v.endsWith('p')) v += 'p';
  return QUALITY_PRESETS.some(p => p.id === v) ? v : null;
}
function qualityResponse() {
  const p = currentPreset();
  return { quality: p.id, jpegQuality: p.jpegQuality, presets: QUALITY_PRESETS };
}
function setQuality(value) {
  const id = normalizeQuality(value);
  if (!id) return null;
  const changed = id !== currentQualityId;
  currentQualityId = id;
  if (changed && currentChannel && !manuallyStopped) startFFmpeg(currentChannel);
  return currentPreset();
}
function parseResolutionFromName(name) {
  const m = String(name).match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);
  return m ? Number(m[1] || m[2]) || 0 : 0;
}
function parseM3U(content) {
  const out = [];
  let info = null;
  for (const raw of content.split(/\r?\n/)) {
    const line = raw.trim();
    if (!line) continue;
    if (line.startsWith('#EXTINF:')) { info = line; continue; }
    if (line.startsWith('#') || !info) continue;
    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(line)) { info = null; continue; }
    const name = info.split(',').pop().trim() || 'Unknown channel';
    const group = info.match(/group-title="([^"]*)"/i);
    const logo = info.match(/tvg-logo="([^"]*)"/i);
    const tvgId = info.match(/tvg-id="([^"]*)"/i);
    out.push({
      id: String(out.length), name,
      group: group ? group[1] : '',
      logo: logo ? logo[1] : '',
      tvgId: tvgId ? tvgId[1] : '',
      resolution: parseResolutionFromName(name),
      url: line
    });
    info = null;
  }
  return out;
}
async function loadChannels() {
  let lastError;
  for (const url of M3U_URLS) {
    try {
      const r = await fetch(url, {
        headers: { 'User-Agent': 'Mozilla/5.0' },
        signal: AbortSignal.timeout(15000)
      });
      if (!r.ok) throw new Error(`HTTP ${r.status}`);
      const parsed = parseM3U(await r.text());
      if (!parsed.length) throw new Error('Playlist contains no channels');
      channels = parsed;
      console.log('[M3U] Loaded', channels.length, 'channels');
      return channels;
    } catch (e) {
      lastError = e;
      console.warn('[M3U] Failed:', e.message);
    }
  }
  throw lastError || new Error('No playlist available');
}
function clearAudio() {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioMaxObservedBytes = 0;
}
function clearVideo() {
  jpegPending = Buffer.alloc(0);
  videoQueue = [];
  latestFrame = null;
  frameSequence = 0;
}
function resetReady(reason) {
  if (streamReady && reason) console.log('[STREAM] Reset:', reason);
  streamReady = false;
  streamReadyAt = 0;
  const waiters = readyWaiters.splice(0);
  for (const w of waiters) w(false);
}
function setReady() {
  if (streamReady) return;
  streamReady = true;
  streamReadyAt = Date.now();
  console.log('[STREAM] READY');
  const waiters = readyWaiters.splice(0);
  for (const w of waiters) w(true);
}
function waitForReady(timeoutMs) {
  if (streamReady) return Promise.resolve(true);
  return new Promise(resolve => {
    let done = false;
    const finish = value => {
      if (done) return;
      done = true;
      clearTimeout(timer);
      readyWaiters = readyWaiters.filter(fn => fn !== finish);
      resolve(value);
    };
    const timer = setTimeout(() => finish(false), timeoutMs);
    readyWaiters.push(finish);
  });
}
function disconnectVideo(res) {
  videoClients.delete(res);
}
function disconnectAudio(res) {
  audioClients.delete(res);
}
function closeAllClients() {
  for (const res of videoClients.keys()) { try { res.destroy(); } catch (_) {} }
  for (const res of audioClients.keys()) { try { res.destroy(); } catch (_) {} }
  videoClients.clear();
  audioClients.clear();
}

// ---------------- AUDIO BUFFER ----------------
function pushAudio(chunk) {
  if (!chunk || !chunk.length) return;
  if (chunk.length & 1) chunk = chunk.subarray(0, chunk.length - 1);
  if (!chunk.length) return;

  const total = audioBuffer.length + chunk.length;
  if (total > AUDIO_BUFFER_MAX_BYTES) {
    const drop = Math.min(total - AUDIO_BUFFER_MAX_BYTES, audioBuffer.length);
    const evenDrop = drop + (drop & 1);
    audioOverflowBytes += evenDrop;
    if (evenDrop >= audioBuffer.length) {
      const tail = chunk.subarray(Math.max(0, chunk.length - AUDIO_BUFFER_MAX_BYTES));
      audioBuffer = Buffer.from(tail);
    } else {
      audioBuffer = Buffer.concat([audioBuffer.subarray(evenDrop), chunk]);
    }
  } else {
    audioBuffer = audioBuffer.length
      ? Buffer.concat([audioBuffer, chunk], total)
      : Buffer.from(chunk);
  }
  if (audioBuffer.length > AUDIO_BUFFER_MAX_BYTES) {
    audioBuffer = Buffer.from(audioBuffer.subarray(-AUDIO_BUFFER_MAX_BYTES));
  }
  if (audioBuffer.length & 1) audioBuffer = audioBuffer.subarray(0, audioBuffer.length - 1);
  audioMaxObservedBytes = Math.max(audioMaxObservedBytes, audioBuffer.length);
  if (audioBuffer.length >= AUDIO_SAMPLE_RATE * 2 * AUDIO_START_BUFFER_MS / 1000) {
    audioPrimed = true;
    audioTrackAvailable = true;
  }
}
function takeAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES, 0);
  const n = Math.min(audioBuffer.length, AUDIO_FRAME_BYTES) & ~1;
  if (n) {
    audioBuffer.copy(frame, 0, 0, n);
    audioBuffer = audioBuffer.subarray(n);
  }
  if (n < AUDIO_FRAME_BYTES) audioUnderflows++;
  return { frame, silence: n < AUDIO_FRAME_BYTES };
}
function writeAudio(res, frame, silence) {
  if (res.destroyed || res.writableEnded) {
    disconnectAudio(res);
    return;
  }
  const state = audioClients.get(res);
  if (!state || state.blocked) return;
  try {
    const ok = res.write(frame);
    if (silence) audioSilenceSent++;
    else audioFramesSent++;
    if (!ok) {
      state.blocked = true;
      state.blockedAt = Date.now();
      res.once('drain', () => {
        state.blocked = false;
        state.blockedAt = 0;
      });
    }
  } catch (_) {
    disconnectAudio(res);
    try { res.destroy(); } catch (_) {}
  }
}

// ---------------- VIDEO PARSER / FANOUT ----------------
function processVideoData(chunk, gen) {
  if (gen !== generation || !chunk?.length) return;
  if (jpegPending.length + chunk.length > MAX_VIDEO_PENDING_BYTES) {
    const combined = Buffer.concat([jpegPending, chunk]);
    const start = combined.lastIndexOf(SOI);
    jpegPending = start >= 0 ? Buffer.from(combined.subarray(start)) : Buffer.alloc(0);
    videoInvalidFrames++;
  } else {
    jpegPending = jpegPending.length
      ? Buffer.concat([jpegPending, chunk])
      : Buffer.from(chunk);
  }

  while (jpegPending.length) {
    const start = jpegPending.indexOf(SOI);
    if (start < 0) {
      jpegPending = jpegPending[jpegPending.length - 1] === 0xff
        ? Buffer.from([0xff]) : Buffer.alloc(0);
      return;
    }
    if (start > 0) jpegPending = jpegPending.subarray(start);
    const end = jpegPending.indexOf(EOI, 2);
    if (end < 0) {
      if (jpegPending.length > MAX_JPEG_FRAME_BYTES) {
        videoInvalidFrames++;
        const next = jpegPending.indexOf(SOI, 2);
        jpegPending = next >= 0 ? Buffer.from(jpegPending.subarray(next)) : Buffer.alloc(0);
      }
      return;
    }
    const len = end + 2;
    if (len > MAX_JPEG_FRAME_BYTES) {
      videoInvalidFrames++;
      jpegPending = jpegPending.subarray(len);
      continue;
    }
    const frame = Buffer.from(jpegPending.subarray(0, len));
    jpegPending = jpegPending.subarray(len);
    lastVideoFrameReceived = Date.now();
    videoQueue.push(frame);
    if (videoQueue.length > VIDEO_QUEUE_MAX) {
      videoQueue.shift();
      videoDroppedFrames++;
    }
  }
}
function broadcastFrame(frame) {
  const now = Date.now();
  const seq = frameSequence;
  const header = Buffer.from(
    `--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${frame.length}\r\n\r\n`
  );
  const trailer = Buffer.from('\r\n');

  for (const [res, state] of videoClients) {
    if (res.destroyed || res.writableEnded) {
      disconnectVideo(res);
      continue;
    }
    if (state.blocked) {
      if (now - state.blockedAt > MAX_CLIENT_BLOCK_MS) {
        disconnectVideo(res);
        try { res.destroy(); } catch (_) {}
      } else if (now - state.blockedAt > CLIENT_SKIP_THRESHOLD_MS) {
        state.skipped++;
      }
      continue;
    }
    if (state.lastSeq === seq) continue;
    if (state.interval && now - state.lastSent < state.interval * 0.9) {
      state.skipped++;
      continue;
    }
    try {
      let ok = res.write(header);
      if (!res.write(frame)) ok = false;
      if (!res.write(trailer)) ok = false;
      state.lastSeq = seq;
      state.lastSent = now;
      videoSentFrames++;
      if (!ok) {
        state.blocked = true;
        state.blockedAt = now;
        res.once('drain', () => {
          state.blocked = false;
          state.blockedAt = 0;
        });
      }
    } catch (_) {
      disconnectVideo(res);
      try { res.destroy(); } catch (_) {}
    }
  }
}

// ---------------- SYNC / MASTER CLOCK ----------------
function resetClock() {
  syncEpoch = 0;
  videoFramesSinceSync = 0;
  audioFramesSinceSync = 0;
  audioStartDeadline = 0;
  audioTrackAvailable = false;
  audioTrackTimedOut = false;
}
function masterTick() {
  const now = Date.now();

  // Video readiness is independent. Audio gets a bounded priming window.
  if (!syncEpoch && videoQueue.length >= VIDEO_QUEUE_TARGET) {
    if (!audioStartDeadline) audioStartDeadline = now + AUDIO_START_GRACE_MS;
    if (audioPrimed || now >= audioStartDeadline) {
      if (!audioPrimed) audioTrackTimedOut = true;
      syncEpoch = now;
      videoFramesSinceSync = 0;
      audioFramesSinceSync = 0;
      console.log('[SYNC] Epoch started; audio primed:', audioPrimed);
    }
  }

  if (syncEpoch) {
    const elapsed = now - syncEpoch;

    // Video runs at its own clock; it never waits for an absent audio track.
    const expectedVideo = Math.floor(elapsed / VIDEO_INTERVAL);
    let dueVideo = expectedVideo - videoFramesSinceSync;
    while (dueVideo > 0 && videoQueue.length) {
      const frame = videoQueue.shift();
      videoFramesSinceSync++;
      latestFrame = frame;
      frameSequence++;
      lastVideoFrameTime = now;
      if (streamReady) broadcastFrame(frame);
      dueVideo--;
    }
    // If the input briefly stalls, don't accumulate seconds of stale frames.
    if (videoQueue.length > VIDEO_QUEUE_TARGET + 2) {
      const drop = videoQueue.length - (VIDEO_QUEUE_TARGET + 2);
      videoQueue.splice(0, drop);
      videoDroppedFrames += drop;
    }

    // Audio follows the same epoch. Silence is emitted during short underflows.
    if (audioPrimed || audioTrackAvailable) {
      const expectedAudio = Math.floor(elapsed / AUDIO_FRAME_MS);
      let dueAudio = expectedAudio - audioFramesSinceSync;
      if (dueAudio > 8) {
        const skip = dueAudio - 2;
        const skipBytes = Math.min(skip * AUDIO_FRAME_BYTES, audioBuffer.length) & ~1;
        audioBuffer = audioBuffer.subarray(skipBytes);
        audioFramesSinceSync += skip;
        dueAudio = 2;
      }
      while (dueAudio-- > 0) {
        const { frame, silence } = takeAudioFrame();
        audioFramesSinceSync++;
        if (streamReady) {
          for (const res of audioClients.keys()) writeAudio(res, frame, silence);
        }
      }
    }
  }

  if (!streamReady && syncEpoch && now - syncEpoch >= STREAM_READY_GRACE_MS) setReady();

  for (const [res, state] of audioClients) {
    if (state.blocked && now - state.blockedAt > MAX_AUDIO_BLOCK_MS) {
      disconnectAudio(res);
      try { res.destroy(); } catch (_) {}
    }
    if (res.destroyed || res.writableEnded) disconnectAudio(res);
  }
}
function startMasterTimer() {
  if (masterTimer) clearInterval(masterTimer);
  masterTimer = setInterval(masterTick, MASTER_TICK_MS);
}

// ---------------- FFMPEG ----------------
function clearWatchdog() {
  if (watchdogTimer) clearInterval(watchdogTimer);
  watchdogTimer = null;
}
function stopFFmpeg({ manual = true, disconnectClients = true } = {}) {
  generation++;
  manuallyStopped = manual;
  restarting = false;
  clearWatchdog();
  if (restartTimer) clearTimeout(restartTimer);
  restartTimer = null;

  const old = ffmpeg;
  ffmpeg = null;
  clearAudio();
  clearVideo();
  resetClock();
  resetReady('stop');
  if (old) { try { old.kill('SIGKILL'); } catch (_) {} }
  if (disconnectClients) closeAllClients();
}
function startFFmpeg(channel) {
  if (!channel?.url) throw new Error('Invalid channel URL');
  stopFFmpeg({ manual: false, disconnectClients: false });
  manuallyStopped = false;
  currentChannel = channel;
  clearAudio();
  clearVideo();
  resetClock();
  resetReady('new channel');
  videoDroppedFrames = 0;
  videoInvalidFrames = 0;
  videoSentFrames = 0;
  lastVideoFrameReceived = Date.now();
  lastVideoFrameTime = 0;

  const gen = generation;
  const preset = currentPreset();
  const vf = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    'setsar=1'
  ].join(',');

  // Do not use -re for live network inputs: it can throttle an already-live
  // source. Keep probing modest, but not so low that common IPTV streams fail.
  const args = [
    '-hide_banner', '-loglevel', 'warning', '-nostdin',
    '-probesize', '500000', '-analyzeduration', '500000',
    '-rw_timeout', '30000000',
    '-reconnect', '1', '-reconnect_streamed', '1', '-reconnect_delay_max', '5',
    '-user_agent', 'Mozilla/5.0',
    '-fflags', '+discardcorrupt+genpts',
    '-threads', String(DECODER_THREADS),
    '-filter_threads', '1',
    '-i', channel.url,

    '-map', '0:v:0?', '-an',
    '-vf', vf,
    '-c:v', 'mjpeg', '-q:v', String(preset.jpegQuality),
    '-threads', String(ENCODER_THREADS),
    '-r', String(VIDEO_FPS), '-fps_mode', 'cfr',
    '-flush_packets', '1', '-f', 'image2pipe', 'pipe:1',

    '-map', '0:a:0?', '-vn',
    '-af', `aresample=${AUDIO_SAMPLE_RATE}:async=100:first_pts=0`,
    '-ac', String(AUDIO_CHANNELS), '-ar', String(AUDIO_SAMPLE_RATE),
    '-c:a', 'pcm_s16le', '-flush_packets', '1',
    '-f', 's16le', 'pipe:3'
  ];

  console.log('[FFMPEG] Starting:', channel.name, 'quality:', preset.id);
  const child = spawn('ffmpeg', args, { stdio: ['ignore', 'pipe', 'pipe', 'pipe'] });
  ffmpeg = child;

  child.stdout.on('data', chunk => processVideoData(chunk, gen));
  if (child.stdio[3]) {
    child.stdio[3].on('data', chunk => {
      if (gen === generation) pushAudio(chunk);
    });
    child.stdio[3].on('error', e => {
      if (gen === generation) console.warn('[AUDIO PIPE]', e.message);
    });
  }
  child.stderr.on('data', data => {
    if (gen !== generation) return;
    const s = data.toString().trim();
    if (s) console.log('[FFmpeg]', s);
  });
  child.on('error', e => {
    if (gen === generation) console.error('[FFMPEG ERROR]', e.message);
  });
  child.on('close', (code, signal) => {
    console.log('[FFmpeg] Exited:', code, signal);
    if (gen !== generation) return;
    if (ffmpeg === child) ffmpeg = null;
    clearAudio();
    clearVideo();
    resetClock();
    resetReady('ffmpeg exit');
    if (!manuallyStopped) scheduleRestart();
  });

  watchdogTimer = setInterval(() => {
    if (gen !== generation || !ffmpeg || restarting) return;
    const age = Date.now() - lastVideoFrameReceived;
    if (age > VIDEO_TIMEOUT) {
      console.warn('[WATCHDOG] No video frame for', age, 'ms');
      scheduleRestart();
    }
  }, WATCHDOG_INTERVAL);
}
function scheduleRestart() {
  if (restarting || manuallyStopped) return;
  restarting = true;
  clearWatchdog();
  const old = ffmpeg;
  ffmpeg = null;
  generation++;
  clearAudio();
  clearVideo();
  resetClock();
  resetReady('restart');
  if (old) { try { old.kill('SIGKILL'); } catch (_) {} }
  if (restartTimer) clearTimeout(restartTimer);
  restartTimer = setTimeout(() => {
    restartTimer = null;
    restarting = false;
    if (currentChannel && !manuallyStopped) startFFmpeg(currentChannel);
  }, RESTART_DELAY);
}

// ---------------- STREAM ENDPOINTS ----------------
app.get('/stream', async (req, res) => {
  const requested = Number(req.query.fps);
  const fps = Number.isFinite(requested) && requested > 0
    ? Math.max(MIN_CLIENT_FPS, Math.min(MAX_CLIENT_FPS, Math.floor(requested)))
    : DEFAULT_CLIENT_FPS;
  const interval = fps >= VIDEO_FPS ? 0 : 1000 / fps;

  const ready = await waitForReady(STREAM_READY_TIMEOUT_MS);
  if (!ready) return res.status(503).json({ success: false, error: 'Stream not ready - try again' });

  res.writeHead(200, {
    'Content-Type': 'multipart/x-mixed-replace; boundary=frame',
    'Cache-Control': 'no-cache, no-store, must-revalidate',
    'Pragma': 'no-cache', 'Expires': '0',
    'Connection': 'keep-alive', 'X-Accel-Buffering': 'no',
    'X-Client-FPS': String(fps)
  });
  const state = {
    interval, lastSeq: -1, lastSent: 0,
    blocked: false, blockedAt: 0, skipped: 0
  };
  videoClients.set(res, state);

  if (latestFrame && Date.now() - lastVideoFrameTime < 1500) {
    const header = Buffer.from(`--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${latestFrame.length}\r\n\r\n`);
    res.write(header);
    res.write(latestFrame);
    res.write('\r\n');
    state.lastSeq = frameSequence;
    state.lastSent = Date.now();
  }
  res.on('close', () => disconnectVideo(res));
  res.on('error', () => disconnectVideo(res));
});

app.get('/audio', async (req, res) => {
  const ready = await waitForReady(STREAM_READY_TIMEOUT_MS);
  if (!ready) return res.status(503).json({ success: false, error: 'Stream not ready - try again' });

  res.statusCode = 200;
  res.setHeader('Content-Type', 'application/octet-stream');
  res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
  res.setHeader('Pragma', 'no-cache');
  res.setHeader('Connection', 'keep-alive');
  res.setHeader('Content-Encoding', 'identity');

  audioClients.set(res, { blocked: false, blockedAt: 0 });
  res.on('close', () => disconnectAudio(res));
  res.on('error', () => disconnectAudio(res));
});

// ---------------- QUALITY API ----------------
function qualityHandler(req, res) {
  const requested = req.params.quality || req.body?.quality || req.query.quality;
  const preset = requested === undefined ? currentPreset() : setQuality(requested);
  if (!preset) return res.status(400).json({ success: false, error: 'Unsupported quality', ...qualityResponse() });
  res.json({ success: true, ...qualityResponse() });
}
app.get('/api/config', qualityHandler);
app.get('/api/config/quality', qualityHandler);
app.get('/api/config/quality/:quality', qualityHandler);
app.post('/api/config/quality', qualityHandler);
app.post('/api/config/quality/:quality', qualityHandler);

// ---------------- CHANNEL API ----------------
app.get('/api/channels', (req, res) => {
  const raw = String(req.query.quality || req.query.q || req.query.max || '720').trim().toLowerCase();
  const max = raw === 'all' || raw === 'full' ? Number.MAX_SAFE_INTEGER : Math.max(1, Number.parseInt(raw, 10) || 720);
  const filtered = max === Number.MAX_SAFE_INTEGER ? channels : channels.filter(c => !c.resolution || c.resolution <= max);
  const resetSeconds = Math.max(3, Math.ceil(RESTART_DELAY / 1000));
  res.json({
    success: true,
    streamQuality: currentPreset().id,
    jpegQuality: currentPreset().jpegQuality,
    quality: max === Number.MAX_SAFE_INTEGER ? 'all' : String(max),
    channels: filtered.map(c => ({ ...c, resetSeconds, resetAtMs: Date.now() + resetSeconds * 1000 }))
  });
});
function selectChannelHandler(req, res) {
  let id;
  try { id = decodeURIComponent(req.params.id); }
  catch (_) { return res.status(400).json({ success: false, error: 'Invalid channel ID' }); }
  const channel = channels.find(c => c.id === id || c.name.toLowerCase() === id.toLowerCase());
  if (!channel) return res.status(404).json({ success: false, error: 'Channel not found' });
  try {
    startFFmpeg(channel);
    res.json({ success: true, channel: channel.name });
  } catch (e) {
    res.status(500).json({ success: false, error: e.message });
  }
}
app.get('/api/select/:id', selectChannelHandler);
app.post('/api/select/:id', selectChannelHandler);

function stopHandler(req, res) {
  stopFFmpeg({ manual: true, disconnectClients: true });
  currentChannel = null;
  res.json({ success: true, message: 'Stopped' });
}
app.get('/api/stop', stopHandler);
app.post('/api/stop', stopHandler);

app.get('/api/reload', async (req, res) => {
  try {
    await loadChannels();
    res.json({ success: true, count: channels.length });
  } catch (e) {
    res.status(500).json({ success: false, error: e.message });
  }
});

// ---------------- RENDER BANDWIDTH API ----------------
app.get('/api/bandwidth', async (req, res) => {
  try {
    if (!RENDER_API_KEY) return res.status(500).json({ success: false, error: 'Missing RENDER_API_KEY environment variable' });
    if (!RENDER_SERVICE_IDS.length) return res.status(500).json({ success: false, error: 'Missing RENDER_SERVICE_IDS' });
    if (!Number.isFinite(BANDWIDTH_LIMIT_GB) || BANDWIDTH_LIMIT_GB <= 0) {
      return res.status(500).json({ success: false, error: 'Invalid BANDWIDTH_LIMIT_GB' });
    }
    const now = new Date();
    const start = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), 1));
    const url = new URL('https://api.render.com/v1/metrics/bandwidth');
    url.searchParams.set('startTime', start.toISOString());
    url.searchParams.set('endTime', now.toISOString());
    for (const id of RENDER_SERVICE_IDS) url.searchParams.append('resource', id);

    const response = await fetch(url, {
      headers: { Authorization: `Bearer ${RENDER_API_KEY}`, Accept: 'application/json' },
      signal: AbortSignal.timeout(15000)
    });
    if (!response.ok) {
      const details = await response.text();
      return res.status(response.status).json({ success: false, error: 'Render API error', httpStatus: response.status, details });
    }
    const data = await response.json();
    if (!Array.isArray(data)) throw new Error('Invalid Render bandwidth response');

    let usedGB = 0;
    let totalPoints = 0;
    const services = [];
    for (const series of data) {
      const labels = Array.isArray(series.labels) ? series.labels : [];
      const label = labels.find(x => x.field === 'service');
      const unit = String(series.unit || 'GB').toUpperCase();
      let serviceGB = 0;
      for (const point of (series.values || [])) {
        const value = Number(point.value);
        if (!Number.isFinite(value)) continue;
        if (unit === 'GB') serviceGB += value;
        else if (unit === 'MB') serviceGB += value / 1024;
        else if (['BYTE', 'BYTES', 'B'].includes(unit)) serviceGB += value / (1024 ** 3);
        else throw new Error('Unsupported bandwidth unit: ' + unit);
        totalPoints++;
      }
      usedGB += serviceGB;
      services.push({
        serviceId: label ? label.value : 'unknown',
        usedGB: Number(serviceGB.toFixed(4)),
        unit,
        dataPoints: (series.values || []).length
      });
    }
    usedGB = Number(usedGB.toFixed(4));
    const remainingGB = Math.max(0, BANDWIDTH_LIMIT_GB - usedGB);
    const resetAt = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, 1));
    const resetInSeconds = Math.max(0, Math.ceil((resetAt.getTime() - Date.now()) / 1000));
    const usedPercent = Math.min(100, Number((usedGB / BANDWIDTH_LIMIT_GB * 100).toFixed(2)));
    let status = 'NORMAL';
    if (remainingGB <= 0) status = 'LIMIT_REACHED';
    else if (remainingGB <= BANDWIDTH_LIMIT_GB * 0.1) status = 'WARNING';
    res.json({
      success: true,
      provider: 'Render Official API',
      period: { start: start.toISOString(), end: now.toISOString(), timezone: 'UTC' },
      bandwidth: {
        limitGB: BANDWIDTH_LIMIT_GB, usedGB, remainingGB,
        usedPercent, remainingPercent: Number((100 - usedPercent).toFixed(2))
      },
      resetInSeconds, resetAt: resetAt.toISOString(), status, services,
      serviceCount: RENDER_SERVICE_IDS.length, returnedSeries: data.length,
      totalDataPoints: totalPoints, updatedAt: new Date().toISOString(),
      note: 'Metrics are delayed and may not equal exact real-time billing balance.'
    });
  } catch (e) {
    console.error('[BANDWIDTH ERROR]', e.message);
    res.status(500).json({ success: false, error: e.message });
  }
});

// ---------------- HEALTH ----------------
app.get('/health', (req, res) => {
  const mem = process.memoryUsage();
  const now = Date.now();
  const clientDetails = [];
  for (const [, s] of videoClients) {
    clientDetails.push({
      fps: s.interval ? Math.round(1000 / s.interval) : VIDEO_FPS,
      skipped: s.skipped, blocked: s.blocked,
      blockDurationMs: s.blocked ? now - s.blockedAt : 0,
      lastSentAgoMs: s.lastSent ? now - s.lastSent : null
    });
  }
  res.json({
    status: 'running',
    channelCount: channels.length,
    currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg, restarting, manuallyStopped,
    pipeline: 'LOW_LATENCY_MJPEG_PCM_SHARED_EPOCH',
    videoWidth: VIDEO_WIDTH, videoHeight: VIDEO_HEIGHT, videoFPS: VIDEO_FPS,
    streamReady, streamReadyAt,
    streamReadyWaiters: readyWaiters.length,
    videoPrimed: videoQueue.length >= VIDEO_QUEUE_TARGET,
    videoQueueLength: videoQueue.length,
    videoQueueTarget: VIDEO_QUEUE_TARGET, videoQueueMax: VIDEO_QUEUE_MAX,
    videoDroppedFrames, videoInvalidFrames, videoSentFrames,
    videoClients: videoClients.size, audioClients: audioClients.size,
    videoPendingBytes: jpegPending.length,
    videoLatestFrameBytes: latestFrame ? latestFrame.length : 0,
    videoFrameSequence: frameSequence,
    videoFrameAge: lastVideoFrameReceived ? now - lastVideoFrameReceived : null,
    videoLastBroadcastAge: lastVideoFrameTime ? now - lastVideoFrameTime : null,
    clientDetails,
    sync: {
      epoch: syncEpoch,
      audioFramesSinceSync, videoFramesSinceSync,
      audioTrackAvailable, audioTrackTimedOut,
      audioPrimed
    },
    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFrameBytes: AUDIO_FRAME_BYTES,
    audioFrameMs: AUDIO_FRAME_MS,
    audioBufferBytes: audioBuffer.length,
    audioBufferMs: Math.round(audioBuffer.length / (AUDIO_SAMPLE_RATE * 2) * 1000),
    audioBufferMaxMs: AUDIO_BUFFER_MAX_MS,
    audioUnderflows, audioOverflowBytes,
    audioFramesSent, audioSilenceSent, audioMaxObservedBytes,
    masterTickMs: MASTER_TICK_MS,
    memory: {
      rssMB: Number((mem.rss / 1048576).toFixed(2)),
      heapUsedMB: Number((mem.heapUsed / 1048576).toFixed(2)),
      externalMB: Number((mem.external / 1048576).toFixed(2)),
      arrayBuffersMB: Number((mem.arrayBuffers / 1048576).toFixed(2))
    },
    generation
  });
});

// ---------------- ROOT / START ----------------
app.get('/', (req, res) => {
  res.type('text/plain').send(
    'IPTV SERVER RUNNING - LOW LATENCY SYNC\n' +
    '/stream[?fps=12] -> MJPEG video\n' +
    '/audio -> PCM audio\n' +
    'Video no longer waits indefinitely for audio; audio shares the startup epoch when available.\n'
  );
});

async function main() {
  try { await loadChannels(); }
  catch (e) { console.warn('[STARTUP] Playlist failed:', e.message); }

  startMasterTimer();
  app.listen(PORT, '0.0.0.0', () => {
    console.log('--------------------------------');
    console.log('IPTV SERVER RUNNING');
    console.log('PORT:', PORT);
    console.log('CHANNELS:', channels.length);
    console.log(`VIDEO: ${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
    console.log('VIDEO QUEUE TARGET/MAX:', VIDEO_QUEUE_TARGET, '/', VIDEO_QUEUE_MAX);
    console.log('AUDIO START BUFFER:', AUDIO_START_BUFFER_MS, 'ms');
    console.log('AUDIO START GRACE:', AUDIO_START_GRACE_MS, 'ms');
    console.log('--------------------------------');
  });

  if (!channels.length) {
    const retry = async () => {
      try { await loadChannels(); console.log('[M3U] Playlist recovered:', channels.length); }
      catch (e) { console.warn('[M3U] Retry failed:', e.message); setTimeout(retry, 15000); }
    };
    setTimeout(retry, 15000);
  }
}
main().catch(e => {
  console.error('[SERVER ERROR]', e);
  process.exit(1);
});
