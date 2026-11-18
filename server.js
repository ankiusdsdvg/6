const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = Number(process.env.PORT || 10000);
app.use(express.json({ limit: "32kb" }));

// =====================================================
// CONFIG
// =====================================================
const M3U_URLS = [
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u",
  "https://iptv-org.github.io/iptv/countries/vn.m3u"
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 240;
const VIDEO_FPS = 12;
const DEFAULT_CLIENT_FPS = 12;
const MIN_CLIENT_FPS = 1;
const MAX_CLIENT_FPS = 30;
const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

const QUALITY_PRESETS = Object.freeze([
  Object.freeze({ id: "1080p", label: "1080p", jpegQuality: 10 }),
  Object.freeze({ id: "720p", label: "720p", jpegQuality: 15 }),
  Object.freeze({ id: "540p", label: "540p", jpegQuality: 20 }),
  Object.freeze({ id: "340p", label: "340p", jpegQuality: 25 })
]);
let currentQualityId = "1080p";

// Audio: 16 kHz, mono, signed 16-bit PCM
const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;
const AUDIO_FRAME_MS = 200;
const AUDIO_INTERVAL = AUDIO_FRAME_MS;
const AUDIO_FRAME_BYTES = AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE * AUDIO_FRAME_MS / 1000;
const AUDIO_BYTES_PER_MS = AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE / 1000;

// Lower startup buffering. Audio and video are primed independently.
const AUDIO_START_BUFFER_MS = 600;
const AUDIO_BUFFER_MS = 2500;
const AUDIO_BUFFER_MAX = AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE * AUDIO_BUFFER_MS / 1000;
const VIDEO_QUEUE_TARGET = 6;       // about 500 ms at 12 FPS
const VIDEO_QUEUE_MAX = 24;         // about 2 seconds
const STREAM_READY_GRACE_MS = 100;
const STREAM_READY_TIMEOUT_MS = 25000;
const MASTER_TICK_MS = 10;

const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;
const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;
const MAX_VIDEO_BUFFER = 512 * 1024;
const MAX_JPEG_FRAME_BYTES = 256 * 1024;
const CLIENT_SKIP_THRESHOLD_MS = 300;
const MAX_CLIENT_BLOCK_MS = 3000;
const MAX_AUDIO_BLOCK_MS = 1500;
const JPEG_SOI = Buffer.from([0xff, 0xd8]);
const JPEG_EOI = Buffer.from([0xff, 0xd9]);

// Never hard-code Render credentials. Set RENDER_API_KEY in the environment.
const RENDER_API_KEY = process.env.RENDER_API_KEY || "";
const RENDER_SERVICE_IDS = (process.env.RENDER_SERVICE_IDS || "srv-dbs5vb8n74is738ut5e0")
  .split(",").map(x => x.trim()).filter(Boolean);
const BANDWIDTH_LIMIT_GB = Number(process.env.BANDWIDTH_LIMIT_GB || 5);

// =====================================================
// GLOBAL STATE
// =====================================================
let channels = [];
let currentChannel = null;
let ffmpeg = null;
let generation = 0;
let manuallyStopped = true;
let restarting = false;
let watchdogTimer = null;
let restartTimer = null;

let latestFrame = null;
let frameSequence = 0;
let jpegPending = Buffer.alloc(0);
let videoQueue = [];
let videoPrimed = false;
let videoClients = 0;
const videoClientsMap = new Map();
let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let videoSentFrames = 0;
let videoFramesIn = 0;
let lastVideoFrameReceived = 0;
let lastVideoFrameTime = 0;

let audioBuffer = Buffer.alloc(0);
let audioPrimed = false;
let audioClient = null;
let audioBlocked = false;
let audioBlockedSince = 0;
let audioUnderflows = 0;
let audioOverflowBytes = 0;
let audioFramesSent = 0;
let audioSilenceSent = 0;
let audioSilenceBytes = 0;
let audioMaxObservedBytes = 0;
let audioBytesIn = 0;
let audioStableFrames = 0;
let audioTargetBufferMs = AUDIO_START_BUFFER_MS;

let masterTimer = null;
let videoEpoch = 0;
let audioEpoch = 0;
let videoFramesSinceSync = 0;
let audioFramesSinceSync = 0;
let lastDriftCheck = 0;

// Video readiness and audio readiness are separate so a silent source
// cannot hold /stream indefinitely.
let streamReady = false;
let streamReadyAt = 0;
let audioReady = false;
let audioReadyAt = 0;
const videoReadyWaiters = [];
const audioReadyWaiters = [];

let ffmpegStartTime = 0;
let firstVideoByteAt = 0;
let firstAudioByteAt = 0;
let audioDetected = false;
let audioDetectWarned = false;

// =====================================================
// READY GATES
// =====================================================
function resolveWaiters(waiters) {
  for (const fn of waiters.splice(0)) {
    try { fn(); } catch (_) {}
  }
}
function setVideoReady() {
  if (streamReady) return;
  streamReady = true;
  streamReadyAt = Date.now();
  console.log("[VIDEO] READY — video endpoint released (", streamReadyAt - ffmpegStartTime, "ms )");
  resolveWaiters(videoReadyWaiters);
}
function setAudioReady() {
  if (audioReady) return;
  audioReady = true;
  audioReadyAt = Date.now();
  console.log("[AUDIO] READY — audio endpoint released (", audioReadyAt - ffmpegStartTime, "ms )");
  resolveWaiters(audioReadyWaiters);
}
function resetReady(reason = "") {
  streamReady = false;
  streamReadyAt = 0;
  audioReady = false;
  audioReadyAt = 0;
  if (reason) console.log("[READY] Reset:", reason);
}
function waitForReady(kind, timeoutMs) {
  const isAudio = kind === "audio";
  if (isAudio ? audioReady : streamReady) return Promise.resolve(true);
  const waiters = isAudio ? audioReadyWaiters : videoReadyWaiters;
  return new Promise(resolve => {
    let done = false;
    const timer = setTimeout(() => {
      if (done) return;
      done = true;
      const i = waiters.indexOf(wrap);
      if (i >= 0) waiters.splice(i, 1);
      resolve(false);
    }, timeoutMs);
    const wrap = () => {
      if (done) return;
      done = true;
      clearTimeout(timer);
      resolve(true);
    };
    waiters.push(wrap);
  });
}

// =====================================================
// PLAYLIST / QUALITY
// =====================================================
function parseResolutionFromName(name) {
  const m = name.match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);
  return m ? Number(m[1] || m[2]) || 0 : 0;
}
function parseM3U(content) {
  const result = [];
  let info = null;
  for (const raw of content.split(/\r?\n/)) {
    const line = raw.trim();
    if (!line) continue;
    if (line.startsWith("#EXTINF:")) { info = line; continue; }
    if (line.startsWith("#") || !info) continue;
    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(line)) { info = null; continue; }
    const name = info.split(",").pop().trim() || "Unknown channel";
    const group = info.match(/group-title="([^"]*)"/i);
    const logo = info.match(/tvg-logo="([^"]*)"/i);
    const tvgId = info.match(/tvg-id="([^"]*)"/i);
    result.push({ id: String(result.length), name, group: group?.[1] || "", logo: logo?.[1] || "", tvgId: tvgId?.[1] || "", resolution: parseResolutionFromName(name), url: line });
    info = null;
  }
  return result;
}
function filterChannelsByResolution(list, max = 720) {
  if (!Array.isArray(list)) return [];
  return max === Number.MAX_SAFE_INTEGER ? list : list.filter(c => !c.resolution || c.resolution <= max);
}
function normalizeQualityId(value) {
  const raw = String(value || "").trim().toLowerCase().replace(/\s+/g, "");
  if (!raw) return null;
  const id = raw.endsWith("p") ? raw : `${raw}p`;
  return QUALITY_PRESETS.some(p => p.id === id) ? id : null;
}
function getCurrentQualityPreset() {
  return QUALITY_PRESETS.find(p => p.id === currentQualityId) || QUALITY_PRESETS[0];
}
function qualityResponse() {
  const p = getCurrentQualityPreset();
  return { quality: p.id, jpegQuality: p.jpegQuality, presets: QUALITY_PRESETS.map(x => ({ id: x.id, label: x.label, jpegQuality: x.jpegQuality })) };
}
function setQuality(value) {
  const id = normalizeQualityId(value);
  if (!id) return null;
  const changed = id !== currentQualityId;
  currentQualityId = id;
  if (changed && currentChannel && !manuallyStopped) startFFmpeg(currentChannel);
  return getCurrentQualityPreset();
}
async function loadChannels() {
  console.log("[M3U] Loading playlist...");
  let lastError;
  for (const url of M3U_URLS) {
    try {
      const r = await fetch(url, { headers: { "User-Agent": "Mozilla/5.0" }, signal: AbortSignal.timeout(20000) });
      if (!r.ok) throw new Error("HTTP " + r.status);
      const parsed = parseM3U(await r.text());
      if (!parsed.length) throw new Error("Playlist contains no channels");
      channels = parsed;
      console.log("[M3U] Loaded:", channels.length, "from", url);
      return channels;
    } catch (e) { lastError = e; console.warn("[M3U] Failed:", e.message); }
  }
  throw lastError || new Error("No playlist available");
}

// =====================================================
// BUFFER HELPERS
// =====================================================
function resetAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioStableFrames = 0;
  audioTargetBufferMs = AUDIO_START_BUFFER_MS;
  audioMaxObservedBytes = 0;
}
function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
  videoQueue = [];
  videoPrimed = false;
}
function disconnectAudioClient(clearBuffer = false) {
  const old = audioClient;
  audioClient = null;
  audioBlocked = false;
  audioBlockedSince = 0;
  if (clearBuffer) resetAudioBuffer();
  if (old && !old.destroyed) { try { old.destroy(); } catch (_) {} }
}
function pushAudioBuffer(chunk) {
  if (!chunk?.length) return;
  audioBytesIn += chunk.length;
  if (chunk.length & 1) chunk = chunk.subarray(0, chunk.length - 1);
  if (!chunk.length) return;
  const total = audioBuffer.length + chunk.length;
  if (total > AUDIO_BUFFER_MAX) {
    const excess = total - AUDIO_BUFFER_MAX;
    const drop = excess + (excess & 1);
    audioOverflowBytes += drop;
    if (drop >= audioBuffer.length) {
      audioBuffer = Buffer.from(chunk.subarray(Math.max(0, chunk.length - AUDIO_BUFFER_MAX)));
    } else {
      audioBuffer = Buffer.concat([audioBuffer.subarray(drop), chunk]);
    }
  } else {
    audioBuffer = audioBuffer.length ? Buffer.concat([audioBuffer, chunk], total) : Buffer.from(chunk);
  }
  if (audioBuffer.length > AUDIO_BUFFER_MAX) audioBuffer = Buffer.from(audioBuffer.subarray(-AUDIO_BUFFER_MAX));
  if (audioBuffer.length & 1) audioBuffer = Buffer.from(audioBuffer.subarray(1));
  audioMaxObservedBytes = Math.max(audioMaxObservedBytes, audioBuffer.length);
}
function takeAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES, 0);
  const count = Math.min(audioBuffer.length, AUDIO_FRAME_BYTES) & ~1;
  if (count) { audioBuffer.copy(frame, 0, 0, count); audioBuffer = audioBuffer.subarray(count); }
  if (count < AUDIO_FRAME_BYTES) {
    audioUnderflows++;
    audioSilenceBytes += AUDIO_FRAME_BYTES - count;
    audioStableFrames = 0;
    audioTargetBufferMs = Math.min(2500, audioTargetBufferMs + 100);
  } else {
    audioStableFrames++;
    if (audioStableFrames >= 50) { audioTargetBufferMs = Math.max(300, audioTargetBufferMs - 50); audioStableFrames = 0; }
  }
  return frame;
}
function writeAudioFrame(frame) {
  if (!audioClient || audioClient.destroyed || audioClient.writableEnded) return false;
  try {
    const ok = audioClient.write(frame);
    audioFramesSent++;
    if (!ok) {
      audioBlocked = true;
      audioBlockedSince = Date.now();
      audioClient.once("drain", () => { audioBlocked = false; audioBlockedSince = 0; });
      return false;
    }
    return true;
  } catch (e) { console.error("[AUDIO WRITE]", e.message); disconnectAudioClient(false); return false; }
}

// =====================================================
// VIDEO FRAME PARSER / CLIENTS
// =====================================================
function cleanupVideoClient(res) {
  if (!videoClientsMap.has(res)) return;
  videoClientsMap.delete(res);
  videoClients = Math.max(0, videoClients - 1);
}
function broadcastFrame(frame) {
  if (!frame || !videoClientsMap.size) return;
  const now = Date.now();
  const header = Buffer.from(`--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${frame.length}\r\n\r\n`);
  const trailer = Buffer.from("\r\n");
  for (const [res, s] of videoClientsMap) {
    if (res.destroyed || res.writableEnded) { cleanupVideoClient(res); continue; }
    if (s.blocked) {
      const blockedFor = now - s.blockedSince;
      if (blockedFor > MAX_CLIENT_BLOCK_MS) { cleanupVideoClient(res); try { res.destroy(); } catch (_) {} continue; }
      if (blockedFor > CLIENT_SKIP_THRESHOLD_MS) { s.skippedFrames++; continue; }
    }
    if (s.lastSentSequence === frameSequence) continue;
    if (s.clientInterval > 0 && now - s.lastSentTime < s.clientInterval * 0.9) { s.skippedFrames++; continue; }
    try {
      let ok = res.write(header);
      if (!res.write(frame)) ok = false;
      if (!res.write(trailer)) ok = false;
      s.lastSentSequence = frameSequence;
      s.lastSentTime = now;
      videoSentFrames++;
      if (!ok && !s.blocked) {
        s.blocked = true; s.blockedSince = Date.now(); s.blockCount++;
        res.once("drain", () => { s.blocked = false; s.blockedSince = 0; });
      }
    } catch (e) { console.error("[VIDEO WRITE]", e.message); cleanupVideoClient(res); try { res.destroy(); } catch (_) {} }
  }
}
function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation || !chunk?.length) return;
  if (chunk.length > MAX_VIDEO_BUFFER) { chunk = chunk.subarray(chunk.length - MAX_VIDEO_BUFFER); videoInvalidFrames++; }
  if (jpegPending.length + chunk.length > MAX_VIDEO_BUFFER) {
    const combined = Buffer.concat([jpegPending, chunk]);
    const lastStart = combined.lastIndexOf(JPEG_SOI);
    jpegPending = lastStart >= 0 ? Buffer.from(combined.subarray(lastStart)) : Buffer.alloc(0);
    videoInvalidFrames++;
  } else jpegPending = jpegPending.length ? Buffer.concat([jpegPending, chunk]) : Buffer.from(chunk);

  while (jpegPending.length) {
    const start = jpegPending.indexOf(JPEG_SOI);
    if (start < 0) { jpegPending = jpegPending[jpegPending.length - 1] === 0xff ? Buffer.from([0xff]) : Buffer.alloc(0); return; }
    if (start > 0) jpegPending = jpegPending.subarray(start);
    const end = jpegPending.indexOf(JPEG_EOI, 2);
    if (end < 0) {
      if (jpegPending.length > MAX_JPEG_FRAME_BYTES) {
        videoInvalidFrames++;
        const next = jpegPending.indexOf(JPEG_SOI, 2);
        jpegPending = next >= 0 ? Buffer.from(jpegPending.subarray(next)) : Buffer.alloc(0);
      }
      return;
    }
    const len = end + 2;
    if (len > MAX_JPEG_FRAME_BYTES) { videoInvalidFrames++; jpegPending = jpegPending.subarray(len); continue; }
    const frame = Buffer.from(jpegPending.subarray(0, len));
    lastVideoFrameReceived = Date.now();
    videoFramesIn++;
    videoQueue.push(frame);
    if (videoQueue.length > VIDEO_QUEUE_MAX) { videoQueue.shift(); videoDroppedFrames++; }
    jpegPending = jpegPending.subarray(len);
  }
}

// =====================================================
// MASTER CLOCK — independent video/audio start
// =====================================================
function masterTick() {
  const now = Date.now();

  if (!videoPrimed && videoQueue.length >= VIDEO_QUEUE_TARGET) {
    videoPrimed = true;
    videoEpoch = now;
    videoFramesSinceSync = 0;
    console.log("[VIDEO] Primed:", videoQueue.length, "frames");
  }
  if (!audioPrimed) {
    const targetBytes = Math.floor(AUDIO_BYTES_PER_MS * audioTargetBufferMs);
    if (audioBuffer.length >= targetBytes) {
      audioPrimed = true;
      audioEpoch = now;
      audioFramesSinceSync = 0;
      console.log("[AUDIO] Primed:", audioBuffer.length, "bytes / target:", audioTargetBufferMs, "ms");
    }
  }

  if (videoPrimed && !streamReady && now - videoEpoch >= STREAM_READY_GRACE_MS) setVideoReady();
  if (audioPrimed && !audioReady) setAudioReady();

  // Video clock starts as soon as video is primed; audio absence cannot block picture.
  if (videoPrimed && videoEpoch) {
    const expected = Math.floor((now - videoEpoch) / VIDEO_INTERVAL);
    const gap = expected - videoFramesSinceSync;
    if (gap > 0 && videoQueue.length) {
      const count = Math.min(gap, videoQueue.length, 3);
      for (let i = 0; i < count; i++) {
        const frame = videoQueue.shift();
        if (!frame) break;
        videoFramesSinceSync++;
        latestFrame = frame;
        frameSequence++;
        lastVideoFrameTime = Date.now();
        if (streamReady) broadcastFrame(frame);
      }
    }
  }

  // Audio has its own epoch. If source has no audio, video continues normally.
  if (audioPrimed && audioEpoch) {
    const expected = Math.floor((now - audioEpoch) / AUDIO_INTERVAL);
    const gap = expected - audioFramesSinceSync;
    if (gap > 0) {
      if (gap > 5) {
        const skip = gap - 1;
        const skipBytes = Math.min(skip * AUDIO_FRAME_BYTES, audioBuffer.length) & ~1;
        audioBuffer = audioBuffer.subarray(skipBytes);
        audioFramesSinceSync += skip;
      }
      const count = Math.min(gap, 2);
      for (let i = 0; i < count; i++) {
        const frame = takeAudioFrame();
        audioFramesSinceSync++;
        if (audioReady && audioClient && !audioClient.destroyed && !audioClient.writableEnded && !audioBlocked) writeAudioFrame(frame);
      }
    }
  }

  if (audioClient && (audioClient.destroyed || audioClient.writableEnded)) disconnectAudioClient(false);
  if (audioClient && audioBlocked && now - audioBlockedSince > MAX_AUDIO_BLOCK_MS) {
    console.log("[AUDIO] Slow client disconnected");
    disconnectAudioClient(false);
  }

  if (audioReady && !firstAudioByteAt && !audioDetectWarned && ffmpegStartTime && now - ffmpegStartTime > 5000) {
    audioDetectWarned = true;
    console.log("[AUDIO] WARNING: no audio data after 5s — source may not contain audio");
  }

  if (audioPrimed && videoPrimed && now - lastDriftCheck >= 3000) {
    // Independent clocks are intentional; report their relative startup offset only.
    lastDriftCheck = now;
  }
}
function startMasterTimer() {
  if (masterTimer) clearInterval(masterTimer);
  masterTimer = setInterval(masterTick, MASTER_TICK_MS);
}

// =====================================================
// FFMPEG LIFECYCLE
// =====================================================
function clearWatchdog() {
  if (watchdogTimer) { clearInterval(watchdogTimer); watchdogTimer = null; }
}
function stopFFmpeg({ manual = true, disconnectClients = true } = {}) {
  generation++;
  manuallyStopped = manual;
  restarting = false;
  clearWatchdog();
  if (restartTimer) { clearTimeout(restartTimer); restartTimer = null; }
  const old = ffmpeg;
  ffmpeg = null;
  resetAudioBuffer();
  clearVideoBuffer();
  videoEpoch = 0; audioEpoch = 0;
  videoFramesSinceSync = 0; audioFramesSinceSync = 0;
  resetReady("stopFFmpeg");
  if (old) { try { old.kill("SIGKILL"); } catch (_) {} }
  if (disconnectClients) {
    disconnectAudioClient(true);
    for (const res of videoClientsMap.keys()) { try { res.destroy(); } catch (_) {} }
    videoClientsMap.clear(); videoClients = 0;
  }
}
function startFFmpeg(channel) {
  if (!channel?.url) { console.log("[FFMPEG] Invalid channel"); return; }
  stopFFmpeg({ manual: false, disconnectClients: false });
  manuallyStopped = false;
  currentChannel = channel;
  clearVideoBuffer();
  resetAudioBuffer();
  videoEpoch = 0; audioEpoch = 0;
  videoFramesSinceSync = 0; audioFramesSinceSync = 0;
  resetReady("startFFmpeg");
  videoDroppedFrames = 0; videoInvalidFrames = 0; videoSentFrames = 0;
  audioUnderflows = 0; audioOverflowBytes = 0; audioFramesSent = 0; audioSilenceSent = 0; audioSilenceBytes = 0;
  audioBytesIn = 0; videoFramesIn = 0;
  lastVideoFrameReceived = Date.now();
  lastVideoFrameTime = Date.now();
  ffmpegStartTime = Date.now();
  firstVideoByteAt = 0; firstAudioByteAt = 0; audioDetected = false; audioDetectWarned = false;
  const currentGeneration = generation;
  const preset = getCurrentQualityPreset();

  console.log("\n==================================");
  console.log("CHANNEL:", channel.name);
  console.log("GENERATION:", currentGeneration);
  console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
  console.log("JPEG QUALITY:", preset.label, preset.jpegQuality);
  console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM`);
  console.log("AUDIO START BUFFER:", AUDIO_START_BUFFER_MS, "ms");
  console.log("VIDEO QUEUE TARGET:", VIDEO_QUEUE_TARGET, "frames");
  console.log("MODE: INDEPENDENT VIDEO/AUDIO READY + NO INPUT -re");
  console.log("==================================");

  const videoFilter = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  const args = [
    "-hide_banner", "-loglevel", "warning", "-nostdin",
    "-probesize", "800000",
    "-analyzeduration", "800000",
    "-rw_timeout", "15000000",
    "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "5",
    "-user_agent", "Mozilla/5.0",
    // Deliberately omit -re: IPTV live inputs already arrive in real time.
    "-fflags", "+discardcorrupt+genpts",
    "-threads", String(DECODER_THREADS), "-filter_threads", "1",
    "-i", channel.url,
    "-map", "0:v:0?", "-an", "-vf", videoFilter,
    "-c:v", "mjpeg", "-q:v", String(preset.jpegQuality),
    "-threads", String(ENCODER_THREADS), "-r", String(VIDEO_FPS),
    "-fps_mode", "cfr", "-flush_packets", "1", "-f", "image2pipe", "pipe:1",
    "-map", "0:a:0?", "-vn",
    "-af", `aresample=${AUDIO_SAMPLE_RATE}:async=75:min_hard_comp=0.200:first_pts=0`,
    "-ac", String(AUDIO_CHANNELS), "-ar", String(AUDIO_SAMPLE_RATE),
    "-c:a", "pcm_s16le", "-flush_packets", "1", "-f", "s16le", "pipe:3"
  ];

  const child = spawn("ffmpeg", args, { stdio: ["ignore", "pipe", "pipe", "pipe"] });
  ffmpeg = child;
  child.stdout.on("data", chunk => {
    if (!firstVideoByteAt && chunk?.length) {
      firstVideoByteAt = Date.now();
      console.log("[START] First video byte:", firstVideoByteAt - ffmpegStartTime, "ms");
    }
    processVideoData(chunk, currentGeneration);
  });
  if (child.stdio[3]) {
    child.stdio[3].on("data", chunk => {
      if (!firstAudioByteAt && chunk?.length) {
        firstAudioByteAt = Date.now();
        console.log("[START] First audio byte:", firstAudioByteAt - ffmpegStartTime, "ms");
      }
      if (currentGeneration === generation) pushAudioBuffer(chunk);
    });
    child.stdio[3].on("error", e => { if (currentGeneration === generation) console.error("[AUDIO PIPE]", e.message); });
  }
  child.stderr.on("data", data => {
    if (currentGeneration !== generation) return;
    const message = data.toString().trim();
    if (!message) return;
    if (message.includes("Audio:") || message.includes("Stream #0:1")) audioDetected = true;
    if (message.includes("Stream map '0:a:0'") || message.includes("matches no streams")) console.log("[FFMPEG] WARNING: source may not have audio");
    console.log("[FFmpeg]", message);
  });
  child.on("error", e => { if (currentGeneration === generation) console.error("[FFMPEG ERROR]", e.message); });
  child.on("close", (code, signal) => {
    console.log("[FFmpeg] Exited:", code, signal);
    if (currentGeneration !== generation) return;
    if (ffmpeg === child) ffmpeg = null;
    resetAudioBuffer(); clearVideoBuffer(); videoEpoch = 0; audioEpoch = 0;
    resetReady("ffmpeg exit");
    if (!manuallyStopped) scheduleRestart();
  });
  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation || !ffmpeg || restarting) return;
    const elapsed = Date.now() - lastVideoFrameReceived;
    if (elapsed > VIDEO_TIMEOUT) { console.log("[WATCHDOG] No video frame for", elapsed, "ms"); scheduleRestart(); }
  }, WATCHDOG_INTERVAL);
}
function scheduleRestart() {
  if (restarting || manuallyStopped) return;
  restarting = true;
  console.log("[RESTART] Waiting:", RESTART_DELAY);
  clearWatchdog();
  generation++;
  const old = ffmpeg; ffmpeg = null;
  resetAudioBuffer(); clearVideoBuffer(); videoEpoch = 0; audioEpoch = 0;
  resetReady("scheduleRestart");
  audioBlocked = false; audioBlockedSince = 0;
  if (old) { try { old.kill("SIGKILL"); } catch (_) {} }
  if (restartTimer) clearTimeout(restartTimer);
  restartTimer = setTimeout(() => {
    restartTimer = null; restarting = false;
    if (currentChannel && !manuallyStopped) startFFmpeg(currentChannel);
  }, RESTART_DELAY);
}

// =====================================================
// ROUTES: VIDEO / AUDIO
// =====================================================
app.get("/stream", async (req, res) => {
  const requestedFps = Number(req.query.fps);
  let clientFps = DEFAULT_CLIENT_FPS;
  if (Number.isFinite(requestedFps) && requestedFps > 0) clientFps = Math.max(MIN_CLIENT_FPS, Math.min(MAX_CLIENT_FPS, Math.floor(requestedFps)));
  const clientInterval = clientFps >= VIDEO_FPS ? 0 : 1000 / clientFps;
  console.log("[VIDEO] Client request — waiting for videoReady...");
  if (!await waitForReady("video", STREAM_READY_TIMEOUT_MS)) return res.status(503).json({ success: false, error: "Video not ready — try again" });
  res.writeHead(200, {
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate", "Pragma": "no-cache", "Expires": "0",
    "Connection": "keep-alive", "X-Accel-Buffering": "no", "X-Client-FPS": String(clientFps)
  });
  videoClients++;
  const state = { blocked: false, blockedSince: 0, lastSentSequence: -1, clientFps, clientInterval, lastSentTime: 0, skippedFrames: 0, blockCount: 0 };
  videoClientsMap.set(res, state);
  if (latestFrame && Date.now() - lastVideoFrameTime <= 1500 && frameSequence > 0) {
    const header = Buffer.from(`--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${latestFrame.length}\r\n\r\n`);
    res.write(header); res.write(latestFrame); res.write("\r\n");
    state.lastSentSequence = frameSequence; state.lastSentTime = Date.now(); videoSentFrames++;
  }
  res.on("close", () => cleanupVideoClient(res));
  res.on("error", () => cleanupVideoClient(res));
});

app.get("/audio", async (req, res) => {
  console.log("[AUDIO] Client request — waiting for audioReady...");
  if (!await waitForReady("audio", STREAM_READY_TIMEOUT_MS)) return res.status(503).json({ success: false, error: "Audio not ready or source has no audio" });
  disconnectAudioClient(false);
  audioClient = res;
  res.statusCode = 200;
  res.setHeader("Content-Type", "application/octet-stream");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");
  res.on("close", () => { if (audioClient === res) { console.log("[AUDIO] Client disconnected"); disconnectAudioClient(false); } });
  res.on("error", () => { if (audioClient === res) disconnectAudioClient(false); });
});

// =====================================================
// API CONFIG QUALITY
// =====================================================
function qualityConfigHandler(req, res) {
  const requested = req.params.quality || req.body?.quality || req.query.quality;
  const preset = requested === undefined ? getCurrentQualityPreset() : setQuality(requested);
  if (!preset) return res.status(400).json({ success: false, error: "Unsupported quality", ...qualityResponse() });
  res.json({ success: true, ...qualityResponse() });
}
app.get("/api/config", qualityConfigHandler);
app.get("/api/config/quality", qualityConfigHandler);
app.get("/api/config/quality/:quality", qualityConfigHandler);
app.post("/api/config/quality", qualityConfigHandler);
app.post("/api/config/quality/:quality", qualityConfigHandler);

// =====================================================
// API CHANNELS / SELECT / STOP / RELOAD
// =====================================================
app.get("/api/channels", (req, res) => {
  const requested = req.query.quality || req.query.q || req.query.max || "720";
  const raw = String(requested).trim().toLowerCase();
  let max = 720;
  if (raw === "all" || raw === "full") max = Number.MAX_SAFE_INTEGER;
  else { const n = Number.parseInt(raw, 10); if (Number.isFinite(n) && n > 0) max = n; }
  const resetSeconds = Math.max(3, Math.ceil(RESTART_DELAY / 1000));
  res.json({ success: true, streamQuality: getCurrentQualityPreset().id, jpegQuality: getCurrentQualityPreset().jpegQuality,
    quality: max === Number.MAX_SAFE_INTEGER ? "all" : String(max),
    channels: filterChannelsByResolution(channels, max).map(c => ({ ...c, resetSeconds, resetAtMs: Date.now() + resetSeconds * 1000 })) });
});
function selectChannelHandler(req, res) {
  let id;
  try { id = decodeURIComponent(req.params.id); } catch (_) { return res.status(400).json({ success: false, error: "Invalid channel ID" }); }
  const channel = channels.find(c => c.id === id || c.name.toLowerCase() === id.toLowerCase());
  if (!channel) return res.status(404).json({ success: false, error: "Channel not found" });
  try { startFFmpeg(channel); res.json({ success: true, channel: channel.name }); }
  catch (e) { res.status(500).json({ success: false, error: e.message }); }
}
app.get("/api/select/:id", selectChannelHandler);
app.post("/api/select/:id", selectChannelHandler);
function stopHandler(req, res) { stopFFmpeg({ manual: true, disconnectClients: true }); currentChannel = null; res.json({ success: true, message: "Stopped" }); }
app.get("/api/stop", stopHandler);
app.post("/api/stop", stopHandler);
app.get("/api/reload", async (req, res) => {
  try { await loadChannels(); res.json({ success: true, count: channels.length }); }
  catch (e) { res.status(500).json({ success: false, error: e.message }); }
});

// =====================================================
// RENDER BANDWIDTH API
// =====================================================
app.get("/api/bandwidth", async (req, res) => {
  try {
    if (!RENDER_API_KEY) return res.status(500).json({ success: false, error: "Set RENDER_API_KEY environment variable" });
    if (!RENDER_SERVICE_IDS.length) return res.status(500).json({ success: false, error: "Missing RENDER_SERVICE_IDS" });
    if (!Number.isFinite(BANDWIDTH_LIMIT_GB) || BANDWIDTH_LIMIT_GB <= 0) return res.status(500).json({ success: false, error: "Invalid BANDWIDTH_LIMIT_GB" });
    const now = new Date();
    const start = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), 1));
    const url = new URL("https://api.render.com/v1/metrics/bandwidth");
    url.searchParams.set("startTime", start.toISOString()); url.searchParams.set("endTime", now.toISOString());
    for (const id of RENDER_SERVICE_IDS) url.searchParams.append("resource", id);
    const response = await fetch(url, { headers: { Authorization: `Bearer ${RENDER_API_KEY}`, Accept: "application/json" }, signal: AbortSignal.timeout(20000) });
    if (!response.ok) return res.status(response.status).json({ success: false, error: "Render API error", httpStatus: response.status, details: await response.text() });
    const data = await response.json();
    if (!Array.isArray(data)) throw new Error("Invalid Render bandwidth response");
    let usedGB = 0, totalPoints = 0;
    const services = [];
    for (const series of data) {
      const labels = Array.isArray(series.labels) ? series.labels : [];
      const serviceLabel = labels.find(x => x.field === "service");
      const serviceId = serviceLabel ? serviceLabel.value : "unknown";
      const unit = String(series.unit || "GB").toUpperCase();
      let serviceGB = 0;
      for (const point of (series.values || [])) {
        const value = Number(point.value); if (!Number.isFinite(value)) continue;
        if (unit === "GB") serviceGB += value;
        else if (unit === "MB") serviceGB += value / 1024;
        else if (["BYTE", "BYTES", "B"].includes(unit)) serviceGB += value / (1024 ** 3);
        else throw new Error("Unsupported bandwidth unit: " + unit);
        totalPoints++;
      }
      usedGB += serviceGB;
      services.push({ serviceId, usedGB: Number(serviceGB.toFixed(4)), unit, dataPoints: (series.values || []).length });
    }
    usedGB = Number(usedGB.toFixed(4));
    const remainingGB = Math.max(0, BANDWIDTH_LIMIT_GB - usedGB);
    const resetAt = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, 1));
    const resetInSeconds = Math.max(0, Math.ceil((resetAt.getTime() - Date.now()) / 1000));
    const usedPercent = Math.min(100, Number((usedGB / BANDWIDTH_LIMIT_GB * 100).toFixed(2)));
    const remainingPercent = Number((100 - usedPercent).toFixed(2));
    let status = "NORMAL"; if (remainingGB <= 0) status = "LIMIT_REACHED"; else if (remainingGB <= BANDWIDTH_LIMIT_GB * 0.1) status = "WARNING";
    res.json({ success: true, provider: "Render Official API", period: { start: start.toISOString(), end: now.toISOString(), timezone: "UTC" },
      bandwidth: { limitGB: BANDWIDTH_LIMIT_GB, usedGB, remainingGB, usedPercent, remainingPercent }, resetInSeconds, resetAt: resetAt.toISOString(), status,
      services, serviceCount: RENDER_SERVICE_IDS.length, returnedSeries: data.length, totalDataPoints: totalPoints, updatedAt: new Date().toISOString(),
      note: "Metrics are delayed and may not equal exact real-time billing balance." });
  } catch (e) { console.error("[BANDWIDTH ERROR]", e.message); res.status(500).json({ success: false, error: e.message }); }
});

// =====================================================
// HEALTH
// =====================================================
app.get("/health", (req, res) => {
  const memory = process.memoryUsage();
  const now = Date.now();
  const clientDetails = [];
  for (const [, s] of videoClientsMap) clientDetails.push({ fps: s.clientFps, interval: s.clientInterval, skipped: s.skippedFrames, blockCount: s.blockCount, blocked: s.blocked, blockDurationMs: s.blocked ? now - s.blockedSince : 0, lastSentAgoMs: s.lastSentTime ? now - s.lastSentTime : null });
  const elapsedSec = ffmpegStartTime ? (now - ffmpegStartTime) / 1000 : 0;
  const audioInKbPerSec = elapsedSec > 0 ? audioBytesIn / 1024 / elapsedSec : 0;
  const expectedAudioKbPerSec = AUDIO_BYTES_PER_MS * 1000 / 1024;
  const audioProductionRate = expectedAudioKbPerSec > 0 ? Math.round(audioInKbPerSec / expectedAudioKbPerSec * 100) : 0;
  const videoInFps = elapsedSec > 0 ? videoFramesIn / elapsedSec : 0;
  const videoProductionRate = VIDEO_FPS > 0 ? Math.round(videoInFps / VIDEO_FPS * 100) : 0;
  const audioBufMs = audioBuffer.length / AUDIO_BYTES_PER_MS;
  const videoBufMs = videoQueue.length * VIDEO_INTERVAL;
  res.json({
    status: "running", channelCount: channels.length, currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg, restarting, manuallyStopped, pipeline: "INDEPENDENT_VIDEO_AUDIO_READY",
    videoWidth: VIDEO_WIDTH, videoHeight: VIDEO_HEIGHT, videoFPS: VIDEO_FPS,
    streamReady, streamReadyAt, streamReadyAgeMs: streamReadyAt ? now - streamReadyAt : null,
    audioReady, audioReadyAt, audioReadyAgeMs: audioReadyAt ? now - audioReadyAt : null,
    streamReadyGraceMs: STREAM_READY_GRACE_MS, streamReadyWaiters: videoReadyWaiters.length, audioReadyWaiters: audioReadyWaiters.length,
    startupTiming: { ffmpegStartTime, firstVideoByteAt, firstAudioByteAt, audioDetected,
      firstVideoByteLatencyMs: firstVideoByteAt ? firstVideoByteAt - ffmpegStartTime : null,
      firstAudioByteLatencyMs: firstAudioByteAt ? firstAudioByteAt - ffmpegStartTime : null,
      streamReadyLatencyMs: streamReadyAt && ffmpegStartTime ? streamReadyAt - ffmpegStartTime : null,
      audioReadyLatencyMs: audioReadyAt && ffmpegStartTime ? audioReadyAt - ffmpegStartTime : null },
    productionRate: { audioBytesIn, videoFramesIn, audioKbPerSec: Number(audioInKbPerSec.toFixed(2)), expectedAudioKbPerSec: Number(expectedAudioKbPerSec.toFixed(2)), audioProductionRate,
      videoInFps: Number(videoInFps.toFixed(2)), videoProductionRate, note: "Tỷ lệ thấp có thể do nguồn IPTV hoặc mạng không cấp dữ liệu đủ nhanh." },
    videoPrimed, videoQueueLength: videoQueue.length, videoQueueTarget: VIDEO_QUEUE_TARGET, videoQueueMax: VIDEO_QUEUE_MAX,
    videoDroppedFrames, videoInvalidFrames, videoSentFrames, videoClients, videoPendingBytes: jpegPending.length,
    videoLatestFrameBytes: latestFrame ? latestFrame.length : 0, videoFrameSequence: frameSequence,
    videoFrameAge: lastVideoFrameReceived ? now - lastVideoFrameReceived : null,
    videoLastBroadcastAge: lastVideoFrameTime ? now - lastVideoFrameTime : null, clientDetails,
    clocks: { videoEpoch, audioEpoch, videoFramesSinceSync, audioFramesSinceSync,
      videoElapsedMs: videoEpoch ? now - videoEpoch : 0, audioElapsedMs: audioEpoch ? now - audioEpoch : 0 },
    contentOffsetMs: Math.round(videoBufMs - audioBufMs),
    audioSampleRate: AUDIO_SAMPLE_RATE, audioChannels: AUDIO_CHANNELS, audioFrameBytes: AUDIO_FRAME_BYTES, audioInterval: AUDIO_INTERVAL,
    audioBufferBytes: audioBuffer.length, audioBufferMax: AUDIO_BUFFER_MAX, audioBufferMs: Math.round(audioBufMs),
    audioStartBufferMs: AUDIO_START_BUFFER_MS, audioTargetBufferMs, audioPrimed, audioMaxObservedBytes,
    audioClientConnected: !!audioClient && !audioClient.destroyed, audioBlocked, audioUnderflows, audioOverflowBytes,
    audioSilenceBytes, audioFramesSent, audioSilenceSent, masterTickMs: MASTER_TICK_MS,
    memory: { rssMB: Number((memory.rss / 1048576).toFixed(2)), heapUsedMB: Number((memory.heapUsed / 1048576).toFixed(2)), externalMB: Number((memory.external / 1048576).toFixed(2)), arrayBuffersMB: Number((memory.arrayBuffers / 1048576).toFixed(2)) },
    lastVideoFrameReceived, lastVideoFrameTime, generation
  });
});

app.get("/", (req, res) => res.send(
  "IPTV SERVER RUNNING - INDEPENDENT VIDEO/AUDIO READY\n" +
  "  /stream              -> MJPEG video\n" +
  "  /audio               -> PCM audio (if source has audio)\n" +
  "  /api/channels        -> channel list\n" +
  "  /health              -> diagnostics\n" +
  "Video can start even when the selected IPTV source has no audio."
));

// =====================================================
// START
// =====================================================
async function main() {
  try { await loadChannels(); } catch (e) { console.log("[STARTUP] Playlist failed:", e.message); }
  startMasterTimer();
  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT, "CHANNELS:", channels.length);
    console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
    console.log("AUDIO START BUFFER:", AUDIO_START_BUFFER_MS, "ms");
    console.log("VIDEO QUEUE TARGET:", VIDEO_QUEUE_TARGET, "frames");
    console.log("MODE: INDEPENDENT VIDEO/AUDIO READY; -re DISABLED");
    console.log("--------------------------------");
  });
  if (!channels.length) {
    const retry = async () => {
      try { await loadChannels(); console.log("[M3U] Playlist recovered:", channels.length); }
      catch (e) { console.log("[M3U] Retry failed:", e.message); setTimeout(retry, 15000); }
    };
    setTimeout(retry, 15000);
  }
}
main().catch(e => { console.error("[SERVER ERROR]", e); process.exit(1); });
