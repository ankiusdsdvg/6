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

const JPEG_QUALITY = 10;
const JPEG_QUALITY_720P = 15;
const JPEG_QUALITY_540P = 20;
const JPEG_QUALITY_340P = 25;

const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

const QUALITY_PRESETS = Object.freeze([
  Object.freeze({ id: "1080p", label: "1080p", jpegQuality: JPEG_QUALITY }),
  Object.freeze({ id: "720p", label: "720p", jpegQuality: JPEG_QUALITY_720P }),
  Object.freeze({ id: "540p", label: "540p", jpegQuality: JPEG_QUALITY_540P }),
  Object.freeze({ id: "340p", label: "340p", jpegQuality: JPEG_QUALITY_340P })
]);

let currentQualityId = "1080p";

// =====================================================
// AUDIO CONFIG
// =====================================================

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;

const AUDIO_FRAME_MS = 200;
const AUDIO_INTERVAL = AUDIO_FRAME_MS;

// Audio tick RIÊNG (không dùng masterTick video) — chạy mỗi 50ms
const AUDIO_TICK_MS = 50;

const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_FRAME_MS / 1000;

const AUDIO_BYTES_PER_MS =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE / 1000;

// Prime 4s audio — trade-off: client chờ thêm ~2.5s so với bản gốc,
// nhưng audio mượt từ frame đầu thay vì 15-20s sau
const AUDIO_START_BUFFER_MS = 4000;

// Buffer max 12s — đủ chứa burst từ -readrate 1.4 khi vượt TCP slow-start
const AUDIO_BUFFER_MS = 12000;

const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_BUFFER_MS / 1000;

// Prebuffer tối thiểu trước khi bắt đầu gửi cho client trong /audio
const AUDIO_PREBUFFER_MS = 1500;

let audioTargetBufferMs = AUDIO_START_BUFFER_MS;
let audioStableFrames = 0;

const AUDIO_TARGET_MIN_MS = 800;
const AUDIO_TARGET_MAX_MS = 8000;
const AUDIO_STABLE_FRAMES_TO_REDUCE = 50;

const DECODER_THREADS = 1;
const ENCODER_THREADS = 1;

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

const MAX_VIDEO_BUFFER = 512 * 1024;
const MAX_JPEG_FRAME_BYTES = 256 * 1024;

const CLIENT_SKIP_THRESHOLD_MS = 300;
const MAX_CLIENT_BLOCK_MS = 3000;
const MAX_AUDIO_BLOCK_MS = 1500;

// FFmpeg readrate: 1.4 = đọc nhanh hơn realtime 40% để vượt TCP slow-start.
// Có thể override qua env: FFMPEG_READRATE=2.0
const FFMPEG_READRATE = String(process.env.FFMPEG_READRATE || "1.4");

// =====================================================
// MASTER TIMER / VIDEO QUEUE / SYNC / STREAM READY
// =====================================================

const MASTER_TICK_MS = 10;

const VIDEO_QUEUE_TARGET = 18;
const VIDEO_QUEUE_MAX = 60;   // 5s max (trước 42) — đủ cho readrate 1.4

const SYNC_TRIM_MS = 300;
const MAX_SYNC_DRIFT_MS = 800;

const STREAM_READY_GRACE_MS = 500;
const STREAM_READY_TIMEOUT_MS = 25000;

const JPEG_SOI = Buffer.from([0xff, 0xd8]);
const JPEG_EOI = Buffer.from([0xff, 0xd9]);
const RENDER_API_KEY = process.env.RENDER_API_KEY || "rnd_JolAxI55rXAodSTE5PaNlpGAq5A0";

const RENDER_SERVICE_IDS = (
  process.env.RENDER_SERVICE_IDS || "srv-dbs5vb8n74is738ut5e0"
).split(",").map(x => x.trim()).filter(Boolean);

const BANDWIDTH_LIMIT_GB = Number(
  process.env.BANDWIDTH_LIMIT_GB || 5
);

// =====================================================
// GLOBAL STATE
// =====================================================

let channels = [];
let currentChannel = null;
let ffmpeg = null;
let generation = 0;

let latestFrame = null;
let frameSequence = 0;
let jpegPending = Buffer.alloc(0);

let videoQueue = [];
let videoPrimed = false;

let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let videoSentFrames = 0;
let videoClients = 0;

const videoClientsMap = new Map();

let audioBuffer = Buffer.alloc(0);
let audioClient = null;

let audioBlocked = false;
let audioBlockedSince = 0;

let audioUnderflows = 0;
let audioOverflowBytes = 0;
let audioFramesSent = 0;
let audioSilenceSent = 0;
let audioPrimed = false;
let audioSilenceBytes = 0;
let audioMaxObservedBytes = 0;

let masterTimer = null;
let audioTickTimer = null;

let syncEpoch = 0;
let audioFramesSinceSync = 0;
let videoFramesSinceSync = 0;
let lastDriftCheck = 0;

let streamReady = false;
let streamReadyAt = 0;
const streamReadyWaiters = [];

let watchdogTimer = null;
let restartTimer = null;

let lastVideoFrameReceived = 0;
let lastVideoFrameTime = 0;

let restarting = false;
let manuallyStopped = true;

let ffmpegStartTime = 0;
let firstVideoByteAt = 0;
let firstAudioByteAt = 0;
let audioDetected = false;
let audioDetectWarned = false;

let audioBytesIn = 0;
let videoFramesIn = 0;

// =====================================================
// STREAM READY — GATE
// =====================================================

function setStreamReady() {
  if (streamReady) return;

  streamReady = true;
  streamReadyAt = Date.now();

  const totalWait = ffmpegStartTime ? streamReadyAt - ffmpegStartTime : 0;
  console.log("[STREAM] READY — streaming enabled (total wait:", totalWait, "ms)");

  const waiters = streamReadyWaiters.splice(0);

  for (const fn of waiters) {
    try { fn(); } catch (_) {}
  }
}

function resetStreamReady(reason = "") {
  if (!streamReady) return;

  streamReady = false;
  streamReadyAt = 0;

  if (reason) {
    console.log("[STREAM] Reset:", reason);
  }
}

function waitForStreamReady(timeoutMs) {
  return new Promise(resolve => {
    if (streamReady) return resolve(true);

    let done = false;

    const timer = setTimeout(() => {
      if (done) return;
      done = true;

      const idx = streamReadyWaiters.indexOf(wrap);
      if (idx >= 0) streamReadyWaiters.splice(idx, 1);

      resolve(false);
    }, timeoutMs);

    const wrap = () => {
      if (done) return;
      done = true;
      clearTimeout(timer);
      resolve(true);
    };

    streamReadyWaiters.push(wrap);
  });
}

// =====================================================
// PLAYLIST
// =====================================================

function parseResolutionFromName(name) {
  const match = name.match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);
  return match ? Number(match[1] || match[2]) || 0 : 0;
}

function parseM3U(content) {
  const lines = content.split(/\r?\n/);
  const result = [];
  let currentInfo = null;

  for (const rawLine of lines) {
    const line = rawLine.trim();
    if (!line) continue;

    if (line.startsWith("#EXTINF:")) {
      currentInfo = line;
      continue;
    }

    if (line.startsWith("#") || !currentInfo) continue;

    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(line)) {
      currentInfo = null;
      continue;
    }

    const name = currentInfo.split(",").pop().trim() || "Unknown channel";
    const groupMatch = currentInfo.match(/group-title="([^"]*)"/i);
    const logoMatch = currentInfo.match(/tvg-logo="([^"]*)"/i);
    const idMatch = currentInfo.match(/tvg-id="([^"]*)"/i);

    result.push({
      id: String(result.length),
      name,
      group: groupMatch ? groupMatch[1] : "",
      logo: logoMatch ? logoMatch[1] : "",
      tvgId: idMatch ? idMatch[1] : "",
      resolution: parseResolutionFromName(name),
      url: line
    });

    currentInfo = null;
  }

  return result;
}

function filterChannelsByResolution(list, maxResolution = 720) {
  if (!Array.isArray(list)) return [];
  if (maxResolution === Number.MAX_SAFE_INTEGER) return list;
  return list.filter(c => !c.resolution || c.resolution <= maxResolution);
}

function normalizeQualityId(value) {
  const raw = String(value || "").trim().toLowerCase().replace(/\s+/g, "");
  if (!raw) return null;
  const normalized = raw.endsWith("p") ? raw : `${raw}p`;
  return QUALITY_PRESETS.some(preset => preset.id === normalized)
    ? normalized : null;
}

function getCurrentQualityPreset() {
  return QUALITY_PRESETS.find(p => p.id === currentQualityId) || QUALITY_PRESETS[0];
}

function qualityResponse() {
  const preset = getCurrentQualityPreset();
  return {
    quality: preset.id,
    jpegQuality: preset.jpegQuality,
    presets: QUALITY_PRESETS.map(item => ({
      id: item.id,
      label: item.label,
      jpegQuality: item.jpegQuality
    }))
  };
}

function setQuality(value) {
  const qualityId = normalizeQualityId(value);
  if (!qualityId) return null;

  const changed = qualityId !== currentQualityId;
  currentQualityId = qualityId;

  if (changed && currentChannel && !manuallyStopped) {
    startFFmpeg(currentChannel);
  }

  return getCurrentQualityPreset();
}

async function loadChannels() {
  console.log("[M3U] Loading playlist...");
  let lastError = null;

  for (const url of M3U_URLS) {
    try {
      const response = await fetch(url, {
        headers: { "User-Agent": "Mozilla/5.0" },
        signal: AbortSignal.timeout(20000)
      });

      if (!response.ok) throw new Error("HTTP " + response.status);

      const loaded = parseM3U(await response.text());
      if (!loaded.length) throw new Error("Playlist contains no channels");

      channels = loaded;
      console.log("[M3U] Loaded:", channels.length, "from", url);
      return channels;
    } catch (error) {
      lastError = error;
      console.warn("[M3U] Failed:", error.message);
    }
  }

  throw lastError || new Error("No playlist available");
}

// =====================================================
// SYNC
// =====================================================

function resetSync() {
  syncEpoch = 0;
  audioFramesSinceSync = 0;
  videoFramesSinceSync = 0;
  lastDriftCheck = 0;
}

function rePrimeAll(reason) {
  console.log("[SYNC] Re-priming:", reason);
  clearAudioBuffer();
  videoQueue = [];
  audioPrimed = false;
  videoPrimed = false;
  resetSync();
  resetStreamReady("re-prime");
}

function checkDrift() {
  if (!audioPrimed || !videoPrimed || syncEpoch === 0) return;

  const now = Date.now();
  if (now - lastDriftCheck < 3000) return;
  lastDriftCheck = now;

  const audioMs = audioFramesSinceSync * AUDIO_FRAME_MS;
  const videoMs = videoFramesSinceSync * VIDEO_INTERVAL;
  const drift = audioMs - videoMs;

  if (Math.abs(drift) > MAX_SYNC_DRIFT_MS) {
    rePrimeAll(`drift ${Math.round(drift)}ms`);
  }
}

// =====================================================
// AUDIO BUFFER
// =====================================================

function resetAudioState(resetStats = false) {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioStableFrames = 0;
  audioTargetBufferMs = AUDIO_START_BUFFER_MS;
  audioMaxObservedBytes = 0;

  if (resetStats) {
    audioUnderflows = 0;
    audioOverflowBytes = 0;
    audioFramesSent = 0;
    audioSilenceSent = 0;
    audioSilenceBytes = 0;
    audioBytesIn = 0;
    videoFramesIn = 0;
  }
}

function clearAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioStableFrames = 0;
}

function disconnectAudioClient(clearBuffer = true) {
  const old = audioClient;

  audioClient = null;
  audioBlocked = false;
  audioBlockedSince = 0;

  if (clearBuffer) {
    clearAudioBuffer();
  }

  if (old && !old.destroyed) {
    try { old.destroy(); } catch (_) {}
  }
}

function pushAudioBuffer(chunk) {
  if (!chunk?.length) return;

  audioBytesIn += chunk.length;

  if (chunk.length & 1) {
    chunk = chunk.subarray(0, chunk.length - 1);
  }

  if (!chunk.length) return;

  const total = audioBuffer.length + chunk.length;

  if (total > AUDIO_BUFFER_MAX) {
    const excess = total - AUDIO_BUFFER_MAX;
    const drop = excess + (excess & 1);

    audioOverflowBytes += drop;

    if (drop >= audioBuffer.length) {
      const fromChunk = Math.min(chunk.length, AUDIO_BUFFER_MAX);
      audioBuffer = Buffer.from(chunk.subarray(chunk.length - fromChunk));
    } else {
      const keepOld = audioBuffer.subarray(drop);
      audioBuffer = Buffer.concat([keepOld, chunk]);
    }
  } else {
    audioBuffer = audioBuffer.length
      ? Buffer.concat([audioBuffer, chunk], total)
      : Buffer.from(chunk);
  }

  if (audioBuffer.length > AUDIO_BUFFER_MAX) {
    audioBuffer = Buffer.from(audioBuffer.subarray(-AUDIO_BUFFER_MAX));
  }

  if (audioBuffer.length & 1) {
    audioBuffer = Buffer.from(audioBuffer.subarray(1));
  }

  if (audioBuffer.length > audioMaxObservedBytes) {
    audioMaxObservedBytes = audioBuffer.length;
  }
}

function takeAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES, 0);

  const count = Math.min(audioBuffer.length, AUDIO_FRAME_BYTES) & ~1;

  if (count > 0) {
    audioBuffer.copy(frame, 0, 0, count);
    audioBuffer = audioBuffer.subarray(count);
  }

  if (count < AUDIO_FRAME_BYTES) {
    audioUnderflows++;
    audioSilenceBytes += AUDIO_FRAME_BYTES - count;
    audioStableFrames = 0;
    audioTargetBufferMs = Math.min(
      AUDIO_TARGET_MAX_MS,
      audioTargetBufferMs + 100
    );
  } else {
    audioStableFrames++;

    if (audioStableFrames >= AUDIO_STABLE_FRAMES_TO_REDUCE) {
      audioTargetBufferMs = Math.max(
        AUDIO_TARGET_MIN_MS,
        audioTargetBufferMs - 50
      );
      audioStableFrames = 0;
    }
  }

  return frame;
}

function writeAudioFrame(frame, isSilence = false) {
  if (!audioClient || audioClient.destroyed || audioClient.writableEnded) {
    return false;
  }

  // Force reset nếu blocked quá 1500ms — tránh câm kéo dài
  if (audioBlocked && Date.now() - audioBlockedSince > MAX_AUDIO_BLOCK_MS) {
    console.log("[AUDIO] Force reset blocked client after",
      Date.now() - audioBlockedSince, "ms");
    disconnectAudioClient(false);
    return false;
  }

  try {
    const ok = audioClient.write(frame);

    if (isSilence) {
      audioSilenceSent++;
    } else {
      audioFramesSent++;
    }

    if (!ok && !audioBlocked) {
      audioBlocked = true;
      audioBlockedSince = Date.now();
      audioClient.once("drain", () => {
        audioBlocked = false;
        audioBlockedSince = 0;
      });
    }

    return ok;
  } catch (error) {
    console.error("[AUDIO WRITE]", error.message);
    disconnectAudioClient(false);
    return false;
  }
}

// =====================================================
// AUDIO TICK — RIÊNG, KHÔNG PHỤ THUỘC MASTER TICK VIDEO
// =====================================================

function audioTick() {
  if (!audioPrimed || syncEpoch === 0) return;

  const now = Date.now();
  const expected = Math.floor((now - syncEpoch) / AUDIO_INTERVAL);
  let gap = expected - audioFramesSinceSync;

  if (gap <= 0) return;

  // Nếu gap quá lớn (event loop bị block) → skip để tránh burst quá lớn
  if (gap > 20) {
    const skip = gap - 20;
    const skipBytes = Math.min(skip * AUDIO_FRAME_BYTES, audioBuffer.length) & ~1;
    audioBuffer = audioBuffer.subarray(skipBytes);
    audioFramesSinceSync += skip;
    console.log("[AUDIO] Skip ahead", skip, "frames");
    gap = 20;
  }

  for (let i = 0; i < gap; i++) {
    const frame = takeAudioFrame();
    audioFramesSinceSync++;

    if (
      streamReady &&
      audioClient &&
      !audioClient.destroyed &&
      !audioClient.writableEnded
    ) {
      // Luôn ghi kể cả khi blocked — để TCP tự buffer, tránh câm kéo dài.
      // Chỉ reset client nếu block > 1500ms (đã handle trong writeAudioFrame).
      writeAudioFrame(frame, false);
    }
  }
}

function startAudioTimer() {
  if (audioTickTimer) clearInterval(audioTickTimer);
  audioTickTimer = setInterval(audioTick, AUDIO_TICK_MS);
}

// =====================================================
// VIDEO QUEUE
// =====================================================

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
  videoQueue = [];
  videoPrimed = false;
}

function broadcastFrame(frame) {
  if (!frame || !videoClientsMap.size) return;

  const now = Date.now();

  const header = Buffer.from(
    `--frame\r\n` +
    `Content-Type: image/jpeg\r\n` +
    `Content-Length: ${frame.length}\r\n` +
    `\r\n`
  );

  const trailer = Buffer.from("\r\n");

  for (const [res, state] of videoClientsMap) {
    if (res.destroyed || res.writableEnded) {
      cleanupVideoClient(res);
      continue;
    }

    if (state.blocked) {
      const blockDuration = now - state.blockedSince;

      if (blockDuration > MAX_CLIENT_BLOCK_MS) {
        console.log(
          "[VIDEO] Slow client disconnected after",
          blockDuration, "ms block (skipped:", state.skippedFrames, ")"
        );
        cleanupVideoClient(res);
        try { res.destroy(); } catch (_) {}
        continue;
      }

      if (blockDuration > CLIENT_SKIP_THRESHOLD_MS) {
        state.skippedFrames++;
        continue;
      }
    }

    if (state.lastSentSequence === frameSequence) continue;

    if (state.clientInterval > 0) {
      const timeSinceLastSend = now - state.lastSentTime;
      if (timeSinceLastSend < state.clientInterval * 0.9) {
        state.skippedFrames++;
        continue;
      }
    }

    try {
      let ok = res.write(header);
      if (!res.write(frame)) ok = false;
      if (!res.write(trailer)) ok = false;

      state.lastSentSequence = frameSequence;
      state.lastSentTime = now;
      videoSentFrames++;

      if (!ok) {
        if (!state.blocked) {
          state.blocked = true;
          state.blockedSince = Date.now();
          state.blockCount++;
        }
        res.once("drain", () => {
          state.blocked = false;
          state.blockedSince = 0;
        });
      }
    } catch (error) {
      console.error("[VIDEO WRITE]", error.message);
      cleanupVideoClient(res);
      try { res.destroy(); } catch (_) {}
    }
  }
}

function cleanupVideoClient(res) {
  if (!videoClientsMap.has(res)) return;
  videoClientsMap.delete(res);
  videoClients = Math.max(0, videoClients - 1);
}

function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation || !chunk?.length) return;

  if (chunk.length > MAX_VIDEO_BUFFER) {
    chunk = chunk.subarray(chunk.length - MAX_VIDEO_BUFFER);
    videoInvalidFrames++;
  }

  if (jpegPending.length + chunk.length > MAX_VIDEO_BUFFER) {
    const combined = Buffer.concat([jpegPending, chunk]);
    const lastStart = combined.lastIndexOf(JPEG_SOI);
    jpegPending = lastStart >= 0
      ? Buffer.from(combined.subarray(lastStart))
      : Buffer.alloc(0);
    videoInvalidFrames++;
  } else {
    jpegPending = jpegPending.length
      ? Buffer.concat([jpegPending, chunk])
      : Buffer.from(chunk);
  }

  while (jpegPending.length) {
    const start = jpegPending.indexOf(JPEG_SOI);

    if (start < 0) {
      jpegPending = jpegPending[jpegPending.length - 1] === 0xff
        ? Buffer.from([0xff]) : Buffer.alloc(0);
      return;
    }

    if (start > 0) jpegPending = jpegPending.subarray(start);

    const end = jpegPending.indexOf(JPEG_EOI, 2);

    if (end < 0) {
      if (jpegPending.length > MAX_JPEG_FRAME_BYTES) {
        videoInvalidFrames++;
        const nextStart = jpegPending.indexOf(JPEG_SOI, 2);
        jpegPending = nextStart >= 0
          ? Buffer.from(jpegPending.subarray(nextStart))
          : Buffer.alloc(0);
      }
      return;
    }

    const frameLength = end + 2;

    if (frameLength > MAX_JPEG_FRAME_BYTES) {
      videoInvalidFrames++;
      jpegPending = jpegPending.subarray(frameLength);
      continue;
    }

    const frame = Buffer.from(jpegPending.subarray(0, frameLength));

    lastVideoFrameReceived = Date.now();
    videoFramesIn++;

    if (videoPrimed && audioPrimed) {
      const audioBufMs = audioBuffer.length / AUDIO_BYTES_PER_MS;
      const videoBufMs = videoQueue.length * VIDEO_INTERVAL;
      if (videoBufMs > audioBufMs + SYNC_TRIM_MS) {
        videoQueue.shift();
        videoDroppedFrames++;
      }
    }

    videoQueue.push(frame);

    if (videoQueue.length > VIDEO_QUEUE_MAX) {
      videoQueue.shift();
      videoDroppedFrames++;
    }

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// =====================================================
// MASTER TICK — CHỈ XỬ LÝ VIDEO + PRIMING + STREAM GATE
// (audio đã tách sang audioTick riêng)
// =====================================================

function masterTick() {
  const now = Date.now();

  if (!audioPrimed) {
    const targetBytes = Math.floor(
      AUDIO_BYTES_PER_MS * audioTargetBufferMs
    );
    if (audioBuffer.length >= targetBytes) {
      audioPrimed = true;
      console.log(
        "[AUDIO] Primed:", audioBuffer.length,
        "bytes / target:", audioTargetBufferMs, "ms"
      );
    }
  }

  if (!videoPrimed && videoQueue.length >= VIDEO_QUEUE_TARGET) {
    videoPrimed = true;
    console.log("[VIDEO] Primed:", videoQueue.length, "frames");
  }

  if (audioPrimed && videoPrimed && syncEpoch === 0) {
    syncEpoch = now;
    audioFramesSinceSync = 0;
    videoFramesSinceSync = 0;
    lastDriftCheck = now;
    console.log("[SYNC] Playback started at", now);
  }

  if (videoPrimed && audioPrimed && syncEpoch > 0) {
    const expected = Math.floor((now - syncEpoch) / VIDEO_INTERVAL);
    const gap = expected - videoFramesSinceSync;

    if (gap > 0 && videoQueue.length > 0) {
      const emitCount = Math.min(gap, videoQueue.length, 3);

      for (let i = 0; i < emitCount; i++) {
        const frame = videoQueue.shift();
        if (!frame) break;

        videoFramesSinceSync++;

        if (streamReady) {
          latestFrame = frame;
          frameSequence++;
          lastVideoFrameTime = Date.now();
          broadcastFrame(frame);
        }
      }
    }
  }

  if (!streamReady && audioPrimed && videoPrimed && syncEpoch > 0) {
    if (now - syncEpoch >= STREAM_READY_GRACE_MS) {
      setStreamReady();
    }
  }

  if (
    streamReady &&
    !firstAudioByteAt &&
    !audioDetectWarned &&
    ffmpegStartTime &&
    now - ffmpegStartTime > 5000
  ) {
    audioDetectWarned = true;
    console.log(
      "[AUDIO] WARNING: no audio data after",
      now - ffmpegStartTime, "ms — audio stream may be missing or probesize too small"
    );
  }

  checkDrift();
}

function startMasterTimer() {
  if (masterTimer) clearInterval(masterTimer);
  masterTimer = setInterval(masterTick, MASTER_TICK_MS);
}

// =====================================================
// FFMPEG LIFECYCLE
// =====================================================

function clearWatchdog() {
  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }
}

function stopFFmpeg({
  manual = true,
  disconnectClients = true
} = {}) {
  generation++;
  manuallyStopped = manual;
  restarting = false;

  clearWatchdog();

  if (restartTimer) {
    clearTimeout(restartTimer);
    restartTimer = null;
  }

  const old = ffmpeg;
  ffmpeg = null;

  clearAudioBuffer();
  clearVideoBuffer();
  resetSync();
  resetStreamReady("stopFFmpeg");

  audioBlocked = false;
  audioBlockedSince = 0;

  if (old) {
    try { old.kill("SIGKILL"); } catch (_) {}
  }

  if (disconnectClients) {
    disconnectAudioClient(true);

    for (const res of videoClientsMap.keys()) {
      try { res.destroy(); } catch (_) {}
    }

    videoClientsMap.clear();
    videoClients = 0;
  }
}

function startFFmpeg(channel) {
  if (!channel?.url) {
    console.log("[FFMPEG] Invalid channel");
    return;
  }

  stopFFmpeg({ manual: false, disconnectClients: false });

  manuallyStopped = false;
  currentChannel = channel;

  clearVideoBuffer();
  resetAudioState(true);
  resetSync();
  resetStreamReady("startFFmpeg");

  videoDroppedFrames = 0;
  videoInvalidFrames = 0;
  videoSentFrames = 0;

  const currentGeneration = generation;
  const qualityPreset = getCurrentQualityPreset();

  lastVideoFrameReceived = Date.now();
  lastVideoFrameTime = Date.now();

  ffmpegStartTime = Date.now();
  firstVideoByteAt = 0;
  firstAudioByteAt = 0;
  audioDetected = false;
  audioDetectWarned = false;

  console.log("\n==================================");
  console.log("CHANNEL:", channel.name);
  console.log("GENERATION:", currentGeneration);
  console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS} (max)`);
  console.log("QUALITY:", qualityPreset.label, "JPEG q:", qualityPreset.jpegQuality);
  console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM`);
  console.log("AUDIO START BUFFER:", AUDIO_START_BUFFER_MS, "ms");
  console.log("AUDIO BUFFER MAX:", AUDIO_BUFFER_MS, "ms");
  console.log("AUDIO PREBUFFER:", AUDIO_PREBUFFER_MS, "ms");
  console.log("AUDIO TICK:", AUDIO_TICK_MS, "ms");
  console.log("VIDEO QUEUE TARGET:", VIDEO_QUEUE_TARGET, "frames");
  console.log("VIDEO QUEUE MAX:", VIDEO_QUEUE_MAX, "frames");
  console.log("STREAM READY GRACE:", STREAM_READY_GRACE_MS, "ms");
  console.log("FFMPEG READRATE:", FFMPEG_READRATE);
  console.log("MODE: SPLIT AUDIO/VIDEO TICK + READRATE > 1");
  console.log("==================================");

  const videoFilter = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  // Audio filter đơn giản: async=1 = compensate ngay khi lệch > 1ms
  // (thay cho async=75:min_hard_comp=0.200 — gây chậm 15-20s khi lock)
  const audioFilter =
    `aresample=${AUDIO_SAMPLE_RATE}:async=1:first_pts=0`;

  const args = [
    "-hide_banner",
    "-loglevel", "warning",
    "-nostdin",
    "-probesize", "1000000",
    "-analyzeduration", "1000000",
    "-rw_timeout", "15000000",
    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "5",
    "-user_agent", "Mozilla/5.0",
    // readrate > 1 để vượt TCP slow-start trên 4G trong 15-20s đầu
    "-readrate", FFMPEG_READRATE,
    "-use_wallclock_as_timestamps", "1",
    "-fflags", "+discardcorrupt+genpts+igndts",
    "-avoid_negative_ts", "make_zero",
    "-threads", String(DECODER_THREADS),
    "-filter_threads", "1",
    "-i", channel.url,
    "-map", "0:v:0?",
    "-an",
    "-vf", videoFilter,
    "-c:v", "mjpeg",
    "-q:v", String(qualityPreset.jpegQuality),
    "-threads", String(ENCODER_THREADS),
    "-r", String(VIDEO_FPS),
    "-fps_mode", "cfr",
    "-flush_packets", "1",
    "-f", "image2pipe",
    "pipe:1",
    "-map", "0:a:0?",
    "-vn",
    "-af", audioFilter,
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_SAMPLE_RATE),
    "-c:a", "pcm_s16le",
    "-flush_packets", "1",
    "-f", "s16le",
    "pipe:3"
  ];

  const child = spawn("ffmpeg", args, {
    stdio: ["ignore", "pipe", "pipe", "pipe"]
  });

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
      if (currentGeneration === generation) {
        pushAudioBuffer(chunk);
      }
    });

    child.stdio[3].on("error", error => {
      if (currentGeneration !== generation) return;
      console.error("[AUDIO PIPE]", error.message);
    });
  }

  child.stderr.on("data", data => {
    if (currentGeneration !== generation) return;
    const message = data.toString().trim();
    if (!message) return;

    if (message.includes("Audio:") || message.includes("Stream #0:1")) {
      audioDetected = true;
    }
    if (message.includes("Stream map '0:a:0'") ||
        message.includes("matches no streams")) {
      console.log("[FFMPEG] WARNING: no audio stream found in source");
    }

    console.log("[FFmpeg]", message);
  });

  child.on("error", error => {
    if (currentGeneration !== generation) return;
    console.error("[FFMPEG ERROR]", error.message);
  });

  child.on("close", (code, signal) => {
    console.log("[FFmpeg] Exited:", code, signal);
    if (currentGeneration !== generation) return;
    if (ffmpeg === child) ffmpeg = null;

    clearAudioBuffer();
    clearVideoBuffer();
    resetSync();
    resetStreamReady("ffmpeg exit");

    if (!manuallyStopped) scheduleRestart();
  });

  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation || !ffmpeg || restarting) return;

    const elapsed = Date.now() - lastVideoFrameReceived;
    if (elapsed > VIDEO_TIMEOUT) {
      console.log("[WATCHDOG] No video frame for", elapsed, "ms");
      scheduleRestart();
    }
  }, WATCHDOG_INTERVAL);
}

function scheduleRestart() {
  if (restarting || manuallyStopped) return;

  restarting = true;
  console.log("[RESTART] Waiting:", RESTART_DELAY);

  clearWatchdog();
  generation++;

  const old = ffmpeg;
  ffmpeg = null;

  clearAudioBuffer();
  clearVideoBuffer();
  resetSync();
  resetStreamReady("scheduleRestart");

  audioBlocked = false;
  audioBlockedSince = 0;

  if (old) {
    try { old.kill("SIGKILL"); } catch (_) {}
  }

  if (restartTimer) clearTimeout(restartTimer);

  restartTimer = setTimeout(() => {
    restartTimer = null;
    restarting = false;

    if (currentChannel && !manuallyStopped) {
      startFFmpeg(currentChannel);
    }
  }, RESTART_DELAY);
}

// =====================================================
// VIDEO STREAM
// =====================================================

app.get("/stream", async (req, res) => {
  const requestedFps = Number(req.query.fps);

  let clientFps = DEFAULT_CLIENT_FPS;

  if (Number.isFinite(requestedFps) && requestedFps > 0) {
    clientFps = Math.max(
      MIN_CLIENT_FPS,
      Math.min(MAX_CLIENT_FPS, Math.floor(requestedFps))
    );
  }

  const clientInterval = clientFps >= VIDEO_FPS
    ? 0
    : (1000 / clientFps);

  console.log(
    "[VIDEO] Client request — fps:", clientFps,
    "— waiting for streamReady..."
  );

  const ready = await waitForStreamReady(STREAM_READY_TIMEOUT_MS);

  if (!ready) {
    console.log("[VIDEO] Stream not ready after timeout — 503");
    return res.status(503).json({
      success: false,
      error: "Stream not ready — try again"
    });
  }

  console.log("[VIDEO] Client connected — streamReady=true");

  res.writeHead(200, {
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Pragma": "no-cache",
    "Expires": "0",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no",
    "X-Client-FPS": String(clientFps)
  });

  videoClients++;

  const state = {
    blocked: false,
    blockedSince: 0,
    lastSentSequence: -1,
    clientFps,
    clientInterval,
    lastSentTime: 0,
    skippedFrames: 0,
    blockCount: 0
  };

  videoClientsMap.set(res, state);

  if (
    latestFrame &&
    Date.now() - lastVideoFrameTime <= 1500 &&
    frameSequence > 0
  ) {
    try {
      const header = Buffer.from(
        `--frame\r\n` +
        `Content-Type: image/jpeg\r\n` +
        `Content-Length: ${latestFrame.length}\r\n` +
        `\r\n`
      );

      res.write(header);
      res.write(latestFrame);
      res.write("\r\n");

      state.lastSentSequence = frameSequence;
      state.lastSentTime = Date.now();
      videoSentFrames++;
    } catch (_) {}
  }

  res.on("close", () => cleanupVideoClient(res));
  res.on("error", () => cleanupVideoClient(res));
});

// =====================================================
// AUDIO STREAM — PREBUFFER TRƯỚC KHI GỬI
// =====================================================

app.get("/audio", async (req, res) => {
  console.log("[AUDIO] Client request — waiting for streamReady...");

  const ready = await waitForStreamReady(STREAM_READY_TIMEOUT_MS);

  if (!ready) {
    console.log("[AUDIO] Stream not ready after timeout — 503");
    return res.status(503).json({
      success: false,
      error: "Stream not ready — try again"
    });
  }

  // Chờ thêm cho đến khi buffer đủ AUDIO_PREBUFFER_MS trước khi gửi
  // (đảm bảo client có continuous stream từ byte đầu)
  const prebufferTarget = Math.floor(AUDIO_BYTES_PER_MS * AUDIO_PREBUFFER_MS);
  const waitStart = Date.now();

  while (
    audioBuffer.length < prebufferTarget &&
    Date.now() - waitStart < 5000 &&
    streamReady
  ) {
    await new Promise(r => setTimeout(r, 50));
  }

  console.log("[AUDIO] Buffer at accept:", audioBuffer.length,
    "bytes / target:", prebufferTarget);

  console.log("[AUDIO] Client connected — streamReady=true");

  disconnectAudioClient(false);

  audioClient = res;

  res.statusCode = 200;
  res.setHeader("Content-Type", "application/octet-stream");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");

  res.on("close", () => {
    if (audioClient === res) {
      console.log("[AUDIO] Client disconnected");
      disconnectAudioClient(false);
    }
  });

  res.on("error", () => {
    if (audioClient === res) disconnectAudioClient(false);
  });
});

// =====================================================
// API CONFIG QUALITY
// =====================================================

function qualityConfigHandler(req, res) {
  const requested =
    req.params.quality ||
    req.body?.quality ||
    req.query.quality;

  const preset = requested === undefined
    ? getCurrentQualityPreset()
    : setQuality(requested);

  if (!preset) {
    return res.status(400).json({
      success: false,
      error: "Unsupported quality",
      ...qualityResponse()
    });
  }

  res.json({ success: true, ...qualityResponse() });
}

app.get("/api/config", qualityConfigHandler);
app.get("/api/config/quality", qualityConfigHandler);
app.get("/api/config/quality/:quality", qualityConfigHandler);
app.post("/api/config/quality", qualityConfigHandler);
app.post("/api/config/quality/:quality", qualityConfigHandler);

// =====================================================
// API CHANNELS
// =====================================================

app.get("/api/channels", (req, res) => {
  const requested =
    req.query.quality || req.query.q || req.query.max || "720";

  const rawValue = String(requested).trim().toLowerCase();
  let maxResolution = 720;

  if (rawValue === "all" || rawValue === "full") {
    maxResolution = Number.MAX_SAFE_INTEGER;
  } else {
    const parsed = Number.parseInt(rawValue, 10);
    if (Number.isFinite(parsed) && parsed > 0) maxResolution = parsed;
  }

  const filtered = filterChannelsByResolution(channels, maxResolution);
  const resetSeconds = Math.max(3, Math.ceil(RESTART_DELAY / 1000));

  res.json({
    success: true,
    streamQuality: getCurrentQualityPreset().id,
    jpegQuality: getCurrentQualityPreset().jpegQuality,
    quality: maxResolution === Number.MAX_SAFE_INTEGER
      ? "all" : String(maxResolution),
    channels: filtered.map(channel => ({
      ...channel,
      resetSeconds,
      resetAtMs: Date.now() + resetSeconds * 1000
    }))
  });
});

// =====================================================
// API SELECT / STOP / RELOAD
// =====================================================

function selectChannelHandler(req, res) {
  let id;

  try {
    id = decodeURIComponent(req.params.id);
  } catch (_) {
    return res.status(400).json({
      success: false,
      error: "Invalid channel ID"
    });
  }

  const channel = channels.find(c =>
    c.id === id || c.name.toLowerCase() === id.toLowerCase()
  );

  if (!channel) {
    return res.status(404).json({
      success: false,
      error: "Channel not found"
    });
  }

  try {
    startFFmpeg(channel);
    res.json({ success: true, channel: channel.name });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
}

app.get("/api/select/:id", selectChannelHandler);
app.post("/api/select/:id", selectChannelHandler);

function stopHandler(req, res) {
  stopFFmpeg({ manual: true, disconnectClients: true });
  currentChannel = null;
  res.json({ success: true, message: "Stopped" });
}

app.get("/api/stop", stopHandler);
app.post("/api/stop", stopHandler);

app.get("/api/reload", async (req, res) => {
  try {
    await loadChannels();
    res.json({ success: true, count: channels.length });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// =====================================================
// RENDER BANDWIDTH API
// =====================================================

app.get("/api/bandwidth", async (req, res) => {
  try {
    if (!RENDER_API_KEY) {
      return res.status(500).json({
        success: false,
        error: "Missing RENDER_API_KEY environment variable"
      });
    }

    if (!RENDER_SERVICE_IDS.length) {
      return res.status(500).json({
        success: false,
        error: "Missing RENDER_SERVICE_IDS"
      });
    }

    if (!Number.isFinite(BANDWIDTH_LIMIT_GB) || BANDWIDTH_LIMIT_GB <= 0) {
      return res.status(500).json({
        success: false,
        error: "Invalid BANDWIDTH_LIMIT_GB"
      });
    }

    const now = new Date();
    const start = new Date(
      Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), 1)
    );

    const url = new URL("https://api.render.com/v1/metrics/bandwidth");
    url.searchParams.set("startTime", start.toISOString());
    url.searchParams.set("endTime", now.toISOString());

    for (const id of RENDER_SERVICE_IDS) {
      url.searchParams.append("resource", id);
    }

    const response = await fetch(url, {
      headers: {
        Authorization: `Bearer ${RENDER_API_KEY}`,
        Accept: "application/json"
      },
      signal: AbortSignal.timeout(20000)
    });

    if (!response.ok) {
      const details = await response.text();
      return res.status(response.status).json({
        success: false,
        error: "Render API error",
        httpStatus: response.status,
        details
      });
    }

    const data = await response.json();
    if (!Array.isArray(data)) {
      throw new Error("Invalid Render bandwidth response");
    }

    let usedGB = 0;
    let totalPoints = 0;
    const services = [];

    for (const series of data) {
      const labels = Array.isArray(series.labels) ? series.labels : [];
      const serviceLabel = labels.find(item => item.field === "service");
      const serviceId = serviceLabel ? serviceLabel.value : "unknown";
      const unit = String(series.unit || "GB").toUpperCase();

      let serviceGB = 0;

      for (const point of (series.values || [])) {
        const value = Number(point.value);
        if (!Number.isFinite(value)) continue;

        if (unit === "GB") serviceGB += value;
        else if (unit === "MB") serviceGB += value / 1024;
        else if (["BYTE", "BYTES", "B"].includes(unit)) {
          serviceGB += value / (1024 ** 3);
        } else {
          throw new Error("Unsupported bandwidth unit: " + unit);
        }

        totalPoints++;
      }

      usedGB += serviceGB;
      services.push({
        serviceId,
        usedGB: Number(serviceGB.toFixed(4)),
        unit,
        dataPoints: (series.values || []).length
      });
    }

    usedGB = Number(usedGB.toFixed(4));
    const remainingGB = Math.max(0, BANDWIDTH_LIMIT_GB - usedGB);
    const resetAt = new Date(
      Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, 1)
    );
    const resetInSeconds = Math.max(
      0, Math.ceil((resetAt.getTime() - Date.now()) / 1000)
    );

    const usedPercent = Math.min(
      100, Number((usedGB / BANDWIDTH_LIMIT_GB * 100).toFixed(2))
    );
    const remainingPercent = Number((100 - usedPercent).toFixed(2));

    let status = "NORMAL";
    if (remainingGB <= 0) status = "LIMIT_REACHED";
    else if (remainingGB <= BANDWIDTH_LIMIT_GB * 0.1) status = "WARNING";

    res.json({
      success: true,
      provider: "Render Official API",
      period: {
        start: start.toISOString(),
        end: now.toISOString(),
        timezone: "UTC"
      },
      bandwidth: {
        limitGB: BANDWIDTH_LIMIT_GB,
        usedGB,
        remainingGB,
        usedPercent,
        remainingPercent
      },
      resetInSeconds,
      resetAt: resetAt.toISOString(),
      status,
      services,
      serviceCount: RENDER_SERVICE_IDS.length,
      returnedSeries: data.length,
      totalDataPoints: totalPoints,
      updatedAt: new Date().toISOString(),
      note: "Metrics are delayed and may not equal exact real-time billing balance."
    });
  } catch (error) {
    console.error("[BANDWIDTH ERROR]", error.message);
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// =====================================================
// HEALTH
// =====================================================

app.get("/health", (req, res) => {
  const memory = process.memoryUsage();
  const now = Date.now();

  const clientDetails = [];

  for (const [, state] of videoClientsMap) {
    clientDetails.push({
      fps: state.clientFps,
      interval: state.clientInterval,
      skipped: state.skippedFrames,
      blockCount: state.blockCount,
      blocked: state.blocked,
      blockDurationMs: state.blocked ? now - state.blockedSince : 0,
      lastSentAgoMs: state.lastSentTime ? now - state.lastSentTime : null
    });
  }

  const audioMs = audioFramesSinceSync * AUDIO_FRAME_MS;
  const videoMs = videoFramesSinceSync * VIDEO_INTERVAL;

  const videoBufMs = videoQueue.length * VIDEO_INTERVAL;
  const audioBufMs = audioBuffer.length / AUDIO_BYTES_PER_MS;

  const elapsedSec = ffmpegStartTime ? (now - ffmpegStartTime) / 1000 : 0;
  const audioInKbPerSec = elapsedSec > 0 ? (audioBytesIn / 1024 / elapsedSec) : 0;
  const expectedAudioKbPerSec = (AUDIO_BYTES_PER_MS * 1000) / 1024;
  const audioProductionRate = expectedAudioKbPerSec > 0
    ? Math.round(audioInKbPerSec / expectedAudioKbPerSec * 100) : 0;

  const videoInFps = elapsedSec > 0 ? videoFramesIn / elapsedSec : 0;
  const videoProductionRate = VIDEO_FPS > 0
    ? Math.round(videoInFps / VIDEO_FPS * 100) : 0;

  res.json({
    status: "running",
    channelCount: channels.length,
    currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg,
    restarting,
    manuallyStopped,
    pipeline: "SPLIT_TICK_EPOCH_MJPEG_PCM",
    ffmpegReadrate: FFMPEG_READRATE,

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,
    defaultClientFps: DEFAULT_CLIENT_FPS,
    skipThresholdMs: CLIENT_SKIP_THRESHOLD_MS,
    maxClientBlockMs: MAX_CLIENT_BLOCK_MS,

    streamReady,
    streamReadyAt,
    streamReadyAgeMs: streamReadyAt ? now - streamReadyAt : null,
    streamReadyGraceMs: STREAM_READY_GRACE_MS,
    streamReadyWaiters: streamReadyWaiters.length,

    startupTiming: {
      ffmpegStartTime,
      firstVideoByteAt,
      firstAudioByteAt,
      audioDetected,
      firstVideoByteLatencyMs: firstVideoByteAt ? firstVideoByteAt - ffmpegStartTime : null,
      firstAudioByteLatencyMs: firstAudioByteAt ? firstAudioByteAt - ffmpegStartTime : null,
      streamReadyLatencyMs: streamReadyAt && ffmpegStartTime ? streamReadyAt - ffmpegStartTime : null
    },

    productionRate: {
      audioBytesIn,
      videoFramesIn,
      audioKbPerSec: Number(audioInKbPerSec.toFixed(2)),
      expectedAudioKbPerSec: Number(expectedAudioKbPerSec.toFixed(2)),
      audioProductionRate,
      videoInFps: Number(videoInFps.toFixed(2)),
      videoProductionRate,
      note: "<100% nghĩa là mạng chậm hơn FFmpeg cần → giảm chất lượng hoặc tăng FFMPEG_READRATE"
    },

    videoPrimed,
    videoQueueLength: videoQueue.length,
    videoQueueTarget: VIDEO_QUEUE_TARGET,
    videoQueueMax: VIDEO_QUEUE_MAX,
    syncTrimMs: SYNC_TRIM_MS,

    videoDroppedFrames,
    videoInvalidFrames,
    videoSentFrames,
    videoClients,
    videoPendingBytes: jpegPending.length,
    videoLatestFrameBytes: latestFrame ? latestFrame.length : 0,
    videoFrameSequence: frameSequence,
    videoFrameAge: lastVideoFrameReceived
      ? Date.now() - lastVideoFrameReceived : null,
    videoLastBroadcastAge: lastVideoFrameTime
      ? Date.now() - lastVideoFrameTime : null,
    clientDetails,

    sync: {
      epoch: syncEpoch,
      audioFramesSinceSync,
      videoFramesSinceSync,
      audioMs: Math.round(audioMs),
      videoMs: Math.round(videoMs),
      driftMs: Math.round(audioMs - videoMs),
      maxDriftMs: MAX_SYNC_DRIFT_MS
    },

    contentOffsetMs: Math.round(videoBufMs - audioBufMs),

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFrameBytes: AUDIO_FRAME_BYTES,
    audioInterval: AUDIO_INTERVAL,
    audioTickMs: AUDIO_TICK_MS,
    audioBufferBytes: audioBuffer.length,
    audioBufferMax: AUDIO_BUFFER_MAX,
    audioBufferMs: Math.round(audioBufMs),
    audioStartBufferMs: AUDIO_START_BUFFER_MS,
    audioPrebufferMs: AUDIO_PREBUFFER_MS,
    audioTargetBufferMs,
    audioPrimed,
    audioMaxObservedBytes,
    audioClientConnected: !!audioClient && !audioClient.destroyed,
    audioBlocked,
    audioUnderflows,
    audioOverflowBytes,
    audioSilenceBytes,
    audioFramesSent,
    audioSilenceSent,

    masterTickMs: MASTER_TICK_MS,

    memory: {
      rssMB: Number((memory.rss / 1048576).toFixed(2)),
      heapUsedMB: Number((memory.heapUsed / 1048576).toFixed(2)),
      externalMB: Number((memory.external / 1048576).toFixed(2)),
      arrayBuffersMB: Number((memory.arrayBuffers / 1048576).toFixed(2))
    },

    lastVideoFrameReceived,
    lastVideoFrameTime,
    generation
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.send(
    "IPTV SERVER RUNNING - SPLIT TICK + READRATE + PREBUFFER\n" +
    "Usage:\n" +
    "  /stream              → default " + DEFAULT_CLIENT_FPS + " fps\n" +
    "  /stream?fps=12       → 12 fps\n" +
    "  /audio               → PCM audio (prebuffered)\n" +
    "\nAudio pipeline tách riêng khỏi video tick để đảm bảo mượt từ đầu."
  );
});

// =====================================================
// START
// =====================================================

async function main() {
  try {
    await loadChannels();
  } catch (error) {
    console.log("[STARTUP] Playlist failed:", error.message);
  }

  startMasterTimer();
  startAudioTimer();

  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("CHANNELS:", channels.length);
    console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
    console.log("MASTER TICK:", MASTER_TICK_MS, "ms");
    console.log("AUDIO TICK:", AUDIO_TICK_MS, "ms");
    console.log("VIDEO QUEUE TARGET:", VIDEO_QUEUE_TARGET, "frames");
    console.log("VIDEO QUEUE MAX:", VIDEO_QUEUE_MAX, "frames");
    console.log("AUDIO START BUFFER:", AUDIO_START_BUFFER_MS, "ms");
    console.log("AUDIO BUFFER MAX:", AUDIO_BUFFER_MS, "ms");
    console.log("AUDIO PREBUFFER:", AUDIO_PREBUFFER_MS, "ms");
    console.log("FFMPEG READRATE:", FFMPEG_READRATE);
    console.log("PIPELINE: SPLIT TICK + READRATE");
    console.log("--------------------------------");
  });

  if (!channels.length) {
    const retryPlaylist = async () => {
      try {
        await loadChannels();
        console.log("[M3U] Playlist recovered:", channels.length);
      } catch (error) {
        console.log("[M3U] Retry failed:", error.message);
        setTimeout(retryPlaylist, 15000);
      }
    };

    setTimeout(retryPlaylist, 15000);
  }
}

main().catch(error => {
  console.error("[SERVER ERROR]", error);
  process.exit(1);
});
