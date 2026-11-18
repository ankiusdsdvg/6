const express = require("express");
const { spawn } = require("child_process");
const os = require("os");

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

const JPEG_QUALITY = 10;
const JPEG_QUALITY_720P = 15;
const JPEG_QUALITY_540P = 20;
const JPEG_QUALITY_340P = 25;

const QUALITY_PRESETS = Object.freeze([
  Object.freeze({ id: "1080p", label: "1080p", jpegQuality: JPEG_QUALITY }),
  Object.freeze({ id: "720p", label: "720p", jpegQuality: JPEG_QUALITY_720P }),
  Object.freeze({ id: "540p", label: "540p", jpegQuality: JPEG_QUALITY_540P }),
  Object.freeze({ id: "340p", label: "340p", jpegQuality: JPEG_QUALITY_340P })
]);

let currentQualityId = "1080p";

// ===== AUDIO =====
const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;
const AUDIO_BYTES_PER_MS =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE / 1000;

const AUDIO_PREBUFFER_MS = 200;
const AUDIO_PREBUFFER_BYTES = AUDIO_BYTES_PER_MS * AUDIO_PREBUFFER_MS;
const AUDIO_PREBUFFER_MAX_BYTES = AUDIO_BYTES_PER_MS * 1000;
const AUDIO_LIVE_MAX_BYTES = AUDIO_BYTES_PER_MS * 2000;

const DECODER_THREADS = Math.min(4, Math.max(2, os.cpus().length - 1));
const ENCODER_THREADS = 1;

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

const MAX_VIDEO_BUFFER = 1024 * 1024;  // 🔥 tăng từ 512KB → 1MB
const MAX_JPEG_FRAME_BYTES = 256 * 1024;

const CLIENT_SKIP_THRESHOLD_MS = 30;
const MAX_CLIENT_BLOCK_MS = 3000;

const JPEG_SOI = Buffer.from([0xff, 0xd8]);
const JPEG_EOI = Buffer.from([0xff, 0xd9]);

const RENDER_API_KEY = process.env.RENDER_API_KEY || "rnd_E4m8zGWRFKuhlc7kAuvU8IPoTZd5";
const RENDER_SERVICE_IDS = (
  process.env.RENDER_SERVICE_IDS || "srv-dbphu6vf3r2c738786ng"
).split(",").map(x => x.trim()).filter(Boolean);

const BANDWIDTH_LIMIT_GB = Number(process.env.BANDWIDTH_LIMIT_GB || 5);

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

let frameBroadcastTimer = null;
let lastBroadcastSeq = -1;
let lastBroadcastTime = 0;

let frameTimestamps = [];

let videoInvalidFrames = 0;
let videoSentFrames = 0;
let videoClients = 0;
const videoClientsMap = new Map();

// 🔥 Đo FFmpeg lifecycle
let ffmpegStartedAt = 0;
let firstFrameArrivedAt = 0;
let inputStallCount = 0;
let lastStallAt = 0;

let audioClient = null;
let audioClientSlow = false;
let audioPrebuffer = [];
let audioPrebufferBytes = 0;
let audioStarted = false;

let audioBytesReceived = 0;
let audioBytesSent = 0;
let audioBytesDropped = 0;
let audioBurstDropped = 0;
let audioFirstByteAt = 0;
let audioLastByteAt = 0;

let watchdogTimer = null;
let restartTimer = null;
let lastVideoFrameTime = 0;
let restarting = false;
let manuallyStopped = true;

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
    if (line.startsWith("#EXTINF:")) { currentInfo = line; continue; }
    if (line.startsWith("#") || !currentInfo) continue;
    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(line)) { currentInfo = null; continue; }

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
  return QUALITY_PRESETS.some(p => p.id === normalized) ? normalized : null;
}

function getCurrentQualityPreset() {
  return QUALITY_PRESETS.find(p => p.id === currentQualityId) || QUALITY_PRESETS[0];
}

function qualityResponse() {
  const preset = getCurrentQualityPreset();
  return {
    quality: preset.id,
    jpegQuality: preset.jpegQuality,
    presets: QUALITY_PRESETS.map(i => ({
      id: i.id, label: i.label, jpegQuality: i.jpegQuality
    }))
  };
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
// AUDIO
// =====================================================

function disconnectAudioClient() {
  const old = audioClient;
  audioClient = null;
  audioClientSlow = false;
  audioStarted = false;
  audioPrebuffer = [];
  audioPrebufferBytes = 0;
  if (old && !old.destroyed) {
    try { old.destroy(); } catch (_) {}
  }
}

function handleAudioChunk(chunk) {
  if (!chunk || !chunk.length) return;
  if (chunk.length & 1) chunk = chunk.subarray(0, chunk.length - 1);
  if (!chunk.length) return;

  const now = Date.now();
  if (!audioFirstByteAt) audioFirstByteAt = now;
  audioLastByteAt = now;
  audioBytesReceived += chunk.length;

  if (!audioClient || audioClient.destroyed || audioClient.writableEnded) return;

  if (!audioStarted) {
    audioPrebuffer.push(chunk);
    audioPrebufferBytes += chunk.length;

    if (audioPrebufferBytes >= AUDIO_PREBUFFER_MAX_BYTES) {
      let totalKept = 0;
      const kept = [];
      for (let i = audioPrebuffer.length - 1; i >= 0; i--) {
        const c = audioPrebuffer[i];
        if (totalKept + c.length <= AUDIO_PREBUFFER_BYTES) {
          kept.unshift(c);
          totalKept += c.length;
        } else {
          audioBurstDropped += c.length;
          audioBytesDropped += c.length;
        }
      }
      audioPrebuffer = kept;
      audioPrebufferBytes = totalKept;
      audioStarted = true;
    } else if (audioPrebufferBytes >= AUDIO_PREBUFFER_BYTES) {
      audioStarted = true;
    } else {
      return;
    }

    for (const c of audioPrebuffer) {
      if (audioClientSlow) { audioBytesDropped += c.length; continue; }
      const ok = audioClient.write(c);
      if (ok) audioBytesSent += c.length;
      else {
        audioClientSlow = true;
        audioBytesDropped += c.length;
        audioClient.once("drain", () => { audioClientSlow = false; });
      }
    }
    audioPrebuffer = [];
    audioPrebufferBytes = 0;
    return;
  }

  if (audioClientSlow) { audioBytesDropped += chunk.length; return; }
  if (audioClient.writableLength > AUDIO_LIVE_MAX_BYTES) {
    audioBytesDropped += chunk.length;
    audioBurstDropped += chunk.length;
    return;
  }

  const ok = audioClient.write(chunk);
  if (ok) audioBytesSent += chunk.length;
  else {
    audioClientSlow = true;
    audioBytesDropped += chunk.length;
    audioClient.once("drain", () => { audioClientSlow = false; });
  }
}

// =====================================================
// VIDEO
// =====================================================

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
  frameTimestamps = [];
  firstFrameArrivedAt = 0;
}

function startFrameBroadcastTimer() {
  if (frameBroadcastTimer) return;
  const checkInterval = Math.max(8, Math.floor(VIDEO_INTERVAL / 2));

  frameBroadcastTimer = setInterval(() => {
    if (!latestFrame) return;
    if (frameSequence === lastBroadcastSeq) return;

    const now = Date.now();
    if (now - lastBroadcastTime < VIDEO_INTERVAL * 0.85) return;

    lastBroadcastSeq = frameSequence;
    lastBroadcastTime = now;
    broadcastFrame(latestFrame);
  }, checkInterval);
}

function stopFrameBroadcastTimer() {
  if (frameBroadcastTimer) {
    clearInterval(frameBroadcastTimer);
    frameBroadcastTimer = null;
  }
  lastBroadcastSeq = -1;
  lastBroadcastTime = 0;
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
      const dt = now - state.lastSentTime;
      if (dt < state.clientInterval * 0.9) {
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
        ? Buffer.from([0xff])
        : Buffer.alloc(0);
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

    latestFrame = Buffer.from(jpegPending.subarray(0, frameLength));
    frameSequence++;
    lastVideoFrameTime = Date.now();

    if (!firstFrameArrivedAt) {
      firstFrameArrivedAt = lastVideoFrameTime;
      const waited = ffmpegStartedAt ? (firstFrameArrivedAt - ffmpegStartedAt) / 1000 : 0;
      console.log(`[VIDEO] First frame after ${waited.toFixed(2)}s`);
    }

    // Đo stall: nếu khoảng cách giữa 2 frame > 2 * interval
    if (frameTimestamps.length) {
      const gap = lastVideoFrameTime - frameTimestamps[frameTimestamps.length - 1];
      if (gap > VIDEO_INTERVAL * 2.5) {
        inputStallCount++;
        lastStallAt = lastVideoFrameTime;
        if (inputStallCount <= 10 || inputStallCount % 20 === 0) {
          console.log(`[VIDEO] ⚠ Input stall #${inputStallCount}: gap ${gap}ms`);
        }
      }
    }

    frameTimestamps.push(lastVideoFrameTime);
    if (frameTimestamps.length > 120) frameTimestamps.shift();

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// =====================================================
// FFMPEG LIFECYCLE
// =====================================================

function clearWatchdog() {
  if (watchdogTimer) { clearInterval(watchdogTimer); watchdogTimer = null; }
}

function stopFFmpeg() {
  generation++;
  manuallyStopped = true;
  restarting = false;
  clearWatchdog();
  stopFrameBroadcastTimer();
  if (restartTimer) { clearTimeout(restartTimer); restartTimer = null; }
  disconnectAudioClient();
  for (const res of videoClientsMap.keys()) {
    try { res.destroy(); } catch (_) {}
  }
  videoClientsMap.clear();
  videoClients = 0;
  clearVideoBuffer();
  if (ffmpeg) {
    const old = ffmpeg;
    ffmpeg = null;
    try { old.kill("SIGKILL"); } catch (_) {}
  }
}

function startFFmpeg(channel) {
  if (!channel?.url) { console.log("[FFMPEG] Invalid channel"); return; }

  stopFFmpeg();

  manuallyStopped = false;
  currentChannel = channel;
  clearVideoBuffer();

  audioStarted = false;
  audioPrebuffer = [];
  audioPrebufferBytes = 0;
  audioBytesReceived = 0;
  audioBytesSent = 0;
  audioBytesDropped = 0;
  audioBurstDropped = 0;
  audioFirstByteAt = 0;
  audioLastByteAt = 0;

  videoInvalidFrames = 0;
  videoSentFrames = 0;
  inputStallCount = 0;
  lastStallAt = 0;

  const currentGeneration = generation;
  const qualityPreset = getCurrentQualityPreset();

  ffmpegStartedAt = Date.now();
  lastVideoFrameTime = ffmpegStartedAt;

  const isHls = /\.m3u8(\?|$)/i.test(channel.url);

  console.log("\n==================================");
  console.log("CHANNEL:", channel.name);
  console.log("URL TYPE:", isHls ? "HLS" : "HTTP/other");
  console.log("GENERATION:", currentGeneration);
  console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
  console.log("DECODER THREADS:", DECODER_THREADS, "/ CPU cores:", os.cpus().length);
  console.log("MODE: no -re, buffered input, live_start_index -3");
  console.log("==================================");

  const videoFilter = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  // 🔥 FFmpeg args mới — BỎ -re, tăng buffer input, dùng HLS live_start_index
  const inputArgs = [
    "-hide_banner",
    "-loglevel", "warning",
    "-nostdin",

    // === INPUT BUFFERING ===
    "-probesize", "5M",
    "-analyzeduration", "10000000",
    "-thread_queue_size", "2048",        // 🔥 tăng từ 512 → 2048
    "-max_delay", "500000",              // chờ tối đa 500ms
    "-reorder_queue_size", "4096",

    // === RECONNECT ===
    "-rw_timeout", "30000000",
    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_at_eof", "1",
    "-reconnect_delay_max", "30",

    // === FLAGS ===
    "-user_agent", "Mozilla/5.0",
    "-fflags", "+discardcorrupt+genpts",

    // ❌ BỎ "-re" — đây là thủ phạm chính gây stall HLS
    // "-re",

    // === HLS specific (FFmpeg sẽ ignore nếu không phải HLS) ===
    ...(isHls ? ["-live_start_index", "-3"] : []),

    // === DECODE ===
    "-threads", String(DECODER_THREADS),
    "-filter_threads", "1",

    // === INPUT ===
    "-i", channel.url
  ];

  const outputArgs = [
    // VIDEO
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

    // AUDIO
    "-map", "0:a:0?",
    "-vn",
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_SAMPLE_RATE),
    "-c:a", "pcm_s16le",
    "-flush_packets", "1",
    "-f", "s16le",
    "pipe:3"
  ];

  const args = [...inputArgs, ...outputArgs];

  const child = spawn("ffmpeg", args, {
    stdio: ["ignore", "pipe", "pipe", "pipe"]
  });

  ffmpeg = child;

  child.stdout.on("data", chunk => {
    processVideoData(chunk, currentGeneration);
  });

  if (child.stdio[3]) {
    child.stdio[3].on("data", chunk => {
      if (currentGeneration === generation) handleAudioChunk(chunk);
    });
  }

  child.stderr.on("data", data => {
    const message = data.toString().trim();
    if (message) console.log("[FFmpeg]", message);
  });

  child.on("error", error => {
    console.error("[FFMPEG ERROR]", error.message);
  });

  child.on("close", (code, signal) => {
    console.log("[FFmpeg] Exited:", code, signal);
    if (currentGeneration !== generation) return;
    ffmpeg = null;
    clearVideoBuffer();
    if (!manuallyStopped) scheduleRestart();
  });

  startFrameBroadcastTimer();

  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation || !ffmpeg || restarting) return;
    const elapsed = Date.now() - lastVideoFrameTime;
    if (elapsed > VIDEO_TIMEOUT) {
      console.log("[WATCHDOG] No video frame for", elapsed, "ms");
      scheduleRestart();
    }
  }, WATCHDOG_INTERVAL);
}

function scheduleRestart() {
  if (restarting || manuallyStopped) return;
  restarting = true;
  disconnectAudioClient();
  clearVideoBuffer();
  clearWatchdog();
  stopFrameBroadcastTimer();
  if (ffmpeg) {
    const old = ffmpeg;
    ffmpeg = null;
    try { old.kill("SIGKILL"); } catch (_) {}
  }
  if (restartTimer) clearTimeout(restartTimer);
  restartTimer = setTimeout(() => {
    restartTimer = null;
    restarting = false;
    if (currentChannel && !manuallyStopped) startFFmpeg(currentChannel);
  }, RESTART_DELAY);
}

// =====================================================
// VIDEO STREAM
// =====================================================

app.get("/stream", (req, res) => {
  const requestedFps = Number(req.query.fps);
  let clientFps = DEFAULT_CLIENT_FPS;
  if (Number.isFinite(requestedFps) && requestedFps > 0) {
    clientFps = Math.max(MIN_CLIENT_FPS, Math.min(MAX_CLIENT_FPS, Math.floor(requestedFps)));
  }
  const clientInterval = clientFps >= VIDEO_FPS ? 0 : (1000 / clientFps);

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
    blocked: false, blockedSince: 0,
    lastSentSequence: -1, clientFps, clientInterval,
    lastSentTime: 0, skippedFrames: 0, blockCount: 0
  };
  videoClientsMap.set(res, state);

  if (latestFrame && Date.now() - lastVideoFrameTime <= 1500 && frameSequence > 0) {
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
// AUDIO STREAM
// =====================================================

app.get("/audio", (req, res) => {
  disconnectAudioClient();
  audioClient = res;
  audioClientSlow = false;
  audioStarted = false;
  audioPrebuffer = [];
  audioPrebufferBytes = 0;
  audioBytesReceived = 0;
  audioBytesSent = 0;
  audioBytesDropped = 0;
  audioBurstDropped = 0;

  res.statusCode = 200;
  res.setHeader("Content-Type", "application/octet-stream");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");

  res.on("close", () => {
    if (audioClient === res) disconnectAudioClient();
  });
  res.on("error", () => {
    if (audioClient === res) disconnectAudioClient();
  });
});

// =====================================================
// API
// =====================================================

function qualityConfigHandler(req, res) {
  const requested = req.params.quality || req.body?.quality || req.query.quality;
  const preset = requested === undefined ? getCurrentQualityPreset() : setQuality(requested);
  if (!preset) {
    return res.status(400).json({
      success: false, error: "Unsupported quality", ...qualityResponse()
    });
  }
  res.json({ success: true, ...qualityResponse() });
}

app.get("/api/config", qualityConfigHandler);
app.get("/api/config/quality", qualityConfigHandler);
app.get("/api/config/quality/:quality", qualityConfigHandler);
app.post("/api/config/quality", qualityConfigHandler);
app.post("/api/config/quality/:quality", qualityConfigHandler);

app.get("/api/channels", (req, res) => {
  const requested = req.query.quality || req.query.q || req.query.max || "720";
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
    quality: maxResolution === Number.MAX_SAFE_INTEGER ? "all" : String(maxResolution),
    channels: filtered.map(channel => ({
      ...channel, resetSeconds, resetAtMs: Date.now() + resetSeconds * 1000
    }))
  });
});

function selectChannelHandler(req, res) {
  let id;
  try { id = decodeURIComponent(req.params.id); }
  catch (_) {
    return res.status(400).json({ success: false, error: "Invalid channel ID" });
  }
  const channel = channels.find(c =>
    c.id === id || c.name.toLowerCase() === id.toLowerCase()
  );
  if (!channel) {
    return res.status(404).json({ success: false, error: "Channel not found" });
  }
  startFFmpeg(channel);
  res.json({ success: true, channel: channel.name });
}

app.get("/api/select/:id", selectChannelHandler);
app.post("/api/select/:id", selectChannelHandler);

function stopHandler(req, res) {
  stopFFmpeg();
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
    res.status(500).json({ success: false, error: error.message });
  }
});

// =====================================================
// HEALTH
// =====================================================

function calculateFps(windowMs) {
  if (frameTimestamps.length < 2) return 0;
  const now = Date.now();
  const recent = frameTimestamps.filter(t => now - t < windowMs);
  if (recent.length < 2) return 0;
  const span = recent[recent.length - 1] - recent[0];
  return span > 0 ? Number(((recent.length - 1) / (span / 1000)).toFixed(1)) : 0;
}

app.get("/health", (req, res) => {
  const memory = process.memoryUsage();
  const now = Date.now();

  const clientDetails = [];
  for (const [, state] of videoClientsMap) {
    clientDetails.push({
      fps: state.clientFps,
      skipped: state.skippedFrames,
      blocked: state.blocked,
      lastSentAgoMs: state.lastSentTime ? now - state.lastSentTime : null
    });
  }

  res.json({
    status: "running",
    channelCount: channels.length,
    currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg,
    pipeline: "BUFFERED_INPUT_NO_RE_FIXED_RATE",

    videoFPS: VIDEO_FPS,
    decoderThreads: DECODER_THREADS,
    cpuCores: os.cpus().length,

    // 🔥 CHẨN ĐOÁN QUAN TRỌNG
    ffmpegUptimeSeconds: ffmpegStartedAt
      ? Number(((now - ffmpegStartedAt) / 1000).toFixed(1)) : 0,
    firstFrameDelaySeconds: firstFrameArrivedAt && ffmpegStartedAt
      ? Number(((firstFrameArrivedAt - ffmpegStartedAt) / 1000).toFixed(2)) : null,
    inputStallCount,
    lastStallAgoMs: lastStallAt ? now - lastStallAt : null,

    sourceFpsLast2s: calculateFps(2000),
    sourceFpsLast5s: calculateFps(5000),
    sourceFpsLast10s: calculateFps(10000),
    broadcastTimerActive: !!frameBroadcastTimer,
    lastFrameArrivalAgoMs: lastVideoFrameTime ? now - lastVideoFrameTime : null,
    lastBroadcastAgoMs: lastBroadcastTime ? now - lastBroadcastTime : null,

    videoInvalidFrames,
    videoSentFrames,
    videoClients,
    clientDetails,

    audio: {
      clientConnected: !!audioClient && !audioClient.destroyed,
      started: audioStarted,
      bytesReceived: audioBytesReceived,
      bytesSent: audioBytesSent,
      bytesDropped: audioBytesDropped,
      burstDropped: audioBurstDropped,
      dropPercent: audioBytesReceived > 0
        ? Number((audioBytesDropped / audioBytesReceived * 100).toFixed(2)) : 0
    },

    memory: {
      rssMB: Number((memory.rss / 1048576).toFixed(2)),
      heapUsedMB: Number((memory.heapUsed / 1048576).toFixed(2))
    },

    generation
  });
});

// =====================================================
// ROOT / START
// =====================================================

app.get("/", (req, res) => {
  res.send(
    "IPTV SERVER - BUFFERED INPUT, NO -re, FIXED-RATE OUTPUT\n" +
    "  /stream              → " + DEFAULT_CLIENT_FPS + " fps\n" +
    "  /stream?fps=12\n" +
    "  /audio               → PCM " + AUDIO_SAMPLE_RATE + "Hz mono\n" +
    "  /health              → xem inputStallCount để biết FFmpeg có stall không\n"
  );
});

async function main() {
  try { await loadChannels(); }
  catch (error) { console.log("[STARTUP] Playlist failed:", error.message); }

  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("PIPELINE: BUFFERED INPUT (no -re) + FIXED-RATE OUTPUT");
    console.log("--------------------------------");
  });
}

main().catch(error => {
  console.error("[SERVER ERROR]", error);
  process.exit(1);
});
