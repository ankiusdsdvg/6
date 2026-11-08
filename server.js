
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
const VIDEO_HEIGHT = 180;
const VIDEO_FPS = 8;
const JPEG_QUALITY = 8;
const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;
const AUDIO_FRAME_MS = 200;
const AUDIO_INTERVAL = AUDIO_FRAME_MS;
const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE * AUDIO_FRAME_MS / 1000;

const AUDIO_START_BUFFER_MS = 1200;
const AUDIO_BUFFER_MS = 3000;
const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE * AUDIO_BUFFER_MS / 1000;

let audioTargetBufferMs = AUDIO_START_BUFFER_MS;
let audioStableFrames = 0;

const AUDIO_TARGET_MIN_MS = 1000;
const AUDIO_TARGET_MAX_MS = 1800;
const AUDIO_STABLE_FRAMES_TO_REDUCE = 150;

const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

const MAX_VIDEO_BUFFER = 512 * 1024;
const MAX_JPEG_FRAME_BYTES = 256 * 1024;
const MAX_CLIENT_BLOCK_MS = 1500;
const MAX_AUDIO_BLOCK_MS = 1500;

const JPEG_SOI = Buffer.from([0xff, 0xd8]);
const JPEG_EOI = Buffer.from([0xff, 0xd9]);

const RENDER_API_KEY = process.env.RENDER_API_KEY || "";
const RENDER_SERVICE_IDS = (
  process.env.RENDER_SERVICE_IDS || "srv-dbktk7s9v7es73fb7fcg"
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

let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let videoSentFrames = 0;
let videoClients = 0;

let audioBuffer = Buffer.alloc(0);
let audioClient = null;
let audioTimer = null;
let audioBlocked = false;
let audioBlockedSince = 0;
let audioUnderflows = 0;
let audioOverflowBytes = 0;
let audioFramesSent = 0;
let audioPrimed = false;
let audioSilenceBytes = 0;
let audioLastTick = 0;
let audioMaxObservedBytes = 0;

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
// AUDIO BUFFER / CLOCK
// =====================================================

function resetAudioState(resetStats = false) {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioStableFrames = 0;
  audioTargetBufferMs = AUDIO_START_BUFFER_MS;
  audioLastTick = 0;
  audioMaxObservedBytes = 0;

  if (resetStats) {
    audioUnderflows = 0;
    audioOverflowBytes = 0;
    audioFramesSent = 0;
    audioSilenceBytes = 0;
  }
}

function clearAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
}

function disconnectAudioClient() {
  if (audioTimer) {
    clearInterval(audioTimer);
    audioTimer = null;
  }

  const old = audioClient;

  audioClient = null;
  audioBlocked = false;
  audioBlockedSince = 0;

  clearAudioBuffer();

  if (old && !old.destroyed) {
    try {
      old.destroy();
    } catch (_) {}
  }
}

function pushAudioBuffer(chunk) {
  if (!audioClient || audioClient.destroyed || !chunk?.length) return;

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

function makeSilenceFrame() {
  return Buffer.alloc(AUDIO_FRAME_BYTES, 0);
}

function takeAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES, 0);

  const count = Math.min(
    audioBuffer.length,
    AUDIO_FRAME_BYTES
  ) & ~1;

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

function startAudioTimer() {
  if (audioTimer) clearInterval(audioTimer);

  audioLastTick = Date.now();

  audioTimer = setInterval(() => {
    if (!audioClient || audioClient.destroyed) {
      disconnectAudioClient();
      return;
    }

    if (audioBlocked) {
      if (Date.now() - audioBlockedSince > MAX_AUDIO_BLOCK_MS) {
        console.log("[AUDIO] Slow client disconnected");
        disconnectAudioClient();
      }
      return;
    }

    const now = Date.now();
    const elapsed = now - audioLastTick;

    audioLastTick = now;

    if (elapsed > AUDIO_INTERVAL * 2) {
      console.warn("[AUDIO] Sender clock delayed:", elapsed, "ms");
    }

    const targetBytes = Math.floor(
      AUDIO_SAMPLE_RATE *
      AUDIO_CHANNELS *
      AUDIO_BYTES_PER_SAMPLE *
      audioTargetBufferMs / 1000
    );

    if (!audioPrimed) {
      if (audioBuffer.length < targetBytes) return;

      audioPrimed = true;

      console.log(
        "[AUDIO] Prebuffer ready:",
        audioBuffer.length,
        "bytes"
      );
    }

    const frame = takeAudioFrame();

    try {
      const ok = audioClient.write(frame);

      audioFramesSent++;

      if (!ok) {
        audioBlocked = true;
        audioBlockedSince = Date.now();

        audioClient.once("drain", () => {
          audioBlocked = false;
          audioBlockedSince = 0;
        });
      }

    } catch (error) {
      console.error("[AUDIO WRITE]", error.message);
      disconnectAudioClient();
    }

  }, AUDIO_INTERVAL);
}

// =====================================================
// VIDEO JPEG PARSER
// =====================================================

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
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

    if (start > 0) {
      jpegPending = jpegPending.subarray(start);
    }

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

    if (latestFrame) {
      videoDroppedFrames++;
    }

    latestFrame = Buffer.from(
      jpegPending.subarray(0, frameLength)
    );

    frameSequence++;
    lastVideoFrameTime = Date.now();

    jpegPending = jpegPending.subarray(frameLength);
  }
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

function stopFFmpeg() {
  generation++;
  manuallyStopped = true;
  restarting = false;

  clearWatchdog();

  if (restartTimer) {
    clearTimeout(restartTimer);
    restartTimer = null;
  }

  disconnectAudioClient();
  clearVideoBuffer();

  if (ffmpeg) {
    const old = ffmpeg;
    ffmpeg = null;

    try {
      old.kill("SIGKILL");
    } catch (_) {}
  }
}

function startFFmpeg(channel) {
  if (!channel?.url) {
    console.log("[FFMPEG] Invalid channel");
    return;
  }

  stopFFmpeg();

  manuallyStopped = false;
  currentChannel = channel;

  clearVideoBuffer();
  resetAudioState(true);

  videoDroppedFrames = 0;
  videoInvalidFrames = 0;
  videoSentFrames = 0;

  const currentGeneration = generation;

  lastVideoFrameTime = Date.now();

  console.log("\n==================================");
  console.log("CHANNEL:", channel.name);
  console.log("GENERATION:", currentGeneration);
  console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
  console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM`);
  console.log("AUDIO PREBUFFER:", `${AUDIO_START_BUFFER_MS}ms`);
  console.log("==================================");

  const videoFilter = [
    `fps=${VIDEO_FPS}:round=near`,
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  const args = [
    "-hide_banner",
    "-loglevel", "warning",
    "-nostdin",
    "-rw_timeout", "30000000",
    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "5",
    "-user_agent", "Mozilla/5.0",
    "-fflags", "+discardcorrupt+genpts",
    "-threads", String(DECODER_THREADS),
    "-filter_threads", "1",
    "-i", channel.url,

    // OUTPUT 1: MJPEG VIDEO
    "-map", "0:v:0?",
    "-an",
    "-vf", videoFilter,
    "-c:v", "mjpeg",
    "-q:v", String(JPEG_QUALITY),
    "-threads", String(ENCODER_THREADS),
    "-fps_mode", "cfr",
    "-flush_packets", "1",
    "-f", "image2pipe",
    "pipe:1",

    // OUTPUT 2: PCM AUDIO
    "-map", "0:a:0?",
    "-vn",
    "-af", `aresample=${AUDIO_SAMPLE_RATE}:async=1000:min_hard_comp=0.100:first_pts=0`,
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
    processVideoData(chunk, currentGeneration);
  });

  if (child.stdio[3]) {
    child.stdio[3].on("data", chunk => {
      if (currentGeneration === generation) {
        pushAudioBuffer(chunk);
      }
    });
  }

  child.stderr.on("data", data => {
    const message = data.toString().trim();

    if (message) {
      console.log("[FFmpeg]", message);
    }
  });

  child.on("error", error => {
    console.error("[FFMPEG ERROR]", error.message);
  });

  child.on("close", (code, signal) => {
    console.log("[FFmpeg] Exited:", code, signal);

    if (currentGeneration !== generation) return;

    ffmpeg = null;

    clearAudioBuffer();
    clearVideoBuffer();

    if (!manuallyStopped) {
      scheduleRestart();
    }
  });

  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation || !ffmpeg || restarting) {
      return;
    }

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

  console.log("[RESTART] Waiting:", RESTART_DELAY);

  disconnectAudioClient();
  clearVideoBuffer();
  clearWatchdog();

  if (ffmpeg) {
    const old = ffmpeg;
    ffmpeg = null;

    try {
      old.kill("SIGKILL");
    } catch (_) {}
  }

  if (restartTimer) {
    clearTimeout(restartTimer);
  }

  restartTimer = setTimeout(() => {
    restartTimer = null;
    restarting = false;

    if (currentChannel && !manuallyStopped) {
      startFFmpeg(currentChannel);
    }

  }, RESTART_DELAY);
}

// =====================================================
// VIDEO STREAM - FIXED MJPEG API
// =====================================================

app.get("/stream", (req, res) => {
  res.writeHead(200, {
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Pragma": "no-cache",
    "Expires": "0",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  videoClients++;

  let lastSentSequence = -1;
  let blocked = false;
  let blockedSince = 0;
  let closed = false;

  function cleanup() {
    if (closed) return;

    closed = true;
    clearInterval(timer);

    videoClients = Math.max(0, videoClients - 1);
  }

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    if (blocked) {
      if (Date.now() - blockedSince > MAX_CLIENT_BLOCK_MS) {
        console.log("[VIDEO] Slow client disconnected");

        cleanup();
        res.destroy();
      }

      return;
    }

    const frame = latestFrame;
    const sequence = frameSequence;

    if (!frame || sequence === lastSentSequence) return;

    if (Date.now() - lastVideoFrameTime > 1500) return;

    // IMPORTANT: Real CRLF characters, not escaped backslash sequences.
    const header = Buffer.from(
      `--frame\r\n` +
      `Content-Type: image/jpeg\r\n` +
      `Content-Length: ${frame.length}\r\n` +
      `\r\n`
    );

    try {
      let ok = res.write(header);

      if (!res.write(frame)) {
        ok = false;
      }

      if (!res.write("\r\n")) {
        ok = false;
      }

      lastSentSequence = sequence;
      videoSentFrames++;

      if (!ok) {
        blocked = true;
        blockedSince = Date.now();

        res.once("drain", () => {
          blocked = false;
          blockedSince = 0;
        });
      }

    } catch (error) {
      console.error("[VIDEO WRITE]", error.message);

      cleanup();
      res.destroy();
    }

  }, VIDEO_INTERVAL);

  res.on("close", cleanup);
  res.on("error", cleanup);
});

// =====================================================
// AUDIO STREAM - EXISTING RAW PCM API
// =====================================================

app.get("/audio", (req, res) => {
  disconnectAudioClient();
  resetAudioState(false);

  audioClient = res;

  res.statusCode = 200;

  res.setHeader("Content-Type", "application/octet-stream");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");

  console.log("[AUDIO] Client connected; waiting for PCM prebuffer");

  startAudioTimer();

  res.on("close", () => {
    if (audioClient === res) {
      console.log("[AUDIO] Client disconnected");
      disconnectAudioClient();
    }
  });
});

// =====================================================
// API CHANNELS
// =====================================================

app.get("/api/channels", (req, res) => {
  const requested =
    req.query.quality ||
    req.query.q ||
    req.query.max ||
    "720";

  const rawValue = String(requested).trim().toLowerCase();

  let maxResolution = 720;

  if (rawValue === "all" || rawValue === "full") {
    maxResolution = Number.MAX_SAFE_INTEGER;
  } else {
    const parsed = Number.parseInt(rawValue, 10);

    if (Number.isFinite(parsed) && parsed > 0) {
      maxResolution = parsed;
    }
  }

  const filtered = filterChannelsByResolution(
    channels,
    maxResolution
  );

  const resetSeconds = Math.max(
    3,
    Math.ceil(RESTART_DELAY / 1000)
  );

  res.json({
    success: true,
    quality: maxResolution === Number.MAX_SAFE_INTEGER
      ? "all"
      : String(maxResolution),

    channels: filtered.map(channel => ({
      ...channel,
      resetSeconds,
      resetAtMs: Date.now() + resetSeconds * 1000
    }))
  });
});

// =====================================================
// API SELECT
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
    c.id === id ||
    c.name.toLowerCase() === id.toLowerCase()
  );

  if (!channel) {
    return res.status(404).json({
      success: false,
      error: "Channel not found"
    });
  }

  startFFmpeg(channel);

  res.json({
    success: true,
    channel: channel.name
  });
}

app.get("/api/select/:id", selectChannelHandler);
app.post("/api/select/:id", selectChannelHandler);

// =====================================================
// API STOP
// =====================================================

function stopHandler(req, res) {
  stopFFmpeg();
  currentChannel = null;

  res.json({
    success: true,
    message: "Stopped"
  });
}

app.get("/api/stop", stopHandler);
app.post("/api/stop", stopHandler);

// =====================================================
// API RELOAD
// =====================================================

app.get("/api/reload", async (req, res) => {
  try {
    await loadChannels();

    res.json({
      success: true,
      count: channels.length
    });

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

    const url = new URL(
      "https://api.render.com/v1/metrics/bandwidth"
    );

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
      const labels = Array.isArray(series.labels)
        ? series.labels
        : [];

      const serviceLabel = labels.find(
        item => item.field === "service"
      );

      const serviceId = serviceLabel
        ? serviceLabel.value
        : "unknown";

      const unit = String(series.unit || "GB").toUpperCase();

      let serviceGB = 0;

      for (const point of (series.values || [])) {
        const value = Number(point.value);

        if (!Number.isFinite(value)) continue;

        if (unit === "GB") {
          serviceGB += value;
        } else if (unit === "MB") {
          serviceGB += value / 1024;
        } else if (["BYTE", "BYTES", "B"].includes(unit)) {
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

    const remainingGB = Math.max(
      0,
      BANDWIDTH_LIMIT_GB - usedGB
    );

    const resetAt = new Date(
      Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, 1)
    );

    const resetInSeconds = Math.max(
      0,
      Math.ceil((resetAt.getTime() - Date.now()) / 1000)
    );

    const usedPercent = Math.min(
      100,
      Number((usedGB / BANDWIDTH_LIMIT_GB * 100).toFixed(2))
    );

    const remainingPercent = Number(
      (100 - usedPercent).toFixed(2)
    );

    let status = "NORMAL";

    if (remainingGB <= 0) {
      status = "LIMIT_REACHED";
    } else if (remainingGB <= BANDWIDTH_LIMIT_GB * 0.1) {
      status = "WARNING";
    }

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

  res.json({
    status: "running",
    channelCount: channels.length,
    currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg,
    restarting,
    manuallyStopped,

    pipeline: "REALTIME_MJPEG_PCM_ADAPTIVE_BUFFER",

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,
    videoDroppedFrames,
    videoInvalidFrames,
    videoSentFrames,
    videoClients,
    videoPendingBytes: jpegPending.length,
    videoLatestFrameBytes: latestFrame ? latestFrame.length : 0,
    videoFrameSequence: frameSequence,
    videoFrameAge: lastVideoFrameTime
      ? Date.now() - lastVideoFrameTime
      : null,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFrameBytes: AUDIO_FRAME_BYTES,
    audioInterval: AUDIO_INTERVAL,
    audioBufferBytes: audioBuffer.length,
    audioBufferMax: AUDIO_BUFFER_MAX,
    audioStartBufferMs: AUDIO_START_BUFFER_MS,
    audioTargetBufferMs,
    audioPrimed,
    audioMaxObservedBytes,
    audioClientConnected: !!audioClient && !audioClient.destroyed,
    audioBlocked,
    audioUnderflows,
    audioOverflowBytes,
    audioSilenceBytes,
    audioFramesSent,

    memory: {
      rssMB: Number((memory.rss / 1048576).toFixed(2)),
      heapUsedMB: Number((memory.heapUsed / 1048576).toFixed(2)),
      externalMB: Number((memory.external / 1048576).toFixed(2)),
      arrayBuffersMB: Number((memory.arrayBuffers / 1048576).toFixed(2))
    },

    lastVideoFrameTime,
    generation
  });
});

// =====================================================
// ROOT / START
// =====================================================

app.get("/", (req, res) => {
  res.send("IPTV SERVER RUNNING - REALTIME MJPEG + PCM");
});

async function main() {
  try {
    await loadChannels();
  } catch (error) {
    console.log("[STARTUP] Playlist failed:", error.message);
  }

  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("CHANNELS:", channels.length);
    console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
    console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM`);
    console.log("AUDIO PREBUFFER:", `${AUDIO_START_BUFFER_MS}ms`);
    console.log("PIPELINE: REALTIME MJPEG + PCM ADAPTIVE BUFFER");
    console.log("BANDWIDTH API: /api/bandwidth");
    console.log("HEALTH API: /health");
    console.log("--------------------------------");
  });
}

main().catch(error => {
  console.error("[SERVER ERROR]", error);
  process.exit(1);
});
