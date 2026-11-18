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

const AUDIO_PREBUFFER_BYTES =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE * 0.3;

const AUDIO_PREBUFFER_MAX_BYTES =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE * 5;

// 🔥 WARMUP: 25-30s đầu chỉ phát hình. Audio vẫn được đọc từ pipe:3
// và drop để FFmpeg không bị block, nhưng KHÔNG ghi ra client.
// Sau warmup mới bắt đầu truyền audio.
const AUDIO_WARMUP_MS = Number(process.env.AUDIO_WARMUP_MS || 28000);

const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

const MAX_VIDEO_BUFFER = 512 * 1024;
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

let videoInvalidFrames = 0;
let videoSentFrames = 0;
let videoClients = 0;
const videoClientsMap = new Map();

// ===== AUDIO STATE =====
let audioClient = null;
let audioClientSlow = false;
let audioPrebuffer = [];
let audioPrebufferBytes = 0;
let audioStarted = false;

// Warmup
let streamStartedAt = 0;
let audioWarmupDone = false;
let audioWarmupDroppedBytes = 0;

// Diagnostics
let audioBytesReceived = 0;
let audioBytesSent = 0;
let audioBytesDropped = 0;
let audioFirstByteAt = 0;
let audioLastByteAt = 0;
let audioStarvingLogged = false;
let audioLastWarmupLogAt = 0;

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
// AUDIO — PASSTHROUGH + WARMUP
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

// 🔥 HÀM CỰC NHANH — không Buffer.concat, không alloc, không pause FFmpeg.
// Luôn consume chunk để pipe:3 không đầy → FFmpeg không block → video không lag.
function handleAudioChunk(chunk) {
  if (!chunk || !chunk.length) return;

  if (chunk.length & 1) chunk = chunk.subarray(0, chunk.length - 1);
  if (!chunk.length) return;

  const now = Date.now();
  if (!audioFirstByteAt) {
    audioFirstByteAt = now;
    console.log("[AUDIO] First byte from source arrived");
  }
  audioLastByteAt = now;
  audioBytesReceived += chunk.length;

  // ── WARMUP PHASE ──
  if (!audioWarmupDone) {
    const elapsed = streamStartedAt ? now - streamStartedAt : 0;

    if (elapsed < AUDIO_WARMUP_MS) {
      audioBytesDropped += chunk.length;
      audioWarmupDroppedBytes += chunk.length;

      // Log mỗi ~5s
      if (now - audioLastWarmupLogAt >= 5000) {
        audioLastWarmupLogAt = now;
        console.log(
          `[AUDIO] Warmup ${(elapsed / 1000).toFixed(1)}s / ` +
          `${(AUDIO_WARMUP_MS / 1000).toFixed(0)}s ` +
          `— dropped ${(audioWarmupDroppedBytes / 1024).toFixed(1)} KB`
        );
      }
      return;
    }

    audioWarmupDone = true;
    audioStarted = false;
    audioPrebuffer = [];
    audioPrebufferBytes = 0;
    audioLastWarmupLogAt = 0;
    console.log(
      `[AUDIO] ✅ Warmup complete after ${(elapsed / 1000).toFixed(1)}s ` +
      `(dropped ${(audioWarmupDroppedBytes / 1024).toFixed(1)} KB) ` +
      `— audio stream ENABLED from now`
    );
  }

  // Không có client → drop
  if (!audioClient || audioClient.destroyed || audioClient.writableEnded) {
    return;
  }

  // ── PREBUFFER PHASE ──
  if (!audioStarted) {
    audioPrebuffer.push(chunk);
    audioPrebufferBytes += chunk.length;

    if (audioPrebufferBytes >= AUDIO_PREBUFFER_MAX_BYTES) {
      console.log("[AUDIO] Prebuffer hit safety cap, flushing early");
      audioStarted = true;
    } else if (audioPrebufferBytes >= AUDIO_PREBUFFER_BYTES) {
      audioStarted = true;
      console.log("[AUDIO] Prebuffer ready:", audioPrebufferBytes, "bytes");
    } else {
      const elapsed = (now - audioFirstByteAt) / 1000;
      if (!audioStarvingLogged && elapsed > 5 && audioPrebufferBytes < 1000) {
        audioStarvingLogged = true;
        console.warn(
          `[AUDIO] ⚠ Only ${audioPrebufferBytes}B in ${elapsed.toFixed(1)}s — ` +
          `source may have slow/late audio`
        );
      }
      return;
    }

    for (const c of audioPrebuffer) {
      if (audioClientSlow) {
        audioBytesDropped += c.length;
        continue;
      }
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

  // ── LIVE PHASE ──
  if (audioClientSlow) {
    audioBytesDropped += chunk.length;
    return;
  }

  const ok = audioClient.write(chunk);
  if (ok) {
    audioBytesSent += chunk.length;
  } else {
    audioClientSlow = true;
    audioBytesDropped += chunk.length;
    audioClient.once("drain", () => { audioClientSlow = false; });
  }
}

// =====================================================
// VIDEO JPEG PARSER
// =====================================================

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
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
        console.log("[VIDEO] Slow client disconnected after",
          blockDuration, "ms (skipped:", state.skippedFrames, ")");
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
    broadcastFrame(latestFrame);
    jpegPending = jpegPending.subarray(frameLength);
  }
}

// =====================================================
// FFMPEG LIFECYCLE (SINGLE PROCESS)
// =====================================================

function clearWatchdog() {
  if (watchdogTimer) { clearInterval(watchdogTimer); watchdogTimer = null; }
}

function stopFFmpeg() {
  generation++;
  manuallyStopped = true;
  restarting = false;

  clearWatchdog();

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

  // Reset audio state (không đóng client)
  audioStarted = false;
  audioPrebuffer = [];
  audioPrebufferBytes = 0;
  audioBytesReceived = 0;
  audioBytesSent = 0;
  audioBytesDropped = 0;
  audioFirstByteAt = 0;
  audioLastByteAt = 0;
  audioStarvingLogged = false;
  audioLastWarmupLogAt = 0;

  // 🔥 Reset warmup — mỗi kênh mới đều warmup lại
  streamStartedAt = Date.now();
  audioWarmupDone = false;
  audioWarmupDroppedBytes = 0;

  videoInvalidFrames = 0;
  videoSentFrames = 0;

  const currentGeneration = generation;
  const qualityPreset = getCurrentQualityPreset();

  lastVideoFrameTime = Date.now();

  console.log("\n==================================");
  console.log("CHANNEL:", channel.name);
  console.log("GENERATION:", currentGeneration);
  console.log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}`);
  console.log("QUALITY:", qualityPreset.label);
  console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM (passthrough)`);
  console.log(
    `WARMUP: ${(AUDIO_WARMUP_MS / 1000).toFixed(0)}s — audio muted while FFmpeg stabilizes`
  );
  console.log("MODE: single FFmpeg — audio never pauses FFmpeg");
  console.log("==================================");
  console.log(
    `[AUDIO] Warmup started — audio muted for ${(AUDIO_WARMUP_MS / 1000).toFixed(0)}s`
  );

  const videoFilter = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  // SINGLE FFmpeg, hai output:
  //   pipe:1 → MJPEG video
  //   pipe:3 → PCM s16le audio
  // Không filter phức tạp, không first_pts=0, không async.
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
    "-re",
    "-i", channel.url,

    // OUTPUT 1: VIDEO
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

    // OUTPUT 2: AUDIO — passthrough PCM
    "-map", "0:a:0?",
    "-vn",
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
        handleAudioChunk(chunk);
      }
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
  console.log("[RESTART] Waiting:", RESTART_DELAY);

  disconnectAudioClient();
  clearVideoBuffer();
  clearWatchdog();

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

  console.log("[VIDEO] Client connected fps:", clientFps);

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

  // 🔥 KHÔNG reset streamStartedAt / audioWarmupDone / audioWarmupDroppedBytes
  // để warmup tính từ lúc startFFmpeg, không phải từ lúc client kết nối.

  audioBytesReceived = 0;
  audioBytesSent = 0;
  audioBytesDropped = 0;
  audioStarvingLogged = false;

  res.statusCode = 200;
  res.setHeader("Content-Type", "application/octet-stream");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");

  const remaining = audioWarmupDone
    ? 0
    : Math.max(0, AUDIO_WARMUP_MS - (Date.now() - streamStartedAt));

  if (remaining > 0) {
    console.log(
      `[AUDIO] Client connected — warmup still has ` +
      `${(remaining / 1000).toFixed(1)}s remaining, audio will start after`
    );
  } else {
    console.log("[AUDIO] Client connected — warmup done, prebuffering 300ms");
  }

  res.on("close", () => {
    if (audioClient === res) {
      console.log("[AUDIO] Client disconnected");
      disconnectAudioClient();
    }
  });
  res.on("error", () => {
    if (audioClient === res) disconnectAudioClient();
  });
});

// =====================================================
// API CHANNELS / QUALITY
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
// RENDER BANDWIDTH
// =====================================================

app.get("/api/bandwidth", async (req, res) => {
  try {
    if (!RENDER_API_KEY) {
      return res.status(500).json({ success: false, error: "Missing RENDER_API_KEY" });
    }
    if (!RENDER_SERVICE_IDS.length) {
      return res.status(500).json({ success: false, error: "Missing RENDER_SERVICE_IDS" });
    }
    if (!Number.isFinite(BANDWIDTH_LIMIT_GB) || BANDWIDTH_LIMIT_GB <= 0) {
      return res.status(500).json({ success: false, error: "Invalid BANDWIDTH_LIMIT_GB" });
    }

    const now = new Date();
    const start = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), 1));
    const url = new URL("https://api.render.com/v1/metrics/bandwidth");
    url.searchParams.set("startTime", start.toISOString());
    url.searchParams.set("endTime", now.toISOString());
    for (const id of RENDER_SERVICE_IDS) url.searchParams.append("resource", id);

    const response = await fetch(url, {
      headers: { Authorization: `Bearer ${RENDER_API_KEY}`, Accept: "application/json" },
      signal: AbortSignal.timeout(20000)
    });

    if (!response.ok) {
      const details = await response.text();
      return res.status(response.status).json({
        success: false, error: "Render API error",
        httpStatus: response.status, details
      });
    }

    const data = await response.json();
    if (!Array.isArray(data)) throw new Error("Invalid Render bandwidth response");

    let usedGB = 0;
    let totalPoints = 0;
    const services = [];

    for (const series of data) {
      const labels = Array.isArray(series.labels) ? series.labels : [];
      const serviceLabel = labels.find(i => i.field === "service");
      const serviceId = serviceLabel ? serviceLabel.value : "unknown";
      const unit = String(series.unit || "GB").toUpperCase();
      let serviceGB = 0;
      for (const point of (series.values || [])) {
        const value = Number(point.value);
        if (!Number.isFinite(value)) continue;
        if (unit === "GB") serviceGB += value;
        else if (unit === "MB") serviceGB += value / 1024;
        else if (["BYTE", "BYTES", "B"].includes(unit)) serviceGB += value / (1024 ** 3);
        else throw new Error("Unsupported bandwidth unit: " + unit);
        totalPoints++;
      }
      usedGB += serviceGB;
      services.push({
        serviceId, usedGB: Number(serviceGB.toFixed(4)), unit,
        dataPoints: (series.values || []).length
      });
    }

    usedGB = Number(usedGB.toFixed(4));
    const remainingGB = Math.max(0, BANDWIDTH_LIMIT_GB - usedGB);
    const resetAt = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, 1));
    const resetInSeconds = Math.max(0, Math.ceil((resetAt.getTime() - Date.now()) / 1000));
    const usedPercent = Math.min(100, Number((usedGB / BANDWIDTH_LIMIT_GB * 100).toFixed(2)));
    const remainingPercent = Number((100 - usedPercent).toFixed(2));

    let status = "NORMAL";
    if (remainingGB <= 0) status = "LIMIT_REACHED";
    else if (remainingGB <= BANDWIDTH_LIMIT_GB * 0.1) status = "WARNING";

    res.json({
      success: true, provider: "Render Official API",
      period: { start: start.toISOString(), end: now.toISOString(), timezone: "UTC" },
      bandwidth: { limitGB: BANDWIDTH_LIMIT_GB, usedGB, remainingGB, usedPercent, remainingPercent },
      resetInSeconds, resetAt: resetAt.toISOString(),
      status, services, serviceCount: RENDER_SERVICE_IDS.length,
      returnedSeries: data.length, totalDataPoints: totalPoints,
      updatedAt: new Date().toISOString(),
      note: "Metrics are delayed and may not equal exact real-time billing balance."
    });
  } catch (error) {
    console.error("[BANDWIDTH ERROR]", error.message);
    res.status(500).json({ success: false, error: error.message });
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
      skipped: state.skippedFrames,
      blockCount: state.blockCount,
      blocked: state.blocked,
      blockDurationMs: state.blocked ? now - state.blockedSince : 0,
      lastSentAgoMs: state.lastSentTime ? now - state.lastSentTime : null
    });
  }

  const warmupElapsed = streamStartedAt ? now - streamStartedAt : 0;
  const warmupRemaining = audioWarmupDone
    ? 0
    : Math.max(0, AUDIO_WARMUP_MS - warmupElapsed);

  res.json({
    status: "running",
    channelCount: channels.length,
    currentChannel: currentChannel ? currentChannel.name : null,
    ffmpegRunning: !!ffmpeg,
    restarting,
    manuallyStopped,
    pipeline: "SINGLE_FFMPEG_WITH_AUDIO_WARMUP",

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,
    videoInvalidFrames,
    videoSentFrames,
    videoClients,
    videoPendingBytes: jpegPending.length,
    videoLatestFrameBytes: latestFrame ? latestFrame.length : 0,
    videoFrameAge: lastVideoFrameTime ? now - lastVideoFrameTime : null,
    clientDetails,

    audio: {
      clientConnected: !!audioClient && !audioClient.destroyed,
      clientSlow: audioClientSlow,
      started: audioStarted,
      sampleRate: AUDIO_SAMPLE_RATE,
      channels: AUDIO_CHANNELS,
      prebufferBytes: audioPrebufferBytes,
      prebufferTargetBytes: AUDIO_PREBUFFER_BYTES,
      bytesReceived: audioBytesReceived,
      bytesSent: audioBytesSent,
      bytesDropped: audioBytesDropped,
      dropPercent: audioBytesReceived > 0
        ? Number((audioBytesDropped / audioBytesReceived * 100).toFixed(2))
        : 0,

      // 🔥 WARMUP
      warmupMs: AUDIO_WARMUP_MS,
      warmupDone: audioWarmupDone,
      warmupElapsedMs: warmupElapsed,
      warmupRemainingMs: warmupRemaining,
      warmupDroppedKB: Number((audioWarmupDroppedBytes / 1024).toFixed(1)),

      firstByteAgoSeconds: audioFirstByteAt
        ? Number(((now - audioFirstByteAt) / 1000).toFixed(1))
        : null,
      lastByteAgoSeconds: audioLastByteAt
        ? Number(((now - audioLastByteAt) / 1000).toFixed(1))
        : null,
      starving: audioStarvingLogged,

      note: !audioWarmupDone && warmupRemaining > 0
        ? `Đang warmup — còn ${(warmupRemaining / 1000).toFixed(1)}s nữa mới phát audio`
        : (!audioFirstByteAt && ffmpeg
          ? "Chưa nhận được byte audio nào — nguồn có thể chưa phát audio track"
          : null)
    },

    memory: {
      rssMB: Number((memory.rss / 1048576).toFixed(2)),
      heapUsedMB: Number((memory.heapUsed / 1048576).toFixed(2)),
      externalMB: Number((memory.external / 1048576).toFixed(2))
    },

    lastVideoFrameTime,
    generation
  });
});

// =====================================================
// ROOT / START
// =====================================================

app.get("/", (req, res) => {
  res.send(
    "IPTV SERVER - SINGLE FFmpeg + AUDIO WARMUP\n" +
    "  /stream              → default " + DEFAULT_CLIENT_FPS + " fps\n" +
    "  /stream?fps=12       → 12 fps\n" +
    "  /audio               → PCM " + AUDIO_SAMPLE_RATE + "Hz mono s16le\n" +
    "  /health              → diagnostics\n" +
    "\nAudio warmup: " + (AUDIO_WARMUP_MS / 1000).toFixed(0) + "s " +
    "(chỉ phát hình, audio chạy nền để FFmpeg ổn định)\n" +
    "Override: AUDIO_WARMUP_MS=25000 node server.js\n"
  );
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
    console.log("PIPELINE: SINGLE FFmpeg (video pipe:1 + audio pipe:3)");
    console.log("AUDIO:", `${AUDIO_SAMPLE_RATE}Hz mono PCM passthrough`);
    console.log(
      "AUDIO WARMUP:", (AUDIO_WARMUP_MS / 1000).toFixed(0) + "s",
      "(audio muted while FFmpeg stabilizes)"
    );
    console.log("--------------------------------");
  });
}

main().catch(error => {
  console.error("[SERVER ERROR]", error);
  process.exit(1);
});
