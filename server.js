
const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = process.env.PORT || 10000;

app.use(express.json({ limit: "32kb" }));

// =====================================================
// CONFIG
// =====================================================

const M3U_URLS = [
  "https://raw.githubusercontent.com/anhkhanhdeptrai/Tv/main/Vn.m3u",
  "https://iptv-org.github.io/iptv/countries/vn.m3u"
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 180;
const VIDEO_FPS = 8;
const JPEG_QUALITY = 9;

const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_FRAME_MS = 50;

const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  2 *
  AUDIO_FRAME_MS / 1000;

const AUDIO_INTERVAL = AUDIO_FRAME_MS;

// Giới hạn buffer audio 500ms
const AUDIO_BUFFER_MS = 1500;

const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * 2 *
  AUDIO_BUFFER_MS / 1000;

// Giới hạn xử lý
const DECODER_THREADS = 1;
const ENCODER_THREADS = 1;
const FILTER_THREADS = 1;

const SKIP_NON_REFERENCE = false;

// Không giới hạn readrate đối với live stream
const INPUT_READRATE = "DISABLED";

// Watchdog
const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 35000;
const RESTART_DELAY = 4000;

// Buffer video
const MAX_VIDEO_BUFFER = 2 * 1024 * 1024;

// Giới hạn client
const MAX_VIDEO_CLIENTS = 3;

// Thời gian chờ FFmpeg đóng
const PROCESS_KILL_TIMEOUT = 1500;

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

let audioBuffer = Buffer.alloc(0);
let audioClient = null;
let audioTimer = null;

let audioBlocked = false;
let audioBlockedSince = 0;

let watchdogTimer = null;
let restartTimer = null;

let lastVideoFrameTime = 0;

let restarting = false;
let manuallyStopped = true;

let videoClients = 0;

// Hàng đợi đóng process.
// Không cho phép FFmpeg mới chạy khi process cũ chưa đóng.
let processStopPromise = Promise.resolve();

// =====================================================
// HELPERS
// =====================================================

function clearWatchdog() {
  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }
}

function clearRestartTimer() {
  if (restartTimer) {
    clearTimeout(restartTimer);
    restartTimer = null;
  }
}

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
}

function clearAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
}

function getMemoryUsage() {
  const mem = process.memoryUsage();

  return {
    rssMB: Math.round(mem.rss / 1024 / 1024),
    heapUsedMB: Math.round(mem.heapUsed / 1024 / 1024),
    externalMB: Math.round(mem.external / 1024 / 1024),
    arrayBuffersMB: Math.round(mem.arrayBuffers / 1024 / 1024)
  };
}

// =====================================================
// M3U PARSER
// =====================================================

function parseResolutionFromName(name) {
  const match = name.match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);

  if (!match) return 0;

  return Number(match[1] || match[2]) || 0;
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

    if (line.startsWith("#")) continue;
    if (!currentInfo) continue;

    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(line)) {
      currentInfo = null;
      continue;
    }

    const name = currentInfo.split(",").pop().trim() ||
      "Unknown channel";

    const groupMatch =
      currentInfo.match(/group-title="([^"]*)"/i);

    const logoMatch =
      currentInfo.match(/tvg-logo="([^"]*)"/i);

    const idMatch =
      currentInfo.match(/tvg-id="([^"]*)"/i);

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

  const filtered = list.filter(channel => {
    if (!channel.resolution) return true;
    return channel.resolution <= maxResolution;
  });

  return filtered.length ? filtered : list;
}

// =====================================================
// LOAD CHANNELS
// =====================================================

async function loadChannels() {
  console.log("[M3U] Loading playlist...");

  let lastError = null;

  for (const url of M3U_URLS) {
    try {
      const response = await fetch(url, {
        headers: {
          "User-Agent": "Mozilla/5.0"
        },
        signal: AbortSignal.timeout(20000)
      });

      if (!response.ok) {
        throw new Error("HTTP " + response.status);
      }

      const content = await response.text();

      const parsed = parseM3U(content);

      if (!parsed.length) {
        throw new Error("Playlist is empty");
      }

      channels = parsed;

      console.log("--------------------------------");
      console.log("M3U URL:", url);
      console.log("TOTAL CHANNELS:", channels.length);
      console.log("--------------------------------");

      return channels;

    } catch (error) {
      lastError = error;
      console.warn("[M3U] Failed:", url, error.message);
    }
  }

  throw lastError || new Error("No playlist available");
}

// =====================================================
// AUDIO BUFFER
// =====================================================

function disconnectAudioClient() {
  if (audioTimer) {
    clearInterval(audioTimer);
    audioTimer = null;
  }

  const oldClient = audioClient;

  audioClient = null;

  audioBlocked = false;
  audioBlockedSince = 0;

  clearAudioBuffer();

  if (oldClient) {
    try {
      oldClient.destroy();
    } catch (_) {}
  }
}

function pushAudioBuffer(chunk) {
  if (!chunk || !chunk.length) return;

  // PCM 16-bit phải chẵn byte
  if (chunk.length % 2 !== 0) {
    chunk = chunk.subarray(0, chunk.length - 1);
  }

  if (!chunk.length) return;

  // Nếu chunk quá lớn, chỉ lấy phần cuối
  if (chunk.length >= AUDIO_BUFFER_MAX) {
    audioBuffer = Buffer.from(
      chunk.subarray(chunk.length - AUDIO_BUFFER_MAX)
    );
  } else {
    audioBuffer = Buffer.concat([
      audioBuffer,
      chunk
    ]);
  }

  // Luôn giới hạn buffer
  if (audioBuffer.length > AUDIO_BUFFER_MAX) {
    const excess = audioBuffer.length - AUDIO_BUFFER_MAX;

    const drop = excess + (excess % 2);

    audioBuffer = audioBuffer.subarray(drop);
  }
}

function getAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);

  if (audioBuffer.length === 0) {
    // Thiếu dữ liệu thì phát silence.
    // Không lặp lại mẫu âm thanh cuối.
    return frame;
  }

  const available = Math.min(
    audioBuffer.length,
    AUDIO_FRAME_BYTES
  );

  const usable = available - (available % 2);

  if (usable > 0) {
    audioBuffer.copy(frame, 0, 0, usable);

    audioBuffer = audioBuffer.subarray(usable);
  }

  return frame;
}

// =====================================================
// AUDIO REALTIME
// =====================================================

function startAudioTimer() {
  if (audioTimer) {
    clearInterval(audioTimer);
  }

  audioTimer = setInterval(() => {
    const client = audioClient;

    if (!client || client.destroyed || client.writableEnded) {
      disconnectAudioClient();
      return;
    }

    if (audioBlocked) {
      if (Date.now() - audioBlockedSince > 1500) {
        console.log("[AUDIO] Slow client disconnected");
        disconnectAudioClient();
      }

      return;
    }

    const frame = getAudioFrame();

    try {
      const ok = client.write(frame);

      if (!ok) {
        audioBlocked = true;
        audioBlockedSince = Date.now();

        client.once("drain", () => {
          if (audioClient !== client) return;

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

const JPEG_START = Buffer.from([0xff, 0xd8]);
const JPEG_END = Buffer.from([0xff, 0xd9]);

function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation) return;

  if (!chunk || !chunk.length) return;

  if (jpegPending.length + chunk.length > MAX_VIDEO_BUFFER) {
    const combined = Buffer.concat([
      jpegPending,
      chunk
    ]);

    const lastStart = combined.lastIndexOf(JPEG_START);

    if (lastStart >= 0) {
      jpegPending = Buffer.from(
        combined.subarray(lastStart)
      );
    } else {
      jpegPending = Buffer.alloc(0);
    }

    if (jpegPending.length > MAX_VIDEO_BUFFER) {
      jpegPending = Buffer.alloc(0);
    }

  } else {
    jpegPending = Buffer.concat([
      jpegPending,
      chunk
    ]);
  }

  while (true) {
    const start = jpegPending.indexOf(JPEG_START);

    if (start < 0) {
      jpegPending = Buffer.alloc(0);
      return;
    }

    const end = jpegPending.indexOf(
      JPEG_END,
      start + 2
    );

    if (end < 0) {
      if (start > 0) {
        jpegPending = jpegPending.subarray(start);
      }

      return;
    }

    const jpeg = jpegPending.subarray(
      start,
      end + 2
    );

    latestFrame = Buffer.from(jpeg);

    frameSequence++;

    lastVideoFrameTime = Date.now();

    jpegPending = jpegPending.subarray(end + 2);
  }
}

// =====================================================
// PROCESS STOP
// =====================================================

function terminateChild(child) {
  if (!child) return Promise.resolve();

  if (child.exitCode !== null || child.signalCode !== null) {
    return Promise.resolve();
  }

  return new Promise(resolve => {
    let finished = false;

    let killTimer = null;

    function finish() {
      if (finished) return;

      finished = true;

      if (killTimer) {
        clearTimeout(killTimer);
      }

      resolve();
    }

    child.once("close", finish);

    try {
      child.kill("SIGTERM");
    } catch (_) {
      finish();
      return;
    }

    killTimer = setTimeout(() => {
      if (finished) return;

      console.log("[FFMPEG] SIGTERM timeout, sending SIGKILL");

      try {
        child.kill("SIGKILL");
      } catch (_) {}

    }, PROCESS_KILL_TIMEOUT);

    if (killTimer.unref) killTimer.unref();
  });
}

function queueStop(child) {
  if (!child) return processStopPromise;

  processStopPromise = processStopPromise
    .then(() => terminateChild(child))
    .catch(error => {
      console.error("[PROCESS STOP]", error.message);
    });

  return processStopPromise;
}

// =====================================================
// STOP SERVER STREAM
// =====================================================

function stopFFmpeg() {
  generation++;

  manuallyStopped = true;
  restarting = false;

  clearWatchdog();
  clearRestartTimer();

  disconnectAudioClient();

  clearVideoBuffer();

  const old = ffmpeg;

  ffmpeg = null;

  return queueStop(old);
}

// =====================================================
// FFMPEG ARGUMENTS
// =====================================================

function buildFFmpegArgs(channel) {
  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    // ===============================================
    // NETWORK
    // ===============================================

    "-rw_timeout", "15000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_at_eof", "1",
    "-reconnect_on_network_error", "1",
    "-reconnect_on_http_error", "4xx,5xx",
    "-reconnect_delay_max", "5",

    "-user_agent", "Mozilla/5.0",

    // ===============================================
    // INPUT BUFFER / H264 ERROR TOLERANCE
    // ===============================================

    "-fflags", "+discardcorrupt+genpts",

    "-err_detect", "ignore_err",

    "-probesize", "5000000",
    "-analyzeduration", "5000000",

    // ===============================================
    // DECODER THREADS
    // ===============================================

    "-threads", String(DECODER_THREADS),

    "-filter_threads", String(FILTER_THREADS),

    "-filter_complex_threads", String(FILTER_THREADS),

    ...(SKIP_NON_REFERENCE
      ? ["-skip_frame", "noref"]
      : []),

    // ===============================================
    // INPUT
    // ===============================================

    "-i", channel.url,

    // ===============================================
    // VIDEO OUTPUT
    // ===============================================

    "-map", "0:v:0?",
    "-an",

    "-vf",
    [
      `fps=${VIDEO_FPS}`,
      `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
      `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
      "setsar=1",
      "format=yuvj420p"
    ].join(","),

    "-q:v", String(JPEG_QUALITY),

    "-threads:v", String(ENCODER_THREADS),

    "-flush_packets", "1",

    "-f", "image2pipe",
    "-vcodec", "mjpeg",

    "pipe:1",

    // ===============================================
    // AUDIO OUTPUT
    // ===============================================

    "-map", "0:a:0?",
    "-vn",

    "-af",
    `aresample=${AUDIO_SAMPLE_RATE}:async=100:first_pts=0`,

    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_SAMPLE_RATE),

    "-c:a", "pcm_s16le",

    "-flush_packets", "1",

    "-f", "s16le",

    "pipe:3"
  ];

  return args;
}

// =====================================================
// START FFMPEG
// =====================================================

async function startFFmpeg(channel) {
  if (!channel || !channel.url) {
    console.log("[FFMPEG] Invalid channel");
    return;
  }

  // Tạo generation mới ngay lập tức.
  const currentGeneration = ++generation;

  manuallyStopped = false;
  restarting = false;

  clearWatchdog();
  clearRestartTimer();

  disconnectAudioClient();

  clearVideoBuffer();
  clearAudioBuffer();

  currentChannel = channel;

  // Gỡ process cũ khỏi trạng thái hiện tại.
  const old = ffmpeg;
  ffmpeg = null;

  // Chờ process cũ thực sự đóng.
  await queueStop(old);

  // Nếu có yêu cầu chuyển kênh mới hơn thì bỏ lần khởi động cũ.
  if (currentGeneration !== generation || manuallyStopped) {
    return;
  }

  console.log("");
  console.log("======================================");
  console.log("START CHANNEL:", channel.name);
  console.log("URL:", channel.url);
  console.log("GENERATION:", currentGeneration);
  console.log("DECODER THREADS:", DECODER_THREADS);
  console.log("ENCODER THREADS:", ENCODER_THREADS);
  console.log("FILTER THREADS:", FILTER_THREADS);
  console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
  console.log("FPS:", VIDEO_FPS);
  console.log("AUDIO:", AUDIO_SAMPLE_RATE);
  console.log("======================================");

  lastVideoFrameTime = Date.now();

  const args = buildFFmpegArgs(channel);

  let processRef;

  try {
    processRef = spawn("ffmpeg", args, {
      stdio: [
        "ignore",
        "pipe",
        "pipe",
        "pipe"
      ]
    });

  } catch (error) {
    console.error("[FFMPEG SPAWN]", error.message);
    scheduleRestart();
    return;
  }

  ffmpeg = processRef;

  // ===============================================
  // VIDEO
  // ===============================================

  processRef.stdout.on("data", chunk => {
    processVideoData(chunk, currentGeneration);
  });

  processRef.stdout.on("error", error => {
    console.error("[VIDEO PIPE]", error.message);
  });

  // ===============================================
  // AUDIO
  // ===============================================

  const audioPipe = processRef.stdio[3];

  if (audioPipe) {
    audioPipe.on("data", chunk => {
      if (currentGeneration !== generation) return;

      pushAudioBuffer(chunk);
    });

    audioPipe.on("error", error => {
      console.error("[AUDIO PIPE]", error.message);
    });
  }

  // ===============================================
  // STDERR
  // ===============================================

  processRef.stderr.on("data", data => {
    const message = data.toString().trim();

    if (!message) return;

    console.log("[FFmpeg]", message);
  });

  // ===============================================
  // ERROR
  // ===============================================

  processRef.on("error", error => {
    console.error("[FFMPEG ERROR]", error.message);

    if (currentGeneration === generation) {
      scheduleRestart();
    }
  });

  // ===============================================
  // CLOSE
  // ===============================================

  processRef.on("close", (code, signal) => {
    console.log(
      "[FFmpeg] Exited:",
      code,
      "signal:",
      signal
    );

    if (currentGeneration !== generation) return;

    if (ffmpeg === processRef) {
      ffmpeg = null;
    }

    clearAudioBuffer();
    clearVideoBuffer();

    clearWatchdog();

    if (!manuallyStopped && !restarting) {
      scheduleRestart();
    }
  });

  // ===============================================
  // WATCHDOG
  // ===============================================

  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation) return;

    if (ffmpeg !== processRef || restarting) return;

    const elapsed = Date.now() - lastVideoFrameTime;

    if (elapsed > VIDEO_TIMEOUT) {
      console.log(
        "[WATCHDOG] Video timeout:",
        elapsed,
        "ms"
      );

      scheduleRestart();
    }

  }, WATCHDOG_INTERVAL);

  console.log("[FFMPEG] PID:", processRef.pid);
}

// =====================================================
// RESTART
// =====================================================

function scheduleRestart() {
  if (restarting || manuallyStopped) return;

  if (!currentChannel) return;

  restarting = true;

  console.log(
    "[RESTART] Waiting",
    RESTART_DELAY,
    "ms"
  );

  clearWatchdog();
  clearRestartTimer();

  disconnectAudioClient();

  clearVideoBuffer();
  clearAudioBuffer();

  const old = ffmpeg;
  ffmpeg = null;

  // Invalidate old data immediately.
  generation++;

  const restartGeneration = generation;

  queueStop(old).then(() => {
    if (restartGeneration !== generation) return;
    if (manuallyStopped) return;

    restartTimer = setTimeout(() => {
      restartTimer = null;

      if (restartGeneration !== generation) return;
      if (manuallyStopped) return;

      const channel = currentChannel;

      if (channel) {
        startFFmpeg(channel);
      }

    }, RESTART_DELAY);
  });
}

// =====================================================
// VIDEO STREAM - MJPEG
// =====================================================

app.get("/stream", (req, res) => {
  if (videoClients >= MAX_VIDEO_CLIENTS) {
    return res.status(503).send("Too many video clients");
  }

  videoClients++;

  res.writeHead(200, {
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

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
    if (res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    if (blocked) {
      if (Date.now() - blockedSince > 1500) {
        cleanup();
        res.destroy();
      }

      return;
    }

    if (!latestFrame) return;

    if (frameSequence === lastSentSequence) return;

    const frame = latestFrame;

    const sequence = frameSequence;

    const header = Buffer.from(
      "--frame\r\n" +
      "Content-Type: image/jpeg\r\n" +
      "Content-Length: " + frame.length +
      "\r\n\r\n"
    );

    const packet = Buffer.concat([
      header,
      frame,
      Buffer.from("\r\n")
    ]);

    try {
      const ok = res.write(packet);

      lastSentSequence = sequence;

      if (!ok) {
        blocked = true;
        blockedSince = Date.now();

        res.once("drain", () => {
          if (closed) return;

          blocked = false;
          blockedSince = 0;
        });
      }

    } catch (_) {
      cleanup();
      res.destroy();
    }

  }, VIDEO_INTERVAL);

  res.on("close", cleanup);
  res.on("error", cleanup);
});

// =====================================================
// AUDIO STREAM
// =====================================================

app.get("/audio", (req, res) => {
  // Chỉ hỗ trợ một audio client
  disconnectAudioClient();

  clearAudioBuffer();

  audioClient = res;

  res.statusCode = 200;

  res.setHeader(
    "Content-Type",
    "application/octet-stream"
  );

  res.setHeader(
    "Cache-Control",
    "no-cache, no-store, must-revalidate"
  );

  res.setHeader("Pragma", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("Content-Encoding", "identity");

  console.log("[AUDIO] Client connected");

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

  const filteredChannels =
    filterChannelsByResolution(channels, maxResolution);

  res.json({
    success: true,
    quality:
      maxResolution === Number.MAX_SAFE_INTEGER
        ? "all"
        : String(maxResolution),
    channels: filteredChannels
  });
});

// =====================================================
// API SELECT
// =====================================================

function selectChannelHandler(req, res) {
  const id = String(req.params.id);

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

  startFFmpeg(channel).catch(error => {
    console.error("[SELECT ERROR]", error.message);
  });

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

async function stopHandler(req, res) {
  await stopFFmpeg();

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
// HEALTH
// =====================================================

app.get("/health", (req, res) => {
  const memory = getMemoryUsage();

  res.json({
    status: "running",

    channelCount: channels.length,

    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning: !!ffmpeg,

    ffmpegPid: ffmpeg ? ffmpeg.pid : null,

    restarting,
    manuallyStopped,

    pipeline: "REALTIME_HLS_MJPEG",

    inputReadrate: INPUT_READRATE,

    decoderThreads: DECODER_THREADS,
    encoderThreads: ENCODER_THREADS,
    filterThreads: FILTER_THREADS,

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    jpegQuality: JPEG_QUALITY,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,

    audioFrameBytes: AUDIO_FRAME_BYTES,
    audioInterval: AUDIO_INTERVAL,

    audioBufferBytes: audioBuffer.length,
    audioBufferMax: AUDIO_BUFFER_MAX,

    audioClientConnected:
      !!audioClient && !audioClient.destroyed,

    videoClients,

    lastVideoFrameTime,

    videoFrameAge: lastVideoFrameTime
      ? Date.now() - lastVideoFrameTime
      : null,

    memory,

    generation
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.json({
    name: "IPTV REALTIME SERVER",
    status: "running",
    video: "/stream",
    audio: "/audio",
    channels: "/api/channels",
    health: "/health"
  });
});

// =====================================================
// START SERVER
// =====================================================

async function main() {
  try {
    await loadChannels();

  } catch (error) {
    console.error(
      "[STARTUP] Playlist load failed:",
      error.message
    );
  }

  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("CHANNELS:", channels.length);
    console.log("PIPELINE: REALTIME HLS MJPEG");
    console.log("DECODER THREADS:", DECODER_THREADS);
    console.log("ENCODER THREADS:", ENCODER_THREADS);
    console.log("FILTER THREADS:", FILTER_THREADS);
    console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
    console.log("FPS:", VIDEO_FPS);
    console.log("AUDIO:", AUDIO_SAMPLE_RATE);
    console.log("READRATE: DISABLED");
    console.log("--------------------------------");
  });
}

main();
