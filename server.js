
const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = process.env.PORT || 10000;

app.use(express.json());

// =====================================================
// CONFIG
// =====================================================

const M3U_URLS = [
  "https://raw.githubusercontent.com/anhkhanhdeptrai/Tv/main/Vn.m3u",
  "https://iptv-org.github.io/iptv/countries/vn.m3u"
];

// VIDEO
const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 180;
const VIDEO_FPS = 12;
const JPEG_QUALITY = 8;
const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

// AUDIO
const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;

const AUDIO_FRAME_MS = 250;
const AUDIO_INTERVAL = AUDIO_FRAME_MS;

const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_FRAME_MS / 1000;

// Giảm buffer để tránh phát audio quá xa hình
const AUDIO_BUFFER_MS = 500;

const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_BUFFER_MS / 1000;

// DECODER / ENCODER
const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;

const INPUT_READRATE = "1";

// LOW LATENCY
const LOW_LATENCY = true;
const PROBE_SIZE = "2M";
const ANALYZE_DURATION = "1000000";

// WATCHDOG
const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

// MEMORY
const MAX_VIDEO_BUFFER = 2 * 1024 * 1024;
const MAX_AUDIO_BUFFER = AUDIO_BUFFER_MAX;

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

let audioNextTick = 0;
let audioBytesSent = 0;
let audioUnderruns = 0;
let audioTrimmedBytes = 0;

let watchdogTimer = null;
let restartTimer = null;

let lastVideoFrameTime = 0;
let lastAudioDataTime = 0;

let restarting = false;
let manuallyStopped = true;

// =====================================================
// M3U PARSER
// =====================================================

function parseResolutionFromName(name) {
  const match = name.match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);

  if (!match) return 0;

  const value = Number(match[1] || match[2]);

  return Number.isFinite(value) ? value : 0;
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

    const url = line;

    if (!/^(https?|rtsp|rtmp|udp):\/\//i.test(url)) {
      currentInfo = null;
      continue;
    }

    let name = currentInfo.split(",").pop().trim();

    if (!name) name = "Unknown channel";

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
      url
    });

    currentInfo = null;
  }

  return result;
}

function filterChannelsByResolution(list, maxResolution = 720) {
  if (!Array.isArray(list)) return [];

  const allowed = Number.isFinite(Number(maxResolution))
    ? Number(maxResolution)
    : 720;

  const filtered = list.filter(channel => {
    if (!channel || !channel.resolution) return true;
    return channel.resolution <= allowed;
  });

  return filtered.length ? filtered : list;
}

// =====================================================
// LOAD CHANNELS
// =====================================================

async function loadChannels() {
  console.log("[M3U] Loading playlist...");

  let lastError = null;
  let content = "";
  let chosenUrl = "";

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

      content = await response.text();
      chosenUrl = url;
      break;

    } catch (error) {
      lastError = error;
      console.warn("[M3U] Failed:", url, error.message);
    }
  }

  if (!content) {
    throw lastError || new Error("No playlist available");
  }

  channels = parseM3U(content);

  console.log("[M3U] Loaded:", channels.length);
  console.log("[M3U] Source:", chosenUrl);

  return channels;
}

// =====================================================
// RESET
// =====================================================

function clearAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
}

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);
  latestFrame = null;
  frameSequence = 0;
}

function resetMedia() {
  clearAudioBuffer();
  clearVideoBuffer();

  audioBytesSent = 0;
  audioUnderruns = 0;
  audioTrimmedBytes = 0;

  lastAudioDataTime = 0;
}

// =====================================================
// AUDIO CLIENT
// =====================================================

function disconnectAudioClient() {
  if (audioTimer) {
    clearTimeout(audioTimer);
    audioTimer = null;
  }

  const old = audioClient;

  audioClient = null;

  audioBlocked = false;
  audioBlockedSince = 0;
  audioNextTick = 0;

  clearAudioBuffer();

  if (old) {
    try {
      old.destroy();
    } catch (_) {}
  }
}

// =====================================================
// AUDIO INPUT BUFFER
// =====================================================

function pushAudioBuffer(chunk) {
  if (!chunk || !chunk.length) return;

  if (chunk.length % 2 !== 0) {
    chunk = chunk.subarray(0, chunk.length - 1);
  }

  if (!chunk.length) return;

  audioBuffer = Buffer.concat([
    audioBuffer,
    chunk
  ]);

  lastAudioDataTime = Date.now();

  if (audioBuffer.length > MAX_AUDIO_BUFFER) {
    let excess = audioBuffer.length - MAX_AUDIO_BUFFER;

    if (excess % 2 !== 0) excess++;

    excess = Math.min(excess, audioBuffer.length);

    audioBuffer = audioBuffer.subarray(excess);

    audioTrimmedBytes += excess;
  }
}

// =====================================================
// GET AUDIO FRAME
// =====================================================

function getAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);

  const available = Math.min(
    audioBuffer.length,
    AUDIO_FRAME_BYTES
  );

  if (available > 0) {
    audioBuffer.copy(frame, 0, 0, available);

    audioBuffer = audioBuffer.subarray(available);
  }

  if (available < AUDIO_FRAME_BYTES) {
    audioUnderruns++;
  }

  // Phần thiếu được điền bằng silence
  return frame;
}

// =====================================================
// AUDIO CLOCK
// =====================================================

function scheduleAudioTick() {
  if (!audioClient || audioClient.destroyed) {
    disconnectAudioClient();
    return;
  }

  const delay = Math.max(
    0,
    audioNextTick - performanceNow()
  );

  audioTimer = setTimeout(() => {
    audioTimer = null;
    audioTick();
  }, delay);
}

function performanceNow() {
  return Number(process.hrtime.bigint()) / 1000000;
}

function audioTick() {
  if (!audioClient || audioClient.destroyed) {
    disconnectAudioClient();
    return;
  }

  if (audioBlocked) {
    if (Date.now() - audioBlockedSince > 1500) {
      console.log("[AUDIO] Slow client disconnected");
      disconnectAudioClient();
      return;
    }

    audioTimer = setTimeout(audioTick, 20);
    return;
  }

  const frame = getAudioFrame();

  try {
    const client = audioClient;
    const ok = client.write(frame);

    audioBytesSent += frame.length;

    if (!ok) {
      audioBlocked = true;
      audioBlockedSince = Date.now();

      client.once("drain", () => {
        if (audioClient !== client) return;

        audioBlocked = false;
        audioBlockedSince = 0;

        scheduleAudioTick();
      });

      return;
    }

  } catch (error) {
    console.error("[AUDIO WRITE]", error.message);
    disconnectAudioClient();
    return;
  }

  audioNextTick += AUDIO_INTERVAL;

  const now = performanceNow();

  // Không phát bù nhiều gói sau khi bị nghẽn
  if (now - audioNextTick > AUDIO_INTERVAL) {
    audioNextTick = now + AUDIO_INTERVAL;
  }

  scheduleAudioTick();
}

function startAudioTimer() {
  if (audioTimer) {
    clearTimeout(audioTimer);
    audioTimer = null;
  }

  audioNextTick = performanceNow();

  scheduleAudioTick();
}

// =====================================================
// VIDEO JPEG PARSER
// =====================================================

function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation) return;

  jpegPending = Buffer.concat([
    jpegPending,
    chunk
  ]);

  if (jpegPending.length > MAX_VIDEO_BUFFER) {
    const start = jpegPending.lastIndexOf(
      Buffer.from([0xff, 0xd8])
    );

    if (start >= 0) {
      jpegPending = jpegPending.subarray(start);
    } else {
      jpegPending = Buffer.alloc(0);
    }
  }

  while (true) {
    const start = jpegPending.indexOf(
      Buffer.from([0xff, 0xd8])
    );

    if (start < 0) {
      jpegPending = Buffer.alloc(0);
      return;
    }

    const end = jpegPending.indexOf(
      Buffer.from([0xff, 0xd9]),
      start + 2
    );

    if (end < 0) {
      if (start > 0) {
        jpegPending = jpegPending.subarray(start);
      }

      return;
    }

    // Luôn ghi đè frame cũ bằng frame mới nhất
    latestFrame = Buffer.from(
      jpegPending.subarray(start, end + 2)
    );

    frameSequence++;
    lastVideoFrameTime = Date.now();

    jpegPending = jpegPending.subarray(end + 2);
  }
}

// =====================================================
// STOP FFMPEG
// =====================================================

function stopFFmpeg() {
  generation++;

  manuallyStopped = true;
  restarting = false;

  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }

  if (restartTimer) {
    clearTimeout(restartTimer);
    restartTimer = null;
  }

  disconnectAudioClient();
  resetMedia();

  if (ffmpeg) {
    const old = ffmpeg;
    ffmpeg = null;

    try {
      old.kill("SIGKILL");
    } catch (_) {}
  }
}

// =====================================================
// START FFMPEG
// =====================================================

function startFFmpeg(channel) {
  if (!channel || !channel.url) {
    console.log("[FFMPEG] Invalid channel");
    return;
  }

  stopFFmpeg();

  manuallyStopped = false;
  currentChannel = channel;

  resetMedia();

  const currentGeneration = generation;

  console.log("");
  console.log("======================================");
  console.log("START CHANNEL:", channel.name);
  console.log("GENERATION:", currentGeneration);
  console.log("LOW LATENCY:", LOW_LATENCY);
  console.log("READRATE:", INPUT_READRATE);
  console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
  console.log("FPS:", VIDEO_FPS);
  console.log("AUDIO:", AUDIO_SAMPLE_RATE, "Hz");
  console.log("AUDIO BUFFER:", AUDIO_BUFFER_MS, "ms");
  console.log("======================================");

  lastVideoFrameTime = Date.now();

  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    // Network timeout
    "-rw_timeout", "30000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "5",

    "-user_agent",
    "Mozilla/5.0",

    // Probe
    "-probesize", PROBE_SIZE,
    "-analyzeduration", ANALYZE_DURATION,

    // Input latency
    ...(LOW_LATENCY
      ? [
          "-fflags",
          "+discardcorrupt+nobuffer",
          "-flags",
          "low_delay",
          "-max_delay",
          "0"
        ]
      : [
          "-fflags",
          "+discardcorrupt"
        ]),

    // Input rate
    "-readrate",
    INPUT_READRATE,

    // Decoder
    "-threads",
    String(DECODER_THREADS),

    // Input
    "-i",
    channel.url,

    // ===============================================
    // VIDEO
    // ===============================================

    "-map", "0:v:0?",
    "-an",

    "-vf",
    [
      `fps=${VIDEO_FPS}:round=near`,
      `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
      `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
      "setsar=1"
    ].join(","),

    "-q:v",
    String(JPEG_QUALITY),

    "-threads",
    String(ENCODER_THREADS),

    "-flush_packets",
    "1",

    "-f",
    "image2pipe",

    "-vcodec",
    "mjpeg",

    "pipe:1",

    // ===============================================
    // AUDIO
    // ===============================================

    "-map", "0:a:0?",
    "-vn",

    "-af",
    `aresample=${AUDIO_SAMPLE_RATE}:async=1:first_pts=0`,

    "-ac",
    String(AUDIO_CHANNELS),

    "-ar",
    String(AUDIO_SAMPLE_RATE),

    "-c:a",
    "pcm_s16le",

    "-flush_packets",
    "1",

    "-f",
    "s16le",

    "pipe:3"
  ];

  ffmpeg = spawn("ffmpeg", args, {
    stdio: [
      "ignore",
      "pipe",
      "pipe",
      "pipe"
    ]
  });

  const processRef = ffmpeg;

  // VIDEO
  processRef.stdout.on("data", chunk => {
    processVideoData(
      chunk,
      currentGeneration
    );
  });

  // AUDIO
  if (processRef.stdio[3]) {
    processRef.stdio[3].on("data", chunk => {
      if (currentGeneration !== generation) return;

      pushAudioBuffer(chunk);
    });
  }

  // STDERR
  processRef.stderr.on("data", data => {
    const message = data.toString().trim();

    if (message) {
      console.log("[FFmpeg]", message);
    }
  });

  // ERROR
  processRef.on("error", error => {
    console.error("[FFMPEG ERROR]", error.message);
  });

  // CLOSE
  processRef.on("close", (code, signal) => {
    console.log(
      "[FFmpeg] Exited:",
      code,
      "signal:",
      signal
    );

    if (currentGeneration !== generation) return;

    ffmpeg = null;

    resetMedia();

    if (!manuallyStopped) {
      scheduleRestart();
    }
  });

  // WATCHDOG
  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation) return;
    if (!ffmpeg || restarting) return;

    const elapsed =
      Date.now() - lastVideoFrameTime;

    if (elapsed > VIDEO_TIMEOUT) {
      console.log(
        "[WATCHDOG] No video frame:",
        elapsed,
        "ms"
      );

      scheduleRestart();
    }
  }, WATCHDOG_INTERVAL);
}

// =====================================================
// RESTART
// =====================================================

function scheduleRestart() {
  if (restarting || manuallyStopped) return;

  restarting = true;

  console.log(
    "[RESTART] Restarting in",
    RESTART_DELAY,
    "ms"
  );

  disconnectAudioClient();
  resetMedia();

  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }

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
// VIDEO STREAM
// =====================================================

app.get("/stream", (req, res) => {
  res.writeHead(200, {
    "Content-Type":
      "multipart/x-mixed-replace; boundary=frame",

    "Cache-Control":
      "no-cache, no-store, must-revalidate",

    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  let lastSentSequence = -1;
  let blocked = false;
  let blockedSince = 0;

  const timer = setInterval(() => {
    if (res.destroyed || res.writableEnded) {
      clearInterval(timer);
      return;
    }

    if (blocked) {
      if (Date.now() - blockedSince > 1000) {
        clearInterval(timer);
        res.destroy();
      }

      return;
    }

    // Không có frame mới
    if (!latestFrame) return;

    // Không gửi lại frame cũ
    if (frameSequence === lastSentSequence) return;

    // Nếu response còn quá nhiều dữ liệu chờ,
    // ngắt client chậm thay vì tích lũy frame
    if (res.writableLength > 512 * 1024) {
      clearInterval(timer);
      res.destroy();
      return;
    }

    const frame = latestFrame;

    lastSentSequence = frameSequence;

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

      if (!ok) {
        blocked = true;
        blockedSince = Date.now();

        res.once("drain", () => {
          blocked = false;
          blockedSince = 0;
        });
      }

    } catch (error) {
      clearInterval(timer);
      res.destroy();
    }

  }, VIDEO_INTERVAL);

  res.on("close", () => {
    clearInterval(timer);
  });
});

// =====================================================
// AUDIO STREAM
// =====================================================

app.get("/audio", (req, res) => {
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
    filterChannelsByResolution(
      channels,
      maxResolution
    );

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
  const id = decodeURIComponent(req.params.id);

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
// HEALTH
// =====================================================

app.get("/health", (req, res) => {
  const bytesPerSecond =
    AUDIO_SAMPLE_RATE *
    AUDIO_CHANNELS *
    AUDIO_BYTES_PER_SAMPLE;

  res.json({
    status: "running",

    channelCount: channels.length,

    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning: !!ffmpeg,

    restarting,
    manuallyStopped,

    pipeline: "LOW_LATENCY_MJPEG_PCM",

    lowLatency: LOW_LATENCY,

    inputReadrate: INPUT_READRATE,

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    frameSequence,

    latestFrameBytes:
      latestFrame ? latestFrame.length : 0,

    videoFrameAge: lastVideoFrameTime
      ? Date.now() - lastVideoFrameTime
      : null,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,

    audioFrameMs: AUDIO_FRAME_MS,
    audioFrameBytes: AUDIO_FRAME_BYTES,

    audioBufferBytes: audioBuffer.length,

    audioBufferDurationMs:
      Math.round(
        audioBuffer.length /
        bytesPerSecond * 1000
      ),

    audioBufferMaxBytes: AUDIO_BUFFER_MAX,

    audioUnderruns,
    audioTrimmedBytes,

    audioClientConnected:
      !!audioClient && !audioClient.destroyed,

    audioBlocked,

    audioBytesSent,

    audioExpectedBytesPerSecond:
      bytesPerSecond,

    lastAudioDataAge: lastAudioDataTime
      ? Date.now() - lastAudioDataTime
      : null,

    generation
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.send(`
    <!DOCTYPE html>
    <html>
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width,initial-scale=1">
      <title>IPTV Streaming Server</title>
    </head>

    <body style="background:#111;color:#eee;font-family:Arial;padding:20px">

      <h2>IPTV Low Latency Server</h2>

      <p>Channels: ${channels.length}</p>
      <p>Pipeline: LOW LATENCY MJPEG + PCM</p>

      <p>Video: ${VIDEO_WIDTH}x${VIDEO_HEIGHT} @ ${VIDEO_FPS} FPS</p>
      <p>Audio: ${AUDIO_SAMPLE_RATE}Hz PCM</p>
      <p>Audio frame: ${AUDIO_FRAME_MS}ms</p>
      <p>Audio buffer: ${AUDIO_BUFFER_MS}ms</p>

      <p><a style="color:#8b7cff" href="/api/channels">Channels</a></p>
      <p><a style="color:#8b7cff" href="/health">Health</a></p>

    </body>
    </html>
  `);
});

// =====================================================
// START SERVER
// =====================================================

async function main() {
  try {
    await loadChannels();
  } catch (error) {
    console.log(
      "[STARTUP] Playlist load failed:",
      error.message
    );
  }

  app.listen(PORT, "0.0.0.0", () => {
    console.log("--------------------------------");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("CHANNELS:", channels.length);
    console.log("PIPELINE: LOW LATENCY");
    console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
    console.log("FPS:", VIDEO_FPS);
    console.log("AUDIO:", AUDIO_SAMPLE_RATE);
    console.log("AUDIO FRAME:", AUDIO_FRAME_MS);
    console.log("AUDIO BUFFER:", AUDIO_BUFFER_MS);
    console.log("--------------------------------");
  });
}

main();
