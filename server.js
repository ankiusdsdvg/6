

const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = process.env.PORT || 10000;

app.use(express.json());

// =====================================================
// CONFIG
// =====================================================

const M3U_URLS = [
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u",
  "https://iptv-org.github.io/iptv/countries/vn.m3u"
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 180;
const VIDEO_FPS = 10;
const JPEG_QUALITY = 8;

const VIDEO_INTERVAL = 1000 / VIDEO_FPS;

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;

const AUDIO_FRAME_MS = 180;
const AUDIO_INTERVAL = AUDIO_FRAME_MS;

const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_FRAME_MS / 1000;

const AUDIO_BUFFER_MS = 2900;

const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_BUFFER_MS / 1000;

const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;

const SKIP_NON_REFERENCE = false;
const INPUT_READRATE = "1";

const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

// VIDEO BUFFER
const MAX_VIDEO_BUFFER = 2 * 1024 * 1024;
const MAX_JPEG_FRAME_BYTES = 512 * 1024;

const JPEG_SOI = Buffer.from([0xff, 0xd8]);
const JPEG_EOI = Buffer.from([0xff, 0xd9]);

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

let audioBuffer = Buffer.alloc(0);
let lastAudioSample = Buffer.from([0, 0]);
let audioClient = null;
let audioTimer = null;

let audioBlocked = false;
let audioBlockedSince = 0;

let watchdogTimer = null;
let restartTimer = null;

let lastVideoFrameTime = 0;

let restarting = false;
let manuallyStopped = true;

// =====================================================
// M3U PARSER
// =====================================================

function parseResolutionFromName(name) {
  const match = name.match(/\((\d{3,4})p\)|\b(\d{3,4})p\b/i);

  if (!match) return 0;

  const value = Number(match[1] || match[2]);

  if (!Number.isFinite(value)) return 0;

  return value;
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

    const isStreamUrl =
      /^(https?|rtsp|rtmp|udp):\/\//i.test(url);

    if (!isStreamUrl) {
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

    const resolution = parseResolutionFromName(name);

    result.push({
      id: String(result.length),
      name,
      group: groupMatch ? groupMatch[1] : "",
      logo: logoMatch ? logoMatch[1] : "",
      tvgId: idMatch ? idMatch[1] : "",
      resolution,
      url
    });

    currentInfo = null;
  }

  return result;
}

function filterChannelsByResolution(list, maxResolution = Number.MAX_SAFE_INTEGER) {
  if (!Array.isArray(list)) return [];

  void maxResolution;

  return list;
}

// =====================================================
// LOAD CHANNELS
// =====================================================

async function loadChannels() {
  try {
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

        console.warn(
          "[M3U] Try failed:",
          url,
          error.message
        );
      }
    }

    if (!content) {
      throw lastError || new Error("No playlist available");
    }

    channels = parseM3U(content);

    console.log("--------------------------------");
    console.log("M3U URL:", chosenUrl);
    console.log("TOTAL CHANNELS:", channels.length);
    console.log("--------------------------------");

    return channels;

  } catch (error) {
    console.error("[M3U ERROR]", error.message);
    throw error;
  }
}

// =====================================================
// AUDIO BUFFER - UNCHANGED
// =====================================================

function clearAudioBuffer() {
  audioBuffer = Buffer.alloc(0);
  lastAudioSample = Buffer.from([0, 0]);
}

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

  if (chunk.length % 2 !== 0) {
    chunk = chunk.subarray(0, chunk.length - 1);
  }

  if (!chunk.length) return;

  audioBuffer = Buffer.concat([
    audioBuffer,
    chunk
  ]);

  if (audioBuffer.length > AUDIO_BUFFER_MAX * 1.25) {
    const excess =
      audioBuffer.length - AUDIO_BUFFER_MAX;

    const dropBytes =
      Math.max(2, excess + (excess % 2));

    audioBuffer = audioBuffer.subarray(dropBytes);
  }
}

function getAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);

  if (audioBuffer.length >= AUDIO_FRAME_BYTES) {
    const out =
      audioBuffer.subarray(0, AUDIO_FRAME_BYTES);

    audioBuffer =
      audioBuffer.subarray(AUDIO_FRAME_BYTES);

    if (out.length >= 2) {
      lastAudioSample =
        Buffer.from(out.subarray(out.length - 2));
    }

    out.copy(frame);

    return frame;
  }

  if (audioBuffer.length > 0) {
    const remaining = audioBuffer.length;

    audioBuffer.copy(frame, 0);

    lastAudioSample = Buffer.from(
      frame.subarray(
        Math.max(0, remaining - 2),
        remaining
      )
    );

    audioBuffer = Buffer.alloc(0);
  }

  for (
    let i = 0;
    i < AUDIO_FRAME_BYTES;
    i += 2
  ) {
    if (i >= AUDIO_FRAME_BYTES) break;

    frame[i] = lastAudioSample[0];
    frame[i + 1] = lastAudioSample[1];
  }

  return frame;
}

// =====================================================
// AUDIO REALTIME OUTPUT - UNCHANGED
// =====================================================

function startAudioTimer() {
  if (audioTimer) {
    clearInterval(audioTimer);
  }

  audioTimer = setInterval(() => {
    if (!audioClient || audioClient.destroyed) {
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
      const canContinue = audioClient.write(frame);

      if (!canContinue) {
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
// VIDEO JPEG PARSER - LOW LATENCY
// =====================================================

function clearVideoBuffer() {
  jpegPending = Buffer.alloc(0);

  latestFrame = null;
  frameSequence = 0;
}

function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation) return;
  if (!chunk || !chunk.length) return;

  jpegPending = Buffer.concat([
    jpegPending,
    chunk
  ]);

  while (jpegPending.length > 0) {

    const start = jpegPending.indexOf(JPEG_SOI);

    if (start < 0) {
      if (jpegPending[jpegPending.length - 1] === 0xff) {
        jpegPending = jpegPending.subarray(-1);
      } else {
        jpegPending = Buffer.alloc(0);
      }

      return;
    }

    if (start > 0) {
      jpegPending = jpegPending.subarray(start);
    }

    const end = jpegPending.indexOf(
      JPEG_EOI,
      2
    );

    if (end < 0) {

      if (jpegPending.length > MAX_JPEG_FRAME_BYTES) {

        videoInvalidFrames++;

        const nextStart = jpegPending.indexOf(
          JPEG_SOI,
          2
        );

        if (nextStart >= 0) {
          jpegPending = jpegPending.subarray(nextStart);
          continue;
        }

        jpegPending = Buffer.alloc(0);
      }

      return;
    }

    const frameLength = end + 2;

    if (frameLength > MAX_JPEG_FRAME_BYTES) {

      videoInvalidFrames++;

      jpegPending = jpegPending.subarray(frameLength);

      continue;
    }

    const jpeg = jpegPending.subarray(
      0,
      frameLength
    );

    if (latestFrame !== null) {
      videoDroppedFrames++;
    }

    latestFrame = Buffer.from(jpeg);

    frameSequence++;

    lastVideoFrameTime = Date.now();

    jpegPending = jpegPending.subarray(frameLength);
  }

  if (jpegPending.length > MAX_VIDEO_BUFFER) {

    const lastStart = jpegPending.lastIndexOf(JPEG_SOI);

    if (lastStart >= 0) {
      jpegPending = jpegPending.subarray(lastStart);
    } else {
      jpegPending = Buffer.alloc(0);
    }

    videoInvalidFrames++;
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

  clearVideoBuffer();

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

  clearVideoBuffer();
  clearAudioBuffer();

  videoDroppedFrames = 0;
  videoInvalidFrames = 0;

  const currentGeneration = generation;

  console.log("");
  console.log("======================================");
  console.log("START CHANNEL:", channel.name);
  console.log("URL:", channel.url);
  console.log("GENERATION:", currentGeneration);
  console.log("READRATE:", INPUT_READRATE);
  console.log("DECODER THREADS:", DECODER_THREADS);
  console.log("SKIP NONREF:", SKIP_NON_REFERENCE);
  console.log("OUTPUT:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
  console.log("FPS:", VIDEO_FPS);
  console.log("AUDIO:", AUDIO_SAMPLE_RATE, "Hz");
  console.log("======================================");

  lastVideoFrameTime = Date.now();

  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    // INPUT NETWORK
    "-rw_timeout", "30000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "5",

    "-user_agent",
    "Mozilla/5.0",

    "-fflags",
    "+discardcorrupt+genpts",

    // INPUT RATE
    "-readrate",
    INPUT_READRATE,

    // DECODER
    "-threads",
    String(DECODER_THREADS),

    ...(SKIP_NON_REFERENCE
      ? ["-skip_frame", "noref"]
      : []),

    // INPUT
    "-i", channel.url,

    // VIDEO OUTPUT
    "-map", "0:v:0?",
    "-an",

    "-vf",
    [
      `fps=${VIDEO_FPS}:round=down`,
      `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
      `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
      "setsar=1",
      `setpts=N/(${VIDEO_FPS}*TB)`
    ].join(","),

    "-q:v", String(JPEG_QUALITY),

    "-threads",
    String(ENCODER_THREADS),

    "-fps_mode", "cfr",

    "-flush_packets", "1",

    "-f", "image2pipe",
    "-vcodec", "mjpeg",

    "pipe:1",

    // AUDIO OUTPUT - UNCHANGED
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

  ffmpeg = spawn("ffmpeg", args, {
    stdio: [
      "ignore",
      "pipe",
      "pipe",
      "pipe"
    ]
  });

  const processRef = ffmpeg;

  // VIDEO PIPE
  processRef.stdout.on("data", chunk => {
    processVideoData(chunk, currentGeneration);
  });

  // AUDIO PIPE - UNCHANGED
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

    clearAudioBuffer();
    clearVideoBuffer();

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

  clearVideoBuffer();

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
// VIDEO STREAM - MJPEG
// =====================================================

app.get("/stream", (req, res) => {

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

  const timer = setInterval(() => {

    if (res.destroyed || res.writableEnded) {
      clearInterval(timer);
      return;
    }

    if (blocked) {

      if (Date.now() - blockedSince > 2000) {
        clearInterval(timer);
        res.destroy();
      }

      return;
    }

    if (!latestFrame) return;

    if (frameSequence === lastSentSequence) {
      return;
    }

    if (Date.now() - lastVideoFrameTime > 3000) {
      return;
    }

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
// AUDIO STREAM - UNCHANGED
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
  res.json({
    status: "running",

    channelCount: channels.length,

    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning: !!ffmpeg,

    restarting,
    manuallyStopped,

    pipeline: "REALTIME_HLS_MJPEG_VIDEO_LOW_LATENCY",

    inputReadrate: INPUT_READRATE,

    sourceResolution: "ORIGINAL",

    skipNonReferenceFrames:
      SKIP_NON_REFERENCE,

    decoderThreads: DECODER_THREADS,
    encoderThreads: ENCODER_THREADS,

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    videoDroppedFrames,
    videoInvalidFrames,

    videoPendingBytes: jpegPending.length,

    videoLatestFrameBytes: latestFrame
      ? latestFrame.length
      : 0,

    videoFrameSequence: frameSequence,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,

    audioFrameBytes: AUDIO_FRAME_BYTES,
    audioInterval: AUDIO_INTERVAL,

    audioBufferBytes: audioBuffer.length,
    audioBufferMax: AUDIO_BUFFER_MAX,

    audioClientConnected:
      !!audioClient && !audioClient.destroyed,

    lastVideoFrameTime,

    videoFrameAge: lastVideoFrameTime
      ? Date.now() - lastVideoFrameTime
      : null,

    generation
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.send("IPTV SERVER RUNNING");
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
    console.log("PIPELINE: REALTIME HLS MJPEG");
    console.log("INPUT READRATE:", INPUT_READRATE);
    console.log("SOURCE: ORIGINAL RESOLUTION");
    console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
    console.log("FPS:", VIDEO_FPS);
    console.log("AUDIO:", AUDIO_SAMPLE_RATE);
    console.log("--------------------------------");
  });
}

main();
