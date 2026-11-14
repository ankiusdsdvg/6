
const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = Number(process.env.PORT || 10000);

app.use(express.json({ limit: "32kb" }));

// =====================================================
// CONFIG
// =====================================================

const M3U_URLS = [
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u"
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 240;
const VIDEO_FPS = 12;
const JPEG_QUALITY = 10;

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;
const AUDIO_FRAME_MS = 100;

const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_FRAME_MS / 1000;

// AUDIO BUFFER
const AUDIO_START_BUFFER_MS = 900;
const AUDIO_BUFFER_MS = 4000;

const AUDIO_BUFFER_MAX =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_BUFFER_MS / 1000;

const AUDIO_TARGET_MIN_MS = 700;
const AUDIO_TARGET_MAX_MS = 1800;

const MAX_VIDEO_BUFFER = 512 * 1024;
const MAX_JPEG_FRAME_BYTES = 256 * 1024;

const VIDEO_TIMEOUT = 45000;
const WATCHDOG_INTERVAL = 5000;
const RESTART_DELAY = 3000;

const MAX_CLIENT_BLOCK_MS = 3000;
const MAX_AUDIO_BLOCK_MS = 3000;

const RENDER_API_KEY = process.env.RENDER_API_KEY || "";

const RENDER_SERVICE_IDS = (
  process.env.RENDER_SERVICE_IDS || ""
)
  .split(",")
  .map(x => x.trim())
  .filter(Boolean);

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

let manuallyStopped = true;
let restarting = false;

let restartTimer = null;
let watchdogTimer = null;

let latestFrame = null;
let frameSequence = 0;
let jpegPending = Buffer.alloc(0);

let lastVideoFrameTime = 0;

let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let videoSentFrames = 0;

const videoClients = new Map();

// AUDIO
let audioClient = null;
let audioTimer = null;
let audioBuffer = Buffer.alloc(0);

let audioPrimed = false;
let audioRecovering = false;
let audioTargetBufferMs = AUDIO_START_BUFFER_MS;

let audioNextTick = 0;

let audioBlocked = false;
let audioBlockedSince = 0;

let audioUnderflows = 0;
let audioOverflowBytes = 0;
let audioFramesSent = 0;
let audioSilenceSent = 0;
let audioPrimeCount = 0;

// =====================================================
// PLAYLIST
// =====================================================

function parseM3U(content) {
  const lines = content.split(/\r?\n/);
  const result = [];

  let info = null;

  for (const raw of lines) {
    const line = raw.trim();

    if (!line) continue;

    if (line.startsWith("#EXTINF:")) {
      info = line;
      continue;
    }

    if (line.startsWith("#") || !info) continue;

    if (!/^https?:\/\//i.test(line)) {
      info = null;
      continue;
    }

    const name =
      info.split(",").pop().trim() || "Unknown";

    const group = info.match(/group-title="([^"]*)"/i);
    const logo = info.match(/tvg-logo="([^"]*)"/i);
    const tvgId = info.match(/tvg-id="([^"]*)"/i);

    const resolution = name.match(/\b(\d{3,4})p\b/i);

    result.push({
      id: String(result.length),
      name,
      group: group ? group[1] : "",
      logo: logo ? logo[1] : "",
      tvgId: tvgId ? tvgId[1] : "",
      resolution: resolution
        ? Number(resolution[1])
        : 0,
      url: line
    });

    info = null;
  }

  return result;
}

async function loadChannels() {
  let lastError = null;

  for (const url of M3U_URLS) {
    try {
      console.log("[M3U] Loading:", url);

      const response = await fetch(url, {
        headers: {
          "User-Agent": "Mozilla/5.0"
        },
        signal: AbortSignal.timeout(20000)
      });

      if (!response.ok) {
        throw new Error("HTTP " + response.status);
      }

      const text = await response.text();
      const parsed = parseM3U(text);

      if (!parsed.length) {
        throw new Error("Playlist empty");
      }

      channels = parsed;

      console.log("[M3U] Loaded:", channels.length);

      return channels;

    } catch (error) {
      lastError = error;
      console.log("[M3U ERROR]", error.message);
    }
  }

  throw lastError || new Error("Cannot load playlist");
}

// =====================================================
// VIDEO CLIENTS
// =====================================================

function clearVideoBuffer() {
  latestFrame = null;
  frameSequence = 0;
  jpegPending = Buffer.alloc(0);
}

function removeVideoClient(res) {
  videoClients.delete(res);
}

function broadcastFrame(frame) {
  if (!frame) return;

  const now = Date.now();

  const header = Buffer.from(
    "--frame\r\n" +
    "Content-Type: image/jpeg\r\n" +
    "Content-Length: " + frame.length +
    "\r\n\r\n"
  );

  const end = Buffer.from("\r\n");

  for (const [res, state] of videoClients) {
    if (res.destroyed || res.writableEnded) {
      removeVideoClient(res);
      continue;
    }

    if (state.blocked) {
      if (
        now - state.blockedSince >
        MAX_CLIENT_BLOCK_MS
      ) {
        removeVideoClient(res);
        res.destroy();
      }

      continue;
    }

    try {
      let ok = true;

      if (!res.write(header)) ok = false;
      if (!res.write(frame)) ok = false;
      if (!res.write(end)) ok = false;

      state.lastSentTime = now;
      state.lastSentSequence = frameSequence;

      videoSentFrames++;

      if (!ok) {
        state.blocked = true;
        state.blockedSince = now;

        res.once("drain", () => {
          state.blocked = false;
          state.blockedSince = 0;
        });
      }

    } catch (error) {
      removeVideoClient(res);
      res.destroy();
    }
  }
}

// =====================================================
// JPEG PARSER
// =====================================================

function processVideoData(chunk, currentGeneration) {
  if (currentGeneration !== generation) return;
  if (!chunk || !chunk.length) return;

  if (jpegPending.length + chunk.length > MAX_VIDEO_BUFFER) {
    const combined = Buffer.concat([
      jpegPending,
      chunk
    ]);

    const lastStart = combined.lastIndexOf(
      Buffer.from([0xff, 0xd8])
    );

    jpegPending = lastStart >= 0
      ? Buffer.from(combined.subarray(lastStart))
      : Buffer.alloc(0);

    videoInvalidFrames++;

  } else {
    jpegPending = jpegPending.length
      ? Buffer.concat([jpegPending, chunk])
      : Buffer.from(chunk);
  }

  while (jpegPending.length > 0) {
    const start = jpegPending.indexOf(
      Buffer.from([0xff, 0xd8])
    );

    if (start < 0) {
      jpegPending = Buffer.alloc(0);
      return;
    }

    if (start > 0) {
      jpegPending = jpegPending.subarray(start);
    }

    const end = jpegPending.indexOf(
      Buffer.from([0xff, 0xd9]),
      2
    );

    if (end < 0) {
      if (jpegPending.length > MAX_JPEG_FRAME_BYTES) {
        jpegPending = Buffer.alloc(0);
        videoInvalidFrames++;
      }

      return;
    }

    const frameLength = end + 2;

    if (frameLength > MAX_JPEG_FRAME_BYTES) {
      jpegPending = jpegPending.subarray(frameLength);
      videoInvalidFrames++;
      continue;
    }

    latestFrame = Buffer.from(
      jpegPending.subarray(0, frameLength)
    );

    frameSequence++;
    lastVideoFrameTime = Date.now();

    broadcastFrame(latestFrame);

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// =====================================================
// AUDIO BUFFER
// =====================================================

function resetAudioState() {
  audioBuffer = Buffer.alloc(0);

  audioPrimed = false;
  audioRecovering = false;

  audioTargetBufferMs = AUDIO_START_BUFFER_MS;

  audioNextTick = 0;
}

function disconnectAudioClient() {
  if (audioTimer) {
    clearTimeout(audioTimer);
    audioTimer = null;
  }

  const old = audioClient;

  audioClient = null;

  audioBlocked = false;
  audioBlockedSince = 0;

  resetAudioState();

  if (old && !old.destroyed) {
    old.destroy();
  }
}

// =====================================================
// RECEIVE AUDIO FROM FFMPEG
// =====================================================

function pushAudioBuffer(chunk) {
  if (!audioClient || audioClient.destroyed) return;
  if (!chunk || !chunk.length) return;

  // PCM 16-bit: always keep an even byte count
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
      audioBuffer = Buffer.from(
        chunk.subarray(-AUDIO_BUFFER_MAX)
      );

    } else {
      audioBuffer = Buffer.concat([
        audioBuffer.subarray(drop),
        chunk
      ]);
    }

  } else {
    audioBuffer = audioBuffer.length
      ? Buffer.concat(
          [audioBuffer, chunk],
          total
        )
      : Buffer.from(chunk);
  }
}

// =====================================================
// AUDIO FRAME
// =====================================================

function takeAudioFrame() {
  if (audioBuffer.length < AUDIO_FRAME_BYTES) {
    return null;
  }

  const frame = Buffer.from(
    audioBuffer.subarray(0, AUDIO_FRAME_BYTES)
  );

  audioBuffer = audioBuffer.subarray(
    AUDIO_FRAME_BYTES
  );

  return frame;
}

// =====================================================
// AUDIO OUTPUT
// =====================================================

function writeAudioFrame(frame) {
  if (!audioClient || audioClient.destroyed) {
    return false;
  }

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

      return false;
    }

    return true;

  } catch (error) {
    disconnectAudioClient();
    return false;
  }
}

// =====================================================
// AUDIO BUFFER RECOVERY
// =====================================================

function audioTick() {
  if (!audioClient || audioClient.destroyed) {
    disconnectAudioClient();
    return;
  }

  if (audioBlocked) {
    if (
      Date.now() - audioBlockedSince >
      MAX_AUDIO_BLOCK_MS
    ) {
      console.log("[AUDIO] Client blocked");
      disconnectAudioClient();
    }

    return;
  }

  const targetBytes = Math.floor(
    AUDIO_SAMPLE_RATE *
    AUDIO_CHANNELS *
    AUDIO_BYTES_PER_SAMPLE *
    audioTargetBufferMs / 1000
  );

  // Wait for enough audio before starting or resuming.
  if (!audioPrimed) {
    if (audioBuffer.length < targetBytes) {
      return;
    }

    audioPrimed = true;
    audioPrimeCount++;

    console.log(
      audioRecovering
        ? "[AUDIO] Buffer recovered:"
        : "[AUDIO] Buffer ready:",
      Math.round(audioBuffer.length / 32),
      "ms"
    );

    audioRecovering = false;
  }

  const frame = takeAudioFrame();

  // If source audio runs out, stop output temporarily.
  // Do not insert fake PCM silence into the stream.
  if (!frame) {
    audioUnderflows++;

    audioPrimed = false;
    audioRecovering = true;

    audioTargetBufferMs = Math.min(
      AUDIO_TARGET_MAX_MS,
      Math.max(
        AUDIO_TARGET_MIN_MS,
        audioTargetBufferMs + 150
      )
    );

    console.log(
      "[AUDIO] Underflow, rebuffer:",
      audioTargetBufferMs,
      "ms"
    );

    return;
  }

  writeAudioFrame(frame);

  // Monitor remaining buffered audio.
  const bufferedMs =
    audioBuffer.length /
    (
      AUDIO_SAMPLE_RATE *
      AUDIO_CHANNELS *
      AUDIO_BYTES_PER_SAMPLE
    ) * 1000;

  if (bufferedMs < AUDIO_TARGET_MIN_MS) {
    audioTargetBufferMs = Math.min(
      AUDIO_TARGET_MAX_MS,
      audioTargetBufferMs + 25
    );
  }
}

// =====================================================
// AUDIO CLOCK
// =====================================================

function scheduleAudioTick() {
  if (!audioClient || audioClient.destroyed) {
    audioTimer = null;
    return;
  }

  const now = Date.now();

  if (!audioNextTick) {
    audioNextTick = now + AUDIO_FRAME_MS;
  }

  const wait = Math.max(
    0,
    audioNextTick - now
  );

  audioTimer = setTimeout(() => {
    const current = Date.now();

    audioTick();

    // Fixed 100ms audio clock.
    audioNextTick += AUDIO_FRAME_MS;

    // Do not send accumulated frames in a burst.
    if (current - audioNextTick > AUDIO_FRAME_MS) {
      audioNextTick = current + AUDIO_FRAME_MS;
    }

    scheduleAudioTick();

  }, wait);
}

function startAudioTimer() {
  if (audioTimer) {
    clearTimeout(audioTimer);
    audioTimer = null;
  }

  audioNextTick = Date.now() + AUDIO_FRAME_MS;

  scheduleAudioTick();
}

// =====================================================
// FFMPEG CONTROL
// =====================================================

function clearWatchdog() {
  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }
}

function killCurrentFFmpeg() {
  generation++;

  clearWatchdog();

  if (restartTimer) {
    clearTimeout(restartTimer);
    restartTimer = null;
  }

  const old = ffmpeg;
  ffmpeg = null;

  if (old) {
    try {
      old.kill("SIGKILL");
    } catch (_) {}
  }
}

function stopFFmpeg() {
  manuallyStopped = true;
  restarting = false;

  killCurrentFFmpeg();

  disconnectAudioClient();

  for (const res of videoClients.keys()) {
    try {
      res.destroy();
    } catch (_) {}
  }

  videoClients.clear();

  clearVideoBuffer();

  currentChannel = null;
}

// =====================================================
// START FFMPEG
// =====================================================

function startFFmpeg(channel) {
  if (!channel || !channel.url) return;

  killCurrentFFmpeg();

  manuallyStopped = false;
  restarting = false;

  currentChannel = channel;

  clearVideoBuffer();
  resetAudioState();

  for (const state of videoClients.values()) {
    state.lastSentSequence = -1;
    state.lastSentTime = 0;
    state.blocked = false;
    state.blockedSince = 0;
  }

  videoDroppedFrames = 0;
  videoInvalidFrames = 0;
  videoSentFrames = 0;

  audioUnderflows = 0;
  audioOverflowBytes = 0;
  audioFramesSent = 0;
  audioSilenceSent = 0;
  audioPrimeCount = 0;

  const currentGeneration = generation;

  lastVideoFrameTime = Date.now();

  console.log("");
  console.log("=================================");
  console.log("[CHANNEL]", channel.name);
  console.log("[GENERATION]", currentGeneration);
  console.log("[VIDEO]", VIDEO_WIDTH, "x", VIDEO_HEIGHT, "@", VIDEO_FPS);
  console.log("[AUDIO]", AUDIO_SAMPLE_RATE, "Hz S16LE");
  console.log("[AUDIO BUFFER]", AUDIO_START_BUFFER_MS, "ms");
  console.log("[AUDIO FRAME]", AUDIO_FRAME_MS, "ms");
  console.log("[MODE] STABLE AUDIO VIDEO");
  console.log("=================================");

  const filter = [
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1"
  ].join(",");

  const args = [
    "-hide_banner",
    "-loglevel", "warning",
    "-nostdin",

    "-rw_timeout", "15000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "3",

    "-user_agent", "Mozilla/5.0",

    "-fflags", "+discardcorrupt+genpts",
    "-probesize", "1000000",
    "-analyzeduration", "1000000",

    "-threads", "2",
    "-filter_threads", "1",

    // INPUT
    "-i", channel.url,

    // VIDEO OUTPUT
    "-map", "0:v:0?",
    "-an",
    "-vf", filter,
    "-c:v", "mjpeg",
    "-q:v", String(JPEG_QUALITY),
    "-threads", "1",
    "-r", String(VIDEO_FPS),
    "-fps_mode", "cfr",
    "-flush_packets", "1",
    "-f", "image2pipe",
    "pipe:1",

    // AUDIO OUTPUT
    "-map", "0:a:0?",
    "-vn",
    "-af",
    `aresample=${AUDIO_SAMPLE_RATE}:async=1000:first_pts=0`,
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_SAMPLE_RATE),
    "-c:a", "pcm_s16le",
    "-flush_packets", "1",
    "-f", "s16le",
    "pipe:3"
  ];

  const child = spawn("ffmpeg", args, {
    stdio: [
      "ignore",
      "pipe",
      "pipe",
      "pipe"
    ]
  });

  ffmpeg = child;

  // VIDEO DATA
  child.stdout.on("data", chunk => {
    processVideoData(
      chunk,
      currentGeneration
    );
  });

  // AUDIO DATA
  if (child.stdio[3]) {
    child.stdio[3].on("data", chunk => {
      if (currentGeneration === generation) {
        pushAudioBuffer(chunk);
      }
    });
  }

  // FFMPEG LOG
  child.stderr.on("data", data => {
    const message = data.toString().trim();

    if (message) {
      console.log("[FFmpeg]", message);
    }
  });

  child.on("error", error => {
    console.log(
      "[FFmpeg ERROR]",
      error.message
    );
  });

  child.on("close", (code, signal) => {
    console.log(
      "[FFmpeg EXIT]",
      code,
      signal
    );

    if (currentGeneration !== generation) {
      return;
    }

    ffmpeg = null;

    clearVideoBuffer();
    audioBuffer = Buffer.alloc(0);
    audioPrimed = false;

    if (!manuallyStopped) {
      scheduleRestart();
    }
  });

  // WATCHDOG
  watchdogTimer = setInterval(() => {
    if (currentGeneration !== generation) return;
    if (!ffmpeg || restarting || manuallyStopped) return;

    const age = Date.now() - lastVideoFrameTime;

    if (age > VIDEO_TIMEOUT) {
      console.log(
        "[WATCHDOG] Video timeout:",
        age
      );

      scheduleRestart();
    }
  }, WATCHDOG_INTERVAL);
}

// =====================================================
// RESTART
// =====================================================

function scheduleRestart() {
  if (
    restarting ||
    manuallyStopped ||
    !currentChannel
  ) {
    return;
  }

  restarting = true;

  console.log("[RESTART] FFmpeg restarting...");

  clearWatchdog();

  const old = ffmpeg;
  ffmpeg = null;

  if (old) {
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
// VIDEO STREAM API
// =====================================================

app.get("/stream", (req, res) => {
  const requestedFps = Number(req.query.fps);

  const clientFps =
    Number.isFinite(requestedFps) &&
    requestedFps > 0
      ? Math.min(
          30,
          Math.max(1, Math.floor(requestedFps))
        )
      : VIDEO_FPS;

  res.writeHead(200, {
    "Content-Type":
      "multipart/x-mixed-replace; boundary=frame",

    "Cache-Control":
      "no-cache, no-store, must-revalidate",

    "Pragma": "no-cache",
    "Expires": "0",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  const state = {
    blocked: false,
    blockedSince: 0,
    lastSentSequence: -1,
    lastSentTime: 0,
    clientFps
  };

  videoClients.set(res, state);

  // SEND CURRENT FRAME
  if (
    latestFrame &&
    frameSequence > 0 &&
    Date.now() - lastVideoFrameTime < 1500
  ) {
    const header = Buffer.from(
      "--frame\r\n" +
      "Content-Type: image/jpeg\r\n" +
      "Content-Length: " + latestFrame.length +
      "\r\n\r\n"
    );

    res.write(header);
    res.write(latestFrame);
    res.write("\r\n");

    state.lastSentSequence = frameSequence;
    state.lastSentTime = Date.now();
  }

  res.on("close", () => {
    removeVideoClient(res);
  });

  res.on("error", () => {
    removeVideoClient(res);
  });
});

// =====================================================
// AUDIO STREAM API
// =====================================================

app.get("/audio", (req, res) => {
  if (audioClient && audioClient !== res) {
    disconnectAudioClient();
  }

  audioClient = res;

  resetAudioState();

  res.writeHead(200, {
    "Content-Type": "application/octet-stream",
    "Cache-Control": "no-cache, no-store",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "Content-Encoding": "identity"
  });

  console.log("[AUDIO] Client connected");

  startAudioTimer();

  res.on("close", () => {
    if (audioClient === res) {
      disconnectAudioClient();
      console.log("[AUDIO] Client disconnected");
    }
  });

  res.on("error", () => {
    if (audioClient === res) {
      disconnectAudioClient();
    }
  });
});

// =====================================================
// CHANNEL LIST
// =====================================================

app.get("/api/channels", (req, res) => {
  const quality = String(
    req.query.quality ||
    req.query.q ||
    "720"
  ).toLowerCase();

  let maxResolution = 720;

  if (
    quality === "all" ||
    quality === "full"
  ) {
    maxResolution = Number.MAX_SAFE_INTEGER;

  } else {
    const value = Number.parseInt(quality, 10);

    if (Number.isFinite(value) && value > 0) {
      maxResolution = value;
    }
  }

  const filtered = channels.filter(channel => {
    return (
      !channel.resolution ||
      channel.resolution <= maxResolution
    );
  });

  res.json({
    success: true,
    channelCount: filtered.length,
    channels: filtered
  });
});

// =====================================================
// SELECT CHANNEL
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

  startFFmpeg(channel);

  res.json({
    success: true,
    channel: channel.name,
    starting: true,
    message: "Waiting for first video frame"
  });
}

app.get(
  "/api/select/:id",
  selectChannelHandler
);

app.post(
  "/api/select/:id",
  selectChannelHandler
);

// =====================================================
// STOP
// =====================================================

app.get("/api/stop", (req, res) => {
  stopFFmpeg();

  res.json({
    success: true,
    message: "Playback stopped"
  });
});

app.post("/api/stop", (req, res) => {
  stopFFmpeg();

  res.json({
    success: true,
    message: "Playback stopped"
  });
});

// =====================================================
// RELOAD PLAYLIST
// =====================================================

app.get("/api/reload", async (req, res) => {
  try {
    await loadChannels();

    res.json({
      success: true,
      channelCount: channels.length
    });

  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// =====================================================
// BANDWIDTH API
// =====================================================

app.get("/api/bandwidth", async (req, res) => {
  try {
    if (
      !RENDER_API_KEY ||
      !RENDER_SERVICE_IDS.length
    ) {
      return res.status(500).json({
        success: false,
        error:
          "Missing RENDER_API_KEY or RENDER_SERVICE_IDS"
      });
    }

    const now = new Date();

    const start = new Date(Date.UTC(
      now.getUTCFullYear(),
      now.getUTCMonth(),
      1
    ));

    const url = new URL(
      "https://api.render.com/v1/metrics/bandwidth"
    );

    url.searchParams.set(
      "startTime",
      start.toISOString()
    );

    url.searchParams.set(
      "endTime",
      now.toISOString()
    );

    for (const id of RENDER_SERVICE_IDS) {
      url.searchParams.append("resource", id);
    }

    const response = await fetch(url, {
      headers: {
        Authorization: "Bearer " + RENDER_API_KEY,
        Accept: "application/json"
      },
      signal: AbortSignal.timeout(20000)
    });

    if (!response.ok) {
      throw new Error(
        "Render API HTTP " + response.status
      );
    }

    const data = await response.json();

    let usedGB = 0;

    for (const series of data) {
      const unit = String(
        series.unit || "GB"
      ).toUpperCase();

      for (const point of series.values || []) {
        const value = Number(point.value);

        if (!Number.isFinite(value)) continue;

        if (unit === "GB") {
          usedGB += value;

        } else if (unit === "MB") {
          usedGB += value / 1024;

        } else if (
          ["B", "BYTE", "BYTES"].includes(unit)
        ) {
          usedGB += value / (1024 ** 3);
        }
      }
    }

    usedGB = Number(usedGB.toFixed(4));

    const remainingGB = Math.max(
      0,
      BANDWIDTH_LIMIT_GB - usedGB
    );

    const resetAt = new Date(Date.UTC(
      now.getUTCFullYear(),
      now.getUTCMonth() + 1,
      1
    ));

    res.json({
      success: true,
      provider: "Render",

      limitGB: BANDWIDTH_LIMIT_GB,
      usedGB,
      remainingGB,

      usedPercent: Number(
        (
          usedGB /
          BANDWIDTH_LIMIT_GB *
          100
        ).toFixed(2)
      ),

      remainingPercent: Number(
        (
          remainingGB /
          BANDWIDTH_LIMIT_GB *
          100
        ).toFixed(2)
      ),

      resetAt: resetAt.toISOString(),
      updatedAt: now.toISOString()
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
  const memory = process.memoryUsage();
  const now = Date.now();

  const audioBufferMs =
    audioBuffer.length /
    (
      AUDIO_SAMPLE_RATE *
      AUDIO_CHANNELS *
      AUDIO_BYTES_PER_SAMPLE
    ) * 1000;

  res.json({
    status: "running",

    channelCount: channels.length,

    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning: !!ffmpeg,
    restarting,
    manuallyStopped,

    pipeline: "STABLE_MJPEG_PCM_ADAPTIVE_BUFFER",

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    videoDroppedFrames,
    videoInvalidFrames,
    videoSentFrames,

    videoClients: videoClients.size,

    videoPendingBytes: jpegPending.length,

    videoLatestFrameBytes: latestFrame
      ? latestFrame.length
      : 0,

    videoFrameSequence: frameSequence,

    firstFrameReceived: !!latestFrame,

    firstFrameAgeMs: latestFrame
      ? now - lastVideoFrameTime
      : null,

    videoFrameAgeMs: lastVideoFrameTime
      ? now - lastVideoFrameTime
      : null,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,

    audioFrameMs: AUDIO_FRAME_MS,
    audioFrameBytes: AUDIO_FRAME_BYTES,

    audioBufferBytes: audioBuffer.length,

    audioBufferMs: Number(
      audioBufferMs.toFixed(1)
    ),

    audioBufferMax: AUDIO_BUFFER_MAX,

    audioStartBufferMs: AUDIO_START_BUFFER_MS,
    audioTargetBufferMs,

    audioPrimed,
    audioRecovering,

    audioPrimeCount,

    audioClientConnected:
      !!audioClient && !audioClient.destroyed,

    audioBlocked,
    audioBlockedSince,

    audioUnderflows,
    audioOverflowBytes,

    audioFramesSent,
    audioSilenceSent,

    memory: {
      rssMB: Number(
        (memory.rss / 1048576).toFixed(2)
      ),

      heapUsedMB: Number(
        (memory.heapUsed / 1048576).toFixed(2)
      ),

      externalMB: Number(
        (memory.external / 1048576).toFixed(2)
      )
    },

    generation
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.type("text/plain").send(
    "IPTV SERVER RUNNING\n" +
    "/stream\n" +
    "/audio\n" +
    "/api/channels\n" +
    "/api/select/:id\n" +
    "/api/stop\n" +
    "/api/reload\n" +
    "/health\n" +
    "/api/bandwidth\n"
  );
});

// =====================================================
// START SERVER
// =====================================================

async function main() {
  try {
    await loadChannels();

  } catch (error) {
    console.log(
      "[PLAYLIST ERROR]",
      error.message
    );
  }

  app.listen(PORT, "0.0.0.0", () => {
    console.log("=================================");
    console.log("IPTV SERVER RUNNING");
    console.log("PORT:", PORT);
    console.log("CHANNELS:", channels.length);

    console.log(
      "VIDEO:",
      VIDEO_WIDTH,
      "x",
      VIDEO_HEIGHT
    );

    console.log("FPS:", VIDEO_FPS);
    console.log("AUDIO:", AUDIO_SAMPLE_RATE);

    console.log(
      "AUDIO FRAME:",
      AUDIO_FRAME_MS,
      "ms"
    );

    console.log(
      "AUDIO START BUFFER:",
      AUDIO_START_BUFFER_MS,
      "ms"
    );

    console.log(
      "AUDIO MAX BUFFER:",
      AUDIO_BUFFER_MS,
      "ms"
    );

    console.log("MODE: STABLE AUDIO VIDEO");
    console.log("=================================");
  });
}

// =====================================================
// SHUTDOWN
// =====================================================

function shutdown() {
  console.log("[SERVER] Shutting down");

  stopFFmpeg();

  process.exit(0);
}

process.on("SIGINT", shutdown);
process.on("SIGTERM", shutdown);

main().catch(error => {
  console.error("[SERVER ERROR]", error);
  process.exit(1);
});
