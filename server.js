

const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = Number(process.env.PORT || 10000);

app.use(express.json({ limit: "32kb" }));

// =====================================================
// CONFIG
// =====================================================

const M3U_URL =
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u";

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 240;
const VIDEO_FPS = 12;
const VIDEO_QUALITY = 8;

const AUDIO_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_SAMPLE_BYTES = 2;

// 40ms PCM = 1280 bytes
const AUDIO_FRAME_MS = 40;
const AUDIO_FRAME_BYTES =
  AUDIO_RATE * AUDIO_CHANNELS * AUDIO_SAMPLE_BYTES *
  AUDIO_FRAME_MS / 1000;

// Khởi động cần đủ 1,5 giây dữ liệu
const AUDIO_START_BUFFER_MS = 1500;

// Khi hụt tiếng, đợi buffer hồi lại 500ms
const AUDIO_RECOVERY_BUFFER_MS = 500;

const AUDIO_MAX_BUFFER_MS = 2500;
const AUDIO_MAX_BUFFER_BYTES =
  AUDIO_RATE * AUDIO_CHANNELS * AUDIO_SAMPLE_BYTES *
  AUDIO_MAX_BUFFER_MS / 1000;

const PLAYLIST_TIMEOUT_MS = 30000;
const PLAYLIST_RETRIES = 3;

const RESTART_DELAY_MS = 3000;
const WATCHDOG_TIMEOUT_MS = 45000;

// =====================================================
// GLOBAL STATE
// =====================================================

let channels = [];
let currentChannel = null;

let ffmpeg = null;
let ffmpegRunning = false;
let manuallyStopped = false;
let restarting = false;

let generation = 0;
let restartTimer = null;

const videoClients = new Set();
const audioClients = new Set();

let videoPending = Buffer.alloc(0);
let latestFrame = null;
let latestFrameTime = 0;
let lastVideoTime = 0;

let audioBuffer = Buffer.alloc(0);
let audioPrimed = false;
let audioRecovering = false;
let audioTimer = null;

let ffmpegStartedAt = 0;
let lastAudioTime = 0;

let videoFrames = 0;
let videoDroppedFrames = 0;
let videoInvalidFrames = 0;

let audioFramesSent = 0;
let audioUnderflows = 0;
let audioPrimeCount = 0;

let restartCount = 0;
const serverStartedAt = Date.now();

// =====================================================
// HELPERS
// =====================================================

function log(...args) {
  console.log(new Date().toISOString(), ...args);
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function getAudioBufferMs() {
  return Math.round(
    audioBuffer.length /
    (AUDIO_RATE * AUDIO_CHANNELS * AUDIO_SAMPLE_BYTES) *
    1000
  );
}

function clearAudioState() {
  audioBuffer = Buffer.alloc(0);
  audioPrimed = false;
  audioRecovering = false;
}

function stopAudioTimer() {
  if (audioTimer) {
    clearInterval(audioTimer);
    audioTimer = null;
  }
}

// =====================================================
// PLAYLIST PARSER
// =====================================================

function parseM3U(data) {
  const lines = data
    .replace(/^\uFEFF/, "")
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(Boolean);

  if (!lines.some(line => line.startsWith("#EXTM3U"))) {
    throw new Error("Không tìm thấy #EXTM3U");
  }

  const result = [];
  let info = null;

  for (const line of lines) {
    if (line.startsWith("#EXTINF:")) {
      info = line;
      continue;
    }

    if (line.startsWith("#")) continue;

    if (!/^https?:\/\//i.test(line)) continue;
    if (!info) continue;

    const comma = info.indexOf(",");
    const name = comma >= 0
      ? info.substring(comma + 1).trim()
      : "";

    const tvgId =
      (info.match(/tvg-id="([^"]*)"/i) || [])[1] || "";

    const logo =
      (info.match(/tvg-logo="([^"]*)"/i) || [])[1] || "";

    const group =
      (info.match(/group-title="([^"]*)"/i) || [])[1] || "";

    result.push({
      id: result.length,
      name: name || `Channel ${result.length + 1}`,
      url: line,
      tvgId,
      logo,
      group
    });

    info = null;
  }

  if (!result.length) {
    throw new Error("Playlist không có kênh hợp lệ");
  }

  return result;
}

// =====================================================
// LOAD PLAYLIST
// =====================================================

async function loadChannels() {
  let lastError = null;

  for (let attempt = 1; attempt <= PLAYLIST_RETRIES; attempt++) {
    const controller = new AbortController();
    const timeout = setTimeout(
      () => controller.abort(),
      PLAYLIST_TIMEOUT_MS
    );

    try {
      log(`Tải playlist ${attempt}/${PLAYLIST_RETRIES}`);

      const response = await fetch(M3U_URL, {
        headers: {
          "User-Agent": "Mozilla/5.0 IPTV Server",
          "Accept": "*/*",
          "Cache-Control": "no-cache"
        },
        signal: controller.signal
      });

      if (!response.ok) {
        throw new Error(`HTTP ${response.status}`);
      }

      const data = await response.text();
      const parsed = parseM3U(data);

      // Chỉ thay danh sách khi tải thành công
      channels = parsed;

      log("PLAYLIST OK:", channels.length, "CHANNELS");

      return channels;

    } catch (error) {
      lastError = error;
      log("PLAYLIST ERROR:", error.message);

      if (attempt < PLAYLIST_RETRIES) {
        await sleep(2000);
      }

    } finally {
      clearTimeout(timeout);
    }
  }

  throw lastError || new Error("Không tải được playlist");
}

// =====================================================
// VIDEO
// =====================================================

function broadcastVideo(frame) {
  const header = Buffer.from(
    "--frame\r\n" +
    "Content-Type: image/jpeg\r\n" +
    `Content-Length: ${frame.length}\r\n\r\n`
  );

  for (const client of videoClients) {
    if (client.destroyed || !client.writable) {
      videoClients.delete(client);
      continue;
    }

    try {
      const ok =
        client.write(header) &&
        client.write(frame) &&
        client.write("\r\n");

      if (!ok) videoDroppedFrames++;

    } catch {
      videoClients.delete(client);
    }
  }
}

function handleVideoData(chunk) {
  videoPending = Buffer.concat([videoPending, chunk]);

  while (videoPending.length > 4) {
    const start = videoPending.indexOf(
      Buffer.from([0xff, 0xd8])
    );

    if (start < 0) {
      if (videoPending.length > 1024 * 1024) {
        videoPending = Buffer.alloc(0);
      }
      return;
    }

    const end = videoPending.indexOf(
      Buffer.from([0xff, 0xd9]),
      start + 2
    );

    if (end < 0) {
      if (start > 0) {
        videoPending = videoPending.subarray(start);
      }

      if (videoPending.length > 1024 * 1024) {
        videoPending = Buffer.alloc(0);
      }

      return;
    }

    const frame = videoPending.subarray(start, end + 2);
    videoPending = videoPending.subarray(end + 2);

    if (frame.length < 100 || frame.length > 512 * 1024) {
      videoInvalidFrames++;
      continue;
    }

    latestFrame = Buffer.from(frame);
    latestFrameTime = Date.now();
    lastVideoTime = latestFrameTime;

    videoFrames++;

    broadcastVideo(latestFrame);
  }
}

// =====================================================
// AUDIO BUFFER
// =====================================================

function pushAudioBuffer(chunk) {
  if (!chunk || !chunk.length) return;

  audioBuffer = Buffer.concat([audioBuffer, chunk]);

  if (audioBuffer.length > AUDIO_MAX_BUFFER_BYTES) {
    const excess = audioBuffer.length - AUDIO_MAX_BUFFER_BYTES;
    audioBuffer = audioBuffer.subarray(excess);
  }

  lastAudioTime = Date.now();
}

function broadcastAudio(frame) {
  for (const client of audioClients) {
    if (client.destroyed || !client.writable) {
      audioClients.delete(client);
      continue;
    }

    try {
      client.write(frame);
    } catch {
      audioClients.delete(client);
    }
  }
}

function audioTick() {
  if (audioClients.size === 0) {
    audioPrimed = false;
    audioRecovering = false;
    return;
  }

  const bufferMs = getAudioBufferMs();

  // Giai đoạn khởi động
  if (!audioPrimed) {
    if (bufferMs < AUDIO_START_BUFFER_MS) {
      audioRecovering = true;
      return;
    }

    audioPrimed = true;
    audioRecovering = false;
    audioPrimeCount++;

    log("AUDIO READY:", bufferMs, "ms");
  }

  // Nếu hụt dữ liệu, chờ buffer hồi phục
  if (audioBuffer.length < AUDIO_FRAME_BYTES) {
    audioRecovering = true;
    audioPrimed = false;
    audioUnderflows++;

    broadcastAudio(Buffer.alloc(AUDIO_FRAME_BYTES));
    audioFramesSent++;

    return;
  }

  if (audioRecovering) {
    if (bufferMs < AUDIO_RECOVERY_BUFFER_MS) {
      broadcastAudio(Buffer.alloc(AUDIO_FRAME_BYTES));
      audioFramesSent++;
      return;
    }

    audioRecovering = false;
    audioPrimed = true;

    log("AUDIO RECOVERED:", bufferMs, "ms");
  }

  const frame = audioBuffer.subarray(
    0,
    AUDIO_FRAME_BYTES
  );

  audioBuffer = audioBuffer.subarray(AUDIO_FRAME_BYTES);

  broadcastAudio(frame);
  audioFramesSent++;
}

function startAudioTimer() {
  stopAudioTimer();

  audioTimer = setInterval(
    audioTick,
    AUDIO_FRAME_MS
  );
}

// =====================================================
// STOP FFMPEG SAFELY
// =====================================================

function stopFFmpeg() {
  // Vô hiệu hóa mọi sự kiện của tiến trình cũ
  generation++;

  clearTimeout(restartTimer);
  restarting = false;

  const old = ffmpeg;

  ffmpeg = null;
  ffmpegRunning = false;

  if (old) {
    try {
      old.kill("SIGKILL");
    } catch {}
  }

  videoPending = Buffer.alloc(0);
  latestFrame = null;
  latestFrameTime = 0;

  clearAudioState();
}

// =====================================================
// START FFMPEG
// =====================================================

function startFFmpeg(channel) {
  if (!channel || !channel.url) {
    throw new Error("Kênh không hợp lệ");
  }

  // Tạo phiên mới, vô hiệu hóa phiên cũ
  const myGeneration = ++generation;

  clearTimeout(restartTimer);
  restarting = false;

  const old = ffmpeg;

  ffmpeg = null;
  ffmpegRunning = false;

  if (old) {
    try {
      old.kill("SIGKILL");
    } catch {}
  }

  currentChannel = channel;
  manuallyStopped = false;

  latestFrame = null;
  latestFrameTime = 0;
  lastVideoTime = 0;
  lastAudioTime = 0;

  videoPending = Buffer.alloc(0);
  clearAudioState();

  log("START CHANNEL:", channel.name);

  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    "-thread_queue_size", "512",

    "-rw_timeout", "15000000",
    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_at_eof", "1",
    "-reconnect_delay_max", "5",

    "-probesize", "2000000",
    "-analyzeduration", "2000000",

    "-i", channel.url,

    // VIDEO
    "-map", "0:v:0?",
    "-an",
    "-vf",
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease,pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2,fps=${VIDEO_FPS}`,
    "-q:v", String(VIDEO_QUALITY),
    "-f", "image2pipe",
    "-vcodec", "mjpeg",
    "pipe:1",

    // AUDIO
    "-map", "0:a:0?",
    "-vn",
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_RATE),
    "-c:a", "pcm_s16le",
    "-f", "s16le",
    "pipe:3"
  ];

  const child = spawn("ffmpeg", args, {
    stdio: ["ignore", "pipe", "pipe", "pipe"]
  });

  ffmpeg = child;
  ffmpegRunning = true;
  ffmpegStartedAt = Date.now();

  child.stdout.on("data", chunk => {
    if (generation !== myGeneration) return;
    handleVideoData(chunk);
  });

  if (child.stdio[3]) {
    child.stdio[3].on("data", chunk => {
      if (generation !== myGeneration) return;
      pushAudioBuffer(chunk);
    });

    child.stdio[3].on("error", error => {
      if (generation !== myGeneration) return;
      log("AUDIO PIPE ERROR:", error.message);
    });
  }

  child.stderr.on("data", data => {
    if (generation !== myGeneration) return;

    const message = data.toString().trim();

    if (message) {
      log("FFMPEG:", message.slice(0, 400));
    }
  });

  child.on("error", error => {
    if (generation !== myGeneration) return;

    log("FFMPEG ERROR:", error.message);
    ffmpegRunning = false;
  });

  child.on("close", (code, signal) => {
    log("FFMPEG CLOSED:", code, signal);

    // Không cho tiến trình cũ khởi động lại
    if (generation !== myGeneration) return;

    if (ffmpeg === child) {
      ffmpeg = null;
      ffmpegRunning = false;
    }

    if (!manuallyStopped && currentChannel) {
      scheduleRestart(myGeneration);
    }
  });

  startAudioTimer();

  return true;
}

// =====================================================
// RESTART
// =====================================================

function scheduleRestart(expectedGeneration) {
  if (restarting || manuallyStopped || !currentChannel) {
    return;
  }

  restarting = true;
  restartCount++;

  log("SCHEDULE FFMPEG RESTART");

  clearTimeout(restartTimer);

  restartTimer = setTimeout(() => {
    restarting = false;

    if (generation !== expectedGeneration) return;
    if (manuallyStopped || !currentChannel) return;

    try {
      startFFmpeg(currentChannel);
    } catch (error) {
      log("RESTART ERROR:", error.message);
    }
  }, RESTART_DELAY_MS);
}

// =====================================================
// WATCHDOG
// =====================================================

setInterval(() => {
  if (!ffmpegRunning || manuallyStopped || !currentChannel) {
    return;
  }

  const now = Date.now();

  const startupTimeout =
    !lastVideoTime &&
    now - ffmpegStartedAt > WATCHDOG_TIMEOUT_MS;

  const videoTimeout =
    lastVideoTime &&
    now - lastVideoTime > WATCHDOG_TIMEOUT_MS;

  if (startupTimeout || videoTimeout) {
    log("WATCHDOG: VIDEO TIMEOUT");

    if (ffmpeg) {
      try {
        ffmpeg.kill("SIGKILL");
      } catch {}
    }
  }
}, 10000);

// =====================================================
// API CHANNELS
// =====================================================

app.get("/api/channels", (req, res) => {
  if (!channels.length) {
    return res.status(503).json({
      success: false,
      error: "Playlist not loaded",
      channelCount: 0,
      playlistUrl: M3U_URL
    });
  }

  res.json({
    success: true,
    channelCount: channels.length,
    totalChannels: channels.length,
    currentChannel: currentChannel
      ? currentChannel.name
      : null,
    channels: channels.map(channel => ({
      id: channel.id,
      name: channel.name,
      tvgId: channel.tvgId,
      logo: channel.logo,
      group: channel.group
    }))
  });
});

// =====================================================
// API SELECT
// =====================================================

app.get("/api/select/:id", (req, res) => {
  const id = Number(req.params.id);

  if (!Number.isInteger(id) || id < 0) {
    return res.status(400).json({
      success: false,
      error: "ID không hợp lệ"
    });
  }

  const channel = channels.find(item => item.id === id);

  if (!channel) {
    return res.status(404).json({
      success: false,
      error: "Không tìm thấy kênh",
      channelCount: channels.length
    });
  }

  try {
    startFFmpeg(channel);

    res.json({
      success: true,
      message: "Đang chuyển kênh",
      id: channel.id,
      name: channel.name,
      video: "/stream",
      audio: "/audio"
    });

  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// =====================================================
// API STOP
// =====================================================

app.get("/api/stop", (req, res) => {
  manuallyStopped = true;

  stopFFmpeg();

  currentChannel = null;

  res.json({
    success: true,
    status: "stopped"
  });
});

// =====================================================
// API RELOAD PLAYLIST
// =====================================================

app.get("/api/reload", async (req, res) => {
  try {
    const loaded = await loadChannels();

    res.json({
      success: true,
      channelCount: loaded.length,
      channels: loaded.map(channel => ({
        id: channel.id,
        name: channel.name,
        logo: channel.logo,
        group: channel.group
      }))
    });

  } catch (error) {
    res.status(502).json({
      success: false,
      error: error.message,
      channelCount: channels.length
    });
  }
});

// =====================================================
// VIDEO STREAM
// =====================================================

app.get("/stream", (req, res) => {
  res.writeHead(200, {
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Connection": "keep-alive",
    "Pragma": "no-cache",
    "Access-Control-Allow-Origin": "*"
  });

  videoClients.add(res);

  log("VIDEO CLIENT:", videoClients.size);

  if (latestFrame) {
    const header = Buffer.from(
      "--frame\r\n" +
      "Content-Type: image/jpeg\r\n" +
      `Content-Length: ${latestFrame.length}\r\n\r\n`
    );

    res.write(header);
    res.write(latestFrame);
    res.write("\r\n");
  }

  req.on("close", () => {
    videoClients.delete(res);
    log("VIDEO CLIENT CLOSED:", videoClients.size);
  });
});

// =====================================================
// AUDIO STREAM
// =====================================================

app.get("/audio", (req, res) => {
  res.writeHead(200, {
    "Content-Type": "application/octet-stream",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Connection": "keep-alive",
    "Access-Control-Allow-Origin": "*",
    "X-Audio-Format": "PCM-S16LE",
    "X-Audio-Sample-Rate": String(AUDIO_RATE),
    "X-Audio-Channels": String(AUDIO_CHANNELS),
    "X-Audio-Frame-Ms": String(AUDIO_FRAME_MS)
  });

  audioClients.add(res);

  // Client mới cần khởi tạo buffer riêng
  if (audioClients.size === 1) {
    audioPrimed = false;
    audioRecovering = false;
  }

  log("AUDIO CLIENT:", audioClients.size);

  req.on("close", () => {
    audioClients.delete(res);

    log("AUDIO CLIENT CLOSED:", audioClients.size);

    if (audioClients.size === 0) {
      audioPrimed = false;
      audioRecovering = false;
    }
  });
});

// =====================================================
// HEALTH
// =====================================================

app.get("/health", (req, res) => {
  const now = Date.now();

  res.json({
    name: "ESP32 IPTV Server",
    status: "running",

    uptime: Math.floor(
      (now - serverStartedAt) / 1000
    ),

    channelCount: channels.length,
    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning,
    restarting,
    manuallyStopped,
    restartCount,

    pipeline: "REALTIME_MJPEG_PCM_STABLE_BUFFER",

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    videoClients: videoClients.size,
    videoFrames,
    videoDroppedFrames,
    videoInvalidFrames,

    videoLatestFrameBytes: latestFrame
      ? latestFrame.length
      : 0,

    videoLastFrameAgoMs: lastVideoTime
      ? now - lastVideoTime
      : null,

    audioFormat: "PCM_S16LE",
    audioSampleRate: AUDIO_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFrameMs: AUDIO_FRAME_MS,
    audioFrameBytes: AUDIO_FRAME_BYTES,

    audioClients: audioClients.size,
    audioFramesSent,
    audioBufferBytes: audioBuffer.length,
    audioBufferMs: getAudioBufferMs(),

    audioStartBufferMs: AUDIO_START_BUFFER_MS,
    audioRecoveryBufferMs: AUDIO_RECOVERY_BUFFER_MS,

    audioPrimed,
    audioRecovering,
    audioUnderflows,
    audioPrimeCount,

    audioLastDataAgoMs: lastAudioTime
      ? now - lastAudioTime
      : null,

    playlistUrl: M3U_URL
  });
});

// =====================================================
// ROOT
// =====================================================

app.get("/", (req, res) => {
  res.json({
    name: "ESP32 IPTV Server",
    status: "running",
    channelCount: channels.length,

    endpoints: {
      health: "/health",
      channels: "/api/channels",
      select: "/api/select/0",
      stop: "/api/stop",
      reload: "/api/reload",
      video: "/stream",
      audio: "/audio"
    }
  });
});

// =====================================================
// START SERVER
// =====================================================

async function main() {
  app.listen(PORT, "0.0.0.0", () => {
    log("====================================");
    log("ESP32 IPTV SERVER RUNNING");
    log("PORT:", PORT);
    log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}`, VIDEO_FPS, "FPS");
    log("AUDIO:", AUDIO_RATE, "Hz PCM S16LE");
    log("====================================");
  });

  try {
    await loadChannels();

    if (channels.length) {
      startFFmpeg(channels[0]);
    }

  } catch (error) {
    log("INITIAL PLAYLIST ERROR:", error.message);

    const retry = async () => {
      try {
        await loadChannels();

        if (channels.length && !currentChannel) {
          startFFmpeg(channels[0]);
        }

      } catch (retryError) {
        log("PLAYLIST RETRY ERROR:", retryError.message);
        setTimeout(retry, 15000);
      }
    };

    setTimeout(retry, 15000);
  }
}

// =====================================================
// PROCESS EVENTS
// =====================================================

process.on("uncaughtException", error => {
  log("UNCAUGHT EXCEPTION:", error);
});

process.on("unhandledRejection", error => {
  log("UNHANDLED REJECTION:", error);
});

process.on("SIGTERM", () => {
  log("SIGTERM");
  manuallyStopped = true;
  stopFFmpeg();
  stopAudioTimer();
  process.exit(0);
});

process.on("SIGINT", () => {
  log("SIGINT");
  manuallyStopped = true;
  stopFFmpeg();
  stopAudioTimer();
  process.exit(0);
});

main();
