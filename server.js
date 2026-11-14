

const express = require("express");
const { spawn } = require("child_process");

const app = express();
const PORT = Number(process.env.PORT || 10000);

// =====================================================
// CONFIG
// =====================================================

const M3U_URL =
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u";

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 240;
const VIDEO_FPS = 12;
const VIDEO_JPEG_QUALITY = 8;

const AUDIO_SAMPLE_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_BYTES_PER_SAMPLE = 2;

// 40ms PCM = 1280 bytes at 16kHz mono S16LE
const AUDIO_FRAME_MS = 40;
const AUDIO_FRAME_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_FRAME_MS / 1000;

const AUDIO_START_BUFFER_MS = 500;
const AUDIO_MAX_BUFFER_MS = 2500;

const AUDIO_MAX_BUFFER_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_MAX_BUFFER_MS / 1000;

const PLAYLIST_RETRIES = 3;
const PLAYLIST_TIMEOUT_MS = 30000;

const FFMPEG_RESTART_DELAY = 3000;
const FFMPEG_WATCHDOG_MS = 45000;

app.use(express.json({ limit: "32kb" }));

// =====================================================
// GLOBAL STATE
// =====================================================

let channels = [];
let currentChannel = null;

let ffmpeg = null;
let ffmpegRunning = false;
let manuallyStopped = false;
let restarting = false;

let videoClients = new Set();
let audioClients = new Set();

let latestFrame = null;
let latestFrameTime = 0;

let audioBuffer = Buffer.alloc(0);
let audioTimer = null;
let audioPrimed = false;
let audioRecovering = false;

let ffmpegStartedAt = 0;
let lastVideoTime = 0;
let lastAudioTime = 0;

let videoFrames = 0;
let videoDroppedFrames = 0;
let videoInvalidFrames = 0;
let audioFramesSent = 0;
let audioUnderflows = 0;

let totalMessages = 0;
let restartCount = 0;

let serverStartedAt = Date.now();

// =====================================================
// HELPERS
// =====================================================

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function log(...args) {
  console.log(new Date().toISOString(), ...args);
}

function getAudioBufferMs() {
  return Math.round(
    audioBuffer.length /
    (AUDIO_SAMPLE_RATE * AUDIO_CHANNELS * AUDIO_BYTES_PER_SAMPLE) *
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
// LOAD M3U PLAYLIST
// =====================================================

function parseM3U(data) {
  const lines = data
    .replace(/^\uFEFF/, "")
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(Boolean);

  if (!lines.some(line => line.startsWith("#EXTM3U"))) {
    throw new Error("Playlist không có header #EXTM3U");
  }

  const result = [];
  let pendingInfo = null;

  for (const line of lines) {
    if (line.startsWith("#EXTINF:")) {
      pendingInfo = line;
      continue;
    }

    if (
      line.startsWith("#") ||
      !/^https?:\/\//i.test(line)
    ) {
      continue;
    }

    if (!pendingInfo) {
      continue;
    }

    const commaIndex = pendingInfo.indexOf(",");
    const name = commaIndex >= 0
      ? pendingInfo.substring(commaIndex + 1).trim()
      : "Kênh không tên";

    const id = result.length;

    const tvgId =
      (pendingInfo.match(/tvg-id="([^"]*)"/i) || [])[1] || "";

    const logo =
      (pendingInfo.match(/tvg-logo="([^"]*)"/i) || [])[1] || "";

    const group =
      (pendingInfo.match(/group-title="([^"]*)"/i) || [])[1] || "";

    result.push({
      id,
      name: name || `Channel ${id + 1}`,
      url: line,
      tvgId,
      logo,
      group
    });

    pendingInfo = null;
  }

  if (result.length === 0) {
    throw new Error("Không tìm thấy kênh hợp lệ trong M3U");
  }

  return result;
}

async function loadChannels() {
  let lastError = null;

  for (let attempt = 1; attempt <= PLAYLIST_RETRIES; attempt++) {
    try {
      log(`Đang tải playlist lần ${attempt}/${PLAYLIST_RETRIES}`);

      const controller = new AbortController();
      const timeout = setTimeout(
        () => controller.abort(),
        PLAYLIST_TIMEOUT_MS
      );

      let response;

      try {
        response = await fetch(M3U_URL, {
          method: "GET",
          headers: {
            "User-Agent": "Mozilla/5.0 IPTV-Server",
            "Accept": "*/*",
            "Cache-Control": "no-cache"
          },
          signal: controller.signal
        });
      } finally {
        clearTimeout(timeout);
      }

      if (!response.ok) {
        throw new Error(`HTTP ${response.status}`);
      }

      const data = await response.text();

      if (!data || data.length < 10) {
        throw new Error("Playlist rỗng hoặc quá ngắn");
      }

      const loaded = parseM3U(data);

      // Chỉ thay danh sách khi tải và phân tích thành công
      channels = loaded;

      log(`TẢI PLAYLIST THÀNH CÔNG: ${channels.length} KÊNH`);

      return channels;

    } catch (error) {
      lastError = error;
      log(`Lỗi tải playlist lần ${attempt}:`, error.message);

      if (attempt < PLAYLIST_RETRIES) {
        await sleep(2000);
      }
    }
  }

  throw lastError || new Error("Không tải được playlist");
}

// =====================================================
// VIDEO MJPEG PARSER
// =====================================================

let videoPending = Buffer.alloc(0);

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

    if (
      frame.length < 100 ||
      frame.length > 512 * 1024
    ) {
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
      const ok = client.write(header) && client.write(frame) &&
        client.write("\r\n");

      if (!ok) {
        videoDroppedFrames++;
      }
    } catch {
      videoClients.delete(client);
    }
  }
}

// =====================================================
// AUDIO BUFFER
// =====================================================

function pushAudioBuffer(chunk) {
  if (!chunk || chunk.length === 0) return;

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

  // Chờ đủ dữ liệu trước khi bắt đầu phát
  if (!audioPrimed) {
    if (audioBuffer.length < AUDIO_FRAME_BYTES *
      (AUDIO_START_BUFFER_MS / AUDIO_FRAME_MS)) {
      audioRecovering = true;
      return;
    }

    audioPrimed = true;
    audioRecovering = false;
    log("AUDIO BUFFER READY");
  }

  let frame;

  if (audioBuffer.length >= AUDIO_FRAME_BYTES) {
    frame = audioBuffer.subarray(0, AUDIO_FRAME_BYTES);
    audioBuffer = audioBuffer.subarray(AUDIO_FRAME_BYTES);
    audioRecovering = false;
  } else {
    // Giữ nhịp PCM liên tục khi buffer hụt
    // Không phát lại dữ liệu cũ
    frame = Buffer.alloc(AUDIO_FRAME_BYTES);
    audioUnderflows++;
    audioRecovering = true;
  }

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
// STOP FFMPEG
// =====================================================

function stopFFmpeg() {
  if (ffmpeg) {
    try {
      ffmpeg.kill("SIGKILL");
    } catch {}
  }

  ffmpeg = null;
  ffmpegRunning = false;

  videoPending = Buffer.alloc(0);
  clearAudioState();
}

// =====================================================
// START FFMPEG
// =====================================================

function startFFmpeg(channel) {
  if (!channel || !channel.url) {
    throw new Error("Kênh không hợp lệ");
  }

  stopFFmpeg();

  currentChannel = channel;
  manuallyStopped = false;

  latestFrame = null;
  latestFrameTime = 0;
  videoPending = Buffer.alloc(0);

  clearAudioState();

  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    "-fflags", "nobuffer",
    "-flags", "low_delay",
    "-thread_queue_size", "512",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_at_eof", "1",
    "-reconnect_delay_max", "5",
    "-rw_timeout", "15000000",

    "-i", channel.url,

    // VIDEO OUTPUT
    "-map", "0:v:0?",
    "-an",
    "-vf",
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease,pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2,fps=${VIDEO_FPS}`,
    "-q:v", String(VIDEO_JPEG_QUALITY),
    "-f", "image2pipe",
    "-vcodec", "mjpeg",
    "pipe:1",

    // AUDIO OUTPUT
    "-map", "0:a:0?",
    "-vn",
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_SAMPLE_RATE),
    "-c:a", "pcm_s16le",
    "-f", "s16le",
    "pipe:3"
  ];

  log("START FFMPEG:", channel.name);

  const child = spawn("ffmpeg", args, {
    stdio: ["ignore", "pipe", "pipe", "pipe"]
  });

  ffmpeg = child;
  ffmpegRunning = true;
  ffmpegStartedAt = Date.now();

  child.stdout.on("data", handleVideoData);

  if (child.stdio[3]) {
    child.stdio[3].on("data", pushAudioBuffer);
    child.stdio[3].on("error", error => {
      log("Audio pipe error:", error.message);
    });
  }

  child.stderr.on("data", data => {
    const message = data.toString().trim();

    if (message) {
      log("FFMPEG:", message.slice(0, 500));
    }
  });

  child.on("error", error => {
    log("FFMPEG ERROR:", error.message);
    ffmpegRunning = false;
  });

  child.on("close", (code, signal) => {
    log("FFMPEG CLOSED:", code, signal);

    if (ffmpeg === child) {
      ffmpeg = null;
      ffmpegRunning = false;
    }

    if (!manuallyStopped && currentChannel) {
      scheduleRestart();
    }
  });

  startAudioTimer();

  return true;
}

// =====================================================
// AUTO RESTART
// =====================================================

let restartTimer = null;

function scheduleRestart() {
  if (restarting || manuallyStopped || !currentChannel) {
    return;
  }

  restarting = true;
  restartCount++;

  log(`FFMPEG RESTART IN ${FFMPEG_RESTART_DELAY}ms`);

  clearTimeout(restartTimer);

  restartTimer = setTimeout(() => {
    restarting = false;

    if (!manuallyStopped && currentChannel) {
      try {
        startFFmpeg(currentChannel);
      } catch (error) {
        log("RESTART ERROR:", error.message);
        scheduleRestart();
      }
    }
  }, FFMPEG_RESTART_DELAY);
}

// =====================================================
// WATCHDOG
// =====================================================

setInterval(() => {
  if (!ffmpegRunning || manuallyStopped || !currentChannel) {
    return;
  }

  const now = Date.now();

  const videoIdle =
    lastVideoTime > 0 &&
    now - lastVideoTime > FFMPEG_WATCHDOG_MS;

  const startupTimeout =
    lastVideoTime === 0 &&
    now - ffmpegStartedAt > FFMPEG_WATCHDOG_MS;

  if (videoIdle || startupTimeout) {
    log("WATCHDOG: VIDEO TIMEOUT");

    if (ffmpeg) {
      try {
        ffmpeg.kill("SIGKILL");
      } catch {}
    }
  }
}, 10000);

// =====================================================
// API: CHANNELS
// =====================================================

app.get("/api/channels", (req, res) => {
  if (!channels.length) {
    return res.status(503).json({
      success: false,
      error: "Playlist not loaded",
      playlistUrl: M3U_URL,
      channelCount: 0
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
// API: SELECT CHANNEL
// =====================================================

app.get("/api/select/:id", (req, res) => {
  const id = Number(req.params.id);

  if (!Number.isInteger(id) || id < 0) {
    return res.status(400).json({
      success: false,
      error: "Channel ID không hợp lệ"
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
      message: "Đã chọn kênh",
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
// API: STOP
// =====================================================

app.get("/api/stop", (req, res) => {
  manuallyStopped = true;

  clearTimeout(restartTimer);
  restarting = false;

  stopFFmpeg();

  currentChannel = null;
  latestFrame = null;

  res.json({
    success: true,
    status: "stopped"
  });
});

// =====================================================
// API: RELOAD PLAYLIST
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

  log("VIDEO CLIENT CONNECTED:", videoClients.size);

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
    log("VIDEO CLIENT DISCONNECTED:", videoClients.size);
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
    "X-Audio-Sample-Rate": String(AUDIO_SAMPLE_RATE),
    "X-Audio-Channels": String(AUDIO_CHANNELS)
  });

  audioClients.add(res);

  log("AUDIO CLIENT CONNECTED:", audioClients.size);

  req.on("close", () => {
    audioClients.delete(res);
    log("AUDIO CLIENT DISCONNECTED:", audioClients.size);

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
  res.json({
    name: "ESP32 IPTV Server",
    status: "running",

    uptime: Math.floor(
      (Date.now() - serverStartedAt) / 1000
    ),

    channelCount: channels.length,
    currentChannel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning,
    restarting,
    manuallyStopped,
    restartCount,

    pipeline: "REALTIME_MJPEG_PCM",

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
      ? Date.now() - lastVideoTime
      : null,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFormat: "PCM_S16LE",
    audioFrameMs: AUDIO_FRAME_MS,
    audioFrameBytes: AUDIO_FRAME_BYTES,

    audioClients: audioClients.size,
    audioFramesSent,
    audioBufferBytes: audioBuffer.length,
    audioBufferMs: getAudioBufferMs(),
    audioPrimed,
    audioRecovering,
    audioUnderflows,

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
  // Mở HTTP server trước để Render không đánh dấu service lỗi
  app.listen(PORT, "0.0.0.0", () => {
    log("======================================");
    log("ESP32 IPTV SERVER RUNNING");
    log("PORT:", PORT);
    log("VIDEO:", `${VIDEO_WIDTH}x${VIDEO_HEIGHT}`, VIDEO_FPS, "FPS");
    log("AUDIO:", AUDIO_SAMPLE_RATE, "Hz PCM S16LE MONO");
    log("PLAYLIST:", M3U_URL);
    log("======================================");
  });

  try {
    await loadChannels();

    if (channels.length > 0) {
      startFFmpeg(channels[0]);
    }

  } catch (error) {
    log("PLAYLIST LOAD FAILED:", error.message);
    log("Server vẫn chạy; sẽ thử tải lại sau 15 giây.");

    setTimeout(async function retryPlaylist() {
      try {
        await loadChannels();

        if (channels.length > 0 && !currentChannel) {
          startFFmpeg(channels[0]);
        }

      } catch (retryError) {
        log("PLAYLIST RETRY FAILED:", retryError.message);
        setTimeout(retryPlaylist, 15000);
      }
    }, 15000);
  }
}

process.on("uncaughtException", error => {
  log("UNCAUGHT EXCEPTION:", error);
});

process.on("unhandledRejection", error => {
  log("UNHANDLED REJECTION:", error);
});

process.on("SIGTERM", () => {
  log("SIGTERM RECEIVED");
  manuallyStopped = true;
  stopFFmpeg();
  process.exit(0);
});

process.on("SIGINT", () => {
  log("SIGINT RECEIVED");
  manuallyStopped = true;
  stopFFmpeg();
  process.exit(0);
});

main();
