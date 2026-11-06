
const express = require("express");
const { spawn } = require("child_process");

const app = express();
app.use(express.json());

const PORT = process.env.PORT || 3000;
const FFMPEG_PATH = process.env.FFMPEG_PATH || "ffmpeg";

// ==================== CẤU HÌNH ====================

const M3U_SOURCES = [
  "https://raw.githubusercontent.com/ankiusdsdvg/6/main/relaybongden.m3u",
  "https://iptv-org.github.io/iptv/countries/vn.m3u"
];

const VIDEO_WIDTH = 320;
const VIDEO_HEIGHT = 180;
const VIDEO_FPS = 8;
const JPEG_QUALITY = 8;

const AUDIO_RATE = 16000;
const AUDIO_CHANNELS = 1;
const AUDIO_FRAME_MS = 200;

const AUDIO_FRAME_BYTES =
  AUDIO_RATE * AUDIO_CHANNELS * 2 * AUDIO_FRAME_MS / 1000;

// Chỉ giữ tối đa 200ms audio
const MAX_AUDIO_BUFFER = AUDIO_FRAME_BYTES;

// Video
const MAX_JPEG_BYTES = 256 * 1024;
const MAX_VIDEO_PENDING_BYTES = 512 * 1024;
const MAX_VIDEO_CLIENT_BUFFER = 300 * 1024;
const VIDEO_CLIENT_TIMEOUT_MS = 1000;

// Audio
const AUDIO_CLIENT_TIMEOUT_MS = 1000;

// Render
const RENDER_API_KEY = process.env.RENDER_API_KEY || "rnd_UybRGTZIqEAqpRaUxkylcFUR2MLu";
const RENDER_SERVICE_ID = "srv-dbktk7s9v7es73fb7fcg";
const RENDER_MONTHLY_LIMIT_GB = 5;

// ==================== BIẾN TOÀN CỤC ====================

let channels = [];
let currentChannel = null;
let ffmpegProcess = null;
let ffmpegStartedAt = null;
let manuallyStopped = false;

let latestFrame = null;
let videoFrameCount = 0;
let lastVideoFrameAt = 0;
let jpegPending = Buffer.alloc(0);

let audioBuffer = Buffer.alloc(0);
let audioRemainder = Buffer.alloc(0);
let audioClient = null;
let audioBlocked = false;

let videoClients = 0;
let ffmpegError = "";

let audioDroppedBytes = 0;
let audioSentFrames = 0;
let videoDroppedClients = 0;

// ==================== M3U ====================

function parseM3U(content) {
  const lines = content.split(/\r?\n/);
  const result = [];

  let info = null;
  let id = 0;

  for (const rawLine of lines) {
    const line = rawLine.trim();

    if (!line) continue;

    if (line.startsWith("#EXTINF:")) {
      const nameMatch = line.match(/,(.*)$/);
      const groupMatch = line.match(/group-title="([^"]*)"/i);
      const logoMatch = line.match(/tvg-logo="([^"]*)"/i);
      const tvgIdMatch = line.match(/tvg-id="([^"]*)"/i);

      info = {
        name: nameMatch ? nameMatch[1].trim() : "Unknown",
        group: groupMatch ? groupMatch[1] : "",
        logo: logoMatch ? logoMatch[1] : "",
        tvgId: tvgIdMatch ? tvgIdMatch[1] : "",
        resolution: ""
      };

      continue;
    }

    if (line.startsWith("#")) continue;

    if (/^https?:\/\//i.test(line)) {
      const channel = info || {
        name: "Channel",
        group: "",
        logo: "",
        tvgId: "",
        resolution: ""
      };

      const resolutionMatch = line.match(/(\d{3,4})[xX](\d{3,4})/);

      result.push({
        id: String(id++),
        name: channel.name,
        group: channel.group,
        logo: channel.logo,
        tvgId: channel.tvgId,
        resolution: resolutionMatch ? resolutionMatch[0] : "",
        url: line
      });

      info = null;
    }
  }

  return result;
}

async function loadChannels() {
  const allChannels = [];
  const seenUrls = new Set();

  for (const source of M3U_SOURCES) {
    try {
      const response = await fetch(source, {
        signal: AbortSignal.timeout(20000)
      });

      if (!response.ok) {
        console.error("M3U error:", response.status, source);
        continue;
      }

      const content = await response.text();
      const parsed = parseM3U(content);

      for (const channel of parsed) {
        if (seenUrls.has(channel.url)) continue;

        seenUrls.add(channel.url);
        allChannels.push(channel);
      }

      console.log(`Loaded ${parsed.length} channels from ${source}`);

    } catch (error) {
      console.error("M3U load failed:", source, error.message);
    }
  }

  channels = allChannels.map((channel, index) => ({
    ...channel,
    id: String(index)
  }));

  console.log("Total channels:", channels.length);

  return channels.length;
}

// ==================== VIDEO JPEG PARSER ====================

function processVideoData(chunk) {
  if (!chunk || !chunk.length) return;

  jpegPending = Buffer.concat([jpegPending, chunk]);

  while (jpegPending.length >= 4) {
    const start = jpegPending.indexOf(
      Buffer.from([0xff, 0xd8])
    );

    if (start === -1) {
      const keepLast =
        jpegPending[jpegPending.length - 1] === 0xff;

      jpegPending = keepLast
        ? jpegPending.subarray(jpegPending.length - 1)
        : Buffer.alloc(0);

      return;
    }

    if (start > 0) {
      jpegPending = jpegPending.subarray(start);
    }

    const end = jpegPending.indexOf(
      Buffer.from([0xff, 0xd9]),
      2
    );

    if (end === -1) {
      if (jpegPending.length > MAX_JPEG_BYTES) {
        const nextStart = jpegPending.indexOf(
          Buffer.from([0xff, 0xd8]),
          2
        );

        if (nextStart !== -1) {
          jpegPending = jpegPending.subarray(nextStart);
          continue;
        }

        jpegPending = Buffer.alloc(0);
      }

      if (jpegPending.length > MAX_VIDEO_PENDING_BYTES) {
        jpegPending = Buffer.alloc(0);
      }

      return;
    }

    const frameLength = end + 2;

    if (frameLength <= MAX_JPEG_BYTES) {
      // Luôn thay bằng frame mới nhất
      latestFrame = Buffer.from(
        jpegPending.subarray(0, frameLength)
      );

      videoFrameCount++;
      lastVideoFrameAt = Date.now();
    }

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// ==================== AUDIO LIVE BUFFER ====================

function clearAudioBuffer() {
  audioDroppedBytes += audioBuffer.length;

  audioBuffer = Buffer.alloc(0);
  audioRemainder = Buffer.alloc(0);
}

// Không lưu audio khi không có client.
// Không lưu dữ liệu trong lúc client đang nghẽn.

function processAudioData(chunk) {
  if (!chunk || !chunk.length) return;

  if (!audioClient || audioClient.destroyed || audioBlocked) {
    audioDroppedBytes += chunk.length;
    return;
  }

  let data = chunk;

  // Xử lý PCM 16-bit nếu chunk bị chia lẻ byte
  if (audioRemainder.length) {
    data = Buffer.concat([audioRemainder, chunk]);
    audioRemainder = Buffer.alloc(0);
  }

  if (data.length % 2 !== 0) {
    audioRemainder = Buffer.from(
      data.subarray(data.length - 1)
    );

    data = data.subarray(0, data.length - 1);
  }

  if (!data.length) return;

  audioBuffer = Buffer.concat([audioBuffer, data]);

  // Chỉ giữ phần dữ liệu mới nhất
  if (audioBuffer.length > MAX_AUDIO_BUFFER) {
    const removeBytes =
      audioBuffer.length - MAX_AUDIO_BUFFER;

    const alignedRemoveBytes =
      removeBytes + (removeBytes % 2);

    audioDroppedBytes += alignedRemoveBytes;

    audioBuffer = audioBuffer.subarray(
      alignedRemoveBytes
    );
  }
}

// Lấy một frame PCM.
// Nếu thiếu dữ liệu thì lấp bằng silence (0),
// không lặp lại mẫu âm thanh cũ.

function getAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);

  const available = Math.min(
    audioBuffer.length - (audioBuffer.length % 2),
    AUDIO_FRAME_BYTES
  );

  if (available > 0) {
    audioBuffer.copy(frame, 0, 0, available);

    audioBuffer = audioBuffer.subarray(available);
  }

  return frame;
}

// ==================== DỪNG FFMPEG ====================

function stopFFmpeg() {
  if (ffmpegProcess) {
    try {
      ffmpegProcess.kill("SIGKILL");
    } catch (_) {}
  }

  ffmpegProcess = null;
  currentChannel = null;

  latestFrame = null;
  jpegPending = Buffer.alloc(0);

  clearAudioBuffer();

  audioBlocked = false;
  lastVideoFrameAt = 0;
}

// ==================== CHẠY FFMPEG ====================

function startFFmpeg(channel) {
  if (!channel || !channel.url) {
    throw new Error("Invalid channel");
  }

  stopFFmpeg();

  manuallyStopped = false;
  ffmpegError = "";

  videoFrameCount = 0;
  ffmpegStartedAt = Date.now();

  currentChannel = channel;

  const args = [
    "-hide_banner",
    "-loglevel", "warning",

    // INPUT
    "-fflags", "+discardcorrupt+genpts+nobuffer",
    "-flags", "low_delay",
    "-probesize", "1000000",
    "-analyzeduration", "1000000",
    "-rw_timeout", "15000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "3",

    "-i", channel.url,

    // ================= VIDEO =================

    "-map", "0:v:0?",

    "-vf",
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease,pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2,fps=${VIDEO_FPS}`,

    "-an",
    "-c:v", "mjpeg",
    "-q:v", String(JPEG_QUALITY),
    "-threads", "1",
    "-f", "image2pipe",
    "-flush_packets", "1",
    "pipe:1",

    // ================= AUDIO =================

    "-map", "0:a:0?",
    "-vn",

    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_RATE),

    "-acodec", "pcm_s16le",
    "-threads", "1",
    "-f", "s16le",
    "-flush_packets", "1",
    "pipe:3"
  ];

  console.log("Starting FFmpeg:", channel.name);

  const child = spawn(FFMPEG_PATH, args, {
    stdio: ["ignore", "pipe", "pipe", "pipe"]
  });

  ffmpegProcess = child;

  child.stdout.on("data", processVideoData);

  if (child.stdio[3]) {
    child.stdio[3].on("data", processAudioData);
  }

  child.stderr.on("data", data => {
    const message = data.toString().trim();

    if (message) {
      ffmpegError = message.slice(-1000);
      console.error("FFmpeg:", message);
    }
  });

  child.on("error", error => {
    console.error("FFmpeg spawn error:", error.message);

    ffmpegError = error.message;

    if (ffmpegProcess === child) {
      ffmpegProcess = null;
    }
  });

  child.on("close", (code, signal) => {
    console.log(
      `FFmpeg closed: code=${code}, signal=${signal}`
    );

    if (ffmpegProcess === child) {
      ffmpegProcess = null;
    }

    if (!manuallyStopped) {
      ffmpegError =
        ffmpegError || `FFmpeg stopped (${code})`;
    }
  });

  return true;
}

// ==================== MJPEG STREAM ====================

app.get("/stream", (req, res) => {
  res.status(200);

  res.set({
    "Content-Type": "multipart/x-mixed-replace; boundary=frame",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Pragma": "no-cache",
    "Expires": "0",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  res.flushHeaders?.();

  videoClients++;

  let closed = false;
  let lastSentFrame = -1;
  let blockedSince = 0;

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    // Client đang nghẽn
    if (res.writableNeedDrain) {
      if (!blockedSince) {
        blockedSince = Date.now();
      }

      if (
        Date.now() - blockedSince >
        VIDEO_CLIENT_TIMEOUT_MS
      ) {
        videoDroppedClients++;
        cleanup();
        res.destroy();
      }

      return;
    }

    blockedSince = 0;

    if (
      res.writableLength > MAX_VIDEO_CLIENT_BUFFER
    ) {
      videoDroppedClients++;
      cleanup();
      res.destroy();
      return;
    }

    if (!latestFrame) return;

    if (lastSentFrame === videoFrameCount) return;

    // Luôn gửi frame mới nhất, bỏ qua frame cũ
    const frame = latestFrame;

    const header = Buffer.from(
      `--frame\r\n` +
      `Content-Type: image/jpeg\r\n` +
      `Content-Length: ${frame.length}\r\n\r\n`
    );

    const packet = Buffer.concat([
      header,
      frame,
      Buffer.from("\r\n")
    ]);

    lastSentFrame = videoFrameCount;

    const accepted = res.write(packet);

    if (!accepted) {
      blockedSince = Date.now();
    }

  }, Math.floor(1000 / VIDEO_FPS));

  function cleanup() {
    if (closed) return;

    closed = true;

    clearInterval(timer);

    videoClients = Math.max(0, videoClients - 1);
  }

  res.on("close", cleanup);
  res.on("error", cleanup);
});

// ==================== AUDIO STREAM ====================

app.get("/audio", (req, res) => {
  // Chỉ một audio client
  if (audioClient && !audioClient.destroyed) {
    audioClient.destroy();
  }

  // Không phát lại dữ liệu của phiên trước
  clearAudioBuffer();

  audioBlocked = false;

  res.status(200);

  res.set({
    "Content-Type": "audio/pcm; rate=16000; channels=1",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  res.flushHeaders?.();

  audioClient = res;

  let closed = false;
  let blockedSince = 0;

  // Khi socket sẵn sàng trở lại,
  // bỏ dữ liệu cũ và chỉ nhận dữ liệu mới.
  res.on("drain", () => {
    if (closed) return;

    clearAudioBuffer();

    audioBlocked = false;
    blockedSince = 0;
  });

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    // Client không đọc kịp
    if (res.writableNeedDrain) {
      audioBlocked = true;

      // Không giữ dữ liệu audio tồn đọng
      clearAudioBuffer();

      if (!blockedSince) {
        blockedSince = Date.now();
      }

      if (
        Date.now() - blockedSince >
        AUDIO_CLIENT_TIMEOUT_MS
      ) {
        cleanup();
        res.destroy();
      }

      return;
    }

    if (
      res.writableLength > AUDIO_FRAME_BYTES * 2
    ) {
      audioBlocked = true;

      clearAudioBuffer();

      cleanup();
      res.destroy();

      return;
    }

    blockedSince = 0;
    audioBlocked = false;

    // Không có dữ liệu thì phát silence,
    // không phát lại dữ liệu cũ.
    const frame = getAudioFrame();

    const accepted = res.write(frame);

    audioSentFrames++;

    if (!accepted) {
      audioBlocked = true;
      clearAudioBuffer();
      blockedSince = Date.now();
    }

  }, AUDIO_FRAME_MS);

  function cleanup() {
    if (closed) return;

    closed = true;

    clearInterval(timer);

    if (audioClient === res) {
      audioClient = null;

      audioBlocked = false;

      clearAudioBuffer();
    }
  }

  res.on("close", cleanup);
  res.on("error", cleanup);
});

// ==================== API CHANNELS ====================

app.get("/api/channels", (req, res) => {
  res.json({
    success: true,
    quality: `${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}fps`,
    channels
  });
});

async function selectChannel(req, res) {
  let id;

  try {
    id = decodeURIComponent(req.params.id || "");
  } catch (_) {
    return res.status(400).json({
      success: false,
      error: "Invalid channel ID"
    });
  }

  const channel = channels.find(item =>
    item.id === id ||
    item.name.toLowerCase() === id.toLowerCase()
  );

  if (!channel) {
    return res.status(404).json({
      success: false,
      error: "Channel not found"
    });
  }

  try {
    startFFmpeg(channel);

    return res.json({
      success: true,
      channel
    });

  } catch (error) {
    return res.status(500).json({
      success: false,
      error: error.message
    });
  }
}

app.get("/api/select/:id", selectChannel);
app.post("/api/select/:id", selectChannel);

// ==================== API STOP ====================

function stopHandler(req, res) {
  manuallyStopped = true;

  stopFFmpeg();

  res.json({
    success: true,
    message: "Stopped"
  });
}

app.get("/api/stop", stopHandler);
app.post("/api/stop", stopHandler);

// ==================== API RELOAD ====================

async function reloadHandler(req, res) {
  try {
    const count = await loadChannels();

    res.json({
      success: true,
      count
    });

  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
}

app.get("/api/reload", reloadHandler);
app.post("/api/reload", reloadHandler);

// ==================== HEALTH ====================

app.get("/health", (req, res) => {
  const frameAge = lastVideoFrameAt
    ? Date.now() - lastVideoFrameAt
    : null;

  res.json({
    success: true,

    status: ffmpegProcess ? "running" : "stopped",

    channel: currentChannel
      ? currentChannel.name
      : null,

    ffmpegRunning: !!ffmpegProcess,

    ffmpegPid: ffmpegProcess
      ? ffmpegProcess.pid
      : null,

    video: {
      width: VIDEO_WIDTH,
      height: VIDEO_HEIGHT,
      fps: VIDEO_FPS,
      frameCount: videoFrameCount,
      frameAgeMs: frameAge,
      pendingBytes: jpegPending.length,
      clients: videoClients,
      droppedClients: videoDroppedClients
    },

    audio: {
      sampleRate: AUDIO_RATE,
      channels: AUDIO_CHANNELS,
      frameMs: AUDIO_FRAME_MS,
      bufferBytes: audioBuffer.length,

      bufferMs: Math.round(
        audioBuffer.length / (AUDIO_RATE * 2) * 1000
      ),

      connected: !!audioClient,

      blocked: audioBlocked,

      droppedBytes: audioDroppedBytes,

      sentFrames: audioSentFrames
    },

    ffmpegError,

    uptime: process.uptime()
  });
});

// ==================== RENDER BANDWIDTH ====================

function getCurrentMonthRange() {
  const now = new Date();

  const start = new Date(
    Date.UTC(
      now.getUTCFullYear(),
      now.getUTCMonth(),
      1
    )
  );

  return {
    startTime: start.toISOString(),
    endTime: now.toISOString()
  };
}

app.get("/api/bandwidth", async (req, res) => {
  if (!RENDER_API_KEY) {
    return res.status(503).json({
      success: false,
      error: "Missing RENDER_API_KEY environment variable"
    });
  }

  try {
    const period = getCurrentMonthRange();

    const params = new URLSearchParams({
      startTime: period.startTime,
      endTime: period.endTime
    });

    params.append("resource", RENDER_SERVICE_ID);

    const response = await fetch(
      `https://api.render.com/v1/metrics/bandwidth?${params}`,
      {
        method: "GET",

        headers: {
          "Authorization": `Bearer ${RENDER_API_KEY}`,
          "Accept": "application/json"
        },

        signal: AbortSignal.timeout(20000)
      }
    );

    const raw = await response.text();

    let data;

    try {
      data = JSON.parse(raw);
    } catch (_) {
      data = raw;
    }

    if (!response.ok) {
      return res.status(response.status).json({
        success: false,
        error: "Render API request failed",
        details: data
      });
    }

    res.json({
      success: true,
      period,
      monthlyLimitGB: RENDER_MONTHLY_LIMIT_GB,
      serviceId: RENDER_SERVICE_ID,
      data
    });

  } catch (error) {
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// ==================== TRANG CHỦ ====================

app.get("/", (req, res) => {
  res.json({
    name: "IPTV Streaming Server",

    success: true,

    endpoints: {
      stream: "/stream",
      audio: "/audio",
      channels: "/api/channels",
      select: "/api/select/:id",
      stop: "/api/stop",
      reload: "/api/reload",
      health: "/health",
      bandwidth: "/api/bandwidth"
    }
  });
});

// ==================== START SERVER ====================

async function startServer() {
  await loadChannels();

  app.listen(PORT, "0.0.0.0", () => {
    console.log(`Server running on port ${PORT}`);
    console.log(`Channels loaded: ${channels.length}`);

    console.log(
      `Video: ${VIDEO_WIDTH}x${VIDEO_HEIGHT}@${VIDEO_FPS}fps`
    );

    console.log(
      `Audio: ${AUDIO_RATE}Hz / ${AUDIO_FRAME_MS}ms frames`
    );

    console.log("Live buffer mode: ENABLED");
  });
}

startServer().catch(error => {
  console.error("Server startup error:", error);
  process.exit(1);
});

// ==================== PROCESS CLEANUP ====================

process.on("SIGTERM", () => {
  manuallyStopped = true;
  stopFFmpeg();
  process.exit(0);
});

process.on("SIGINT", () => {
  manuallyStopped = true;
  stopFFmpeg();
  process.exit(0);
});
