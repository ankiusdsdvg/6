
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

// Bộ đệm video chỉ giữ dữ liệu cần thiết
const MAX_JPEG_BYTES = 256 * 1024;
const MAX_VIDEO_PENDING_BYTES = 512 * 1024;
const MAX_VIDEO_CLIENT_BUFFER = 300 * 1024;
const VIDEO_CLIENT_TIMEOUT_MS = 1500;

// Audio giữ tối đa khoảng 800ms
const MAX_AUDIO_BUFFER = Math.floor(AUDIO_RATE * 2 * 0.8);

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
let lastAudioSample = Buffer.from([0, 0]);
let audioClient = null;

let videoClients = 0;
let ffmpegError = "";

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

      console.log(
        `Loaded ${parsed.length} channels from ${source}`
      );
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
      // Giữ lại byte cuối nếu có thể là đầu marker JPEG
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
      // Copy để không giữ lại vùng nhớ của buffer parser
      latestFrame = Buffer.from(
        jpegPending.subarray(0, frameLength)
      );

      videoFrameCount++;
      lastVideoFrameAt = Date.now();
    }

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// ==================== AUDIO BUFFER ====================

function processAudioData(chunk) {
  if (!chunk || !chunk.length) return;

  // Giữ mẫu âm thanh cuối để lấp phần frame còn thiếu
  if (chunk.length >= 2) {
    lastAudioSample = Buffer.from(
      chunk.subarray(chunk.length - 2)
    );
  }

  audioBuffer = Buffer.concat([audioBuffer, chunk]);

  if (audioBuffer.length > MAX_AUDIO_BUFFER) {
    let removeBytes =
      audioBuffer.length - MAX_AUDIO_BUFFER;

    // PCM 16-bit cần số byte chẵn
    if (removeBytes % 2 !== 0) removeBytes++;

    audioBuffer = audioBuffer.subarray(removeBytes);
  }
}

function getAudioFrame() {
  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);

  const available = Math.min(
    audioBuffer.length - (audioBuffer.length % 2),
    AUDIO_FRAME_BYTES
  );

  if (available > 0) {
    audioBuffer.copy(frame, 0, 0, available);

    lastAudioSample = Buffer.from(
      audioBuffer.subarray(available - 2, available)
    );

    audioBuffer = audioBuffer.subarray(available);
  }

  // Lấp phần thiếu bằng mẫu cuối, không ghi đè phần đã copy
  for (let i = available; i < AUDIO_FRAME_BYTES; i += 2) {
    frame[i] = lastAudioSample[0];
    frame[i + 1] = lastAudioSample[1];
  }

  return frame;
}

// ==================== DỪNG FFMPEG ====================

function stopFFmpeg() {
  if (ffmpegProcess) {
    try {
      ffmpegProcess.kill("SIGKILL");
    } catch (_) {
      // Process có thể đã kết thúc
    }
  }

  ffmpegProcess = null;
  currentChannel = null;

  latestFrame = null;
  jpegPending = Buffer.alloc(0);

  audioBuffer = Buffer.alloc(0);
  lastAudioSample = Buffer.from([0, 0]);

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

    // Giảm buffering đầu vào
    "-fflags", "+discardcorrupt+genpts+nobuffer",
    "-flags", "low_delay",
    "-probesize", "1000000",
    "-analyzeduration", "1000000",
    "-rw_timeout", "15000000",

    // Tự kết nối lại với nguồn HTTP/HLS khi có thể
    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "3",

    "-i", channel.url,

    // VIDEO OUTPUT
    "-map", "0:v:0?",
    "-vf",
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease,pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2,fps=${VIDEO_FPS}`,
    "-an",
    "-c:v", "mjpeg",
    "-q:v", String(JPEG_QUALITY),
    "-f", "image2pipe",
    "-flush_packets", "1",
    "pipe:1",

    // AUDIO OUTPUT
    "-map", "0:a:0?",
    "-vn",
    "-ac", String(AUDIO_CHANNELS),
    "-ar", String(AUDIO_RATE),
    "-acodec", "pcm_s16le",
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

  function cleanup() {
    if (closed) return;

    closed = true;
    clearInterval(timer);
    videoClients = Math.max(0, videoClients - 1);
  }

  res.on("close", cleanup);
  res.on("error", cleanup);

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    // Không ghi thêm dữ liệu khi client đang bị nghẽn
    if (res.writableNeedDrain) {
      if (!blockedSince) blockedSince = Date.now();

      if (
        Date.now() - blockedSince >
        VIDEO_CLIENT_TIMEOUT_MS
      ) {
        cleanup();
        res.destroy();
      }

      return;
    }

    blockedSince = 0;

    if (
      res.writableLength > MAX_VIDEO_CLIENT_BUFFER
    ) {
      cleanup();
      res.destroy();
      return;
    }

    if (!latestFrame) return;

    // Không gửi lại cùng một frame
    if (lastSentFrame === videoFrameCount) return;

    const frame = latestFrame;

    const header = Buffer.from(
      `--frame\r\n` +
      `Content-Type: image/jpeg\r\n` +
      `Content-Length: ${frame.length}\r\n\r\n`
    );

    // Gửi mỗi frame thành một packet
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

});

// ==================== AUDIO STREAM ====================

app.get("/audio", (req, res) => {
  // Chỉ cho một audio client tại một thời điểm
  if (audioClient && !audioClient.destroyed) {
    audioClient.destroy();
  }

  res.status(200);

  res.set({
    "Content-Type": "audio/pcm; rate=16000; channels=1",
    "Cache-Control": "no-cache, no-store, must-revalidate",
    "Connection": "keep-alive",
    "X-Accel-Buffering": "no"
  });

  res.flushHeaders?.();

  audioClient = res;

  let closed = false;

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    // Không để audio bị xếp hàng quá nhiều
    if (res.writableLength > 64 * 1024) {
      cleanup();
      res.destroy();
      return;
    }

    // Client đang nghẽn: bỏ qua frame này.
    // Buffer đầu vào vẫn được giới hạn và sẽ bỏ dữ liệu cũ.
    if (res.writableNeedDrain) return;

    const frame = getAudioFrame();

    if (!res.write(frame)) {
      // Chờ drain ở lần timer tiếp theo
    }
  }, AUDIO_FRAME_MS);

  function cleanup() {
    if (closed) return;

    closed = true;
    clearInterval(timer);

    if (audioClient === res) {
      audioClient = null;
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

// Chọn kênh bằng ID hoặc tên
async function selectChannel(req, res) {
  const id = decodeURIComponent(req.params.id || "");

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

app.get("/api/stop", (req, res) => {
  manuallyStopped = true;
  stopFFmpeg();

  res.json({
    success: true,
    message: "Stopped"
  });
});

app.post("/api/stop", (req, res) => {
  manuallyStopped = true;
  stopFFmpeg();

  res.json({
    success: true,
    message: "Stopped"
  });
});

// ==================== API RELOAD ====================

app.get("/api/reload", async (req, res) => {
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
});

app.post("/api/reload", async (req, res) => {
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
});

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
      clients: videoClients
    },

    audio: {
      sampleRate: AUDIO_RATE,
      channels: AUDIO_CHANNELS,
      bufferBytes: audioBuffer.length,
      bufferMs: Math.round(
        audioBuffer.length / (AUDIO_RATE * 2) * 1000
      ),
      connected: !!audioClient
    },

    ffmpegError,
    uptime: process.uptime()
  });
});

// ==================== RENDER BANDWIDTH ====================

function getCurrentMonthRange() {
  const now = new Date();

  const start = new Date(
    Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), 1)
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

    // Trả dữ liệu gốc để không làm sai đơn vị do API trả về
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
