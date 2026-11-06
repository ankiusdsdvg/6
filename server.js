
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

// Bộ đệm chung theo thời gian
const BUFFER_DELAY_MS = 3000;
const MAX_BUFFER_MS = 4000;

// Giới hạn bộ đệm hình
const MAX_JPEG_BYTES = 256 * 1024;
const MAX_VIDEO_PENDING_BYTES = 512 * 1024;
const MAX_VIDEO_QUEUE_FRAMES =
  Math.ceil(VIDEO_FPS * MAX_BUFFER_MS / 1000);

const MAX_VIDEO_CLIENT_BUFFER = 300 * 1024;
const VIDEO_CLIENT_TIMEOUT_MS = 3000;

// Giới hạn bộ đệm tiếng
const MAX_AUDIO_BUFFER =
  AUDIO_RATE * AUDIO_CHANNELS * 2 * MAX_BUFFER_MS / 1000;

const AUDIO_CLIENT_TIMEOUT_MS = 3000;

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

// Hàng đợi hình
let videoQueue = [];
let playbackFrame = null;
let playbackFrameSeq = 0;

// Hàng đợi tiếng
let audioQueue = [];
let audioQueuedBytes = 0;
let audioRemainder = Buffer.alloc(0);

let audioClient = null;
let audioBlocked = false;

let videoClients = 0;
let ffmpegError = "";

let audioDroppedBytes = 0;
let audioSentFrames = 0;
let videoDroppedClients = 0;
let videoDroppedFrames = 0;

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

// ==================== XÓA BỘ ĐỆM ====================

function clearVideoBuffer() {
  videoQueue = [];
  playbackFrame = null;
}

function clearAudioBuffer() {
  audioDroppedBytes += audioQueuedBytes;

  audioQueue = [];
  audioQueuedBytes = 0;
  audioRemainder = Buffer.alloc(0);
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
      const frame = Buffer.from(
        jpegPending.subarray(0, frameLength)
      );

      latestFrame = frame;
      videoFrameCount++;
      lastVideoFrameAt = Date.now();

      // Chỉ xếp hàng khi có người xem
      if (videoClients > 0) {
        videoQueue.push({
          data: frame,
          readyAt: Date.now() + BUFFER_DELAY_MS
        });

        // Giới hạn hàng đợi hình
        while (videoQueue.length > MAX_VIDEO_QUEUE_FRAMES) {
          videoQueue.shift();
          videoDroppedFrames++;
        }
      }
    }

    jpegPending = jpegPending.subarray(frameLength);
  }
}

// ==================== AUDIO BUFFER ====================

function dropOldestAudioBytes(bytesToDrop) {
  let remaining = bytesToDrop;

  while (remaining > 0 && audioQueue.length > 0) {
    const item = audioQueue[0];
    const available = item.data.length - item.offset;

    const remove = Math.min(available, remaining);

    item.offset += remove;
    audioQueuedBytes -= remove;
    audioDroppedBytes += remove;
    remaining -= remove;

    if (item.offset >= item.data.length) {
      audioQueue.shift();
    }
  }
}

function processAudioData(chunk) {
  if (!chunk || !chunk.length) return;

  // Không giữ tiếng khi chưa có người nghe
  if (!audioClient || audioClient.destroyed) {
    audioDroppedBytes += chunk.length;
    return;
  }

  let data = chunk;

  // Giữ lại byte lẻ để bảo đảm PCM 16-bit
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

  audioQueue.push({
    data: Buffer.from(data),
    offset: 0,
    readyAt: Date.now() + BUFFER_DELAY_MS
  });

  audioQueuedBytes += data.length;

  // Giới hạn bộ đệm tiếng tối đa 4 giây
  if (audioQueuedBytes > MAX_AUDIO_BUFFER) {
    const excess = audioQueuedBytes - MAX_AUDIO_BUFFER;

    const alignedExcess =
      excess + (excess % 2);

    dropOldestAudioBytes(alignedExcess);
  }
}

// Lấy PCM đã đủ thời gian đệm.
// Phần thiếu được lấp bằng silence, không lặp âm thanh cũ.

function getAudioFrame() {
  const now = Date.now();

  const frame = Buffer.alloc(AUDIO_FRAME_BYTES);
  let written = 0;

  while (
    written < AUDIO_FRAME_BYTES &&
    audioQueue.length > 0
  ) {
    const item = audioQueue[0];

    // Chưa đến thời gian phát
    if (item.readyAt > now) break;

    const available = item.data.length - item.offset;

    const needed = AUDIO_FRAME_BYTES - written;
    const take = Math.min(available, needed);

    item.data.copy(
      frame,
      written,
      item.offset,
      item.offset + take
    );

    item.offset += take;
    written += take;
    audioQueuedBytes -= take;

    if (item.offset >= item.data.length) {
      audioQueue.shift();
    }
  }

  // Chưa có dữ liệu đã sẵn sàng
  if (written === 0) {
    return null;
  }

  // Phần còn lại của frame đã là silence (0)
  return frame;
}

// ==================== VIDEO PLAYBACK CLOCK ====================

// Phát hình theo tốc độ cố định.
// Không phát dồn frame để bù dữ liệu bị trễ.

setInterval(() => {
  if (videoClients <= 0) {
    videoQueue = [];
    return;
  }

  if (videoQueue.length === 0) return;

  const now = Date.now();

  if (videoQueue[0].readyAt > now) return;

  const item = videoQueue.shift();

  playbackFrame = item.data;
  playbackFrameSeq++;

}, Math.floor(1000 / VIDEO_FPS));

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

  clearVideoBuffer();
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

    // VIDEO
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

    // AUDIO
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

  // Khi có người xem mới, bắt đầu đệm lại từ đầu
  if (videoClients === 0) {
    clearVideoBuffer();
    playbackFrameSeq = 0;
  }

  videoClients++;

  let closed = false;
  let lastSentFrame = -1;
  let blockedSince = 0;

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    if (res.writableNeedDrain) {
      if (!blockedSince) {
        blockedSince = Date.now();
      }

      if (
        Date.now() - blockedSince > VIDEO_CLIENT_TIMEOUT_MS
      ) {
        videoDroppedClients++;
        cleanup();
        res.destroy();
      }

      return;
    }

    blockedSince = 0;

    if (res.writableLength > MAX_VIDEO_CLIENT_BUFFER) {
      videoDroppedClients++;
      cleanup();
      res.destroy();
      return;
    }

    if (!playbackFrame) return;

    if (lastSentFrame === playbackFrameSeq) return;

    const frame = playbackFrame;

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

    lastSentFrame = playbackFrameSeq;

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

    if (videoClients === 0) {
      clearVideoBuffer();
    }
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

  res.on("drain", () => {
    if (closed) return;

    blockedSince = 0;
    audioBlocked = false;
  });

  const timer = setInterval(() => {
    if (closed || res.destroyed || res.writableEnded) {
      cleanup();
      return;
    }

    // Không xóa bộ đệm chỉ vì socket vừa nghẽn.
    // Để dữ liệu chờ trong giới hạn 4 giây.
    if (res.writableNeedDrain) {
      audioBlocked = true;

      if (!blockedSince) {
        blockedSince = Date.now();
      }

      if (
        Date.now() - blockedSince > AUDIO_CLIENT_TIMEOUT_MS
      ) {
        cleanup();
        res.destroy();
      }

      return;
    }

    if (res.writableLength > AUDIO_FRAME_BYTES * 4) {
      audioBlocked = true;

      if (!blockedSince) {
        blockedSince = Date.now();
      }

      if (
        Date.now() - blockedSince > AUDIO_CLIENT_TIMEOUT_MS
      ) {
        cleanup();
        res.destroy();
      }

      return;
    }

    blockedSince = 0;
    audioBlocked = false;

    const frame = getAudioFrame();

    // Chưa có dữ liệu đã qua thời gian đệm
    if (!frame) return;

    const accepted = res.write(frame);

    audioSentFrames++;

    if (!accepted) {
      audioBlocked = true;
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

    buffer: {
      targetDelayMs: BUFFER_DELAY_MS,
      maxBufferMs: MAX_BUFFER_MS
    },

    video: {
      width: VIDEO_WIDTH,
      height: VIDEO_HEIGHT,
      fps: VIDEO_FPS,
      frameCount: videoFrameCount,
      frameAgeMs: frameAge,
      pendingBytes: jpegPending.length,
      queuedFrames: videoQueue.length,
      queuedMs: Math.round(
        videoQueue.length / VIDEO_FPS * 1000
      ),
      clients: videoClients,
      droppedClients: videoDroppedClients,
      droppedFrames: videoDroppedFrames
    },

    audio: {
      sampleRate: AUDIO_RATE,
      channels: AUDIO_CHANNELS,
      frameMs: AUDIO_FRAME_MS,
      bufferBytes: audioQueuedBytes,

      bufferMs: Math.round(
        audioQueuedBytes / (AUDIO_RATE * 2) * 1000
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

    console.log(`A/V buffer delay: ${BUFFER_DELAY_MS}ms`);
    console.log(`Maximum buffer: ${MAX_BUFFER_MS}ms`);
    console.log("Buffered live mode: ENABLED");
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
