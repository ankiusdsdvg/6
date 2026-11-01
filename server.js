
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

// 4000 mẫu = 250ms tại 16kHz
const AUDIO_SAMPLES_PER_PACKET = 4000;
const AUDIO_FRAME_MS =
  AUDIO_SAMPLES_PER_PACKET * 1000 / AUDIO_SAMPLE_RATE;

const AUDIO_PACKET_BYTES =
  AUDIO_SAMPLES_PER_PACKET *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE;

// Giới hạn hàng đợi audio khi chưa có client hoặc client chậm
const AUDIO_QUEUE_MAX_MS = 2500;
const AUDIO_QUEUE_MAX_BYTES =
  AUDIO_SAMPLE_RATE *
  AUDIO_CHANNELS *
  AUDIO_BYTES_PER_SAMPLE *
  AUDIO_QUEUE_MAX_MS / 1000;

// FFMPEG
const DECODER_THREADS = 2;
const ENCODER_THREADS = 1;
const SKIP_NON_REFERENCE = false;
const INPUT_READRATE = "1";

// WATCHDOG
const WATCHDOG_INTERVAL = 5000;
const VIDEO_TIMEOUT = 45000;
const RESTART_DELAY = 3000;

// Giới hạn bộ nhớ
const MAX_VIDEO_BUFFER = 4 * 1024 * 1024;
const MAX_PENDING_VIDEO = 40;
const MAX_PENDING_AUDIO_META = 40;
const MAX_AUDIO_RAW_BUFFER = 1024 * 1024;

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
let pendingJpegs = [];
let pendingVideoPts = [];

let audioRawBuffer = Buffer.alloc(0);
let pendingAudioMeta = [];
let audioSequence = 0;

let audioQueue = [];
let audioQueueBytes = 0;
let audioClient = null;
let audioBlocked = false;

let stderrPending = "";

let watchdogTimer = null;
let restartTimer = null;

let lastVideoFrameTime = 0;
let lastAudioPacketTime = 0;

let restarting = false;
let manuallyStopped = true;

let videoPtsCount = 0;
let audioPtsCount = 0;
let audioPacketsBuilt = 0;
let audioPacketsSent = 0;
let audioPacketsDropped = 0;

let lastVideoPtsUs = null;
let lastAudioPtsUs = null;

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

  const target = Number(maxResolution);
  const allowed = Number.isFinite(target) ? target : 720;

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
      console.warn("[M3U] Try failed:", url, error.message);
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
}

// =====================================================
// RESET MEDIA STATE
// =====================================================

function clearAudioState() {
  audioRawBuffer = Buffer.alloc(0);
  pendingAudioMeta = [];

  audioQueue = [];
  audioQueueBytes = 0;

  audioSequence = 0;

  audioBlocked = false;

  audioPtsCount = 0;
  audioPacketsBuilt = 0;
  audioPacketsSent = 0;
  audioPacketsDropped = 0;

  lastAudioPacketTime = 0;
  lastAudioPtsUs = null;
}

function clearVideoState() {
  jpegPending = Buffer.alloc(0);

  pendingJpegs = [];
  pendingVideoPts = [];

  latestFrame = null;
  frameSequence = 0;

  videoPtsCount = 0;
  lastVideoFrameTime = 0;
  lastVideoPtsUs = null;
}

function resetMediaState() {
  clearAudioState();
  clearVideoState();

  stderrPending = "";
}

// =====================================================
// AUDIO CLIENT
// =====================================================

function disconnectAudioClient() {
  const oldClient = audioClient;

  audioClient = null;
  audioBlocked = false;

  if (oldClient) {
    try {
      oldClient.destroy();
    } catch (_) {}
  }
}

function attachAudioClient(res) {
  disconnectAudioClient();

  audioClient = res;
  audioBlocked = false;

  console.log("[AUDIO] Client connected");

  flushAudioQueue();

  res.on("close", () => {
    if (audioClient === res) {
      console.log("[AUDIO] Client disconnected");

      audioClient = null;
      audioBlocked = false;
    }
  });
}

// =====================================================
// AUDIO PACKET FORMAT
//
// 0..3   MAGIC       AUD0
// 4..7   SEQUENCE    uint32 BE
// 8..15  PTS_US      int64 BE
// 16..19 SAMPLES     uint32 BE
// 20..   PCM         s16le
// =====================================================

function createAudioPacket(meta, pcm) {
  const header = Buffer.alloc(20);

  header.write("AUD0", 0, 4, "ascii");

  header.writeUInt32BE(
    audioSequence >>> 0,
    4
  );

  header.writeBigInt64BE(
    BigInt(Math.round(meta.ptsUs)),
    8
  );

  header.writeUInt32BE(
    meta.samples,
    16
  );

  audioSequence++;

  return Buffer.concat([
    header,
    pcm
  ]);
}

// =====================================================
// AUDIO QUEUE
// =====================================================

function queueAudioPacket(packet) {
  audioQueue.push(packet);
  audioQueueBytes += packet.length;

  while (
    audioQueueBytes > AUDIO_QUEUE_MAX_BYTES &&
    audioQueue.length > 1
  ) {
    const removed = audioQueue.shift();

    audioQueueBytes -= removed.length;
    audioPacketsDropped++;
  }

  flushAudioQueue();
}

function flushAudioQueue() {
  if (!audioClient || audioClient.destroyed) return;
  if (audioBlocked) return;

  while (audioQueue.length > 0) {
    const packet = audioQueue[0];

    let ok = false;

    try {
      ok = audioClient.write(packet);
    } catch (error) {
      console.error("[AUDIO WRITE]", error.message);
      disconnectAudioClient();
      return;
    }

    audioQueue.shift();
    audioQueueBytes -= packet.length;

    audioPacketsSent++;

    if (!ok) {
      audioBlocked = true;

      const client = audioClient;

      client.once("drain", () => {
        if (audioClient !== client) return;

        audioBlocked = false;
        flushAudioQueue();
      });

      return;
    }
  }
}

// =====================================================
// AUDIO METADATA + PCM PAIRING
// =====================================================

function pushAudioMetadata(ptsUs, samples) {
  if (!Number.isFinite(ptsUs)) return;
  if (!Number.isFinite(samples) || samples <= 0) return;

  pendingAudioMeta.push({
    ptsUs,
    samples
  });

  audioPtsCount++;

  if (pendingAudioMeta.length > MAX_PENDING_AUDIO_META) {
    pendingAudioMeta.shift();
  }

  processAudioPairs();
}

function pushAudioData(chunk) {
  if (!chunk || !chunk.length) return;

  audioRawBuffer = Buffer.concat([
    audioRawBuffer,
    chunk
  ]);

  if (audioRawBuffer.length > MAX_AUDIO_RAW_BUFFER) {
    console.warn("[AUDIO] Raw buffer overflow, resetting pairing");

    audioRawBuffer = Buffer.alloc(0);
    pendingAudioMeta = [];

    return;
  }

  processAudioPairs();
}

function processAudioPairs() {
  while (pendingAudioMeta.length > 0) {
    const meta = pendingAudioMeta[0];

    const bytesNeeded =
      meta.samples *
      AUDIO_CHANNELS *
      AUDIO_BYTES_PER_SAMPLE;

    if (audioRawBuffer.length < bytesNeeded) {
      return;
    }

    const pcm = audioRawBuffer.subarray(
      0,
      bytesNeeded
    );

    audioRawBuffer = audioRawBuffer.subarray(
      bytesNeeded
    );

    pendingAudioMeta.shift();

    const packet = createAudioPacket(meta, pcm);

    audioPacketsBuilt++;
    lastAudioPacketTime = Date.now();
    lastAudioPtsUs = meta.ptsUs;

    queueAudioPacket(packet);
  }
}

// =====================================================
// VIDEO METADATA + JPEG PAIRING
// =====================================================

function pushVideoMetadata(ptsUs) {
  if (!Number.isFinite(ptsUs)) return;

  pendingVideoPts.push(ptsUs);
  videoPtsCount++;

  if (pendingVideoPts.length > MAX_PENDING_VIDEO) {
    pendingVideoPts.shift();
  }

  processVideoPairs();
}

function pushJPEG(jpeg) {
  if (!jpeg || !jpeg.length) return;

  pendingJpegs.push(Buffer.from(jpeg));

  if (pendingJpegs.length > MAX_PENDING_VIDEO) {
    pendingJpegs.shift();
  }

  processVideoPairs();
}

function processVideoPairs() {
  while (
    pendingJpegs.length > 0 &&
    pendingVideoPts.length > 0
  ) {
    const jpeg = pendingJpegs.shift();
    const ptsUs = pendingVideoPts.shift();

    latestFrame = {
      data: jpeg,
      ptsUs,
      sequence: ++frameSequence
    };

    lastVideoFrameTime = Date.now();
    lastVideoPtsUs = ptsUs;
  }
}

// =====================================================
// JPEG PARSER
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

    const jpeg = jpegPending.subarray(
      start,
      end + 2
    );

    pushJPEG(jpeg);

    jpegPending = jpegPending.subarray(end + 2);
  }
}

// =====================================================
// FFMPEG STDERR TIMESTAMP PARSER
// =====================================================

function processFFmpegLogLine(line) {
  // Ví dụ showinfo:
  // n: 12 pts: 108000 pts_time:1.2 ...

  if (line.includes("showinfo")) {
    const match = line.match(
      /pts_time:\s*(-?\d+(?:\.\d+)?)/ 
    );

    if (match) {
      const ptsUs = Number(match[1]) * 1000000;
      pushVideoMetadata(ptsUs);
    }
  }

  // Ví dụ ashowinfo:
  // pts_time:1.2 ... nb_samples:4000

  if (line.includes("ashowinfo")) {
    const ptsMatch = line.match(
      /pts_time:\s*(-?\d+(?:\.\d+)?)/
    );

    const samplesMatch = line.match(
      /nb_samples:\s*(\d+)/
    );

    if (ptsMatch && samplesMatch) {
      const ptsUs =
        Number(ptsMatch[1]) * 1000000;

      const samples =
        Number(samplesMatch[1]);

      pushAudioMetadata(
        ptsUs,
        samples
      );
    }
  }
}

function processFFmpegStderr(chunk, currentGeneration) {
  if (currentGeneration !== generation) return;

  stderrPending += chunk.toString("utf8");

  if (stderrPending.length > 256 * 1024) {
    stderrPending = stderrPending.slice(-128 * 1024);
  }

  const lines = stderrPending.split(/\r?\n/);

  stderrPending = lines.pop() || "";

  for (const line of lines) {
    processFFmpegLogLine(line);
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

  resetMediaState();

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

  resetMediaState();

  const currentGeneration = generation;

  console.log("");
  console.log("======================================");
  console.log("START CHANNEL:", channel.name);
  console.log("URL:", channel.url);
  console.log("GENERATION:", currentGeneration);
  console.log("READRATE:", INPUT_READRATE);
  console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
  console.log("FPS:", VIDEO_FPS);
  console.log("AUDIO:", AUDIO_SAMPLE_RATE, "Hz");
  console.log("AUDIO SAMPLES/PACKET:", AUDIO_SAMPLES_PER_PACKET);
  console.log("AUDIO PACKET:", AUDIO_FRAME_MS, "ms");
  console.log("TIMESTAMP: PTS FROM FFMPEG");
  console.log("======================================");

  lastVideoFrameTime = Date.now();

  const videoFilter = [
    `fps=${VIDEO_FPS}:round=near`,
    `scale=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:force_original_aspect_ratio=decrease:flags=fast_bilinear`,
    `pad=${VIDEO_WIDTH}:${VIDEO_HEIGHT}:(ow-iw)/2:(oh-ih)/2`,
    "setsar=1",
    "showinfo"
  ].join(",");

  const audioFilter = [
    `aresample=${AUDIO_SAMPLE_RATE}:async=1`,
    `asetnsamples=n=${AUDIO_SAMPLES_PER_PACKET}:p=1`,
    "ashowinfo"
  ].join(",");

  const args = [
    "-hide_banner",

    // showinfo / ashowinfo cần log info
    "-loglevel", "info",

    "-rw_timeout", "30000000",

    "-reconnect", "1",
    "-reconnect_streamed", "1",
    "-reconnect_delay_max", "5",

    "-user_agent",
    "Mozilla/5.0",

    "-fflags",
    "+discardcorrupt+genpts",

    "-readrate",
    INPUT_READRATE,

    "-threads",
    String(DECODER_THREADS),

    ...(SKIP_NON_REFERENCE
      ? ["-skip_frame", "noref"]
      : []),

    "-i", channel.url,

    // ===============================================
    // VIDEO OUTPUT
    // ===============================================

    "-map", "0:v:0?",
    "-an",

    "-vf", videoFilter,

    "-q:v", String(JPEG_QUALITY),

    "-threads",
    String(ENCODER_THREADS),

    "-flush_packets", "1",

    "-f", "image2pipe",
    "-vcodec", "mjpeg",

    "pipe:1",

    // ===============================================
    // AUDIO OUTPUT
    // ===============================================

    "-map", "0:a:0?",
    "-vn",

    "-af", audioFilter,

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
    processVideoData(
      chunk,
      currentGeneration
    );
  });

  // AUDIO PIPE
  if (processRef.stdio[3]) {
    processRef.stdio[3].on("data", chunk => {
      if (currentGeneration !== generation) return;

      pushAudioData(chunk);
    });
  }

  // STDERR
  processRef.stderr.on("data", chunk => {
    processFFmpegStderr(
      chunk,
      currentGeneration
    );
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

    resetMediaState();

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
  resetMediaState();

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
// VIDEO STREAM - MJPEG + PTS
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
      if (Date.now() - blockedSince > 2000) {
        clearInterval(timer);
        res.destroy();
      }

      return;
    }

    if (!latestFrame) return;

    if (latestFrame.sequence === lastSentSequence) {
      return;
    }

    const frame = latestFrame;

    lastSentSequence = frame.sequence;

    const header = Buffer.from(
      "--frame\r\n" +
      "Content-Type: image/jpeg\r\n" +
      "Content-Length: " + frame.data.length + "\r\n" +
      "X-PTS-US: " + Math.round(frame.ptsUs) + "\r\n" +
      "X-SEQ: " + frame.sequence + "\r\n" +
      "\r\n"
    );

    const packet = Buffer.concat([
      header,
      frame.data,
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
// AUDIO STREAM - TIMESTAMPED PCM
// =====================================================

app.get("/audio", (req, res) => {
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
  res.setHeader("X-Audio-Protocol", "AUD0");
  res.setHeader("X-Audio-Sample-Rate", String(AUDIO_SAMPLE_RATE));
  res.setHeader("X-Audio-Channels", String(AUDIO_CHANNELS));
  res.setHeader("X-Audio-Format", "s16le");
  res.setHeader("X-Audio-Header-Bytes", "20");

  attachAudioClient(res);
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
  const audioBytesPerSecond =
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

    pipeline: "PTS_SYNC_MJPEG_PCM",

    audioProtocol: "AUD0",
    audioHeaderBytes: 20,

    inputReadrate: INPUT_READRATE,

    videoWidth: VIDEO_WIDTH,
    videoHeight: VIDEO_HEIGHT,
    videoFPS: VIDEO_FPS,

    videoFrameSequence: frameSequence,
    videoPtsCount,
    lastVideoPtsUs,

    audioSampleRate: AUDIO_SAMPLE_RATE,
    audioChannels: AUDIO_CHANNELS,
    audioFormat: "s16le",

    audioSamplesPerPacket: AUDIO_SAMPLES_PER_PACKET,
    audioFrameMs: AUDIO_FRAME_MS,
    audioPacketBytes: AUDIO_PACKET_BYTES,

    audioPtsCount,
    audioPacketsBuilt,
    audioPacketsSent,
    audioPacketsDropped,

    audioQueuePackets: audioQueue.length,
    audioQueueBytes,

    audioQueueDurationMs:
      Math.round(
        audioQueueBytes /
        audioBytesPerSecond * 1000
      ),

    audioQueueMaxBytes: AUDIO_QUEUE_MAX_BYTES,

    audioRawBufferBytes: audioRawBuffer.length,
    audioPendingMetadata: pendingAudioMeta.length,

    audioClientConnected:
      !!audioClient && !audioClient.destroyed,

    audioBlocked,

    lastAudioPacketTime,

    lastAudioPtsUs,

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
  res.send(`
    <!DOCTYPE html>
    <html>
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width,initial-scale=1">
      <title>IPTV Streaming Server</title>
    </head>

    <body style="background:#111;color:#eee;font-family:Arial;padding:20px">

      <h2>IPTV Streaming Server</h2>

      <p>Channels: ${channels.length}</p>
      <p>Pipeline: PTS SYNC MJPEG + PCM</p>

      <p>Video: ${VIDEO_WIDTH}x${VIDEO_HEIGHT} @ ${VIDEO_FPS} FPS</p>
      <p>Audio: ${AUDIO_SAMPLE_RATE}Hz PCM S16LE</p>
      <p>Audio packet: ${AUDIO_FRAME_MS}ms</p>
      <p>Audio protocol: AUD0</p>

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
    console.log("PIPELINE: PTS SYNC MJPEG PCM");
    console.log("VIDEO:", VIDEO_WIDTH + "x" + VIDEO_HEIGHT);
    console.log("FPS:", VIDEO_FPS);
    console.log("AUDIO:", AUDIO_SAMPLE_RATE);
    console.log("AUDIO PACKET:", AUDIO_FRAME_MS, "ms");
    console.log("AUDIO PROTOCOL: AUD0");
    console.log("--------------------------------");
  });
}

main();
