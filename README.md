# 

Converts a public HTTP(S) TV stream (HLS/M3U8 or a direct stream supported by FFmpeg) into 320x240 MJPEG at about 10 FPS.

## Run locally with Docker
```bash
docker build -t esp32-tv-server .
docker run --rm -p 3000:3000 esp32-tv-server
```

Or install Node.js 18+ and FFmpeg, then run:
```bash
npm start
```

## Endpoints
- `GET /health` — health check
- `GET /channels` — parse the default IPTV-org Vietnam playlist
- `GET /stream?url=ENCODED_STREAM_URL` — multipart MJPEG stream

Example: open `/channels`, copy a channel's `url`, URL-encode it, then open:
`http://SERVER:3000/stream?url=https%3A%2F%2Fexample.com%2Flive.m3u8`

For ESP32, use the full `/stream?url=...` URL as the MJPEG HTTP source. URL-encode the source stream URL.

## Notes
- This server must run somewhere that has FFmpeg installed. The included Dockerfile installs it.
- Some channels may be geo-blocked, token-protected, offline, or unsupported.
- MJPEG uses much more bandwidth than H.264; start with 320x240, 8–10 FPS, JPEG quality 8.
- This is a basic personal-use prototype. Do not expose it publicly without adding authentication, rate limits, and stricter URL allowlisting.
