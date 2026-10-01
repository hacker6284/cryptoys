# doubledeal-grid-deal: DoubleDeal play: packet dealt into the 4×13 grid (`deal`, `dealrm`)

`seatPacket`, 36 ms per card. Play one fan per step, or the contact tick per card at ≤ 15/s. Verified 2026-09-30. Every file is **CC0** (licence text as shown on the source page); no CC-BY.

## How these were made
- **Sources:** existing verified picks from `/workspace/scrounger/megadreifach/`, `/workspace/scrounger/demos-sfx/`, the SpaceJoe "Rubik Cube Sounds" pack (all 25 turns plus "Small Noises", CC0) and Kenney packs, re-cut from the **untouched originals** (copied into `originals/`). Freesound originals are the public HQ-preview MP3s, because the lossless uploads need a login. Kenney originals are the OGGs from the official ZIPs.
- **Processing:** mono at 44.1 kHz; silence trimmed; 3 ms fade-in; squared fade-out; linear gain only (no limiter, compressor or EQ). Encoded as OGG Vorbis q4 and MP3 96 kbps CBR, metadata stripped.
- **Loudness:** measured with ffmpeg `ebur128` (BS.1770-4 / EBU R128) on the *encoded* files. The target is **−16 LUFS**, with true peak ≤ **−1 dBTP** on both the OGG and the MP3.
  - Clips ≥ 1.0 s use **integrated** loudness (I).
  - Clips < 1.0 s are too short for a meaningful integrated value, so they use **maximum momentary loudness** (M, 400 ms window, clip padded with silence).
- **TP-limited:** most foley transients (clicks, pats, ticks) hit the −1 dBTP ceiling before −16 LUFS. They are at the loudest level that keeps TP ≤ −1 dBTP, and the "To −16" column is the extra gain needed. They were **not** peak-limited on purpose, because limiting blunts the transient. For level-matched A/B, apply each file's "To −16" gain in the page (WebAudio gain is float, so it won't clip before the master) and put a limiter on the master bus, or lower the page's reference level.
- **Peak** is the offset in ms of the loudest sample (the contact moment) in the decoded OGG, recomputed after trimming and normalising. The MP3 value is shown only where it differs by more than 2 ms (two near-equal clicks).
- **Clicks** are the major transients within 6 dB of the loudest, at least 40 ms apart, in ms. They sync the turn groups and multi-touch sounds.
- `candidates.json` has the same data in machine-readable form for the tuning page.
- I haven't listened to any of these; slices were cut by waveform only.
- **`-lim` files (peak-limited variants):** made for every candidate more than 6 dB short of −16 LUFS. They are listed in the second table below, sitting beside the original (`<name>-lim.ogg` / `.mp3`). Recipe: the original's trimmed audio, plus extra linear gain of at most **6 dB**, through ffmpeg `alimiter` (lookahead, attack 1 ms, release 40 ms, auto-level off, latency compensated), run at 4× oversampling with a −1.5 dBFS ceiling. True peak ≤ −1 dBTP is re-measured on the encoded OGG and MP3. The 6 dB cap keeps the limiter transparent on clicks and taps: on a 20 ms click, pushing all the way to −16 LUFS (M) takes 15–30 dB of gain reduction and flattens the click into a different sound. So many `-lim` files are louder but still short of −16; the "Still short" column shows by how much. Use the **original's** peak offset for sync: on the `-lim` file the loudest sample can jump to another, now near-equal click.

| File | Group | Duration | Peak (ms) | Clicks (ms) | Loudness | TP dBTP (max of ogg/mp3) | TP-limited | To −16 | Size ogg / mp3 | Source | Author (as shown) | Licence (as shown) | Description |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `fan-1_kenney-card-fan-1.ogg` / `.mp3` | — | 0.61 s | 467 | 468, 558 | -21.3 LUFS (M max) | -1.9 | yes | +5.3 dB | 11.8 / 8.0 KB | [Casino Audio (1.1) / card-fan-1.ogg](https://kenney.nl/assets/casino-audio) | Kenney Vleugels (Kenney.nl) | Creative Commons CC0 (page); License.txt: "Creative Commons Zero, CC0" (http://creativecommons.org/publicdomain/zero/1.0/) | Kenney: short card fan / ripple (~0.7 s). Original: `originals/kenney-casino-audio_card-fan-1.ogg` |
| `fan-2_kenney-card-fan-2.ogg` / `.mp3` | — | 1.31 s | 1054 | 1055 | -29.9 LUFS (I) | -1.9 | yes | +13.9 dB | 15.9 / 16.3 KB | [Casino Audio (1.1) / card-fan-2.ogg](https://kenney.nl/assets/casino-audio) | Kenney Vleugels (Kenney.nl) | Creative Commons CC0 (page); License.txt: "Creative Commons Zero, CC0" (http://creativecommons.org/publicdomain/zero/1.0/) | Kenney: longer fan (~1.3 s) with distinct card ticks. Original: `originals/kenney-casino-audio_card-fan-2.ogg` |
| `contact_bmaczero-96127.ogg` / `.mp3` | — | 0.08 s | 20 | 19 | -29.9 LUFS (M max) | -1.5 | yes | +13.9 dB | 4.5 / 1.6 KB | [Contact1.wav](https://freesound.org/people/BMacZero/sounds/96127/) | BMacZero | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Tiny card-on-card contact (80 ms); fire per card, throttled. Original: `originals/freesound-96127_BMacZero_hq-preview.mp3` |

## Peak-limited variants (`-lim`): 2 of 3 candidates

Same source, licence, author and description as the original row above. Only the level processing differs.

| File | Original loudness | `-lim` loudness | Still short of −16 | Extra gain | Peak gain reduction | TP dBTP | Peak (ms) orig → lim | Clicks (ms) | Size ogg / mp3 |
|---|---|---|---|---|---|---|---|---|---|
| `fan-2_kenney-card-fan-2-lim.ogg` / `.mp3` | -29.9 | -25.2 LUFS (I) | 9.2 dB | +6.0 dB | 5.7 dB | -1.5 | 1054 → 1053 | 875, 937, 1000, 1052 | 16.2 / 16.3 KB |
| `contact_bmaczero-96127-lim.ogg` / `.mp3` | -29.9 | -26.9 LUFS (M max) | 10.9 dB | +6.0 dB | 5.9 dB | -1.7 | 20 → 20 | 19 | 4.5 / 1.6 KB |
