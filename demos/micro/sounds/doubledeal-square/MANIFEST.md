# doubledeal-square: DoubleDeal play: piles squared (knock)

End of `pass`; also the knock after a scoop. Verified 2026-09-30. Every file is **CC0** (licence text as shown on the source page); no CC-BY.

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
| `knock-a_hoganthelogan-466789-slice.ogg` / `.mp3` | — | 0.20 s | 13 | 12 | -25.2 LUFS (M max) | -1.4 | yes | +9.2 dB | 5.2 / 3.1 KB | [Pounding Cards On Table](https://freesound.org/people/HogantheLogan/sounds/466789/) | HogantheLogan | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Card stack pounded on a wooden table, knock 1 (softer). Cut 0.30–0.58 s. Original: `originals/freesound-466789_HogantheLogan_hq-preview.mp3` |
| `knock-b_hoganthelogan-466789-slice.ogg` / `.mp3` | — | 0.29 s | 80 | 79 | -24.9 LUFS (M max) | -1.4 | yes | +8.9 dB | 5.9 / 4.3 KB | [Pounding Cards On Table](https://freesound.org/people/HogantheLogan/sounds/466789/) | HogantheLogan | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Knock 2 (loudest; demos-sfx square-1). Cut 0.57–0.90 s. Original: `originals/freesound-466789_HogantheLogan_hq-preview.mp3` |
| `knock-c_hoganthelogan-466789-slice.ogg` / `.mp3` | — | 0.22 s | 35 | 32 | -24.8 LUFS (M max) | -2.1 | yes | +8.8 dB | 5.6 / 3.4 KB | [Pounding Cards On Table](https://freesound.org/people/HogantheLogan/sounds/466789/) | HogantheLogan | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Knock 3 (lighter). Cut 0.88–1.15 s. Original: `originals/freesound-466789_HogantheLogan_hq-preview.mp3` |

## Peak-limited variants (`-lim`): 3 of 3 candidates

Same source, licence, author and description as the original row above. Only the level processing differs.

| File | Original loudness | `-lim` loudness | Still short of −16 | Extra gain | Peak gain reduction | TP dBTP | Peak (ms) orig → lim | Clicks (ms) | Size ogg / mp3 |
|---|---|---|---|---|---|---|---|---|---|
| `knock-a_hoganthelogan-466789-slice-lim.ogg` / `.mp3` | -25.2 | -23.5 LUFS (M max) | 7.5 dB | +6.0 dB | 6.0 dB | -1.9 | 13 → 13 | 12 | 5.3 / 3.1 KB |
| `knock-b_hoganthelogan-466789-slice-lim.ogg` / `.mp3` | -24.9 | -23.1 LUFS (M max) | 7.1 dB | +6.0 dB | 6.0 dB | -1.9 | 80 → 80 | 79 | 6.0 / 4.3 KB |
| `knock-c_hoganthelogan-466789-slice-lim.ogg` / `.mp3` | -24.8 | -22.5 LUFS (M max) | 6.5 dB | +6.0 dB | 6.0 dB | -1.4 | 35 → 35 | 32 | 5.6 / 3.4 KB |
