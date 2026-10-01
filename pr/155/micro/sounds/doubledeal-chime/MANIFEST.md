# doubledeal-chime: DoubleDeal: ciphertext / output shown

End of run. The map pick is the music box, kept distinct from Scramble's kalimba. Verified 2026-09-30. Every file is **CC0** (licence text as shown on the source page); no CC-BY.

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
| `chime-2_thomasjaunism-218459-musicbox.ogg` / `.mp3` | — | 2.23 s | 42 (mp3 12) | 52 | -16.0 LUFS (I) | -7.0 | no | +0.0 dB | 19.8 / 27.0 KB | [Music box note](https://freesound.org/people/thomasjaunism/sounds/218459/) | thomasjaunism | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Single music-box note: toy-like, gentle decay (map pick for DoubleDeal output). Original: `originals/freesound-218459_thomasjaunism_hq-preview.mp3` |
| `chime-1_hollandm-691805-kalimba-g4.ogg` / `.mp3` | — | 1.23 s | 3 | 2 | -24.3 LUFS (I) | -1.5 | yes | +8.3 dB | 12.6 / 15.0 KB | [G4 soft - kalimba](https://freesound.org/people/hollandm/sounds/691805/) | hollandm | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Kalimba G4, soft velocity: warm, woody (Scramble's digest chime). Original: `originals/freesound-691805_hollandm_hq-preview.mp3` |
| `chime-3_steffcaffrey-449947.ogg` / `.mp3` | — | 2.65 s | 45 | 152 | -16.0 LUFS (I) | -7.3 | no | +0.0 dB | 19.8 / 31.9 KB | [Single Chime 2](https://freesound.org/people/steffcaffrey/sounds/449947/) | steffcaffrey | Creative Commons 0 (http://creativecommons.org/publicdomain/zero/1.0/) | Single garden chime: pure tone, longer ring, faded at 3.2 s. Cut 0.00–3.20 s. Original: `originals/freesound-449947_steffcaffrey_hq-preview.mp3` |

## Peak-limited variants (`-lim`): 1 of 3 candidates

Same source, licence, author and description as the original row above. Only the level processing differs.

| File | Original loudness | `-lim` loudness | Still short of −16 | Extra gain | Peak gain reduction | TP dBTP | Peak (ms) orig → lim | Clicks (ms) | Size ogg / mp3 |
|---|---|---|---|---|---|---|---|---|---|
| `chime-1_hollandm-691805-kalimba-g4-lim.ogg` / `.mp3` | -24.3 | -22.7 LUFS (I) | 6.7 dB | +6.0 dB | 6.0 dB | -1.6 | 3 → 2 | — | 13.0 / 15.0 KB |
