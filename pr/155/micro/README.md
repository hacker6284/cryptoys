# Microdemos

Tiny standalone pages, each looping one animation primitive from the real
demo code in the real playroom, with its sounds. Use them to tune timing and
pick sounds by ear, then press **Copy settings**: you get JSON shaped like
the source demo's config, and it is also logged to the console.

- `index.html` lists the pages. The harness is `shared/micro.js`, and the
  sound engine is `../shared/sound.js` (the MegaDreifach Web Audio path). It
  unlocks on the first gesture and has a limiter on the master.
- **Defaults are the real values.** Timing sliders write the exported
  timing tables (`UNBOX_TIMING`, `TABLE_TIMING`, `DIRECTOR_TIMING`,
  `CUBE_STAGE_TIMING`). Each page names its source file.
- **Sound slots.** Each slot has:
  - a candidate picker, driven by Scrounger's `candidates.json`, with rank 1
    as the default
  - gain in dB, seeded from the file's "To −16" level
  - an offset in ms relative to the slot's contact moment, seeded to −peak
    so the loudest sample lands on contact
  - length and fade-out controls for long creaks

  The real demos have no sound hooks yet. `offsetMs` is relative to the
  contact as each page defines it; `sound.js` supports this through
  `play(name, { leadMs })`.
- **Twisty pages.** The double and triple slots can play the single-turn
  file once per detent click, at cubing.js smootherStep click times.
- **Sounds.**
  - `tools/sync-micro-sounds.py` copies them from `scrounger/micro/` (CC0
    only) into `sounds/`, with `sounds/index.json` and `sounds/LICENSE.md`
    (credits).
  - `tools/check-micro-sounds.py` checks that every OGG and MP3 decodes.
  - If an MP3 will not decode in the browser, the loader falls back to the
    OGG and logs it.
- **Models.** `models/` holds Scrounger's procedural peg, grid, cup and
  tray. See `models/LICENSE.md`.
- Settings persist per page in localStorage (`cryptoys.micro.<page>`).
