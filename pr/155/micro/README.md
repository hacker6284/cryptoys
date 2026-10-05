# Microdemos

Tiny pages, each looping one animation from the real demo code in the
playroom with its sound. There are no controls: open a page, click once to
turn sound on, and listen. `index.html` lists them.

- **Animation library:** a page whose animation Zachary has approved is
  only a viewer of its entry in `../anim/` (see `../anim/README.md`):
  the values live there and the real demos import them. So far:
  `scramble-turn` (viewed by `scramble-turn` and `scramble-rotate`),
  `megaminx-turn` and `doubledeal-grid-deal` (animation approved; sound on hold),
  and the general primitives `carry` and `hinge` (not yet approved; silent,
  each showing only its own move, looped with a different seeded placement
  every cycle and checked as drawn, see `../anim/README.md`). The rest keep their own `settings.js` until approved.
- **Settings:** each other page's `settings.js` holds everything you hear and
  see move: one sound file per slot, `gainDb`, `offsetMs` (when the file
  starts relative to the contact moment; −peak puts the loudest sample on
  it), `fadeMs`/`maxMs`, the timings and easings (real code values) and
  the loop gap. To change something, edit that line and reload.
- **Swapping a sound:** put another candidate's path in `file`, then run
  `python3 tools/sync-micro-sounds.py`. It copies only the files the
  settings name, from Scrounger's folders, and rewrites
  `sounds/LICENSE.md` (credits). `--list [primitive]` prints what can be
  swapped in. `python3 tools/check-micro-sounds.py` checks every shipped
  file decodes.
- **Code:** `shared/micro.js` is the harness: full-window scene, the
  view fitted to the toy, and the loop. Sound goes through
  `../shared/sound.js` (the MegaDreifach Web Audio path, limiter on the
  master). If an MP3 won't decode, it falls back to the OGG and logs it.
- **Models:** `models/` holds project-owned procedural blockouts (peg,
  grid, dice cup, tray); see `models/LICENSE.md`.
