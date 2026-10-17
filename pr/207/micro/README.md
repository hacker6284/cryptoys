# Microdemos

Tiny pages, each looping one animation from the real demo code in the
playroom with its sound. There are no controls: open a page, click once to
turn sound on, and listen. `index.html` lists them.

- **Animation library:** a page whose animation is in `../anim/` (see
  `../anim/README.md`) is only a viewer of that entry: the values live
  there and the real demos import them. The library is by object, and so
  are these pages, one per object move:
  - `deck/carry/` (deck/carry), `deck/deal/` (deck/deal, the locked grid
    deal; sound on hold), `deck/box/open-close-flap/` (deck/box);
  - `chest/open-close-lid/` (chest);
  - `cube/face-turn/`, `cube/rotate/` (cube, approved);
  - `megaminx/face-turn/` (megaminx, locked).

  Each shows one object doing one move in one fixed placement, looping;
  `?seed=N` picks another placement on load (no cuts mid-loop). Carry is
  the exception: changing place is the move, so it varies its flights,
  with the chest shut and nothing else moving. Objects are never mixed in
  one page. The unapproved moves are silent and checked as drawn (in the
  page's `window.__primitive`). The old flat URLs (`carry/`,
  `scramble-turn/`, `scramble-rotate/`, `megaminx-turn/`,
  `doubledeal-grid-deal/`) redirect to the new ones; `hinge/` (removed)
  sends you to this index.
  The rest keep their own `settings.js` until approved.
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
