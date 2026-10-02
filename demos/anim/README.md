# Animation library

One entry per animation. The entry is the only place its motion and
sound are defined: timings, easings, sound slots, files, gains and
offsets. Everything that plays it imports it.

```
anim/
  scramble-turn/
    settings.js   the values (edit these)
    index.js      the entry: exports settings and the hooks the demo code calls
  sounds/         the files the entries name (generated, see below)
  voice.js        settings.sounds → a sound.js player with contact timing
  twisty.js       cubing.js move timing shared by twisty-puzzle entries
```

## The rule

1. **Defined once.** An entry's values live in its `settings.js` and
   nowhere else. Demo code reads them from the entry; nothing is copied
   or pasted back.
2. **The microdemo audits it.** `demos/micro/<name>/` is a thin viewer
   that loops the entry on the real demo code (an entry with several
   sounds can have more than one viewer, e.g. `micro/scramble-rotate/`). What you hear and see
   there is what every demo does.
3. **Demos import it.** Demo code calls the entry's hooks (e.g.
   `playroom/cube-stage.js` calls `scrambleTurnVoice().turns(...)` and
   reads `timing`), so changing a value changes it everywhere at once.
4. **Approved once Zachary signs off.** An entry is marked approved
   below at the commit he heard. Changing an approved entry's values
   needs his sign-off again; bump the commit here when he gives it.

Microdemos not in this table still keep their own `settings.js` in
`demos/micro/<page>/`. Each moves here once Zachary approves it.

## Entries

| Entry | Played by | Microdemo | Status |
|---|---|---|---|
| `scramble-turn` | playroom Scramble seat (`playroom/cube-stage.js`): a click per face turn, a sound per whole-cube rotation, a muffled pat when the cube lands on the felt | `micro/scramble-turn/` (single, double and triple face turns, one step each), `micro/scramble-rotate/` (rotation) | approved by Zachary: the single face-turn click's file and gain, the landing pat and the lift timing at `af9a8fb`; the rotation sound (Sadiquecat broomstick swish, swell at mid-rotation) on 2026-10-02. **Single, double and triple face-turn sounds approved and LOCKED at `6014bfc`** (Zachary: "All look pretty good."): their files, gains, `align: "peak-velocity"` and `nudgeMs: 0`, under his rule "the audible part of the sound should be centered over the part of the animation where the face is at maximum velocity" (each file's audible centroid half way through its turn, cubing.js smootherStep, at any tempo); pinned by `library.test.mjs` |

## Sounds

`file` in a `settings.js` is a path under `sounds/` without extension.
`offsetMs` is when the file starts relative to the contact. A sound tied
to a motion whose speed changes (a face turn at the dock's tempo) is
tuned at the entry's `timing.speed`; at another speed the entry scales
the time from the file's loudest sample to the contact with the motion,
so the sound keeps its place in it.
After changing one, run `python3 tools/sync-micro-sounds.py`: it copies
the named files (both `.ogg` and `.mp3`) and rewrites `sounds/index.json`
and `sounds/LICENSE.md`. `--list [primitive]` prints what can be swapped
in; `python3 tools/check-micro-sounds.py` checks every file decodes.

Sounds play on the page's one shared AudioContext (`shared/sound.js`):
the hub tap unlocks it, with the iOS fixes, so a demo never needs its
own prompt.
