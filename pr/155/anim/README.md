# Animation library

One entry per animation. The entry is the only place its motion and
sound are defined: timings, easings, sound slots, files, gains and
offsets. Everything that plays it imports it.

```
anim/
  scramble-turn/
    settings.js   the values (edit these)
    index.js      the entry: exports settings and the hooks the demo code calls
  megaminx-turn/  (same layout)
  doubledeal-grid-deal/ (same layout)
  carry/          P1 carry (a general primitive; placements.js: its seeded audit loop)
  hinge/          P2 hinge (a general primitive; placements.js: its seeded audit loop)
  geom.js         pure geometry for the primitives: quaternions (slerp), oriented boxes, overlap
  room.js         the playroom's solids and seats, measured from the drawn meshes (the chest at any spot: chestAt)
  poses.js        placement helpers (the deck box's bounds, orientations, a seated pose); no motion
  sounds/         the files the entries name (generated, see below)
  voice.js        settings.sounds → a sound.js player with contact timing
  twisty.js       cubing.js move timing shared by twisty-puzzle entries
  twisty-voice.js the lift / turns / landing hooks of a twisty-puzzle entry
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
`demos/micro/<page>/` until they move here. A new entry starts from the
default rules: a turn sound's audible centre at the face's peak
velocity (`align: "peak-velocity"`), the scramble-turn landing pat; a
moving card's sound has its audible centre where the card moves fastest.

## General primitives

Some entries are general primitives (`carry`, `hinge`; the agreed plan
adds extract/insert, peel, deal, gather, shift and turn). A primitive is tuned once and plays everywhere:
**placement is always an input** (where from, where to, any yaw, flips,
what is around it), and what Zachary approves is its laws: the timing,
the curves and the object's own motion. Rotations use quaternion slerp;
arcs clear whatever is under and around the path (`room.js` solids and
the other toys), measured from the drawn geometry, not fixed heights.
Each primitive's microdemo loops it with a different, seeded start and
end every cycle (real playroom poses, edge cases, random ones; the seed
and cycle are shown small on the page; `?seed=N`, `?cycle=N`, `?only=N`,
`?view=cycle`), from one fixed camera framing the union of the loop, and
checks every cycle as drawn: real sizes, no overlap, seated by drawn
geometry, nothing jumps or scales, duration and peak speed on the law.

**Primitives are atomic.** Each one is a single move and its microdemo
shows only that move: nothing else animates, and no primitive calls or
imports another (shared code is placement only: `geom.js`, `room.js`,
`poses.js`; `library.test.mjs` checks the import graphs). Composing moves
(open the chest, then carry out of it) is for the real hub demos. Where a
primitive's placement cannot follow from the move itself (a hinge), a
cycle boundary is a placement reset: a clean cut to the next pose, not
motion.
`library.test.mjs` runs the same checks over the seeds.

## Real-life scale

Every toy an entry animates is at real-life scale; never fit a toy to
another toy's box. Each puzzle is sized to its own real measure from the
one table, `REAL_SIZES` in `../playroom/constants.js` (3×3 57 mm edge,
megaminx 70 mm face to face, pyraminx 97 mm edge, with sources; see
`../README.md`). A puzzle may share the cube's size only when that is its
own real size. Lift heights and timings are in metres and milliseconds
in the real room, so they hold for a bigger toy. Cards are 63 × 88 mm
poker cards laid out by `../doubledeal/real-layout.js` (each grid with
small even gaps, nothing overlapping, the cards' drawn bottoms on the felt).

## Entries

| Entry | Played by | Microdemo | Status |
|---|---|---|---|
| `scramble-turn` | playroom Scramble seat (`playroom/cube-stage.js`): a click per face turn, a sound per whole-cube rotation, a muffled pat when the cube lands on the felt | `micro/scramble-turn/` (single, double and triple face turns, one step each), `micro/scramble-rotate/` (rotation) | approved by Zachary: the single face-turn click's file and gain, the landing pat and the lift timing at `af9a8fb`; the rotation sound (Sadiquecat broomstick swish, swell at mid-rotation) on 2026-10-02; it now follows the turns' rule (`align: "peak-velocity"`, `centre: "swell"`): its swell at mid-rotation for any rotation (y, y2) at any tempo, unchanged (within 1 ms) for the quarter rotation he approved. **Single, double and triple face-turn sounds approved and LOCKED at `6014bfc`** (Zachary: "All look pretty good."): their files, gains, `align: "peak-velocity"` and `nudgeMs: 0`, under his rule "the audible part of the sound should be centered over the part of the animation where the face is at maximum velocity" (each file's audible centroid half way through its turn, cubing.js smootherStep, at any tempo); pinned by `library.test.mjs` |
| `megaminx-turn` | the megaminx in a cube stage (`playroom/cube-stage.js` with `{ voice: megaminxTurnVoice(), timing }`): a click per face turn (72°), a muffled pat when it lands. MegaDreifach's own stage is on PR #153 (held): import this entry there when it lands | `micro/megaminx-turn/` (single, double and triple turns U, U2, U3, one step each, in the Scramble seat's debug megaminx) | **Animation and sounds APPROVED and LOCKED at `a927bb2`** (Zachary approved the animation: the megaminx at its real 70 mm face to face, seated on the felt by its drawn geometry; the lift, turn tempo and settle timing and every sound as they are). **Single, double and triple face-turn sounds approved and LOCKED at `d952e6a`** (Zachary: "Sounds are ok for that one."): their files, gains, `align: "peak-velocity"` and `nudgeMs: 0` (SpaceJoe clicks centred on peak face velocity, cubing.js smootherStep, half way); pinned by `library.test.mjs`. Landing: scramble-turn's muffled pat |
| `doubledeal-grid-deal` | `doubledeal/table.js` on the real-size layout (`doubledeal/real-layout.js`, via `playroom/card-stage.js` `stageCardTable(..., { layout: REAL_LAYOUT })`): the hand packet, a neat stack with its top card first, dealt card by card onto the message grid, column by column, each card hopping from the packet to its seat; one card-fan sound per deal (Kenney card fan), its audible centre on the mean of the cards' peak-velocity times. A per-card slot (`card`, no file chosen yet) has `align: "motion-start"`: each card's sound starts as that card leaves the packet (the file's audible onset, `sound.js` `audibleOnsetMs`, on the card's departure, scaling with the pace), and every card's sound plays, overlapping freely (no gap, a voice per card). `TABLE_TIMING` reads `dealMs` and `dealStaggerMs` from it. The playroom DoubleDeal keeps the old 4×13 layout (no sound) until its other moves have moved | `micro/doubledeal-grid-deal/` (the deal, both grids at real size, 8 columns × 13 rows) | **Animation APPROVED and LOCKED at `7b5028f`** (Zachary: "at speed it looks fine"): the motion, timing (`pace` 1.8, `dealMs` 260, `dealStaggerMs` 36, the card hop `liftHop` 0.9), the real-size layout and the camera of `0aef6e8`; pinned by `library.test.mjs`. Sound on hold project-wide: the stream sound is unapproved and the per-card sound is pending (`card: null`) |
| `carry` | nothing yet (the playroom flights, `toy-director.js` flyToy, unbox lay/aside, move here once approved) | `micro/carry/` (only a carry: the KEY and MSG deck boxes carried between poses on the felt and the shelf, 24 seeded cycles, each from where the last left off: the real poses (borrowed to the table centre, set aside at the rests, home in the shelf slot), flips, half turns, its side, the felt's far edge, shortest hop to longest flight, 12 mm beside the other box, random; the chest is shut scenery and nothing else moves) | **not yet approved**: laws in `carry/settings.js` (vertical take-off and touchdown, a Bézier arc whose top is 3 cm + 18 % of the horizontal distance above the higher end, capped at 50 cm, raised until the box clears every solid by 3 cm; smootherstep pace along the path, fastest half way; duration 450 + 650 × √(path m) ms in 500–2000; slerp over the middle 12–88 % of the path) |
| `hinge` | nothing yet (`toy-director.js` animateLid, `unbox-physical.js` unboxFlap / restow flap close move here once approved) | `micro/hinge/` (only a swing: each cycle cuts to a new seeded placement and only the hinge moves; 19 cycles the KEY tuck box set down at a new pose and its flap swings (table centre, shelf slot, lying on its back so the felt stops it, face down, on its side, 5 mm from the shelf's backboard so it meets it, 6 mm from the MSG box, half swings, random), 5 cycles the chest set down at its own spot and its lid swings (its corner, turned as the live room has it so the lid meets the wall, a step in front of the shelf so it meets the shelf board, random spots)) | **not yet approved**: curves in `hinge/settings.js` (chest lid opens 640 ms easeInOutCubic with a 3 % overshoot settling back, drops shut in 520 ms under its weight with a 3.5 % rebound; tuck flap opens 380 ms with a 6 % overshoot, tucks shut in 300 ms; partial sweeps ms × √fraction; stops short of anything in its sweep) |

**The chest in the primitive microdemos is turned to yaw π (proposed).**
In the live playroom (yaw π/2) its lid hinges on the wall side and its
47 cm dome swings 35 cm into the wall at full open (the drawn dome meets
the wall at about 26°; its planning box at 6°, where the hinge microdemo's
yaw π/2 cycle stops it). Turned half round against the same wall, it
opens clear of the wall and of every flight out of it. The live room is unchanged until Zachary
decides; `room.js` CHEST and `library.test.mjs` record both.

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
