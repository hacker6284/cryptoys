# Animation library

Organised **by object**, not by mechanism: each object's folder holds its
own moves, and importing it gives a meaningful animation of that object
wherever it is. An entry (a folder with `settings.js`) is the only place
its motion and sound are defined: timings, easings, sound slots, files,
gains and offsets. Everything that plays it imports it.

```
anim/
  index.js            import { deck, chest, cube, megaminx } from "./anim/index.js"
  deck/               the deck: one logical object
    index.js          deck.carry, deck.deal, deck.box, deck.card
    carry/            its carry from place to place (settings.js, index.js, placements.js: the microdemo's seeded flights)
    deal/             its deal into the grid layout (the locked doubledeal grid deal)
    box/              sub-object, the tuck box: deck.box.openFlap(box), deck.box.closeFlap(box) (placements.js: one pose per seed)
    card/             sub-object, a single card: deck.card.turnOver(mesh), deck.card.move(mesh, to) (not yet approved)
  chest/              the toy chest: chest.openLid(chest), chest.closeLid(chest) (placements.js: one spot per seed)
  cube/               the 3×3: face turns and whole-cube rotations (the locked scramble-turn entry)
  megaminx/           the megaminx: face turns (locked)
  battleship/         the Battleship set: one logical object
    box/              its retail box: lid off / on, a unit out / in (not yet approved)
    unit/             a unit: open / close its lid (not yet approved)
  yahtzee/            the dice game's retail box: one logical object
    box/              lid off / on, the cup out / in (not yet approved)
  shared/             helpers the objects share; not entries, no constants of their own
    geom.js           pure geometry: quaternions (slerp), oriented boxes, overlap
    room.js           the playroom's solids and seats, measured from the drawn meshes (the chest at any spot: chestAt)
    poses.js          placement helpers (the deck box's bounds, orientations, a seated pose); no motion
    swing.js          private helper: hinged-part curves, duration law, stop-short scan (each object passes its own constants)
    hop.js            private helper: lift straight up, across, straight down (a lid off, a unit or cup out, a die placed), clearing what is around
    lidbox.js         private helper: a lift-off-lid box's card as oriented boxes and its moves (lid off / on, what it holds out / in), from the object's own constants and settings
    cup.js            the dice cup's shape, written once (like room.js, measured): what holds it (yahtzee/box) and what goes in it (dice) take it from here
    run.js            play a planned move on the real clock; read and set an object's world pose
    voice.js          settings.sounds → a sound.js player with contact timing
    twisty.js         cubing.js move timing shared by the twisty puzzles
    twisty-voice.js   the lift / turns / landing hooks of a twisty puzzle
  sounds/             the files the entries name (generated, see below)
```

## The rule

1. **Defined once.** An entry's values live in its `settings.js` and
   nowhere else. Demo code reads them from the entry; nothing is copied
   or pasted back.
2. **The microdemo audits it.** One page per object move,
   `demos/micro/<object>/<move>/` (e.g. `micro/deck/box/open-close-flap/`,
   `micro/cube/rotate/`), a thin viewer that loops that one move of that
   one object on the real demo code. What you hear and see there is what
   every demo does.
3. **Demos import it.** Demo code calls the entry's hooks (e.g.
   `playroom/cube-stage.js` calls `anim/cube` `scrambleTurnVoice().turns(...)`
   and reads `timing`), so changing a value changes it everywhere at once.
4. **Approved once Zachary signs off.** An entry is marked approved
   below at the commit he heard. Changing an approved entry's values
   needs his sign-off again; bump the commit here when he gives it.

Microdemos not in this table still keep their own `settings.js` in
`demos/micro/<page>/` until they move here. A new entry starts from the
default rules: a turn sound's audible centre at the face's peak
velocity (`align: "peak-velocity"`), the scramble-turn landing pat; a
moving card's sound has its audible centre where the card moves fastest.

## Objects and their moves

An object's moves take **placement as an input** (where it is, where it
goes, any yaw, flips, what is around it); what Zachary approves is the
laws: the timing, the curves and the object's own motion. Rotations use
quaternion slerp; arcs and swings clear whatever is around them
(`shared/room.js` solids, other toys), measured from the drawn geometry.

**Atomic, and one object per microdemo.** Each move is one object doing
one thing. No object imports another (deck's own index gathers its
sub-objects; `library.test.mjs` checks the import graphs). Composing moves
(open the chest, then carry the deck out) is for the real hub demos.

**Microdemos:** one object, one move, one fixed placement, looping so it
can be watched; `?seed=N` picks a different placement on load (real
playroom poses first, then edge cases, then random ones; the seed is shown
small on the page). Carry is the exception: changing place is the move,
so its page flies the deck boxes through 24 seeded flights, the chest shut
and nothing else moving (`?cycle=N`, `?only=N`, `?view=cycle`). Every
page checks what it draws: real sizes, no overlap, seated by drawn
geometry, nothing jumps or scales, duration and peak speed on the law;
`library.test.mjs` runs the same checks over the seeds. The camera's
direction is fixed per page; its distance frames the placement.

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
| `cube` | playroom Scramble seat (`playroom/cube-stage.js`): a click per face turn, a sound per whole-cube rotation, a muffled pat when the cube lands on the felt | `micro/cube/face-turn/` (single, double and triple face turns, one step each), `micro/cube/rotate/` (rotation) | approved by Zachary: the single face-turn click's file and gain, the landing pat and the lift timing at `af9a8fb`; the rotation sound (Sadiquecat broomstick swish, swell at mid-rotation) on 2026-10-02; it now follows the turns' rule (`align: "peak-velocity"`, `centre: "swell"`): its swell at mid-rotation for any rotation (y, y2) at any tempo, unchanged (within 1 ms) for the quarter rotation he approved. **Single, double and triple face-turn sounds approved and LOCKED at `6014bfc`** (Zachary: "All look pretty good."): their files, gains, `align: "peak-velocity"` and `nudgeMs: 0`, under his rule "the audible part of the sound should be centered over the part of the animation where the face is at maximum velocity" (each file's audible centroid half way through its turn, cubing.js smootherStep, at any tempo); pinned by `library.test.mjs` |
| `megaminx` | the megaminx in a cube stage (`playroom/cube-stage.js` with `{ voice: megaminxTurnVoice(), timing }`): a click per face turn (72°), a muffled pat when it lands. MegaDreifach's own stage (PR #194) imports this entry | `micro/megaminx/face-turn/` (single, double and triple turns U, U2, U3, one step each, in the Scramble seat's debug megaminx) | **Animation and sounds APPROVED and LOCKED at `a927bb2`** (Zachary approved the animation: the megaminx at its real 70 mm face to face, seated on the felt by its drawn geometry; the lift, turn tempo and settle timing and every sound as they are). **Single, double and triple face-turn sounds approved and LOCKED at `d952e6a`** (Zachary: "Sounds are ok for that one."): their files, gains, `align: "peak-velocity"` and `nudgeMs: 0` (SpaceJoe clicks centred on peak face velocity, cubing.js smootherStep, half way); pinned by `library.test.mjs`. Landing: scramble-turn's muffled pat |
| `deck/deal` | `doubledeal/table.js` on the real-size layout (`doubledeal/real-layout.js`, via `playroom/card-stage.js` `stageCardTable(..., { layout: REAL_LAYOUT })`): the hand packet, a neat stack with its top card first, dealt card by card onto the message grid, column by column, each card hopping from the packet to its seat; one card-fan sound per deal (Kenney card fan), its audible centre on the mean of the cards' peak-velocity times. A per-card slot (`card`, no file chosen yet) has `align: "motion-start"`: each card's sound starts as that card leaves the packet (the file's audible onset, `sound.js` `audibleOnsetMs`, on the card's departure, scaling with the pace), and every card's sound plays, overlapping freely (no gap, a voice per card). `TABLE_TIMING` reads `dealMs`, `dealStaggerMs` and `liftHop` from it. The playroom DoubleDeal keeps the old 4×13 layout (no sound) until its other moves have moved | `micro/deck/deal/` (the deal, both grids at real size, 8 columns × 13 rows) | **Animation APPROVED and LOCKED at `7b5028f`** (Zachary: "at speed it looks fine"): the motion, timing (`pace` 1.8, `dealMs` 260, `dealStaggerMs` 36, the card hop `liftHop` 0.9), the real-size layout and the camera of `0aef6e8`; pinned by `library.test.mjs`. Sound on hold project-wide: the stream sound is unapproved and the per-card sound is pending (`card: null`) |
| `deck/carry` | nothing yet (the playroom flights, `toy-director.js` flyToy, unbox lay/aside, move here once approved) | `micro/deck/carry/` (only a carry: the KEY and MSG deck boxes carried between poses on the felt and the shelf, 24 seeded cycles, each from where the last left off: the real poses (borrowed to the table centre, set aside at the rests, home in the shelf slot), flips, half turns, its side, the felt's far edge, shortest hop to longest flight, 12 mm beside the other box, random; the chest is shut scenery and nothing else moves) | **not yet approved**: laws in `deck/carry/settings.js` (vertical take-off and touchdown, a Bézier arc whose top is 3 cm + 18 % of the horizontal distance above the higher end, capped at 50 cm, raised until the box clears every solid by 3 cm; smootherstep pace along the path, fastest half way; duration 450 + 650 × √(path m) ms in 500–2000; slerp over the middle 12–88 % of the path) |
| `deck/box` | nothing yet (`unbox-physical.js` unboxFlap / restow flap close move here once approved) | `micro/deck/box/open-close-flap/` (one KEY tuck box at one pose, its flap opened and shut on a loop; `?seed=N`: 1 table centre, 2 shelf slot, 3 lying on its back so the felt stops the flap, 4 on the shelf 5 mm from the backboard so it meets it, 5 face down, 6 on its side, 7 half turn at the felt's edge, 8+ random) | **not yet approved**: `deck/box/settings.js` flap (opens 380 ms to 123°, easeInOutCubic with a 6 % overshoot settling back; tucks shut in 300 ms; partial sweeps ms × √fraction; stops 1 mm short of anything in its sweep) |
| `deck/card` | the MegaDreifach v3 stage (`playroom/drei-stage.js`): each card step turns its card face up on its seat, card 52 moves to the held seat, the echoes turn their counter cards face down, and the gather moves the cards back into the box | none yet | **not yet approved** (placeholders for the v3 demo): `deck/card/settings.js` turnOver (rises, rolls 180° about its long axis, easeInOutCubic, 520 ms, clears its half width + 12 mm) and move (slide easeInOutQuad, hop sin(πu) × 60 mm, 420 ms) |
| `chest` | nothing yet (`toy-director.js` animateLid moves here once approved) | `micro/chest/open-close-lid/` (the chest at one spot, its lid opened and dropped shut on a loop; `?seed=N`: 1 its corner turned to the room, 2 turned as the live room has it so the lid meets the wall, 3 a step in front of the shelf so it meets the shelf, 4+ random spots in view) | **not yet approved**: `chest/settings.js` lid (opens 640 ms to 83°, easeInOutCubic with a 3 % overshoot settling back; drops shut in 520 ms under its weight with a 3.5 % rebound; stops 10 mm short of anything in its sweep) |
| `peg` | the BS stage (`playroom/bs-stage.js`): each peg into a key-grid hole (BUILD) or a lid workspace hole (out of the lid, toward the player), out of one, and slid from the product strip into a register; Play runs them at `tempos.play` (a summary's pegs together), Step at `tempos.step` (one move after another) | `micro/peg/insert-slide-remove/` (a white peg into the key grid and out; a red peg into the workspace, slid two rows, out) | **not yet approved**: `peg/settings.js` insert (approach 420 ms easeInOutCubic from 28 mm out, push the last 5 mm in 140 ms easeInCubic), remove (320 ms easeOutCubic, 28 mm), slide (560 ms easeInOutQuad, a sin(πu) × 20 mm arc); starting values from the pre-library `micro/peg/` page |
| `ship` | the BS stage: BUILD lays a Destroyer and swaps it up as the ship grows (SPEC §4.2); the walk cursor's two Destroyers move along the key grid's frame (§4.3) | `micro/ship/place-move-lift/` (Destroyer laid, swapped for the Sub; the cursor slides along the number strip; both lift off) | **not yet approved**: `ship/settings.js` place (420 ms easeInOutCubic down 30 mm), lift (340 ms easeOutCubic up 30 mm), move (260 ms easeInOutQuad, no hop) |
| `dice` | the BS stage: the row cup's five d10s at a row's first hole (a zero face thrown again), the hole die (d12) and the d6, each landing on the face the generated trace read; entering, each die lifted out of the dice box's strip onto its spot in the row, leaving, back in (`playroom/bs-unbox.js`, `tempos.unbox` / `tempos.repack`) | `micro/dice/roll/` (a d10, the d12 and the d6, each thrown onto its next face), `micro/dice/place/` (a d6, the d12 and a d10 out of the dice box onto their spots and back) | **not yet approved**: `dice/settings.js` roll (640 ms; hop sin(πu) × 50 mm; 2 turns about a tilted axis; slerps onto the landing face over the last quarter); place (a hop, `shared/hop.js`: straight up until its bottom is 15 mm over what it passes (the box's rim, the cup standing on its spot), across turning onto its face (slerp), straight down; each leg easeInOutSine, 90 + 520 × √(leg m) ms in 150–700, ÷ tempo). Face normals of the Facehunter dice (CC0) in `dice/faces.js` |
| `battleship/box` | the BS demo's unboxing (`playroom/bs-unbox.js`, the moves in `playroom/bs-unbox-plan.js`): entering, the Battleship retail box's lid off to its rest, then each unit lifted out to its seat; leaving, the same backwards (`tempos.unbox` / `tempos.repack`) | `micro/battleship/box/lid-off-on/` (the box on the felt, its lid off beside it and back on), `micro/battleship/box/lift-units-out-in/` (the open box, both units lifted out to their seats and back) | **not yet approved**: `battleship/box/settings.js` lid and unit (hops, `shared/hop.js`: straight up until the bottom is 20 mm over the base's walls and anything on the way, across at that height, a unit turning from its pocket to its seat (slerp), straight down; each leg easeInOutSine; lid 140 + 700 × √(leg m) ms in 220–900, unit 140 + 760 × √(leg m) ms in 240–1000, ÷ tempo). The box: 400 × 265 × 52.5 mm (Scrounger's model, CC0), both units in it shut, either side of its card divider |
| `battleship/unit` | the BS demo's unboxing: each unit's lid opened at its seat (T1: the lid's grid is the workspace), shut before it is packed | `micro/battleship/unit/open-close-lid/` (a shut unit, its lid up and down) | **not yet approved**: `battleship/unit/settings.js` lid (opens 760 ms to 90° (the GLB's lid_open), easeInOutCubic, no overshoot; shuts in 640 ms; partial sweeps ms × √fraction; stops 5 mm short of anything in its sweep) |
| `yahtzee/box` | the BS demo's unboxing: entering, the dice box's lid off to its rest, then the cup, lying in its well, lifted out and stood up on its spot (the dice come out of the box's strip after it, `dice` place); leaving, the same backwards | `micro/yahtzee/box/lid-off-on/` (the box on the felt, its lid off beside it and back on), `micro/yahtzee/box/lift-cup-out-in/` (the open box, the cup lifted out lying, stood upright beside it, and laid back) | **not yet approved**: `yahtzee/box/settings.js` lid and cup (hops as `battleship/box`'s: 20 mm over the rim, the cup turning from lying to standing on the way across; lid 140 + 700 × √(leg m) ms in 220–900, cup 160 + 760 × √(leg m) ms in 260–1000, ÷ tempo). The box: 120.3 × 113.6 × 88.6 mm, designed to fit the cup lying and the key dice in a strip beside it (`tools/bs_boxes.py`) |

**The chest in the microdemos stands turned to yaw π (proposed).**
In the live playroom (yaw π/2) its lid hinges on the wall side and its
47 cm dome swings 35 cm into the wall at full open (the drawn dome meets
the wall at about 26°; its planning box at 6°, where the open-close-lid
microdemo's `?seed=2` stops it). Turned half round against the same wall, it
opens clear of the wall and of every flight out of it. The live room is unchanged until Zachary
decides; `shared/room.js` CHEST and `library.test.mjs` record both.

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

Sounds play on the page's one shared AudioContext (`demos/shared/sound.js`):
the hub tap unlocks it, with the iOS fixes, so a demo never needs its
own prompt.
