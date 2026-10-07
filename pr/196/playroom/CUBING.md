# cubing.js in the playroom

Production Scramble (`?algo=scramble`) adopts a cubing.js `TwistyPlayer` 3D
object into the shared playroom scene. The Maps chrome, Message-first dock,
and crypto session are unchanged.

Spike that proved adopt-into-scene (isolated page, not this path):
[PR #27](https://github.com/hacker6284/cryptoys/pull/27),
`demos/cubing-spike/NOTES.md` on `cursor/cubing-js-spike-3b69`.

## What cubing.js owns

`createTwistyRig` / `adoptTwistyPuzzle` in `twisty-rig.js`:

| Ours | cubing.js |
| --- | --- |
| construct / adopt | `new TwistyPlayer({ puzzle, alg, hintFacelets: "none", backView: "none", background: "none", controlPanel: "none" })` then `experimentalCurrentThreeJSPuzzleObject` |
| Play | `player.play()` |
| Pause | `player.pause()` |
| Reset | `player.jumpToStart()` |
| Step / session leaf | `experimentalModel.indexer` + `detailedTimelineInfo` + `timestampRequest.set` |
| setAlg | `player.alg = "…"` |
| Setup (Solve) | `player.experimentalSetupAlg` |
| Tempo | `player.tempoScale` (speed slider) |
| Seat / fly | translate `rig.group` (toy-director from motion #25) |
| Lift-off-felt | `stageCubeView` still lifts `rig.group.y` (#25). `rig.lift` is the local hook. |
| Size | scale `rig.fit` only — never the adopted Object3D. Every toy is at real-life scale (invariant; never fit a toy to another toy's box): each puzzle is fitted to its own real measure from `REAL_SIZES` in `constants.js` (3×3 57 mm edge, megaminx 70 mm face to face, pyraminx 97 mm edge), measured on that true measure, not the bounding box. Fit from **local** TRS (`fitToRealSize` / `keepFitted`), then re-apply on every Twisty `render-scheduled` and again in `world.render` so a post-spawn layout cannot permanently crush the puzzle. |

Session moves (including Rule B / seat as `x`/`y`/`z`) become `player.alg`.
`createScrambleSession` drives that timeline via `playLeaves` / `jumpToLeaf`.
Typing / paste updates Digest only; `setAlg` waits for Play / Step / teach
(`shared/live-digest.js`).

Product Scramble is 3×3 only. Megaminx / pyraminx stay in the dock as a
debug toolkit (`?debug=1`, same flag as flight / beat debug): 3×3,
Mega, Pyra. Selection calls `swapPuzzle` (recreate the player — cubing
leaves the adopted object stale). Deep link:
`?algo=scramble&debug=1&puzzle=megaminx`. Without debug, `?puzzle=` is
ignored and the control is hidden.

The hash walk is 3×3 only (normative Scramble SPEC). Digest stays the 3×3
Scramble digest on every puzzle. Megaminx plays U/R/F/D/L/B face turns
(visual only). Pyraminx plays U/R/L/B. cubing.js rejects the whole alg if
it contains `x`/`y`/`z` on those puzzles, so Rule B / seat rotations are
dropped — Play/Step still advance; those leaves are empty. Solve is 3×3
only. MegaDreifach is a different product; this UI does not run it.

MegaDreifach ([`drei-stage.js`](drei-stage.js)) seats **three** megaminx
rigs (`createTwistySeat`, edge `MINX` 72 mm): A (the shelf toy `drei`),
B and C as their own toys (`dreiB`, `dreiC`) that fly from the toy chest.
All three stand straight on the felt in one row, B | A | C, as wide as
the deal (no tray, cups or label cards; the roll call's status line names
them left to right). Each gets its
own player and alg (the show's A / B / C move lists, literal turns such
as `U2'`); grips are a quaternion on `rig.lift`, never on the adopted
object. Adopting three players costs about three times the 3×3 boot on
software GL. `playLeaves` takes an optional `onLeaf(index)` callback
(used only by MegaDreifach, for its turn sound and to ring the face each
turn moves); without it behaviour is unchanged. The puzzles always rest
on the felt: face turns play seated, and a re-grip or King spin lifts
A by `REGRIP_HOP` (14 mm) while it rotates, then sets it down. A puzzle
is only ever solved by undoing its turns (SPEC §5.7): on leave each rig
keeps its turns since it was last solved (its alg becomes that list,
jumped to the end), and the next enter plays them backwards, fast, in
the scene (`resetPuzzles`). The list lives in the page, so a reload
starts solved. The fast-forward (blocks 2–N) puts the trace's final positions on the
rigs with an empty alg and `experimentalModel.setupTransformation`
(`megadreifach/pattern.js` builds the KTransformation); the next enter
clears it with a spin instead of an undo. Rest heights come from `measureLocalBox(seat.fit)`: a
world box measured mid-flight left C floating.

## Host / matrix / three.js

- Host stays a tiny in-viewport canvas (`80×56`, opacity `0.02`).
  `display:none` / `visibility:hidden` hang adopt forever.
- Do not write the adopted Object3D matrix. Twisty keeps writing it; a
  wrapper (`rig.fit`) is how we hit the puzzle's real size. Mutating the puzzle object made
  pyraminx vanish on the spike.
- Fit from the puzzle's **local** shape (parent-space TRS), not a
  rotated world box: its face-to-face width (narrowest across its face
  normals) or its edge (longest line across), per `REAL_SIZES`.
- Measure and seat only what three.js draws (`drawnRanges` in
  `motion.js`). cubing.js keeps hidden geometry in the same buffers
  (hint stickers behind invisible group materials). Counting it fitted
  the megaminx's visible faces to 52.7 mm instead of 70 and seated it
  9.6 mm above the felt. Seating uses the exact drawn vertices, not a
  mesh bounding box. Shelf yaw used to inflate the measured edge and
  lock in an undersized scale for the rest of the scene.
- `keepFitted` runs on Twisty's render-scheduled callback and on every
  host frame. Rest-pose `nativeMeasure` is locked; only a *root*
  `puzzle.scale` change remeasures. Face-turn cubie AABB swell cannot
  pulse scale. `playLeaves` sets `turnBusy` so mid-turn frames skip
  remesure entirely.
- Seat surface is explicit (`userData.seatSurface`). Borrow writes
  `table`, home writes `shelf`. Fit-change reseat uses that, never
  `flightBusy ? table : shelf`.
- Judge size in **world space** (`userData.worldEdge` / AABB Y, ~0.057 m).
  Wide hub frames looking small are camera distance, not underscale.
  Real-life check: a classic 3×3 is slightly shorter than a poker card
  width (63 mm) and shorter than the standing deck box.
- **`instanceof THREE.Object3D` is false.** cubing ships its own `three`
  despite the import map. Meshes still render.
- Adopted look is **MeshBasicMaterial**. Stickers ignore pendant/HDR.
  Plastic-look retarget is later — not this PR.

## Highlights

Layer / cubie / Rule B glow has no cubing.js equivalent. Those view methods
are no-ops. Teach copy still names the turn.

## `createCubeRig`

Playroom has one drawing path: cubing.js `TwistyPlayer`. There is no
`?legacyCube=1` fallback and no hand-rolled hub mesh. Standalone
`scramble/?standalone=1` still uses `createCubeRig` for the teaching
page (not a playroom twisty toy).

## Deps / license

CDN pin: `https://cdn.cubing.net/v0/js/cubing/twisty` (official v0, cubing
0.63.x). Not vendored, not forked.

**MPL-2.0 OR GPL-3.0-or-later.** Library use is fine. Do not fork or patch
cubing.js in-tree without publishing those modifications.

Attribution: [cubing/cubing.js](https://github.com/cubing/cubing.js),
js.cubing.net team.

## Hand-rolled remaining

- Placement on shelf / felt (`getShelfPose` / `getTablePose`)
- Lift / fly (`toy-director` on `rig.group`, turn lift in `cube-stage.js`)
- Room camera framing (`poses.js`)
- Playroom chrome / teach dock
- Scramble digest (crypto session, not 3D)
- Teach highlights (gated)

**Not remaining:** cubie meshes, facelet paint, layer pivots, alg
interpolation, megaminx/pyraminx geometry.
