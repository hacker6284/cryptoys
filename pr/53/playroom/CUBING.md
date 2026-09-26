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
| Size | scale `rig.fit` only — never the adopted Object3D. Target edge is `CUBE` (57 mm, real-life 3×3). Fit from **local** TRS (`fitToLocalEdge` / `keepFitted`), then re-apply on every Twisty `render-scheduled` and again in `world.render` so a post-spawn layout cannot permanently crush the cube. |

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

## Host / matrix / three.js

- Host stays a tiny in-viewport canvas (`80×56`, opacity `0.02`).
  `display:none` / `visibility:hidden` hang adopt forever.
- Do not write the adopted Object3D matrix. Twisty keeps writing it; a
  wrapper (`rig.fit`) is how we hit the playroom `CUBE` edge. Mutating the puzzle object made
  pyraminx vanish on the spike.
- Fit from the puzzle's **local** AABB (parent-space TRS), not a
  rotated world box. Shelf yaw used to inflate the measured edge and
  lock in an undersized scale for the rest of the scene.
- `keepFitted` runs on Twisty's render-scheduled callback and on every
  host frame. Rest-pose `nativeMax` is locked; only a *root*
  `puzzle.scale` change remesures. Face-turn cubie AABB swell cannot
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
