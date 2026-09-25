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
| Size | scale `rig.fit` only — never the adopted Object3D |

Session moves (including Rule B / seat as `x`/`y`/`z`) become `player.alg`.
`createScrambleSession` drives that timeline via `playLeaves` / `jumpToLeaf`.

Scramble is 3×3. `PUZZLES` + `swapPuzzle` (recreate the player) are the
megaminx / pyraminx hooks. Recreate on puzzle change — cubing leaves the
adopted object stale.

## Host / matrix / three.js

- Host stays a tiny in-viewport canvas (`80×56`, opacity `0.02`).
  `display:none` / `visibility:hidden` hang adopt forever.
- Do not write the adopted Object3D matrix. Twisty keeps writing it; a
  wrapper (`rig.fit`) is how we hit 57 mm. Mutating the puzzle object made
  pyraminx vanish on the spike.
- **`instanceof THREE.Object3D` is false.** cubing ships its own `three`
  despite the import map. Meshes still render.
- Adopted look is **MeshBasicMaterial**. Stickers ignore pendant/HDR.
  Plastic-look retarget is later — not this PR.

## Highlights

Layer / cubie / Rule B glow has no cubing.js equivalent. Those view methods
are no-ops. Teach copy still names the turn.

## `createCubeRig`

Gated, not deleted. Playroom uses cubing.js. `?legacyCube=1` (and adopt
failure) still install the hand-rolled cubie rig. Standalone
`scramble/?standalone=1` still uses `createCubeRig`.

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
