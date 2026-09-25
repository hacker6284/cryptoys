# SPIKE: cubing.js in the playroom

Isolated page. Production Scramble (`createCubeRig` / `cube.js` facelets) is untouched.

**Preview:** `demos/cubing-spike/` (PR preview: `…/pr/<N>/cubing-spike/`)

```sh
python3 -m http.server --directory demos
# open http://127.0.0.1:8000/cubing-spike/
```

Query: `?puzzle=megaminx` or `?puzzle=pyraminx`.

## What this proves

`TwistyPlayer.experimentalCurrentThreeJSPuzzleObject(cb)` returns a three.js `Object3D`. We parent it under a seat/lift group and add that group to the existing playroom scene (`mountWorld` renderer, lights, camera, HDR). The TwistyPlayer custom element stays in the DOM (required for the 3D object to exist) but is offscreen — no second canvas in the room.

Same adapter surface for **3×3×3**, **megaminx**, and **pyraminx**. Switching puzzles recreates the player: cubing.js documents that changing `puzzle` leaves the adopted object stale.

## API we would own

Thin `createTwistyRig` in `twisty-rig.js`:

| Ours | cubing.js call |
| --- | --- |
| construct / adopt | `new TwistyPlayer({ puzzle, alg, hintFacelets: "none", backView: "none", background: "none", controlPanel: "none" })` then `experimentalCurrentThreeJSPuzzleObject` |
| `play` / `pause` | `player.play()` / `player.pause()` |
| `reset` | `player.jumpToStart()` |
| `step` | `experimentalModel.indexer` + `detailedTimelineInfo` + `timestampRequest.set(endOfLeaf)` |
| `setAlg` | `player.alg = "…"` |
| `setTempo` | `player.tempoScale` |
| seat / fly | translate `rig.group` (same object `toy-director` already flies) |
| lift-off-felt | translate `rig.lift.position.y` |

Do **not** keyframe the adopted puzzle object. TwistyPlayer owns layer animation.

## Motion PR map

Today `toy-director` samples a lift → arc → table path on `world.toys.cube`. After cutover that toy is `rig.group`. Local lift (the first 380 ms off the shelf, or a later “pick up while seated”) can be `rig.lift` so cubing.js move animation and room motion do not write the same transform. Camera framing stays in `poses.js` (`scramble` / `seated`); cubing.js camera latitude/longitude is unused once we adopt the object.

## Materials / look (honest)

Default Twisty stickers are the Twizzle look: saturated speedcube colors, thin plastic, often Lambert/Phong (or PG3D equivalents), not our `MeshStandardMaterial` cubies (`roughness ~0.55`, `metalness ~0.04`, muted room palette). Under playroom ACES + dim HDR they read brighter and flatter than the hand-rolled 57 mm toy.

To match the plastic room aesthetic later (optional, not this spike):

- Traverse adopted meshes and swap in `MeshStandardMaterial` with our `COLOR` / `PLASTIC` hexes, or
- Accept Twisty look and only match *size* / shadows / seat, or
- Ask cubing.js for a style hook if one lands before the experimental 3D API is replaced.

Hint facelets are off (`hintFacelets: "none"`). Shadows are enabled on adopted meshes; they only look right if the material is a lit type.

The on-page note reports live `material.type` counts and `object instanceof THREE.Object3D` against playroom r170.

## Deps

Demos have no `package.json`. Three.js is already a CDN import map (`three@0.170.0`). This spike adds:

```text
https://cdn.cubing.net/v0/js/cubing/twisty
```

Official cubing CDN (workers / WASM-safe). Not vendored, not npm — load only on this page so production Scramble does not pay the download. cubing 0.63.x depends on `three@^0.170.0`, same minor as the room.

**Bundle:** twisty + puzzle-geometry chunks are large (hundreds of KB, more if search/scramble is pulled later). Keep the import on the spike / future adapter, never on the landing playroom module graph.

**License:** cubing.js is **MPL-2.0 OR GPL-3.0-or-later**. Using it as a library is fine; **do not fork/patch cubing.js source in-tree** without publishing those modifications. Attribution: [cubing/cubing.js](https://github.com/cubing/cubing.js), js.cubing.net team. We do not vendor a copy in this spike.

`cdn.cubing.net/v0` is a floating v0 URL. Pin a npm version (or vendor) before a production cutover.

## Risks

1. **Experimental / deprecated API.** `experimentalCurrentThreeJSPuzzleObject` may go away or leave the main thread. Adopt-into-scene is the whole spike; have a fallback (keep TwistyPlayer as a hidden viewport, or fork a thin PG3D loader) before committing the room to it.
2. **three.js instance skew.** If cubing bundles its own `three`, `instanceof Object3D` fails. Meshes often still render; `replaceToy` / shadows / dispose get sharper. Import map `"three"` → 0.170.0 is the intended share. Check the on-page skew line.
3. **Player must stay connected.** The custom element is hidden, not destroyed, while the puzzle is shown. Extra WebGL context inside Twisty is waste; we should confirm whether cubing still spins its own renderer after adopt.
4. **Stale object on `puzzle` change.** Recreate the rig (this spike does).
5. **Alg / orientation.** 3×3 WCA, megaminx `R++ D++`, pyraminx. Scramble’s facelet string and “white up, green front, red right” still have to be mapped onto cubing.js setup/alg — not done here.
6. **License / CDN.** Floating v0 + MPL source-mod publish if we patch.

## Recommended unify plan

1. Keep this adapter (`createTwistyRig`) as the only 3D puzzle path for 3×3, megaminx, pyraminx.
2. Teach `createScrambleAdapter.install` to `replaceToy("cube", rig.group)` behind a flag, then delete the flag. **Do not delete `createCubeRig` until** play + step + reset + speed + teach highlights have a cubing.js equivalent (or we drop highlights).
3. Map Scramble session moves to `player.alg` / `timestampRequest` (or append moves) instead of `animateMove` on cubies.
4. Reuse `rig.group` / `rig.lift` for `toy-director` fly and seated lift. Camera stays room-owned.
5. Megaminx (MegaDreifach) and a future pyraminx demo share the same adapter; only alg / seat / chrome differ.
6. Pin `cubing` (npm or vendored ESM) when leaving spike status. Keep MPL attribution in `demos/`.
7. Beauty pass last: either accept Twisty stickers or retarget materials.

## Hand-rolled remaining (should stay thin)

- Placement on shelf / felt (`getShelfPose` / `getTablePose`)
- Lift / fly (`toy-director` on `rig.group`, local lift on `rig.lift`)
- Room camera framing (`poses.js`)
- Playroom chrome / teach dock
- Scramble-specific: facelet digest, highlights, rule-B glow, reorient-to-white-green

**Not remaining (cubing.js owns):** cubie meshes, facelet paint, layer pivots, megaminx/pyraminx geometry, alg playback interpolation.

## Out of scope (this PR)

Ripping out `createCubeRig` as the only path. Full lift/seat polish. Matching plastic look. Wiring the crypto session. Normative SPEC / `.sudo`.
