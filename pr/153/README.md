<!-- Owns: the playroom and demo behaviour, local demo builds, production URLs and PR previews. Maintenance rules: ../DOCS.md. -->
# Demos (playroom)

The playroom hub is `demos/`. GitHub Pages publishes that tree.

## IO fields

Message / Key / Nonce / Digest (and standalone DoubleDeal output) use the shared growable field in [`shared/grow-field.css`](shared/grow-field.css) + [`shared/grow-field.js`](shared/grow-field.js). Fields start at one row and grow with content. Height cap is `--grow-field-max: 8.5rem` (~5–6 lines at 15px / 1.4); past that the field scrolls so one box cannot eat the stage or the portrait IO band. Portrait transport stays on the stage (`--io-band`). Prefer grow over truncate — do not clip with ellipsis or a one-line `<input>`.

Live-hashed inputs (Message, plus DoubleDeal Key / Nonce) also have a **4096-character** length cap ([`shared/input-cap.js`](shared/input-cap.js)). Paste/input over the cap keeps the first 4 KiB, drops the rest, and shows a quiet “Kept the first 4,096 characters.” note. Digest updates are debounced (150ms). **Typing updates Digest only** ([`shared/live-digest.js`](shared/live-digest.js)). Scramble does not call cubing.js `setAlg` / rebuild the leave-trace until Play, Step, or teach. DoubleDeal already keeps `preview` (Digest + first-block layout) off the play `computeTrace`. Digest for a capped message still shows in full.

Scramble's Message also takes a **file** (paperclip) of up to **4 KiB** (`FILE_MAX_BYTES` in [`scramble/session.js`](scramble/session.js)), a cap set by the generated module's speed. Its bytes are the message, as with hex Message, and never go into the textarea; a row under Message shows name and size. A Web Worker ([`scramble/hash-worker.js`](scramble/hash-worker.js)) runs the generated module's `update` + `evaluate` ([`scramble/hash.js`](scramble/hash.js)) once over the bytes. If the Worker fails, the page runs it and blocks (up to ~5 s at the cap in Gen 2). While a file is selected, typing and Encoding do not touch Digest; Gen rehashes the file. Clear returns to typed Message.

## Local

```sh
export SUDOC=/path/to/sudoc
sh tools/build.sh
# then serve this directory, e.g. python3 -m http.server --directory demos
```

[`tools/build.sh`](../tools/build.sh) writes `generated/` and a SPEC copy next to each demo. Those paths are gitignored; CI generates them before publish. `tools/build.sh` looks for `sudoc` at `~/Documents/Projects/sudocode/sudoc/target/debug/sudoc` when `SUDOC` is unset.

## Adding a demo

A demo supplies:

- `<id>/index.html` and `<id>/app.js`: the standalone page the noscript link opens, with `<id>/session.js` (the session both pages drive) and `<id>/view.js` (the standalone view).
- A camera pose in [`playroom/poses.js`](playroom/poses.js), unless it reuses one.
- An adapter in [`playroom/adapters.js`](playroom/adapters.js). Required:
  - `install(world, opts)`, at boot: registers every light the demo will use before `world.lights.seal()`; each must be visible at seal and dark until needed ([`shared/lights.js`](shared/lights.js)).
  - `preload()`: loads the session module and assets; called at boot and again on enter.
  - `view()`: its playroom view; once the toys land, the playroom calls the view's optional `rememberSeated()`.
  - `enter({ snap })`: its enter choreography; mounts the dock, creates the session with its view, shows the dock.
  - `leave({ snap })`: disposes the session, closes the dock, resets its props.
- Optional adapter hooks:
  - `ready()`: boot waits for it before the hub is ready.
  - `prepareEnter()`: runs while the camera leaves the hub; the toys fly once it resolves.
  - `skipEnter()`: click / Escape during enter.
  - `busy`: true while enter choreography runs, so click / Escape can skip it.
  - `leaveMs({ snap })`: length of `leave()`'s own beats; the camera's shot home spans them plus the flight home.
  - `revealShelf()`: after the toys are home (or a failed enter), shows its shelf props again.
- Toys: the hub shelf holds exactly **one** copy of each toy. Extra copies live in the toy chest (kept in boxes where the toy has one) and come out when a demo needs them (`chest: true`; every toy after the first in `toys` flies from the chest). Strength settings that need more toys pull them from the chest inside the scene.
- One entry in [`playroom/demos.js`](playroom/demos.js) (fields described there). Every name in `toys` must already be in `world.toys`. A new toy means [`playroom/world.js`](playroom/world.js) work (the toy with its `rim:<name>` light, its shelf pose for `shelfHome`), a `SLOTS` entry in [`playroom/constants.js`](playroom/constants.js), and maybe a fly beat.

Still manual:

- [`index.html`](index.html): hub button with the title as its label, and the noscript link (`playroom/room.test.mjs` checks both against the registry). The load-error text in [`playroom/app.js`](playroom/app.js) names the demos too.
- The `build_one` line in [`tools/build.sh`](../tools/build.sh) and the `test -f` lines in [`tools/generate-demos.sh`](../tools/generate-demos.sh).
- The primitive's path in the `paths` filter of [`preview.yml`](../.github/workflows/preview.yml). Its PR comment links only Scramble's generated module.
- The required generated files in [`.github/RENDER.md`](../.github/RENDER.md).
- Demo-named branches: `writeQuery` in `playroom/app.js` keeps `?puzzle=` only for `scramble`; [`playroom/toy-director.js`](playroom/toy-director.js) names the `cube-fly` / `key-fly` / `drei-fly` and `msg-out` beats (`capture-strip.test.mjs` reads `cube-fly`).

## Production

https://hacker6284.github.io/cryptoys/ and https://cryptoygraphy.com/ (`cryptoys.onrender.com`).

Scramble, DoubleDeal and MegaDreifach all run in the room (`?algo=scramble`, `?algo=doubledeal`, `?algo=megadreifach`). The standalone teaching pages remain at `scramble/?standalone=1`, `doubledeal/?standalone=1` and `megadreifach/?standalone=1`.

MegaDreifach puts three cubing.js megaminxes (A carries `h`, B `h⁻¹`, C stays solved) on a tray with folded paper tent cards, plus a boxed 52-card deck. The shelf holds one megaminx (A, on the tray: toy `drei`); B and C (`dreiB`, `dreiC`) and the DEAL deck (`deck3`) come out of the toy chest, 260 ms apart, and B and C land in their cups on the tray. Hashing and the show trace run in a Web Worker on the generated module ([`megadreifach/worker.js`](megadreifach/worker.js)); the show plays every turn of block 1 from the generated `trace_hash`: the cook, the deal, 52 card steps and 36 F3 rounds, and the full 3-solve (SPEC §5.7). A one-block message (up to 19 bytes) is the whole show. Longer messages then get a marked **fast-forward**: a “Fast-forward: blocks 2–N” line with a block counter, the three puzzles spinning in a blur and the deck dealing face down and gathering, for 1.4–5 s. No turns or card faces of those blocks are shown. The puzzles settle on the trace's real last chaining value (A = h, the digest), its inverse (B) and solved (C), set as cubing.js setup positions: [`megadreifach/pattern.js`](megadreifach/pattern.js) maps a generated Position onto the cubing.js megaminx, working the piece numbering out from the generated face turns and cubing.js's own moves (no hand table). Reduced motion snaps to the end state. Block 2's undo alone would add 1,656 turns, a third block 3,696, which is why later blocks are not played turn by turn. The table is laid out square to the seat: deck box, then the tray (B | A | C, each with its tent card), with the deal in four rows below, as wide as the tray. Teach mode gives one action per step (turn a face, read a piece, re-grip), rings the face being turned and dots the piece being read. On **Back** everything goes home (cards into their box, B and C into the chest, the tray to the shelf) but the puzzles stay as they were; the next enter undoes their turns in place (after a fast-forward there is no short word to undo, so they spin back to solved). It is also the only demo with **sound**: CC0 clicks, card and chime files ([`megadreifach/assets/LICENSE.md`](megadreifach/assets/LICENSE.md)) through Web Audio, started by the first gesture, thinned at high speed, with a Sound toggle in the dock.

DoubleDeal enter is continuous: KEY tuck-box off the shelf, MSG deck out of the toy chest, physical unbox / packet deal, boxes set standing on the felt, then the live 4×13 lays from those two decks. No opacity fades and no hide-prop / show-table cut. Shared playroom motion helpers ([`playroom/motion.js`](playroom/motion.js): hop, hold, camera track, rest seat) drive that path; flap/extract and 4×13 form stay DoubleDeal-only. Skip / reduced-motion use a shorter continuous path (shared pose controller may still instant-seat for `prefers-reduced-motion`).

Scramble’s product dock is 3×3 only. Megaminx / pyraminx stay behind the room debug flag: `?algo=scramble&debug=1` shows the Puzzle control; `?puzzle=megaminx` or `puzzle=pyraminx` is ignored unless `debug=1`.

Scramble’s 3D cube is cubing.js only (`createTwistyRig` in [`playroom/twisty-rig.js`](playroom/twisty-rig.js)), adopted into the playroom scene, scaled to the real-life 57 mm table edge from local (not world) bounds, kept at that edge for the whole scene, and seated from the post-scale AABB. Session Play / Step / Reset / speed drive `player.alg` and the Twisty timeline. Notes, license, and remaining hand-rolled bits: [`playroom/CUBING.md`](playroom/CUBING.md).

Motion proof strips (agents / review): `?debugCapture=1` samples the canvas **after** `world.render` on a **fixed 200 ms play-time grid**, plus named beats and `camAccel` spikes. Beats do not redistribute the grid. Nearly-black frames are dropped. Production is a no-op without the flag. Headless:

```sh
# serve demos/, then
CAPTURE_TAG=after CAPTURE_URL=http://127.0.0.1:4173 \
  CAPTURE_OUT=/opt/cursor/artifacts/strips \
  node demos/playroom/run-capture-strips.mjs
```

Sheets land in `$CAPTURE_OUT` as `{tag}_{algo}-{enter|leave}_strip.png` plus per-frame JPEGs under `{tag}/{algo}-{enter|leave}/`. Overlay on each frame: beat label + ms. Do not claim enter/leave smoothness without a strip. Chest hinge is locked (opens into the room) unless a strip shows a regression.

Render (`cryptoygraphy.com`) must generate, then publish `demos/`: [`.github/RENDER.md`](../.github/RENDER.md).

## PR previews

GitHub Actions, same `sudoc` generate as `pages.yml`. Not Render PR previews.

Same-repo PRs that touch `demos/**`, the generate workflows, or the sudo that feeds generate publish a playroom at:

```text
https://hacker6284.github.io/cryptoys/pr/<N>/
```

The workflow leaves a sticky PR comment with that link.

**Review:** open the preview URL, click **Scramble**, and confirm the generated module loads (teach dock appears; no import / 404 error). Then **Back** and click **DoubleDeal** — the deck should leave the shelf and the same Maps dock should run the card tool in-room. Then **MegaDreifach** — the tray and a deck land on the felt, the three puzzles hop, and KAT → any vector says “digest matches the KAT file ✓”. Smoke-check `scramble/generated/scramble.mjs`, `doubledeal/generated/doubledeal.mjs` and `megadreifach/generated/megadreifach.mjs` — they should be HTTP 200 and JavaScript.

Files land on the `gh-pages` branch under `pr/<N>/`. Official Pages is a single artifact from `main`, so the `github.io` URL appears after `republish-pages` (or the next `pages` deploy) copies that branch. Closing the PR deletes `pr/<N>/`.

Optional: after a `pages` deploy from `main` has written the production root to `gh-pages`, Settings → Pages → **Deploy from a branch** (`gh-pages` / `/`) makes every `gh-pages` push live without republish. Do not switch while the branch is preview-only or production 404s. Keep `.nojekyll` (sudoc emits `_*.mjs`).
