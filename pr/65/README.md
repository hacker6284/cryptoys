<!-- Owns: the playroom and demo behaviour, local demo builds, production URLs and PR previews. Maintenance rules: ../DOCS.md. -->
# Demos (playroom)

The playroom hub is `demos/`. GitHub Pages publishes that tree.

## IO fields

Message / Key / Nonce / Digest (and standalone DoubleDeal output) use the shared growable field in [`shared/grow-field.css`](shared/grow-field.css) + [`shared/grow-field.js`](shared/grow-field.js). Fields start at one row and grow with content. Height cap is `--grow-field-max: 8.5rem` (~5–6 lines at 15px / 1.4); past that the field scrolls so one box cannot eat the stage or the portrait IO band. Portrait transport stays on the stage (`--io-band`). Prefer grow over truncate — do not clip with ellipsis or a one-line `<input>`.

Live-hashed inputs (Message, plus DoubleDeal Key / Nonce) also have a **4096-character** length cap ([`shared/input-cap.js`](shared/input-cap.js)). Paste/input over the cap keeps the first 4 KiB, drops the rest, and shows a quiet “Kept the first 4,096 characters.” note. Digest updates are debounced (150ms). **Typing updates Digest only** ([`shared/live-digest.js`](shared/live-digest.js)). Scramble does not call cubing.js `setAlg` / rebuild the leave-trace until Play, Step, or teach. DoubleDeal already keeps `preview` (Digest + first-block layout) off the play `computeTrace`. Digest for a capped message still shows in full.

Scramble's Message also takes a **file** (paperclip; [`shared/file-hash.js`](shared/file-hash.js)). Files are up to **10 MB** and never go into the textarea, so the 4096-character cap does not apply; a row under Message shows name and size. The file's bytes are the message, as with hex Message. A Web Worker ([`scramble/hash-worker.js`](scramble/hash-worker.js)) hashes them on a JS cube ([`scramble/fast-hash.js`](scramble/fast-hash.js), tested against the generated module) and Digest fills when it finishes. While a file is selected, typing and Encoding do not touch Digest; Gen rehashes the file. Play / Step / Skip to end walk files up to 4 KiB and stay off above that. Clear returns to typed Message.

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
- One entry in [`playroom/demos.js`](playroom/demos.js) (fields described there). Every name in `toys` must already be in `world.toys`. A new toy means [`playroom/world.js`](playroom/world.js) work (the toy with its `rim:<name>` light, its shelf pose for `shelfHome`), a `SLOTS` entry in [`playroom/constants.js`](playroom/constants.js), and maybe a fly beat.

Still manual:

- [`index.html`](index.html): hub button with the title as its label, and the noscript link (`playroom/room.test.mjs` checks both against the registry). The load-error text in [`playroom/app.js`](playroom/app.js) names the demos too.
- The `build_one` line in [`tools/build.sh`](../tools/build.sh) and the `test -f` lines in [`tools/generate-demos.sh`](../tools/generate-demos.sh).
- The primitive's path in the `paths` filter of [`preview.yml`](../.github/workflows/preview.yml). Its PR comment links only Scramble's generated module.
- The required generated files in [`.github/RENDER.md`](../.github/RENDER.md).
- Demo-named branches: `writeQuery` in `playroom/app.js` keeps `?puzzle=` only for `scramble`; [`playroom/toy-director.js`](playroom/toy-director.js) names the `cube-fly` / `key-fly` and `msg-out` beats (`capture-strip.test.mjs` reads `cube-fly`).

## Production

https://hacker6284.github.io/cryptoys/ and https://cryptoygraphy.com/ (`cryptoys.onrender.com`).

Scramble and DoubleDeal both run in the room (`?algo=scramble`, `?algo=doubledeal`). The standalone teaching pages remain at `scramble/?standalone=1` and `doubledeal/?standalone=1`.

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

**Review:** open the preview URL, click **Scramble**, and confirm the generated module loads (teach dock appears; no import / 404 error). Then **Back** and click **DoubleDeal** — the deck should leave the shelf and the same Maps dock should run the card tool in-room. Smoke-check `scramble/generated/scramble.mjs` and `doubledeal/generated/doubledeal.mjs` — they should be HTTP 200 and JavaScript.

Files land on the `gh-pages` branch under `pr/<N>/`. Official Pages is a single artifact from `main`, so the `github.io` URL appears after `republish-pages` (or the next `pages` deploy) copies that branch. Closing the PR deletes `pr/<N>/`.

Optional: after a `pages` deploy from `main` has written the production root to `gh-pages`, Settings → Pages → **Deploy from a branch** (`gh-pages` / `/`) makes every `gh-pages` push live without republish. Do not switch while the branch is preview-only or production 404s. Keep `.nojekyll` (sudoc emits `_*.mjs`).
