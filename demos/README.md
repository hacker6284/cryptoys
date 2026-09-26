# Demos (playroom)

The playroom hub is `demos/`. GitHub Pages publishes that tree.

## IO fields

Message / Key / Nonce / Digest (and standalone DoubleDeal output) use the shared growable field in `shared/grow-field.css` + `shared/grow-field.js`. Fields start at one row and grow with content. Height cap is `--grow-field-max: 8.5rem` (~5–6 lines at 15px / 1.4); past that the field scrolls so one box cannot eat the stage or the portrait IO band. Portrait transport stays on the stage (`--io-band`). Prefer grow over truncate — do not clip with ellipsis or a one-line `<input>`.

Live-hashed inputs (Message, plus DoubleDeal Key / Nonce) also have a **4096-character** length cap (`shared/input-cap.js`). Paste/input over the cap keeps the first 4 KiB, drops the rest, and shows a quiet “Kept the first 4,096 characters.” note. Digest updates are debounced (150ms). **Typing updates Digest only** (`shared/live-digest.js`). Scramble does not call cubing.js `setAlg` / rebuild the leave-trace until Play, Step, or teach. DoubleDeal already keeps `preview` (Digest + first-block layout) off the play `computeTrace`. Digest for a capped message still shows in full.

Scramble can also hash a **file** (`shared/file-hash.js`, `scramble/hash-worker.js`). File is a separate path: first ceiling **10 MB**, Message shows filename + size (never the bytes), and the worker `update`s the generated impl in chunks while dropping the teach step list (no host conversion of a leave list, no `setAlg` until Play). Digest fills when the worker finishes. Play / Step stay on for files ≤ 4 KiB (same scale as typed Message) via `ensureTimeline`; larger files keep Digest correct and skip the leave list. Oversized picks are rejected with a quiet note. Clear/replace returns to typed Message. DoubleDeal Message is cipher plaintext, not a hash input — no file path there.

## Local

```sh
export SUDOC=/path/to/sudoc
sh tools/build.sh
# then serve this directory, e.g. python3 -m http.server --directory demos
```

`tools/build.sh` writes `generated/` and a SPEC copy next to each demo. Those paths are gitignored; CI generates them before publish.

## Production

https://hacker6284.github.io/cryptoys/ and https://cryptoygraphy.com/ (`cryptoys.onrender.com`).

Scramble and DoubleDeal both run in the room (`?algo=scramble`, `?algo=doubledeal`). DoubleDeal enter is continuous: KEY tuck-box off the shelf, MSG deck out of the toy chest, physical unbox / packet deal, boxes set standing on the felt, then the live 4×13 lays from those two decks. No opacity fades and no hide-prop / show-table cut. Shared playroom motion helpers (`playroom/motion.js`: hop, hold, camera track, rest seat) drive that path; flap/extract and 4×13 form stay DoubleDeal-only. Skip / reduced-motion use a shorter continuous path (shared pose controller may still instant-seat for `prefers-reduced-motion`). Scramble’s product dock is 3×3 only. Megaminx / pyraminx stay behind the room debug flag: `?algo=scramble&debug=1` shows the Puzzle control; `?puzzle=megaminx` or `puzzle=pyraminx` is ignored unless `debug=1`. The standalone teaching pages remain at `scramble/?standalone=1` and `doubledeal/?standalone=1`.

Scramble’s 3D cube is cubing.js only (`createTwistyRig` in `playroom/twisty-rig.js`), adopted into the playroom scene, scaled to the real-life 57 mm table edge from local (not world) bounds, kept at that edge for the whole scene, and seated from the post-scale AABB. Session Play / Step / Reset / speed drive `player.alg` and the Twisty timeline. Notes, license, and remaining hand-rolled bits: `playroom/CUBING.md`. The standalone teaching page remains at `scramble/?standalone=1`.

Motion proof strips (agents / review): `?debugCapture=1` samples the canvas **after** `world.render` on a **fixed 200 ms play-time grid**, plus named beats and `camAccel` spikes. Beats do not redistribute the grid. Nearly-black frames are dropped. Production is a no-op without the flag. Headless:

```sh
# serve demos/, then
CAPTURE_TAG=after CAPTURE_URL=http://127.0.0.1:4173 \
  CAPTURE_OUT=/opt/cursor/artifacts/strips \
  node demos/playroom/run-capture-strips.mjs
```

Sheets land in `$CAPTURE_OUT` as `{tag}_{algo}-{enter|leave}_strip.png` plus per-frame JPEGs under `{tag}/{algo}-{enter|leave}/`. Overlay on each frame: beat label + ms. Do not claim enter/leave smoothness without a strip. Chest hinge is locked (opens into the room) unless a strip shows a regression.

**Render must generate, then publish `demos/`.** `generated/*.mjs` is gitignored on `main`. The static site deploys from `main` with build command `sh tools/render-build.sh` (same `sudoc` + `tools/build.sh` path as Pages) and publish directory `demos`. Do not publish ungenerated `demos/` and do not point Render at `gh-pages`. Dashboard fields: `.github/RENDER.md`.

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
