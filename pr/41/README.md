# Demos (playroom)

The playroom hub is `demos/`. GitHub Pages publishes that tree.

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

Motion proof strips (agents / review): `?debugCapture=1` samples the canvas **after** `world.render` on named beats (`markBeat`) and every 240 ms of animation time (`CLOCK_STEP_MS` cap, same as the director / beat-clock / camera). Beat marks only label the next rendered frame — they do not snapshot a stale or pre-render canvas. Nearly-black frames are dropped. Production is a no-op without the flag (`installCapture` returns stubs; no rAF work, no overlay, no `toDataURL`). Headless:

```sh
# serve demos/, then
CAPTURE_TAG=before CAPTURE_URL=http://127.0.0.1:4173 \
  CAPTURE_OUT=/opt/cursor/artifacts/strips \
  node demos/playroom/run-capture-strips.mjs
```

Sheets land in `$CAPTURE_OUT` as `{tag}_{algo}-{enter|leave}_strip.png` plus per-frame JPEGs under `{tag}/{algo}-{enter|leave}/`. Overlay on each frame: beat label + ms. Do not claim enter/leave smoothness without a strip. Chest hinge is locked (opens into the room) unless a strip shows a regression.

Scramble’s 3D cube is cubing.js (`createTwistyRig` in `playroom/twisty-rig.js`), adopted into the playroom scene. Session Play / Step / Reset / speed drive `player.alg` and the Twisty timeline. Notes, license, and remaining hand-rolled bits: `playroom/CUBING.md`. Rollback: `?legacyCube=1`.

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
