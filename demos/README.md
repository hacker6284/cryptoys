<!-- Owns: the playroom and demo behaviour, local demo builds, production URLs and PR previews. Maintenance rules: ../DOCS.md. -->
# Demos (playroom)

The playroom hub is `demos/`. GitHub Pages publishes that tree.

## Real-life scale (invariant)

Every toy in the room is at real-life scale; never fit a toy to another toy's box (Zachary, 2026-10-02: "All toys in real life scale in the room and that's an invariant."). Each toy is sized to its own real measure. A puzzle may share the cube's size only when that is its own real size. The one table of real sizes, with a source beside each to check by eye, is `REAL_SIZES` in [`playroom/constants.js`](playroom/constants.js):

| Toy | Real size | Measure | Source |
| --- | --- | --- | --- |
| 3×3 (Scramble) | 57 mm | edge (face to face) | Rubik's 3×3 "57mm" (rubiksgift.com/faqs); "the original cube size was 57mm" (funCUBING) |
| Megaminx | 70 mm (≈88 mm corner to corner) | face to face | Tomy Megaminx "2.75 inches between opposite faces" (J. A. Storer); ShengShou Megaminx 72 × 72 × 72 mm |
| Pyraminx | 97 mm | edge | QiYi Pyraminx "Edge-Length: 97.0mm"; QiYi QiMing A 97.5 mm |
| Playing card | 63 × 88 mm | face | poker size 2.5 × 3.5 in (63.5 × 88.9 mm) |
| Deck box | 67 × 92 × 20 mm | box | poker tuck box 66 × 91 × 19 mm; Bicycle 807 70 × 95 × 20 mm |
| Toy chest | 95 cm | longest side | IKEA SMÅSTAD 90 cm; KALIX 93.5 cm |

Twisty puzzles are fitted on that true measure ([`playroom/motion.js`](playroom/motion.js) `fitToRealSize`: face to face is the narrowest width across the puzzle's face normals; edge is the longest line across it), not on their bounding box, and `seatOnSurface` seats the live post-scale shape. Known exceptions, waiting on a decision: the playroom DoubleDeal 4×13 grid (`DEAL_SCALE`) draws its cards at 38 × 55 mm (real scale would make the two grids ~1.96 m wide on the 2.05 m table); the DoubleDeal moves that have moved into the animation library use the real-size layout instead ([`doubledeal/real-layout.js`](doubledeal/real-layout.js): 63 × 88 × 0.3 mm cards with the card art redrawn undistorted at 63 : 88, the two grids 8 columns × 13 rows with 4 mm gaps and a 40 mm gutter, 568 × 1192 mm), and the unbox stand-in packets use 1.35 mm thick cards (real ~0.3 mm) so eight cards read as a deck. Shelf plants are set dressing, each fitted to its own height.

## IO fields

Message / Key / Nonce / Digest use the shared growable field in [`shared/grow-field.css`](shared/grow-field.css) + [`shared/grow-field.js`](shared/grow-field.js). Fields start at one row and grow with content. Height cap is `--grow-field-max: 8.5rem` (~5–6 lines at 15px / 1.4); past that the field scrolls so one box cannot eat the stage or the portrait IO band. Portrait transport stays on the stage (`--io-band`). Prefer grow over truncate — do not clip with ellipsis or a one-line `<input>`.

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

- `<id>/index.html`: a forwarder to the playroom's demo (`<script src="../shared/forward.js" data-algo="<id>">`, which keeps the other query parameters and the hash), and `<id>/session.js`, the session the dock drives. Each demo has exactly one implementation, the room's: no standalone page, view or controls (`playroom/one-copy.test.mjs`).
- Speed: the dock's one shared slider ([`shared/speed.js`](shared/speed.js)), 0.1× to 100× on a log scale, 1× (a third of the way along) by default, the multiplier shown beside it. 1× is the demo's locked default tempo; the session hands the multiplier to its view (`view.setSpeed`), which maps it onto its own units. Every pause, hold and motion of Play scales with it; one shorter than a frame jumps to its end and passes its time on [`shared/pacer.js`](shared/pacer.js)'s clock, so every step still applies, in order, and 100× really runs a hundred times faster.
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

Scramble, DoubleDeal and MegaDreifach run only in the room (`?algo=scramble`, `?algo=doubledeal`, `?algo=megadreifach`). Each demo's own address (`scramble/`, `doubledeal/`, `megadreifach/`, old `?standalone=1` links included) forwards there with its other query parameters. Speed is the shared log slider (1× = Scramble 1.4, DoubleDeal 1.8, MegaDreifach 1.4, the locked tempos).

MegaDreifach shows **v3 (ZP26)**, the current version (SPEC: `primitives/hash/megadreifach/v3/SPEC.md`, copied beside the page by `tools/build.sh`). Three cubing.js megaminxes (A carries `h`, B `h⁻¹`, C stays solved) stand straight on the felt, plus the DEAL deck in its tuck box: only toys, at real size (megaminx 70 mm face to face, cards 63 × 88 mm), no tray, pedestals or label cards. The shelf holds A (toy `drei`); B and C (`dreiB`, `dreiC`) and the DEAL deck (`deck3`) come out of the toy chest and land on the felt in one line: deck box | B A C | the held card's seat, with the deal's 13 × 4 grid in front (4 mm between cards, nothing overlaps; `playroom/constants.js` has the layout and `playroom/room.test.mjs` checks it fits on the felt). Hashing runs in a Web Worker on the sudoc-generated module ([`megadreifach/worker.js`](megadreifach/worker.js)); the KAT menu checks the live digest against `megaminx_hash_kats_v3.json`. The message box opens empty. Play uses only the generated `trace_hash` (non-exported, demo-only; v3 sudo, with three sudo tests tying it to `Hash` on every KAT). A one-block message (up to 19 bytes) plays every turn, literally and at the dock's tempo, never truncated or time-lapsed (about 1,500 turns): cook A (IV-COOK12) and B backwards; the deal laid face down from the box (`anim/deck/deal`'s locked law); 52 card steps (each card turns face up where it lies, then its six turns: the rank-and-suit turn, the edge and corner named by colour, five single clicks); card 52 moves to the held seat; 26 echoes (a dealt card turns face down as the counter, the look marks the held pieces' stickers X and Y that give P, then P's six turns); and the 3-solve (B onto A; A onto B and C; C onto A). The cards go back in the box. Longer messages are too long to trace and get the digest only. Every face turn lifts and sets down with `anim/megaminx`'s locked timing via `playroom/cube-stage.js`; the cards use `anim/deck` (box flap, deal, and `deck/card` turnOver / move / straight, not yet approved). Teach mode gives one action per step, rings the face being turned and dots the named edge (cream) and corner (blue). On **Back** the cards go into their box, B and C into the chest, A to the shelf; the puzzles stay as they were and the next enter undoes their turns in place. No sound (on hold).

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

**Review:** open the preview URL, click **Scramble**, and confirm the generated module loads (teach dock appears; no import / 404 error). Then **Back** and click **DoubleDeal** — the deck should leave the shelf and the same Maps dock should run the card tool in-room. Then **MegaDreifach** — three megaminxes and a deck land on the felt (no tray, no labels), the three puzzles hop, and KAT → any vector says “digest matches the KAT file ✓”. Smoke-check `scramble/generated/scramble.mjs`, `doubledeal/generated/doubledeal.mjs` and `megadreifach/generated/megadreifach.mjs` — they should be HTTP 200 and JavaScript.

Files land on the `gh-pages` branch under `pr/<N>/`. Official Pages is a single artifact from `main`, so the `github.io` URL appears after `republish-pages` (or the next `pages` deploy) copies that branch. Closing the PR deletes `pr/<N>/`.

Optional: after a `pages` deploy from `main` has written the production root to `gh-pages`, Settings → Pages → **Deploy from a branch** (`gh-pages` / `/`) makes every `gh-pages` push live without republish. Do not switch while the branch is preview-only or production 404s. Keep `.nojekyll` (sudoc emits `_*.mjs`).
