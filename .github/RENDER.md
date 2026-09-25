# Render must generate demos, then publish `demos/`

`cryptoygraphy.com` / `cryptoys.onrender.com` is Render static site `cryptoys`
(`srv-daqdlq0u01pc73fpv6t0`, workspace `tea-cspvckggph6c739g2p40` if still valid).

**Do not publish ungenerated `demos/` from `main`, and do not take the
`gh-pages` shortcut.** `demos/**/generated/` and the copied `demos/**/SPEC.md`
files are gitignored. Scramble imports `./generated/scramble.mjs`; DoubleDeal
imports `./generated/doubledeal.mjs`. A deploy that skips generate 404s those
modules and three.js never boots.

## What the build must do

Same path as GitHub Pages (`.github/actions/generate-demos` →
`tools/generate-demos.sh`):

1. Build `sudoc` from [hacker6284/sudocode](https://github.com/hacker6284/sudocode)
   (`cargo build --release --manifest-path .sudocode/sudoc/Cargo.toml`).
2. Run the primitive JS tests and `tools/build.sh`.
3. Require these files before publish:

   ```text
   demos/scramble/generated/scramble.mjs
   demos/doubledeal/generated/doubledeal.mjs
   ```

`tools/render-build.sh` is that sequence for Render (install rustup if `cargo`
is missing, wipe and shallow-clone sudocode every build, cargo build, then
`tools/generate-demos.sh`). Sudoc is the default-branch tip on both Pages and
Render (no pin); pin later if deploys must be reproducible.

## Dashboard settings (existing service — do not create a second site)

Blueprint (`render.yaml`) records the same values. If the live `cryptoys`
service is not Blueprint-linked, set them under
[Settings → Build & Deploy](https://dashboard.render.com/static/srv-daqdlq0u01pc73fpv6t0):

| Setting | Value |
|---|---|
| Branch | `main` |
| Root directory | empty / repo root (not `demos/`) |
| Build command | `sh tools/render-build.sh` |
| Publish directory | `demos` |
| Auto-Deploy | On commit |

Environment (optional, also in `render.yaml`):

| Key | Value |
|---|---|
| `SKIP_INSTALL_DEPS` | `true` (no `package.json`; skip npm auto-install) |

Save, then **Manual Deploy → Deploy latest commit** after this lands on `main`.
First build compiles `sudoc` (several minutes). Watch the build log for rustup
or `cargo build` errors.

Smoke-check (expect HTTP 200, JavaScript):

```text
https://cryptoygraphy.com/scramble/generated/scramble.mjs
https://cryptoygraphy.com/doubledeal/generated/doubledeal.mjs
```

Apply `render.yaml` only to this existing service. A new Blueprint site would
be a duplicate.
