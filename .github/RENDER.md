# Render must serve the generated demo tree

`cryptoygraphy.com` / `cryptoys.onrender.com` is Render static site `cryptoys`
(`srv-daqdlq0u01pc73fpv6t0`, workspace `tea-cspvckggph6c739g2p40` if still valid).

**Do not publish ungenerated `demos/` from `main`.** `demos/**/generated/` and the
copied `demos/**/SPEC.md` files are gitignored. Scramble imports
`./generated/scramble.mjs`; DoubleDeal imports `./generated/doubledeal.mjs`.
Serving raw `main` + publish directory `demos/` 404s those modules and three.js
never boots.

## Source of truth

`.github/workflows/pages.yml` runs `.github/actions/generate-demos` (builds
`sudoc`, runs `tools/build.sh`) and publishes that tree to branch `gh-pages`.
`gh-pages` **is** the demos tree (`index.html` at the branch root), the same
artifact GitHub Pages serves.

Point Render at that branch. Do not add a second generate workflow, and do not
compile `sudoc` on Render (rustup already failed on the static builder; see
superseded draft PR #8).

## Dashboard settings (existing service — do not create a second site)

Service: [cryptoys](https://dashboard.render.com/static/srv-daqdlq0u01pc73fpv6t0)
→ **Settings → Build & Deploy**

| Setting | Value |
|---|---|
| Branch | `gh-pages` (not `main`) |
| Publish directory | `.` or `./` (not `demos/`) |
| Build command | empty, or `true` |
| Auto-Deploy | On commit |

Save, then **Manual Deploy → Deploy latest commit**.

Smoke-check (expect HTTP 200, JavaScript):

```text
https://cryptoygraphy.com/scramble/generated/scramble.mjs
https://cryptoygraphy.com/doubledeal/generated/doubledeal.mjs
```

`render.yaml` at the repo root records the same settings (`branch: gh-pages`,
`staticPublishPath: .`). Apply it only to this existing service. A new Blueprint
site would be a duplicate.
