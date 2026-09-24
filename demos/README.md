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

https://hacker6284.github.io/cryptoys/

Scramble runs in the room (`?algo=scramble`). DoubleDeal is still its own teaching page.

## PR previews

Same-repo PRs that touch `demos/**`, the generate workflows, or the sudo that feeds generate publish a playroom at:

```text
https://hacker6284.github.io/cryptoys/pr/<N>/
```

The workflow leaves a sticky PR comment with that link.

**Review:** open the preview URL, click **Scramble**, and confirm the generated module loads (teach dock appears; no import / 404 error). Smoke-check `scramble/generated/scramble.mjs` — it should be HTTP 200 and JavaScript.

Files land on the `gh-pages` branch under `pr/<N>/`. Official Pages is a single artifact from `main`, so the `github.io` URL appears after `republish-pages` (or the next `pages` deploy) copies that branch. Closing the PR deletes `pr/<N>/`.

Optional: Settings → Pages → **Deploy from a branch** (`gh-pages` / `/`). Then every push to `gh-pages` is live without waiting for republish. Keep `.nojekyll` (sudoc emits `_*.mjs`).

Render (`cryptoys.onrender.com`) currently serves raw `main` / `demos/`, so `scramble/generated/scramble.mjs` 404s. Point that static site at `gh-pages` (publish path `/`) to serve the same generated tree as Pages.
