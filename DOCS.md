<!-- Owns: the maintenance rules for every README in this repository. -->
# README maintenance

Rules for every `README.md` in this repository.

1. **One home per fact.** The [root README](README.md) is the map: a one-line purpose for each primitive, links to each `SPEC.md` and to the per-area READMEs, and the build and test commands. Detail lives in its most specific home (the SPEC, or that primitive's or proofs README). Other files link there instead of restating it.
2. **Relative links.** Use relative Markdown links for paths people navigate. Plain code spans are fine for commands.
3. **Generated files.** Before editing a README in or next to generated output, check whether a tool or workflow writes it (`rg` its path in `tools/`, `.github/`, `proofs/`). If one does, change the generator, not the output.
4. **Frozen and deprecated versions.** READMEs under `proofs/deprecated/` are historical records. Fix only broken links, wrong paths and formatting. Do not rewrite their content.
5. **Structure.** A one-line purpose, then contents or layout, then how to run or check, then links. Keep each README only as long as it needs to be. Split walls of text; do not pad.
6. **Tone.** Terse headings and wording. No marketing, emoji or badges.

## Header comment

Each hand-written README starts with one hidden comment:

```html
<!-- Owns: <what this file is the single home for>. Maintenance rules: <relative path to DOCS.md>. -->
```

Do not use YAML frontmatter; GitHub renders it as a visible table.

## Special cases

- `proofs/*/lean/Generated/README.md` files are hand-written. `tools/emit_lean.py` keeps them, `.gitignore` and `lake-manifest.json` when it reinstalls a `Generated/` tree, and skips them in `--check`. It emits the rest of `Generated/` (including `EMITTED_FROM.json`); do not edit those files.
- READMEs under `proofs/deprecated/` get the header comment and nothing else beyond rule 4.
- [`proofs/megadreifach/README.md`](proofs/megadreifach/README.md) is checked: `proofs/doubledeal/check_axioms.py --selftest` requires its backticked theorem names to equal `MD_README_THEOREMS`. Change both together.
- Some README headings are cited from code comments (for example "Roadmap" in [`proofs/doubledeal/security/README.md`](proofs/doubledeal/security/README.md), and numbered sections of the analysis READMEs). Keep them, or update the citing files.
