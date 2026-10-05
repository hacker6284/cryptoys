<!-- Owns: the index of ECBS's historical logs. Maintenance rules: ../../../../DOCS.md. -->
# History: recorded logs, not re-runnable here

Everything below is docs and logs only. The scripts that produced them were hand-written models of the board and were deleted when [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) replaced them (git history: commit `ad80f54` and earlier). The current, re-runnable evidence is in [`../evidence/`](../evidence/README.md). SPEC cites these files as `[log: history/…]` only where the claim is about the design's history.

| Directory | What it records |
| --- | --- |
| [`card/`](card/README.md) | Phase-1 Python simulation of the v3 card (`card_sim_v3_*`, `soundness_v3_*`, `extras_v3`, the `sf3_*` / `sp3_*` traces) and [`V3_NOTES.md`](card/V3_NOTES.md) |
| [`demo/`](demo/README.md) | Phase-1 Demo-tier runs (`card_sim_demo`, `soundness_demo`) |
| [`twist/`](twist/README.md) | Phase-1 §7 twist-certificate runs (parts A–C) |
| `core/` | Logs of the 2026-09-30 draft's harness: peg recipes, the physical board and its costs (`ecbs_physical*`, `ecbs_costs_*`), workbench and F-form (`ecbs_workbench*`, `ecbs_fform*`, `ecbs_walks`, `ecbs_verse`, `ecbs_layout`), base point, exchange and validation runs, the grid budget (`ecbs_budget*`) and the never-adopted key encodings (`ecbs_entropy`, `fleet_*`) |
| `evidence/` | The last `card_sim` run of the store-P variant (P kept on the board all game), before that variant was dropped |
| [`trace-check/`](trace-check/TRACE_CHECK.md) | **Losing option**: the trace check the certificate replaced, with the v2 card and its runs |
