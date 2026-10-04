<!-- Owns: the core analysis scripts and the draft harness's recorded logs. Maintenance rules: ../../../../DOCS.md. -->
# Core: analysis and recorded logs

Analysis scripts (none models the board; each sits beside its recorded output `*_results.txt` / `.json`; run from this directory):

| Script | What it computes |
| --- | --- |
| `ecbs_curve.py` | Curve facts: #E, ℓ prime, ordinary, embedding degrees |
| `ecbs_tiers.py` | Key-limited cell counts, H∞, BSGS, rho, Frobenius-aware search |
| `ecbs_extractor.py` | The fold as an extractor: bounds, exact Demo, Toy bias test |
| `ecbs_twists.py` | Twist, E′ and node orders and factorisations |
| `ecbs_budget.py` | Grid and control-hole bookkeeping over measured band peaks (`ecbs_workbench.json`) |
| `ecbs_keys.py` | Key encodings (pegs-only and the never-adopted fleet encodings; imported by `../review/mr_pairs.py`) |

They import PARI from [`../oracle/ecbs_oracle.py`](../oracle/).

**Recorded logs (history).** The other `*_results.txt` / `.json` here are the outputs of the 2026-09-30 draft's hand-written harness: peg recipes (`ecbs_pegs`), the physical board and its costs (`ecbs_physical*`, `ecbs_costs`), workbench and F-form (`ecbs_workbench*`, `ecbs_fform*`, `ecbs_walks`, `ecbs_verse`, `ecbs_layout`), base point (`ecbs_basepoint`), the exchange and validation runs (`ecbs_exchange`, `ecbs_validation`, `ecbs_review_checks`), the lazy-y budget (`ecbs_budget_fform`) and the never-adopted key encodings (`ecbs_entropy`, `fleet_count`, `fleet_maxmult`). Those scripts were deleted when [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) replaced them (git history: commit `ad80f54`); SPEC cites their logs as `[log: core/…]`.
