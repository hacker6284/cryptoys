<!-- Owns: the core analysis scripts. Maintenance rules: ../../../../DOCS.md. -->
# Core: curve, tier, extractor and twist analysis

Analysis scripts over PARI. None models the board or the card's schedules (those live only in [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo)). Each sits beside its recorded output `*_results.txt` / `.json`; run them from this directory with the venv of [`../evidence/README.md`](../evidence/README.md).

| Script | What it computes |
| --- | --- |
| `ecbs_curve.py` | Curve facts: #E, ℓ prime, ordinary, embedding degrees |
| `ecbs_tiers.py` | Key-limited cell counts, H∞, BSGS, rho, Frobenius-aware search; the exceptional-key check walks keys with the generated `walk_key` |
| `ecbs_extractor.py` | The fold as an extractor: bounds, exact Demo, Toy bias test (the fold is the oracle's `fold_mod`) |
| `ecbs_twists.py` | Twist, E′ and node orders and factorisations |
| `ecbs_keys.py` | Key encodings (pegs-only and the never-adopted fleet encodings); no script of its own, imported by [`../review/mr_pairs.py`](../review/) |

They import PARI and the tier table from [`../oracle/ecbs_oracle.py`](../oracle/), which reads the tier constants from the generated `tier()`.

The recorded logs of the 2026-09-30 draft's deleted harness are in [`../history/core/`](../history/README.md).
