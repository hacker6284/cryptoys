<!-- Owns: the file map and run commands for the ECBS evidence. Maintenance rules: ../../../DOCS.md. -->
# ECBS evidence

Status: **evidence, not proof, and not a reference implementation.** Nothing here is proved in Lean and there is no `ecbs.sudo` yet. The design is [`primitives/key_exchange/ecbs/SPEC.md`](../../../primitives/key_exchange/ecbs/SPEC.md) with its player's card [`CARD.md`](../../../primitives/key_exchange/ecbs/CARD.md). Every simulated exchange is checked against PARI/GP. SPEC tags such as `[run: card/card_sim_v3]` point at files below.

## Layout

| Path | Contents |
| --- | --- |
| [`core/`](core/) | Curve, tiers, keys, base point, recipes, budgets, fold/extractor, F-form, walks, twists (the 2026-09-30 draft's harness; `ecbs_*.py` with `*_results.txt` / `.json`) |
| [`card/`](card/) | Card v3 on the literal board: fixed band homes (`homes_v3.py`), full exchanges (`card_sim_v3.py`), certificate soundness (`soundness_v3.py`), per-operation costs (`extras_v3.py`), calling (`calling_check.py`); notes [`V3_NOTES.md`](card/V3_NOTES.md). `homes.py` and `soundness.py` are the v2 base classes the v3 scripts import. |
| [`demo/`](demo/) | Demo (½ set, n = 7, chord walk): `homes_demo.py`, `card_sim_demo.py` (every non-empty key), `soundness_demo.py` (all 3^14 pairs), `gf37.py` (GF(3^7) tables) |
| [`twist/`](twist/) | SPEC §7.1: `s7_certificate.py` parts A (Demo exhaustive), B (every tier: twists, node, leak), C (key recovery from the node without the curve test) |
| [`trace-check/`](trace-check/TRACE_CHECK.md) | **Losing option**: the trace check the certificate replaced, with its v2 card runs |
| [`review/`](review/REVIEW.md) | Mathematician's review of the 2026-09-30 draft and its `mr_*` scripts (C sources only; build them to re-run) |
| [`MATH_REVIEW.md`](MATH_REVIEW.md) | The math review packet (C1–C27, Q1–Q13) against the draft; C11 and the trace part of C12 concern the trace check |
| [`HISTORY.md`](HISTORY.md) | The draft's change tables and the key encodings not chosen |

## Run

Python 3 with `cypari2`, `numpy`, `sympy` and `gmpy2` (some `review/` scripts also use `python-flint`). Run each script from its own directory; seeds are fixed.

```sh
cd demo && python card_sim_demo.py && python soundness_demo.py
cd ../card && python card_sim_v3.py Toy && python soundness_v3.py field Toy 5000 && python calling_check.py
cd ../twist && python s7_certificate.py A && python s7_certificate.py B && python s7_certificate.py C
```

Hobby and Serious runs of `card_sim_v3.py` and `soundness_v3.py` take minutes; part A of `s7_certificate.py` about a minute; part C at Hobby is a discrete log in GF(3^118) and may not finish (SPEC §7.1).
