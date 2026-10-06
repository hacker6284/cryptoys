<!-- Owns: the file map and run commands for the ECBS evidence. Maintenance rules: ../../../DOCS.md. -->
# ECBS evidence

Status: **evidence, not proof.** The rules are normative in [`primitives/key_exchange/ecbs/SPEC.md`](../../../primitives/key_exchange/ecbs/SPEC.md), its player's card [`CARD.md`](../../../primitives/key_exchange/ecbs/CARD.md) and the runnable spec [`ecbs.sudo`](../../../primitives/key_exchange/ecbs/ecbs.sudo) beside them. Every measurement here runs the code sudoc generates from `ecbs.sudo` (JS target, sudocode pin [`proofs/SUDOCODE_PIN`](../../SUDOCODE_PIN)) and checks it against PARI/GP. There is no hand-written implementation of ECBS in this tree. The Lean emitted from `ecbs.sudo` is committed (`lean/Generated/`); its build status is recorded in [`evidence/README.md`](evidence/README.md#lean), and nothing about it is proved (no Link 2). SPEC tags `[run: evidence/…]` point at the drivers below; `[log: …]` points at a recorded output whose script was removed (see History).

## Layout

| Path | Contents |
| --- | --- |
| [`evidence/`](evidence/README.md) | Drivers of the generated code: full exchanges, soundness (Demo exhaustive), calling, twist §7. Results in `evidence/results/` |
| [`vectors/`](vectors/README.md) | Known-answer vectors per tier, generated from `ecbs.sudo` by sudoc at the pin, cross-checked against PARI |
| [`oracle/`](oracle/) | The PARI oracle: `ecbs_oracle.py` (field, curve, P by rule, λ, key scalar, π(C) − C, the §6 fold) and `gf37.py` (GF(3^7) tables built from PARI, for exhaustive Demo checks). No board, no card steps |
| [`lean/Generated/`](lean/Generated/README.md) | Lean emitted from `ecbs.sudo` by `proofs/emit_lean.sh ecbs`; `ecbs_test` runs the sudo tests |
| [`core/`](core/README.md) | Curve, tier, extractor and twist analysis over PARI (`ecbs_curve.py`, `ecbs_tiers.py`, `ecbs_extractor.py`, `ecbs_twists.py`) and the key-encoding analysis `ecbs_keys.py` (imported by `review/mr_pairs.py`), with their logs |
| [`history/`](history/README.md) | Docs and logs only: the Phase-1 Python simulation (`card/`, `demo/`, `twist/`; re-run on `ecbs.sudo` in `evidence/`), the 2026-09-30 draft harness's logs (`core/`), the store-P run (`evidence/`) and the losing trace check (`trace-check/`) |
| [`review/`](review/REVIEW.md) | Mathematician's review of the 2026-09-30 draft: its curve, field and entropy scripts (`mr_*.py`, and `mr_fleets*.c` as C sources; build them to re-run) and every script's `*_results.txt`. The three scripts that modelled the card's schedules by hand were removed (logs kept; see the note in REVIEW.md) |
| [`MATH_REVIEW.md`](MATH_REVIEW.md) | The math review packet (C1–C27, Q1–Q13) against the draft; C11 and the trace part of C12 concern the trace check |
| [`HISTORY.md`](HISTORY.md) | The draft's change tables and the key encodings not chosen |

## Run

Node 20, the pinned `sudoc` (`proofs/sudocode.sh` builds it), Python 3 with `cypari2` and `numpy` (`core/` and `review/` also use `sympy`, `gmpy2`, `mpmath`, `python-flint`). From the repo root:

```sh
proofs/key_exchange/ecbs/vectors/regen.sh --check                 # vectors from ecbs.sudo (= proofs/key_exchange/vectors_regen.sh ecbs --check)
python3 proofs/key_exchange/ecbs/vectors/check_oracle.py          # against PARI
proofs/emit_lean.sh ecbs                                          # Lean
```

The evidence drivers and their run times: [`evidence/README.md`](evidence/README.md). They run the generated JS through [`proofs/sudo_js.py`](../../sudo_js.py) (generic: any `.sudo`), the JS sibling of `proofs/sudo_py.py`.

## History

Until `ecbs.sudo` landed, the evidence ran on a hand-written Python model of the board (`history/card/homes*.py`, `history/demo/homes_demo.py`, the `core/ecbs_pegs.py` recipes and the scripts built on them). Those scripts were deleted when `ecbs.sudo` replaced them; their recorded outputs are under [`history/`](history/README.md), and the scripts are in the git history of the landing branch (commit `ad80f54`). Every exchange, soundness, calling and twist measurement was re-run on the generated code ([`evidence/`](evidence/README.md)); where the keys could be reproduced the numbers are identical.
