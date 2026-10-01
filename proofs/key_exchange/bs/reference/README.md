<!-- Owns: the BS evidence harness (peg recipes, integer arithmetic, parameters) and its test outputs. Maintenance rules: ../../../../DOCS.md. -->
# BS reference code

Status: **a note, not a theorem.** The recipes are normative in [`primitives/key_exchange/bs/SPEC.md`](../../../../primitives/key_exchange/bs/SPEC.md) §3 and in `bs.sudo` beside it. The Python here is an **evidence harness, cross-checked against `bs.sudo` by `../vectors/check_oracle.py`; not a reference.** `bspegs.py` simulates the recipes on colours only and is tested against the integer arithmetic of `bsref.py` and Python's `pow`. Test results, not proofs. The harness is due to be replaced (`../README.md`, "Evidence harness").

| Script | What it does | Output | SPEC |
| --- | --- | --- | --- |
| `bspegs.py` | The peg recipes B0–B10 (colours only), with a move counter | (library) | §3 |
| `bsref.py` | Integer arithmetic: register encode/decode, key exponent | (library) | §3, §4.4 |
| `bsparams.py` | Prime search and verification (MR-50 + BPSW, deterministic MR for T1/T2, 3^q = 1); `bsparams.py 323` for R512 | `params.json`, `params_output.txt`; `params_323.json`, `params_323_output.txt` | §2 |
| `run_bs.py` | Arithmetic tests (multiply, nudge, worst case, tidy) and malicious received values, T1 / T2 / T6 | `run_output.json`, `.txt` | §5, §8 |
| `bigmul.py` | Full-size multiplications with the long tolls: correctness and moves per multiplication | `bigmul_output.json`, `.txt` | §7, §8, §10 |
| `parity_check.py` | The B10 "pair off the whites" checksum: passes on correct products, catch rate on injected errors | `parity_check_output.txt` | §3 B10, §8 |
| `break_small.py`, `break_t2.c` | T1 by baby-step/giant-step, T2 by Pollard rho in C, on public keys from ships+pegs key grids | `break_small_output.txt` | §8, §9 |
| `peg_supply.py` | Peak white and red pegs in use per player during an exchange (registers only); `peg_supply.py R1024` is a 30-cell spot check | `peg_supply_output.json`, `.txt`; `peg_supply_output_R1024.json`, `peg_supply_R1024_output.txt` | No-paper rule |
| `tiers.py` | The §7 tier table for the ships+pegs key (reads `../ships-pegs/combined_results.json` and `../exchange/exchange_output.json`) | `tiers_output.json`, `.txt` | §0, §4.6, §7 |

Keys for `run_bs.py`, `break_small.py` and `peg_supply.py` come from [`../ships-pegs/keygrid.py`](../ships-pegs/keygrid.py) (the SPEC dice). Full exchanges are in [`../exchange/`](../exchange/README.md).

## Run

Every script builds its paths from its own directory (`Path(__file__)`), so it can be started from anywhere:

```sh
python3 bsparams.py > params_output.txt              # ~30 s
python3 bsparams.py 323 > params_323_output.txt
python3 run_bs.py > run_output.txt
python3 bigmul.py > bigmul_output.txt
python3 parity_check.py > parity_check_output.txt
cc -O2 -o break_t2 break_t2.c && python3 break_small.py > break_small_output.txt
python3 peg_supply.py > peg_supply_output.txt
python3 peg_supply.py R1024 > peg_supply_R1024_output.txt
python3 tiers.py > tiers_output.txt                  # after ../exchange/ and ../ships-pegs/combined.py
```

Reruns reproduce the recorded outputs apart from timings (`search_seconds`, `python_seconds_per_mul`, the rho time in `break_small_output.txt`).
