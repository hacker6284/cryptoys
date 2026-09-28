# SumRanks v10 survival bound: paper proof

This is the paper proof behind `../DoubleDealSecurity/SumRanksDP/`. The Lean comments there cite it as `PROOF.md §n`.

It proves that every card relabelling outside `v10Sym` commutes with v10 SumRanks (one layer, no key) on at most
`0.012768 · 52! < 52!/64` decks. Lean formalises only the `52!/64` bound. §5b adds a corollary that the maximum is `9/1105`. That corollary is
computer-assisted: it relies on the computer-checked Lemma R of §8, and it is not formalised in Lean and not
independently reviewed. None of this is a security claim about the full cipher.

| file | what |
|---|---|
| `PROOF.md` | the proof (§§0–5), computer-assisted corollary 9/1105 (§5b; not formalised, not independently reviewed), numerical checks (§6), side results (§8), Lean route (§9) |
| `verify_proof.py` → `verify_output.txt` | numerical checks of every lemma against the C model in `../../analysis/v10-sumranks/sbox-search/` (about 2 min; needs gcc with OpenMP and numpy; 0 failures) |
| `model.py` | pure-Python SumRanks v10, checked equal to `sbox.c` by `verify_proof.py` |
| `rowlemma_exact.py` | exact one-row distributions (Lemma 2) |
| `alt_analytic_bigm.py` → `alt_analytic_bigm_output.txt` | Case A table `E_A(n*)`, exact rationals (§3 (A2)) |
| `caseB_analytic.py` → `caseB_analytic_output.txt` | Case B transfer-matrix bound per `m'`, exact rationals (§4 Theorem B) |
| `alt_analytic_rows.py` → `alt_analytic_rows_output.txt` | extra check for `3 ≤ m ≤ 12` |
| `p0scan.c`, `caseB_tm.c` | exhaustive computations for the side results (§8), compiled into `build/` by `verify_proof.py` |

These scripts are manual checks and are not run in CI.
