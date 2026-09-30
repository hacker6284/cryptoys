<!-- Owns: the file map for the BS key-selection analysis. Maintenance rules: ../../../../DOCS.md. -->
# BS key selection

Status: **a note, not a theorem.** Analysis only: none of the keys compared here, other than ships + pegs, is an option of [`primitives/key_exchange/bs/SPEC.md`](../../../../primitives/key_exchange/bs/SPEC.md). The comparison and its result are in [`NOTES.md`](NOTES.md).

| Script | What it computes | Output |
| --- | --- | --- |
| `costs.py` | Multiplications and moves per key for pegs-only, free fleet alone and ships + pegs (reads `../ships-pegs/` results) | `costs_results.json` |
| `ecbs_lemma_a.py` | ECBS Lemma A positions for a free-fleet page and a ships+pegs page (NOTES §4); the ECBS n and ℓ values are copied into the script from the ECBS spec | `ecbs_lemma_a_results.txt` |
| `themed_kit.py` | The themed fleet's d20 / d8 / d4 face rules, and the full-restart placement (former part D of the randomizer kit): per-ship placement distribution computed face by face for the spec d10 and best-fit along-dice, with negative controls (a die too small for the ship) that must fail, plus Monte Carlo reads / re-rolls / restarts | `themed_kit_results.txt`, `.json` |
| `ecbs13_kit.py` | The themed full-restart placement end to end | `ecbs13_kit_results.txt`, `.json` |

## Run

From this directory:

```sh
python3 costs.py
python3 ecbs_lemma_a.py > ecbs_lemma_a_results.txt
python3 themed_kit.py > themed_kit_results.txt
python3 ecbs13_kit.py > ecbs13_kit_results.txt
```

`themed_kit.py` has its own seed (2026), so its Monte Carlo counts differ from those of the former part D, which shared the randomizer kit's stream. The former part D's per-ship check was vacuous: it built the distribution as uniform by construction, so its assertion could not fail. It now enumerates the die faces and the re-roll, and the negative controls show it can fail.
