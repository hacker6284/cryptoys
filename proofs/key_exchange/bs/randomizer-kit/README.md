<!-- Owns: the file map and run commands for the BS / ECBS randomizer-kit checks. Maintenance rules: ../../../../DOCS.md. -->
# BS / ECBS keying: randomizer-kit checks

Status: **a note, not a theorem.** Nothing in this directory is proved in Lean. Parts A and B are exact enumerations (Fractions); part C is Monte Carlo counts with a fixed seed. The dice rules they check are stated in [`primitives/key_exchange/bs/SPEC.md`](../../../../primitives/key_exchange/bs/SPEC.md) §4.2 (hole die, growth, Sub/Cruiser, row cup, all-d6 fallback) and, for the row cup, the ECBS spec §4 (ECBS is not in this repository yet; the row-cup counts in part C are the ones it cites).

| Script | What it checks | Output |
| --- | --- | --- |
| `randomizer_kit.py` | A: every face rule enumerated face by face (exact uniformity, void rate, bits per read), including the row-cup keypad and the d6 halves + parity counterexample. B: the d12 hole die and the all-d6 fallback equal the former d6 wording's local distribution in all 25 room states, and exact whole-build equality on 2×3, 3×3, 2×5, 3×4, cross-checked with the float model. C: reads / throws / voids per grid for each build wording, and the row cup at 100 holes and at the ECBS key sizes | `randomizer_kit_results.txt`, `.json` |

`randomizer_kit.py` imports `brute_build` and `rules` from [`../ships-pegs/`](../ships-pegs/README.md) (numpy). The themed-fleet dice checks that used to be here (d20 / d8 / d4 face rules, part D, `ecbs13_kit.py`) are analysis of a key that was not chosen and now live in [`../key-selection/`](../key-selection/README.md).

## Run

From this directory:

```sh
python3 randomizer_kit.py > randomizer_kit_results.txt
```

The row cup is still simulated at 100, 200, 2, 16, 51 and 162 holes in that order, so the seeded stream, and the counts ECBS §4 cites, reproduce.
