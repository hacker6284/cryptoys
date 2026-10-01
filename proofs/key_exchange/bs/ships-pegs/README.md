<!-- Owns: the evidence for the BS ships+pegs key (BUILD, READ, entropy, injectivity, walk cost). Maintenance rules: ../../../../DOCS.md. -->
# BS ships+pegs key

Status: **a note, not a theorem.** Exact enumerations, an exact DP and Monte Carlo checks with fixed seeds; nothing is proved in Lean. The key's rules (BUILD "one hole at a time: ship, then peg", "grow until it bumps", READ "ships, then pegs", the fleet walk) are stated in [`primitives/key_exchange/bs/SPEC.md`](../../../../primitives/key_exchange/bs/SPEC.md) §4.2–§4.3 and only there.

Two implementations of the build are used. `keygrid.py` follows the SPEC wording literally (d12 hole die, d6 growth and Sub/Cruiser rolls, d10 row cup). Its `fallback="d6"` mode is the all-d6 layout, which the SPEC dropped; it is kept only so `keygrid_check.py` can compare it (`../key-selection/NOTES.md` §5). The older scripts use the former d6 wording of the ship decision, which has exactly the same distribution (`../randomizer-kit/`, part B), and in `rules.py` that rule is `bump_reroll`.

| Script | What it checks | Output | SPEC |
| --- | --- | --- | --- |
| `keygrid.py` | Literal BUILD and READ (start marker, ship pass, peg pass) and the exponent; its ship pass is asserted equal to `read_rule.encode` on every read | (library) | §4.2–§4.4 |
| `keygrid_check.py` | `keygrid.build` against the exact model on 2×2, 2×3, 3×2, 1×5, 5×1 (layout, pegs, and the 2×2 joint), for the SPEC dice and the dropped all-d6 layout; 20,000 10×10 builds round-trip; cells, hit units, rolls per grid | `keygrid_check_results.txt`, `.json` | §4.2, §4.5, §4.7 |
| `rules.py`, `build_dp.py` | Candidate build rules as local distributions; exact DP over 5^10 row profiles for H, H₂, H∞ | (libraries) | §4.7 |
| `brute_build.py` | Brute-force enumeration of whole builds on small grids, against the DP | `brute_build_results.txt` | §4.7 |
| `run_rules.py` | The DP for every candidate rule (four batches) | `run_rules1.log` … `run_rules4.log`, `rules_*.json` | §4.7 |
| `viterbi.py` | The most likely layout (min-entropy) for `bump_reroll` and `grow` | `vit_bump.log`, `vit_grow.log`, `viterbi_*.json` | §4.7 |
| `sim_build.py` | Monte Carlo of the build against the model's log-probabilities (`model_logp`) | `sim_build.log`, `sim_build_results.json` | §4.7 |
| `sim_bump.py` | Walk statistics of the free fleet alone (cells, hit units) | `sim_bump.log`, `sim_bump_results.json` | ../key-selection |
| `read_rule.py` | The fleet walk: encode/decode, exhaustive injectivity of the ship pass up to 4×4 | `read_rule_results.txt` | §4.5 |
| `combined.py` | Ships + pegs: exhaustive injectivity on 7 small grids; the board-only build with random let-go/resume against the exact joint model; 20,000 10×10 round trips; walk cost; entropy totals | `combined_results.txt`, `.json` | §4.2, §4.5–§4.8 |
| `combined_multi.py` | 3,000 two-page keys decode to both grids | `combined_multi_results.txt` | §4.5 |
| `free_fleet_count.py` | Exact layout counts on 10×10 (uniform-layout ceiling 150.19 bits; the standard fleet, 30,093,975,536 labelled placements = 34.81 bits), then a Monte Carlo stage | `run.log`, `results_exact.json`, `results_mc.json` | ../key-selection |

**Let-go and resume.** `combined.py`'s `step()` lets go after the whole ship decision (growth and Sub/Cruiser rolls included) with the lane peg standing, or after the peg, at every hole. It draws each hole's peg on its own, so there are no row-cup pairs. Its let-go points are a superset of those the SPEC allows, since the SPEC also forbids letting go inside a row-cup die's pair (§4.2). The resumed build reads only the board. The chi-squares match the exact model, which is the evidence for the "finish the hole before you let go" rule as written. A build that let go between a Destroyer and its growth roll would, on resuming, see a covered hole and leave the Destroyer short; that case is excluded by the rule and is not simulated.

## Run

From this directory (redirected logs land in the current directory; JSON outputs are written beside the scripts, and `combined.py` reads `sim_bump_results.json` from there):

```sh
python3 brute_build.py > brute_build_results.txt
python3 run_rules.py len grow grow2 pow > run_rules1.log
python3 run_rules.py grow_w pow_w > run_rules2.log
python3 run_rules.py bump_turn bump_reroll grow_turn > run_rules3.log
python3 run_rules.py br_2_6_3 br_2_3_6 br_3_6_6 > run_rules4.log
python3 viterbi.py bump_reroll > vit_bump.log
python3 viterbi.py grow > vit_grow.log
python3 sim_build.py > sim_build.log
python3 sim_bump.py > sim_bump.log
python3 read_rule.py > read_rule_results.txt
python3 combined.py > combined_results.txt
python3 combined_multi.py > combined_multi_results.txt
python3 keygrid_check.py > keygrid_check_results.txt
python3 free_fleet_count.py > run.log                 # exact stage ~5 min, then MC stage (~4.5 GB)
```

`run_rules.py` prints rules in completion order; compare its JSON, not its log order. `free_fleet_count.py` is the one script whose full run was not repeated from this directory: twice the shared machine killed it for memory during the 4×4 brute-force check (> 4.4 GB). Its recorded `run.log`, `results_exact.json` and `results_mc.json` are the originals. The two figures the SPEC and `../key-selection/NOTES.md` use were recomputed from this directory with its own functions and match `run.log`: `standard_fleet(10, 10)` = 30,093,975,536 (log₂ 34.808756) and `exact_count(10, 10, "A")` = log₂ 150.187464.
