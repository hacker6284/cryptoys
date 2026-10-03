<!-- Owns: the evidence for MegaDreifach v3 (candidate, ZP26): what the repo checks (sudo tests, the in-tree harness on the sudoc build and its logs), the one note on the out-of-tree study code behind the other logs, and which log backs each SPEC v3 §8 number. Maintenance rules: ../../../../DOCS.md. -->
# MegaDreifach v3: evidence

This directory backs the numbers in [SPEC v3 §8](../../../../primitives/hash/megadreifach/v3/SPEC.md#8-security-status). It is empirical evidence, not a proof of security. The design analysis, including every rejected variant, is in [`ANALYSIS.md`](ANALYSIS.md).

The normative definition of v3 is [`v3/megadreifach.sudo`](../../../../primitives/hash/megadreifach/v3/megadreifach.sudo). The repo has no other implementation of v3's `W`. What the repo checks:
- **The sudo's own tests** (PROVED in SPEC and ANALYSIS): the KATs, the exact cost counts, coverage, the 60 distinct read words per piece, the re-derivable card-pass last face, and the King turn.
- **The in-tree harness** (IN-TREE): [`harness/zp26_stats.mjs`](harness/zp26_stats.mjs) runs D2, D1/D1′, merge and D3 on the sudoc JS build of the sudo, with the logs in [`logs/intree/`](logs/intree/).

Every other log in [`logs/`](logs/) is a record of a run of out-of-tree code (OUT-OF-TREE; next section).

## Files

| File | Role |
| --- | --- |
| [`ANALYSIS.md`](ANALYSIS.md) | The study: the v2 baseline, the constraints, NRk52, SBR26, the per-card scrambles and board registers, ZP26, ZP13 and ZP0F0E26, and the in-tree battery (§12.9) |
| [`harness/zp26_stats.mjs`](harness/zp26_stats.mjs) | The statistics harness. It calls only functions from the sudoc JS build (`dm_step`, `em_block`, `compose`, `inverse`, `identity`, `iv_cook12`, `opposites`, `face_turn`, `position_to_bytes`, `HashDeckBodyFrom`); it samples, counts and runs the statistics, and implements no part of `W`, `E_m` or the Davies–Meyer step |
| [`logs/intree/`](logs/intree/) | IN-TREE logs. The first line of each is the command that reproduces it |
| [`logs/`](logs/) (the rest) | OUT-OF-TREE study logs, unedited run output, kept as the record of what was run |

## Out-of-tree study code

This is the one place that describes the code behind the OUT-OF-TREE logs.

- **What produced them.** Every log in `logs/` outside `logs/intree/` was produced on 2026-10-01/02 by scratch study code that is not in the repo. That code had a fast engine for each candidate rule (for ZP26, `mdw4_lib.em4`, kind `ZP3F0E`, m = 26), a literal slow transliteration of each rule's hand text to check it (`mdw4_lib.slow_em4` and its siblings in `mdw_lib` and `mdw3_lib`), and a statistics harness built on the v2 Python engine.
- **How it was tied to the sudo.** The ZP26 fast engine gave the same digests as the sudoc JS build of the v3 sudo on the 8 `HashDeckBody` KATs and on 64 seeded random (h, deal) pairs, including 4 with a King held (checked out of tree on 2026-10-02). That comparison is not in the repo either.
- **Why it is not committed.** Zachary's rule for this repo: no hand-written implementation of the algorithm, in Python or JS. An earlier revision of PR #173 committed the study code (and a second hand-written copy of W, `hand_em`); they were removed under that rule.
- **What that means.** The OUT-OF-TREE logs are records, not in-tree reproducible checks. Nothing in CI re-runs them, and every SPEC and ANALYSIS figure that rests on them is tagged OUT-OF-TREE. They are not edited. Their preambles print the out-of-tree self-tests (the v2 self-check, and "fast == slow literal transliteration" lines); 25 of the 36 `mdw4_*` / `mdw5_*` preambles print an older self-test list, a subset of the final list in the 11 `mdw5_*` logs.
- **The path to in-tree reproduction** is a fast-enough sudo/sudoc path: a sudoc speed-up, in its own PR, which needs Zachary's OK first. On the study machine (4 workers), the harness on the sudoc JS build runs at about 320–370 blocks/s (`# time` lines of `logs/intree/`), against about 6,300 (D2 4M) to 7,100 (D1 8M) blocks/s for the out-of-tree engine: **about 18–21× slower**. The full ZP26 battery (2 × 8M D1 + D1′, D2 4M, merge and D3 400k) is about 58M blocks, or **about 46 h** at that rate; one 8M D1 + D1′ run alone is about 19 h.

## The in-tree harness

```sh
sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
MD3_OUT=/tmp/megadreifach-v3 node proofs/megadreifach/security/v3/harness/zp26_stats.mjs d2 100000 80000000      # one log's command
MD3_OUT=/tmp/megadreifach-v3 node proofs/megadreifach/security/v3/harness/zp26_stats.mjs --check proofs/megadreifach/security/v3/logs/intree/zp26_ci_slice.log ci 84000000
```

- Each run starts with a self-check against the build: the sampled positions are group elements of the build, the harness's `y = dm_step(h, deal)` (the build's Davies–Meyer step) equals the build's `HashDeckBodyFrom` digest, the sampler's legality matches the build's face turns, and the reference laws sum to 1. Both sides of the digest check now run `dm_step`, so it checks only the JS bridge and the digest encoding; only the KATs pin the feed-forward.
- Work is split into chunks whose size depends only on N, and chunk c uses seed SEED0 + c, so the output does not depend on the worker count. Only the `# time` lines vary.
- `--check LOG COMMAND` runs COMMAND and compares its whole output, including the `# command:` first line, with the log, ignoring `# time` lines; it prints `OK` or `STALE` (exit 1). Without COMMAND it runs the log's own first line. `tools/generate-demos.sh` pins the command: `--check logs/intree/zp26_ci_slice.log ci 84000000` (a fixed-seed slice of all four tests, about 3,000 blocks).
- Merge and D3 count output collisions only. The out-of-tree "state equal right after the swapped pair" and "card-phase positions equal" counts need a partial block, which no function from the sudoc build returns, so the harness does not measure them.

**The in-tree ZP26 battery** (2026-10-02, about 29 min, one heavy job on 4 workers; ANALYSIS §12.9):

| Test (ZP26, IN-TREE) | Log, seeds | Result (±: 95% half-width) |
| --- | --- | --- |
| D2, 100k | `logs/intree/zp26_d2_100k.log`, 80,000,000 + c | P(fixE ≥ 2) / P(fixC ≥ 2) adv **+.00015 / −.00103** (±.0027); mean moved −.0021 ± .0057; histogram p .44 / .79; cycle type p .45 / .062 |
| D1 + D1′, 50k (same samples) | `logs/intree/zp26_d1_50k.log`, 81,000,000 + c | D1: E +.00190, C −.00228; D1′: E +.00256, C +.00208 (±.0039 each); histogram p ≥ .47; cycle type p ≥ .48; **0 exact predictions in 100k quotients** (≤ 6.0e-5 per side) |
| Merge, 8 positions × IV/uniform × 4,000 | `logs/intree/zp26_merge_64k.log`, 82,000,000 + … | **0 output collisions in 64k adjacent swaps** (≤ 4.7e-5 per pair); mean differing slots IV / uniform in line with 49.1667 |
| D3, 4 pair classes × IV/uniform × 8,000 | `logs/intree/zp26_d3_64k.log`, 83,000,000 + … | **0 output collisions in 64k** (≤ 3.7e-4 per cell) |

All four are consistent with a uniform W at these sizes. They are much smaller than the OUT-OF-TREE runs: at 50k, D1 + D1′ has 90% power only at about |adv| ≥ .0064 per side, against .00026 for the 16M pooled run.

## Evidence for each SPEC v3 statement

| SPEC v3 statement | Tag | Where | Log |
| --- | --- | --- | --- |
| All 50 pieces read in every block (§5.8) | PROVED | sudo test "coverage: …" | — |
| Exact cost counts (§5.6) | PROVED | sudo test "cost per block" (`em_run`) | — |
| 60 distinct two-turn read words per piece (§5.8) | PROVED | sudo test "read words" | — |
| ZP26 in-tree battery (§8) | IN-TREE | ANALYSIS §12.9 | `logs/intree/zp26_{d2_100k,d1_50k,merge_64k,d3_64k}.log` |
| v2 reads 41.2 of 50 pieces | OUT-OF-TREE | ANALYSIS §1 | `logs/mdw_base_coverage.log` |
| v2 free start: 5.18% exact prediction, +.0796 / +.0550 | OUT-OF-TREE | ANALYSIS §1 | `logs/mdfix_d1prime.log` |
| ZP26 D1 + D1′, 16M per side pooled: −.00004 / −.00005 ± .00016; 0 exact predictions in 32M | OUT-OF-TREE | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_big8M.log` (seeds 68,000,000 + c), `logs/mdw4_final_ZP3F0E26_big8M_b.log` (71,000,000 + c) |
| ZP26 D2 at 4M | OUT-OF-TREE | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_d2_4M.log` (69,000,000 + c) |
| ZP26 merge and D3, 400k each: 0 / 0 | OUT-OF-TREE | ANALYSIS §12.5 | `logs/mdw4_screen_ZP3F0E26_merge.log` (65,100,000), `logs/mdw4_screen_ZP3F0E26_d3.log` (65,200,000) |
| ZP26 end diagnostic, 2M | OUT-OF-TREE | ANALYSIS §12.5 | `logs/mdw4_diag2M_ZP3F0E26.log` (67,000,000) |
| ZP13 and ZP0F0E26 rejected (D2 edges) | OUT-OF-TREE | ANALYSIS §13 | `logs/mdw5_final_*`, `logs/mdw4_screen_ZP3F0E13_d2.log` |
| Power | OUT-OF-TREE | ANALYSIS §7, §12.5 | `logs/mdfix_power.log` |

The per-test rows for the rejected variants are in ANALYSIS §11–§13, with their logs. The kind, size and seed of each OUT-OF-TREE run are printed at the top of its log. The sudo implements only ZP26, so the rejected variants cannot be re-run in tree.

**Special logs.**
- `logs/mdw4_screen_ZB3F0E26_merge2M.log` is a crashed run, kept as the record of the out-of-tree harness's merge bug (ANALYSIS §12.3). Its traceback shows the scratch paths it ran from.
- `logs/mdw3_screen_SCR26_merge_recount.log` is the recount after that fix.
- Every other merge log was written before the fix. Their zero-collision claims stand, because their [0–40] bins are 0 (ANALYSIS §12.3).
