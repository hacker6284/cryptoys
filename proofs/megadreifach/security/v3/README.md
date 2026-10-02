<!-- Owns: the in-tree evidence for MegaDreifach v3 (candidate, ZP26): the study engine vs the sudo build, which log backs each SPEC v3 §8 number, how the study logs were made, and what the study scripts are. Maintenance rules: ../../../../DOCS.md. -->
# MegaDreifach v3: evidence

This directory backs the numbers in [SPEC v3 §8](../../../../primitives/hash/megadreifach/v3/SPEC.md#8-security-status). It is empirical evidence, not a proof of security. The design analysis, including every rejected variant, is in [`ANALYSIS.md`](ANALYSIS.md).

The normative definition of v3 is [`v3/megadreifach.sudo`](../../../../primitives/hash/megadreifach/v3/megadreifach.sudo). Nothing here checks it. The only other implementation of W here is the study's fast engine `em4`, and it is tested against the sudo (below), not the other way round. The sudo's own tests cover:
- the KATs;
- the exact cost counts;
- coverage;
- the 60 distinct read words per piece.

## Files

| File | Role |
| --- | --- |
| [`em4_vs_sudo.py`](em4_vs_sudo.py), [`sudo_body_from.mjs`](sudo_body_from.mjs) | The study's fast engine `em4` against `HashDeckBodyFrom` of the sudoc JS build, on 64 seeded random (h, deal) pairs; checked against [`logs/em4_vs_sudo.log`](logs/em4_vs_sudo.log) in `tools/generate-demos.sh` |
| [`ANALYSIS.md`](ANALYSIS.md) | The study: the v2 baseline, the constraints, NRk52, SBR26, the per-card scrambles and board registers, ZP26, ZP13 and ZP0F0E26 |
| [`study/`](study/) | The study scripts, as run (two in-tree changes, below) |
| [`logs/`](logs/) | The study logs, unedited run output, plus `em4_vs_sudo.log` |

## The study engine vs the sudo

Every ZP26 statistic in SPEC v3 §8 was computed with the study's fast engine, `study/mdw4_lib.em4` (kind `ZP3F0E`, m = 26). `em4_vs_sudo.py` tests that this engine computes the same function as the normative sudo:
- It draws 60 seeded uniform (legal h, deal) pairs, plus 4 deals with each King held for the echoes.
- For each pair it compares the digest of `compose(h, em4(h, deal))` with `HashDeckBodyFrom(deal, h)` of the sudoc JS build.
- It runs in `tools/generate-demos.sh` with `--check`, which reruns it and compares the result with the committed log.

```sh
sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
MD3_OUT=/tmp/megadreifach-v3 python3 proofs/megadreifach/security/v3/em4_vs_sudo.py --check
```

This is not a check of the spec. It ties the statistics to the sudo. Whether `em4` stays in tree is a question for the maintainer. Changing em4's m from 26 to 25 makes it fail.

## Evidence for each SPEC v3 statement

| SPEC v3 statement | Where | Log |
| --- | --- | --- |
| All 50 pieces read in every block (§5.8) | sudo test "coverage: …"; [`study/mdw4_lib.py`](study/mdw4_lib.py) `selftest` | the top of every `mdw4_*` / `mdw5_*` log |
| Exact cost counts (§5.6) | sudo test "cost per block" (`em_run`) | — |
| 60 distinct two-turn read words per piece (§5.8) | sudo test "read words"; [`study/mdw_lib.py`](study/mdw_lib.py) `selftest` | the top of every `mdw_*` log |
| v2 reads 41.2 of 50 pieces | ANALYSIS §1 | `logs/mdw_base_coverage.log` |
| v2 free start: 5.18% exact prediction, +.0796 / +.0550 | ANALYSIS §1 | `logs/mdfix_d1prime.log` |
| ZP26 D1 + D1′, 16M per side pooled: −.00004 / −.00005 ± .00016; 0 exact predictions in 32M | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_big8M.log` (seeds 68,000,000 + c), `logs/mdw4_final_ZP3F0E26_big8M_b.log` (71,000,000 + c) |
| ZP26 D2 at 4M | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_d2_4M.log` (69,000,000 + c) |
| ZP26 merge and D3, 400k each: 0 / 0 | ANALYSIS §12.5 | `logs/mdw4_screen_ZP3F0E26_merge.log` (65,100,000), `logs/mdw4_screen_ZP3F0E26_d3.log` (65,200,000) |
| ZP26 end diagnostic, 2M | ANALYSIS §12.5 | `logs/mdw4_diag2M_ZP3F0E26.log` (67,000,000) |
| NRk52 corner bias +.00060 ± .00022 (comparison; ANALYSIS only) | ANALYSIS §4.1, §12.5 | `logs/mdw_d1big_NRk52_8M.log` |
| Power | ANALYSIS §7, §12.5 | `logs/mdfix_power.log` |

The per-test rows for the rejected variants are in ANALYSIS §11–§13, with their logs.

## How the logs were made

The study ran on 2026-10-01 and 2026-10-02, one heavy job at a time, on 4 worker processes (fixed in the scripts). Results do not depend on the worker count: work is split into fixed seeded chunks.

Each log is the unedited stdout/stderr of one command, run from `study/` with output redirected to `../logs/<name>.log`. Most were wrapped in the shell's `time`, which accounts for the `real` / `user` / `sys` lines at the end. The finalist runs, for example, were:

```sh
cd study
python3 mdw4_tests.py d2    ZP3F0E 26  400000 65000000 > ../logs/mdw4_screen_ZP3F0E26_d2.log 2>&1
python3 mdw4_tests.py merge ZP3F0E 26   25000 65100000 > ../logs/mdw4_screen_ZP3F0E26_merge.log 2>&1
python3 mdw4_tests.py d3    ZP3F0E 26   50000 65200000 > ../logs/mdw4_screen_ZP3F0E26_d3.log 2>&1
python3 mdw4_tests.py big   ZP3F0E 26 2000000 66000000 > ../logs/mdw4_screen_ZP3F0E26_big2M.log 2>&1
python3 mdw4_tests.py diag  ZP3F0E 26 2000000 67000000 > ../logs/mdw4_diag2M_ZP3F0E26.log 2>&1
python3 mdw4_tests.py big   ZP3F0E 26 8000000 68000000 > ../logs/mdw4_final_ZP3F0E26_big8M.log 2>&1   # about 56 min
python3 mdw4_tests.py d2    ZP3F0E 26 4000000 69000000 > ../logs/mdw4_final_ZP3F0E26_d2_4M.log 2>&1   # about 21 min
python3 mdw4_tests.py big   ZP3F0E 26 8000000 71000000 > ../logs/mdw4_final_ZP3F0E26_big8M_b.log 2>&1 # about 56 min
```

The other logs follow the same pattern:
- the `mdw3_*` logs come from `mdw3_tests.py`;
- the `mdw_*` logs from `mdw_tests.py`, `mdw_d1big.py`, `mdw_probe_merge.py` and `mdw_naming_enum.py`;
- `mdfix_d1prime.log` and `mdfix_power.log` from `mdfix_d1prime.py` and `mdfix_power.py`.

The kind, size and seed of each run are printed at the top of its log and given in its ANALYSIS row.

Nothing here runs in CI except `em4_vs_sudo.py`. The study runs took about 14 h of wall time in total: §1–§4 about 3 h, §11 3.4 h, §12 5.0 h and §13 2.5 h (ANALYSIS, "Compute" lines).

**Special logs.**
- `logs/mdw4_screen_ZB3F0E26_merge2M.log` is a crashed run, kept as the record of the `mdfix_dist.merge()` bug (ANALYSIS §12.3). Its traceback shows the scratch paths it ran from.
- `logs/mdw3_screen_SCR26_merge_recount.log` is the recount after that fix.
- Every other merge log was written before the fix. Their zero-collision claims stand, because their [0–40] bins are 0 (ANALYSIS §12.3).
- **Self-test preambles.** 25 of the 36 `mdw4_*` / `mdw5_*` logs print an older self-test list at the top. The kind list in `mdw4_tests.py` grew during the study (ZP3F0E13, ZP0F0E9 and ZP0F0E26 were added for §13). The 11 `mdw5_*` logs print the final list. Each older list is a subset of the final one, and every kind in it shows the same 8/8 result in the final-list logs. The random blocks per kind differ, because one seeded stream is used in list order. The logs are not edited.
- **Removed slow copy.** The fast == slow result lines in the `mdw4_*` / `mdw5_*` preambles came from `mdw4_lib.slow_em4`. That function was removed after the runs (next section).

## Study scripts

The scripts in `study/` are the study's scratch scripts, committed as run, with two in-tree changes:
1. **The v2 engine import path** in [`study/mdfix_lib.py`](study/mdfix_lib.py). The study imported a byte-identical export of `proofs/megadreifach/security/v2/` (same `engine.py`, `m9_search.py`, `md.py`, `tables.py`, `Em.lean`); in tree, it imports `../../v2`.
2. **`slow_em4` removed** from [`study/mdw4_lib.py`](study/mdw4_lib.py) after the runs (2026-10-02 review). It was a second literal copy of the ZP-family rules. `selftest` no longer runs fast == slow, and keeps only the naming and board-register enumerations. The rejected-variant transliterations in `mdw_lib.py` and `mdw3_lib.py` (NRk, SB/SC rules) are still there, unchanged, as the record of §1–§11.

| Script | Role |
| --- | --- |
| `mdfix_lib.py`, `mdfix_dist.py` | v2 engine adapter, sampling, the quotient statistics, chunked runs |
| `mdfix_d1prime.py`, `mdfix_power.py` | v2 D1′ baseline; power table |
| `mdw_lib.py`, `mdw_tests.py`, `mdw_naming_enum.py`, `mdw_probe_merge.py`, `mdw_d1big.py` | §1–§4: coverage, naming, register need, NRk52 |
| `mdw3_lib.py`, `mdw3_tests.py` | §11: SBR26 and the other single-pass rules |
| `mdw4_lib.py`, `mdw4_tests.py` | §12–§13: per-card scrambles, registers, ZP26, ZP13, ZP0F0E26 |

`mdw4_lib.em4('ZP3F0E', 26, h, deal)` is the fast ZP26 engine.
