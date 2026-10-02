<!-- Owns: the in-tree evidence for MegaDreifach v3 (candidate, ZP26): the hand-vs-sudo check, which log backs each SPEC v3 §8 number, how the study logs were made, and what the study scripts are. Maintenance rules: ../../../../DOCS.md. -->
# MegaDreifach v3: evidence

This directory backs the numbers in [SPEC v3 §8](../../../../primitives/hash/megadreifach/v3/SPEC.md#8-security-status) and the check that the hand recipe matches the runnable spec. It is empirical evidence, not a proof of security. The design analysis, including every rejected variant, is in [`ANALYSIS.md`](ANALYSIS.md).

## Files

| File | Role |
| --- | --- |
| [`check_v3.py`](check_v3.py) | Hand transliteration of SPEC v3 §5 vs the v3 KATs (from the sudo), the exact cost counts, and fast engine == transliteration. Run in CI (`proofs.yml`, megadreifach-lean) |
| [`ANALYSIS.md`](ANALYSIS.md) | The study: the v2 baseline, the constraints, NRk52, SBR26, the per-card scrambles and board registers, ZP26, ZP13 and ZP0F0E26 |
| [`study/`](study/) | The study scripts, as run |
| [`logs/`](logs/) | The study logs, unedited run output |

## Hand recipe == runnable spec

`python3 check_v3.py` (stdlib only, about 1 s) checks three things.

1. **The KATs.** `hand_em` is written from the SPEC v3 §5.3–§5.4 prose. Its words are "the face its n-coloured sticker is on" and "count up from X by Y's rank". It works on m9_search positions, using the Em.lean tables, which are unchanged since v1. It reproduces every vector in [`megaminx_hash_kats_v3.json`](../../../../primitives/hash/megadreifach/kats/megaminx_hash_kats_v3.json):
   - the 8 `Hash` digests;
   - `HashDeck`;
   - the IV-COOK12 digest;
   - the 8 `HashDeckBody` vectors, 4 of them with a King held.

   That file is written by `kats/regen_v3.mjs` from the sudoc build of [`v3/megadreifach.sudo`](../../../../primitives/hash/megadreifach/v3/megadreifach.sudo). So this check is prose == sudo.
2. **The cost.** On those 8 deals, W makes 468 face turns and 520 + 26k clicks.
3. **The fast engine.** The study's fast engine (`study/mdw4_lib.py`, kind `ZP3F0E`, m = 26), which computed every ZP26 statistic, equals `hand_em` on 60 random blocks. (While preparing v3, the 9 KAT digests were also computed with that engine directly and matched.)

**Limits.**
- `hand_em` and the study engine share m9_search's tables and its piece-colour reads. So (3) checks the engine's compiled tables and stepping, not those primitives. That is the same limit as [v2's self-check](../v2/README.md#limits-of-the-self-check).
- (1) does not share code with the sudo: the sudo has its own tables and reads.
- Mutating the transliteration makes (1) fail. Mutations tried while writing it: 25 echoes, P off by one, and the corner's second turn on the wrong sticker.

## Evidence for each SPEC v3 statement

| SPEC v3 statement | Where | Log |
| --- | --- | --- |
| All 50 pieces read in every block (§5.8) | sudo test "coverage: …"; [`study/mdw4_lib.py`](study/mdw4_lib.py) `selftest` | the top of every `mdw4_*` / `mdw5_*` log |
| 60 distinct two-turn read words per piece (§5.8) | [`study/mdw_lib.py`](study/mdw_lib.py) `selftest` | the top of every `mdw_*` log |
| v2 reads 41.2 of 50 pieces | ANALYSIS §1 | `logs/mdw_base_coverage.log` |
| v2 free start: 5.18% exact prediction, +.0796 / +.0550 | ANALYSIS §1 | `logs/mdfix_d1prime.log` |
| ZP26 D1 + D1′, 16M per side pooled: −.00004 / −.00005 ± .00016; 0 exact predictions in 32M | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_big8M.log` (seeds 68,000,000 + c), `logs/mdw4_final_ZP3F0E26_big8M_b.log` (71,000,000 + c) |
| ZP26 D2 at 4M | ANALYSIS §12.5 | `logs/mdw4_final_ZP3F0E26_d2_4M.log` (69,000,000 + c) |
| ZP26 merge and D3, 400k each: 0 / 0 | ANALYSIS §12.5 | `logs/mdw4_screen_ZP3F0E26_merge.log` (65,100,000), `logs/mdw4_screen_ZP3F0E26_d3.log` (65,200,000) |
| ZP26 end diagnostic, 2M | ANALYSIS §12.5 | `logs/mdw4_diag2M_ZP3F0E26.log` (67,000,000) |
| NRk52 corner bias +.00060 ± .00022 (comparison) | ANALYSIS §4.1 | `logs/mdw_d1big_NRk52_8M.log` |
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

The kind, size and seed of each run are printed at the top of its log and given in its ANALYSIS row. The study's shell wrappers are not committed, because they held machine-specific paths.

Nothing here runs in CI except `check_v3.py`. The study runs took about 14 h of wall time in total: §1–§4 about 3 h, §11 3.4 h, §12 5.0 h and §13 2.5 h (ANALYSIS, "Compute" lines).

**Special logs.**
- `logs/mdw4_screen_ZB3F0E26_merge2M.log` is a crashed run, kept as the record of the `mdfix_dist.merge()` bug (ANALYSIS §12.3). Its traceback shows the scratch paths it ran from.
- `logs/mdw3_screen_SCR26_merge_recount.log` is the recount after that fix.
- Every other merge log was written before the fix. Their zero-collision claims stand, because their [0–40] bins are 0 (ANALYSIS §12.3).

## Study scripts

The scripts in `study/` are the study's scratch scripts, committed as run. There is one change: the v2 engine import path in [`study/mdfix_lib.py`](study/mdfix_lib.py). The study imported a byte-identical export of `proofs/megadreifach/security/v2/` (same `engine.py`, `m9_search.py`, `md.py`, `tables.py`, `Em.lean`); in tree, it imports `../../v2`.

| Script | Role |
| --- | --- |
| `mdfix_lib.py`, `mdfix_dist.py` | v2 engine adapter, sampling, the quotient statistics, chunked runs |
| `mdfix_d1prime.py`, `mdfix_power.py` | v2 D1′ baseline; power table |
| `mdw_lib.py`, `mdw_tests.py`, `mdw_naming_enum.py`, `mdw_probe_merge.py`, `mdw_d1big.py` | §1–§4: coverage, naming, register need, NRk52 |
| `mdw3_lib.py`, `mdw3_tests.py` | §11: SBR26 and the other single-pass rules |
| `mdw4_lib.py`, `mdw4_tests.py` | §12–§13: per-card scrambles, registers, ZP26, ZP13, ZP0F0E26 |

`mdw4_lib.em4('ZP3F0E', 26, h, deal)` is the fast ZP26 engine.
