<!-- Owns: the in-tree evidence for MegaDreifach v2's empirical security status (SPEC §8): which experiment and log back each statement, how the runs are seeded and checked, where each was ported from, and what is still out of tree. Maintenance rules: ../../../../DOCS.md. The logs in logs/ are written and checked by experiments.py. -->
# MegaDreifach v2: security evidence

Seeded measurements on MegaDreifach v2 (the grip rule C36) behind [SPEC §8](../../../../primitives/hash/megadreifach/SPEC.md#8-security-status). They are empirical evidence, not proofs of security. A zero count bounds a rate for one structured family of inputs. It says nothing about other attacks. The numbers are stated in SPEC §8 (the normative home) and printed in [`logs/`](logs/). This file maps each statement to its evidence.

The experiments are the v2-relevant scripts of the grip-rule review (2026-09-29, kept out of tree), ported here and re-run from the review's own seeds. Every number SPEC §8 cites from them reproduced exactly. Re-running checks the review's numbers. It is not an independent choice of tests.

## Files

| File | Role |
| --- | --- |
| [`engine.py`](engine.py) | Fast engine for C36 and three comparison rules, the slow reference, and the self-check |
| [`experiments.py`](experiments.py) | The experiments; writes or checks `logs/<name>.log` |
| [`logs/`](logs/) | Committed output, one log per experiment |

## Engine and self-check

`engine.py` is stdlib-only and transcribes no tables by hand:

- Face-turn, rotation, neighbour, corner and edge tables, and the slow reference E_m, come from [`../../m9/m9_search.py`](../../m9/m9_search.py). That script reads them out of [`Em.lean`](../../lean/MegaDreifach/Em.lean).
- Pad, φ, the digest encoding, `compose` / `inverse`, and v1's table noon (rule `A` only) come from [`../md.py`](../md.py), the transliteration of the frozen v1 sudo. The rule-independent parts did not change in v2.
- The fast engine is a port of the review engine `md3.py`, cut down to rules that read one piece right after the held-face turn:

| Rule | Noon | F3 rounds | Used for |
| --- | --- | --- | --- |
| `C36` | visual | 36 | v2 itself |
| `A_vn` | visual | 12 | card-phase tests (its 52 card steps are v2's) |
| `C76` | visual | 76 | the C36 vs C76 comparison |
| `A` | table (v1) | 12 | the review's "v2e": the control for the visual-noon repair |

`selfcheck()` runs before every experiment, and nothing runs if it fails. Its output is [`logs/selfcheck.log`](logs/selfcheck.log). It checks:

1. The `Em.lean` tables equal [`../tables.py`](../tables.py) (the v1 sudo's tables; the face turns did not change).
2. The fast engine reproduces all 8 v2 `Hash` digests, the `HashDeck` vector, the IV-COOK12 digest and `|G|` of [`megaminx_hash_kats_v2.json`](../../../../primitives/hash/megadreifach/kats/megaminx_hash_kats_v2.json).
3. The slow reference reproduces the 8 digests too.
4. Fast and slow E_m agree, grip sequence included, on 40 random (uniform `h`, random deal) blocks for each of the four rules.
5. `Hash('')` and `Hash('abc')` under `A_vn`, `C36` and `A` start with the prefixes the review engine printed.

Limits of the self-check:

- Fast == slow is not an independent check of the read model. The slow reference and the fast engine's compiled step tables both use m9_search's read primitives (`read_slot`, `read_colours_piece`, `abs_reorient`), so the comparison checks the fast engine's table compilation, not those primitives. Where a log says "re-verified with the slow reference", read it in that sense: different stepping code on the same tables and read primitives.
- The KATs anchor only C36 (v2 itself) to the sudo. `A_vn`, `A` and C36 also match the review engine's printed digest prefixes (item 5).
- C76 has no review prefix. It is anchored only by fast == slow and by reproducing every coverage statistic the review printed for it.

## Run and check

```sh
python3 experiments.py --check              # quick set: about 1 s, local and CI (CI: proofs.yml, megadreifach-lean)
python3 experiments.py --check --set heavy  # 13–15 min wall local (4 workers), 32–36 min in CI (CI: proofs-heavy.yml, megadreifach-attack-logs)
python3 experiments.py --only swaps         # rewrite one log
python3 experiments.py --list
```

Every experiment is seeded. The work is split into a fixed number of chunks with per-chunk seeds, so no result depends on `--workers`. Exit status is non-zero if the self-check fails, if an experiment's own re-verification fails, or (with `--check`) if a committed log differs from a fresh run. Measured wall times for the heavy set: local with 4 workers, 13 min in one run (`swaps` 433 s, `targeted_T` 172 s, `telescoping` 84 s, `local` 39 s, `truncated` 26 s, `coverage_chunks` 26 s, `same_blocks` 14 s, the rest under 3 s each) and 15.2 min in the reviewer's run; CI (`megadreifach-attack-logs` step, 4 workers), 31.7 and 36.0 min (`swaps` 1020 s, `targeted_T` 442 s, `telescoping` 218 s in the first). The quick set takes about 1 s, local and CI.

## Evidence for each SPEC statement

| SPEC statement | Experiment | Review source (seed; chunks) |
| --- | --- | --- |
| Cost per block (§5.7) and C36 vs C76 turns and reads (§8) | [`cost`](logs/cost.log) | `t8_cost.py` (8). v1 turns come from `../md.py` |
| Unread pieces, unread pieces never change `W`, read-class pseudo-collisions, 2-edge flip; the same for C76 | [`coverage`](logs/coverage.log), with the chunk-count spread in [`coverage_chunks`](logs/coverage_chunks.log) | `t6_coverage.py` (777 + c; C36: 3, C76: 4) |
| The second pseudo-collision run (20 of 40 draws, re-verified) | [`pseudo_pairs`](logs/pseudo_pairs.log) | `pseudo_check.py` of the v2 spec draft (7). It re-verified with the out-of-tree `megadreifach_v2_ref.py`; here the slow reference re-verifies |
| Table: swaps at distance 1–4 and ≥ 5, different-rank swaps, suit change | [`swaps`](logs/swaps.log) | `t4_swaps.py` (99; 20) |
| Table: local and window reorderings | [`local`](logs/local.log) | `t5_local.py` (per size; 6) |
| Table: 32-bit truncated birthday | [`truncated`](logs/truncated.log) | `t7b_truncated.py` (55). The log's "Poisson 95% range ~0-9" is a normal approximation; the SPEC gives the exact range |
| v1's blocks and swaps under v2 | [`same_blocks`](logs/same_blocks.log) | new: the first run of [`../suit_blind_collision.py`](../suit_blind_collision.py) `--full` (99), under C36 |
| Telescoping card pairs | [`telescoping`](logs/telescoping.log) | `t4e_identity.py` `pairs` (6; 24) |
| T card next to a same-rank swap; the table-noon collisions (3 in 999,873) | [`targeted_T`](logs/targeted_T.log) | `t4d_targeted.py` (4; 20). Each printed collision is re-verified with the fast and slow Hash |
| Grip pairs with identical turns and read slot: 0, and 192 (all rank T) for the table noon | [`grip_merge`](logs/grip_merge.log) | `t4c_grip_merge.py` (exact) |
| Suit dependence | [`suit_exact`](logs/suit_exact.log), [`suit_sampled`](logs/suit_sampled.log) | `suit_exact` is new: exhaustive over grips, parities and ranks, for every state. `suit_sampled` is `t3_suit.py` (3) |
| The review's recorded v2e collision (SPEC naming note, §8) | [`v2e_pair`](logs/v2e_pair.log) | REPORT §1 of the review. It collides under `A` (fast and slow) and not under C36 |

**Chunk counts.** The review ran each script with a number of worker processes, and that number also set how many seeded chunks the work was split into. The counts here are those of its recorded runs. Most come from its run scripts (`run_swaps.sh`, `queue2.sh`, `queue3.sh`, `run_local_toy.sh`). No recorded command line gives the `t6_coverage.py` runs. For those runs, 3 chunks (C36) and 4 (C76) are the counts that reproduce every statistic the review printed. Other chunk counts split the draws differently and give other, partly overlapping samples of the same statistics: [`coverage_chunks`](logs/coverage_chunks.log) runs 1–12 chunks. Over those counts the C36 unread means range over 2.04–2.08 corners and 6.67–6.75 edges, its read-class rate over 47–50% and its 2-edge-flip count over 122–159 of 3000; C76's read-class rate ranges over 7.2–9.4%. The confidence intervals are the result, not the last digit.

## Still out of tree

These statements in the docs still rest on the review alone. They are marked *out of tree* where they appear:

- The review's earlier rule also called "v2" (alternating reads after all three turns, table noon): IV-anchored collisions at about 2^12.5–2^13 (SPEC naming note; [`../REPORT.md`](../REPORT.md) §0).
- The review's toy models (generic collision, preimage and multicollision costs) that SPEC §8 mentions under "What these do not cover".

The review's dual-read rules (B, B2, Bp, B2p) and its other tests are not cited by the SPEC and were not ported.
