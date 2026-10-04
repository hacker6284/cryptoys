<!-- Owns: the evidence for DoubleDeal-CBC-Sandwich v2 SPEC §8 (the Sandwich tests on MegaDreifach v3 and the v2 positive control). Maintenance rules: ../../../DOCS.md. -->
# DoubleDeal-CBC-Sandwich v2: Sandwich tests on MegaDreifach v3

The MAC of DoubleDeal-CBC-Sandwich v2 is a Sandwich (Yasuda, ACISP 2007) on MegaDreifach. Theorem S in [SPEC §8](../../../primitives/aead/doubledeal-cbc-hmac/SPEC.md#8-security-honesty) needs two PRF assumptions on the compression f(h, D) = h·W·h: **f′** (keyed through the key block, at chaining values the adversary picks) and **f̌** (keyed through a secret chaining value, two queries). On MegaDreifach v2 both failed. This directory re-runs those tests on MegaDreifach v3 (ZP26), the hash the MAC now uses, and keeps a positive control on v2.

Everything here is COMPUTED evidence about these tests. It is not a proof: the assumptions on v3 remain unproven (HEURISTIC), so the Sandwich theorem's security for this instance is conditional.

| File | What it is |
| --- | --- |
| [`sandwich_v3_stats.mjs`](sandwich_v3_stats.mjs) | The harness. Hand-written, but it implements no part of MegaDreifach: every block is the build's `dm_step`, every group operation the build's `compose` / `inverse` / `iv_cook12`, and each chunk checks its first block against the build's `HashDeckBodyFrom` (E3 also against `HashDecksBody`, the MAC's own call). On a build of the deprecated v2 sudo, which has no `dm_step`, a block is the build's `compose(h, em_block(h, deal))`, the two calls v2's `Hash` makes per block. The harness only samples inputs, counts and prints statistics. |
| [`logs/v3_a1_100k.log`](logs/v3_a1_100k.log) | A1 (f′) on v3, 100,000 games |
| [`logs/v3_e1_120k.log`](logs/v3_e1_120k.log) | A2 / E1 (f̌, cards 51 and 52 swapped) on v3, 120,000 pairs |
| [`logs/v3_e3_40k.log`](logs/v3_e3_40k.log) | E3, the whole Sandwich f*(IV, [K, D, L, K turned over]) with D's last two cards swapped, on v3, 40,000 pairs |
| [`logs/v2build_control_a1_4k.log`](logs/v2build_control_a1_4k.log), [`logs/v2build_control_e1_6k.log`](logs/v2build_control_e1_6k.log) | Positive control: A1 and E1 on a sudoc build of the deprecated v2 sudo. Both detect v2's flaws, so the harness can see them |
| [`logs/ci_slice.log`](logs/ci_slice.log) | `ci 85000000`: a1 400, e1 400, e3 100 on v3; `tools/generate-demos.sh` re-runs it with `--check` (a reproducibility check, not a statistical test; see below) |
| [`ARGUMENT.md`](ARGUMENT.md) | The full security argument behind SPEC §8, step by step with the tags below |

Every log is the unedited output of the command on its first line. Every line is deterministic except the `# time` lines; `--check LOG` re-runs the command and compares.

## Results (COMPUTED)

| Test | v2 build (control) | v3 build | Could have seen (v3) |
| --- | --- | --- | --- |
| A1: f′ two-edge-flip prediction | 213/4,000 accepted (5.3%, CI 4.7–6.1%) | **0/100,000**; one-sided 95% upper bound 3.0·10⁻⁵ | rate 2.3·10⁻⁵ (≥ 1 hit with 90% probability) |
| A2 / E1: P(fixE ≥ 2) − 0.264241 | +0.0704 ± 0.0119 | −0.0014 ± 0.0025 (fixC +0.0002 ± 0.0025), 0 equal outputs | about 0.004 (5% level, 90% power) |
| E3: the whole Sandwich | (not run) | fixE −0.0016 ± 0.0043, fixC −0.0033 ± 0.0043, 0 equal tags | about 0.007 |

Tags as in SPEC §8: PROVED only where a named sudo test checks the claim; ARGUED is a pen-and-paper argument here or in [`ARGUMENT.md`](ARGUMENT.md); COMPUTED is a number from a committed log in this directory. ± and "CI" are 95%.

The ideal values are exact: A1 accepts a random function with probability 1/|G| ≈ 2^-225.9 (ARGUED, ARGUMENT.md §3), and 0.264241 is P(at least 2 fixed points) for a uniform even permutation of 30 edges (or 20 corners), computed exactly in the harness.

How to read the table:
- The A1 bound is on this test's per-game acceptance probability on v3. It is not a bound on Adv^prf_{f′}, which no test can give.
- "Could have seen" is hand-derived, not a harness output. For A1 it is the rate r with 1 − (1 − r)^100000 = 0.90. For A2 and E3 it is (1.96 + 1.28) standard errors of P(fix ≥ 2) at the run's n (a normal approximation: two-sided 5% level, 90% power).

**The CI slice checks reproducibility, not statistics.** `--check logs/ci_slice.log ci 85000000` re-runs the fixed seeds and requires the same output line for line (all but the `# time` lines), so it catches a changed build or harness. At n = 400 and n = 100 its numbers are noisy. For example, its E1 fixC is 0.2200 [0.1822, 0.2632], just below the ideal 0.264241 (about 2.1 standard errors). That is expected noise: the slice prints six such P(fix ≥ 2) figures, and at the 5% level each one misses about one time in twenty. The evidence is the full runs above.

## Rebuild

From the repo root, with `sudoc` at the pin (`proofs/SUDOCODE_PIN`):

```sh
sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
MD_OUT=/tmp/megadreifach-v3 node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs --check proofs/doubledeal-cbc-hmac/security/logs/ci_slice.log ci 85000000
MD_OUT=/tmp/megadreifach-v3 node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs a1 100000 1000000   # about 9 min on 4 workers
sudoc build --target js -o /tmp/megadreifach-v2-js primitives/hash/megadreifach/megadreifach.sudo
MD_OUT=/tmp/megadreifach-v2-js node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs a1 4000 500
```

Run times are in each log's `# time` lines (4 workers on a shared 8-core box).
