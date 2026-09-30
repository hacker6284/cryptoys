# v12 whole cipher and final no-mix round: measurements (roadmap milestone M7)

**EMPIRICAL ONLY.** Everything in this note is sampled. No theorem uses it, and no
number here is proved. **No numeric bound on the full-cipher differential is proved**
anywhere. Not a bit-security claim. These measurements found no weakness.

## 0. What is proved (pointer)

The statements are in the header of `security/DoubleDealSecurity/FullCipher.lean`
(status: security README, "Roadmap", M7). This note holds only the measurements that are
new in M7. The exact SumRanks survival figures have their home in
[`../v10-sumranks/`](../v10-sumranks/) (`README.md`, `sbox-search/`); the one-round DP
values have theirs in [`../v12-differential/NOTES.md`](../v12-differential/NOTES.md).
Neither is restated here; §2 and §3 only compare against them.

## 1. Method

C, reusing `../v12-differential/ddiff.h` (the v12 round, its stem and inverse; see that
note, §1, for the cross-checks). `sh run.sh` rebuilds and rewrites the logs (`final` and
`mixfinal` about 12 min on the dev box, `scoping` about 4 min more; not run by CI;
binaries go to `$BUILD`, default `/tmp/v12-fullcipher`). Card indices and difference specs are as in
`../v12-differential/NOTES.md` (`13·suit + rank`, suits ♣ ♥ ♠ ♦; `a,b` a swap, `a,b,c`
a 3-cycle, `a,b;c,d` a double swap, `v10:a,x` the relabelling `v10Sym a x`).
Output differences are compared by a 64-bit hash (collisions are possible in principle;
they would merge distinct differences). Intervals are exact Poisson 95% intervals.

* `final1.c`: the final no-mix round without its keys (`unkeyedNoMix`: lay, SumRanks,
  ShiftRows, scoop; the Compose keys never change a relabelling difference). `x` uniform;
  records the output difference `γ` of the pair `(x, α·x)`. 10^6 decks per spec, seed 1.
  Sampled analogue of the row `dpFCount α · / 52!`.
* `mixfinal.c`: independent uniform keys, one mix round then the final round, output
  difference `γ = α`. Markov sampling (valid under independent uniform keys by
  `fullDiffCount_eq`): `x` uniform, `β` = difference after the unkeyed mix round, fresh
  uniform `w`, test `U(β·w) = α·U(w)`. Sampled analogue of
  `fullDiffCount α α 1 y / (52!)^3`. 8 × 2.5·10^7 samples per run: A♣↔2♣ seeds 101–108
  (`logs/mixfinal.log`); 5♦↔8♦ twice, seeds 101–108 (the M7 scoping run,
  `logs/mixfinal_scoping.log`, reproduced line for line by `sh run.sh scoping`) and seeds
  111–118 (`logs/mixfinal.log`). The scoping run of A♣↔2♣ used the same seeds 101–108 and
  is identical to the committed one, so it is not an independent run.

## 2. Final round alone: spread of the output difference (`logs/final1.log`)

| α | output differences seen (of 10^6) | largest count of one `γ` other than α | note |
|---|---|---|---|
| A♣↔2♣ (`0,1`) | 995 439, i.e. 1 (α) + 995 438 each seen once | 1 | all 995 438 non-α pairs distinct |
| 5♦↔8♦ (`43,46`) | 995 574, i.e. 1 + 995 573 each seen once | 1 | same |
| K♣↔K♦ (`12,51`) | 999 647 | 3 | α itself never seen |
| A♣↔2♥ (`0,14`) | 1 000 000 | 1 | α itself never seen |
| A♣→2♣→3♣ (`0,1,2`) | 991 816, i.e. 1 + 991 815 each seen once | 1 | |
| A♣↔2♣, 3♣↔4♣ (`0,1;2,3`) | 997 678, i.e. 1 + 997 677 each seen once | 1 | |
| `v10:1,0`, `v10:0,1` | 1 (α itself, every deck) | – | as proved (`dpFCount_v10Sym`) |

The support histograms are in the log. Reading: apart from γ = α, no single output
difference of the final round was seen more than 3 times in 10^6 decks for these specs
(sampled frequency ≤ 3·10^-6 each; this is the resolution of the sample, not a bound).
The γ = α counts (the SumRanks survivors) match the exact survival figures of
`../v10-sumranks/`: A♣↔2♣ 4562 and 5♦↔8♦ 4427 against 4524.9 expected from the exact
1/221 (z = +0.55 and −1.46), A♣→2♣→3♣ 8185 against 8144.8 from the exact 9/1105
(z = +0.45).

Measured, not proved. What Lean proves about the final round's one-step counts
`dpFCount` (`FullCipher.lean`, B): rows sum to `52!` (`sum_dpFCount`) and columns sum to
`52!` (`sum_dpFCount_left`); the diagonal `dpFCount σ σ` is the SumRanks survivor count
(`dpFCount_self_eq_survivors`), at most `52!/64` for `σ` outside `v10Sym`
(`dpFCount_self_le_64`); a `v10Sym a x` row is `52!` on the diagonal and `0` elsewhere
(`dpFCount_v10Sym`), and a `v10Sym a x` column is `0` off the diagonal
(`dpFCount_to_v10Sym`). Nothing about single off-diagonal entries is proved.

## 3. One mix round, then the final round (`logs/mixfinal.log`, `logs/mixfinal_scoping.log`)

| α → α, run | DP (hits / 2·10^8) | hits via β = α | β = α after the mix round | hits expected from the exact 1/221 | P(X ≤ hits) |
|---|---|---|---|---|---|
| A♣↔2♣, seeds 101–108 | 2.15e-7 [1.56, 2.90]e-7 (43) | 43 of 43 | 11 710 (5.86e-5) | 53.0 | 0.09 |
| 5♦↔8♦, seeds 101–108 (scoping) | 2.55e-7 [1.90, 3.35]e-7 (51) | 51 of 51 | 11 229 (5.61e-5) | 50.8 | 0.55 |
| 5♦↔8♦, seeds 111–118 | 2.10e-7 [1.51, 2.84]e-7 (42) | 42 of 42 | 11 403 (5.70e-5) | 51.6 | 0.10 |
| 5♦↔8♦, both runs (4·10^8) | 2.33e-7 [1.88, 2.85]e-7 (93) | 93 of 93 | 22 632 | 102.4 | 0.19 |

Every hit came through the constant path β = α; no hit through any β ≠ α was seen.
Comparison: given the number of samples with β = α, the hits through β = α are
Binomial(that number, p) with p the survival of α through SumRanks at a uniform deck,
exactly 1/221 for these same-suit swaps; paths through β ≠ α could only add hits. The
expected column is (β = α count) / 221, i.e. predicted DP ≈ 2.65e-7 (A♣↔2♣) and
≈ 2.56e-7 (5♦↔8♦). P(X ≤ hits) is the one-sided Poisson lower tail (the binomial tail
agrees to 0.001). A♣↔2♣ together with the second 5♦↔8♦ run: 85 hits against 104.6
expected, one-sided p ≈ 0.03; all three runs: 136 against 155.4, p ≈ 0.06. So the runs sit
somewhat low against the exact 1/221. No bug has been found: the final-round test in
`mixfinal.c` on samples with β = α is the same test as in `final1.c`, whose survivor counts
match 1/221 (§2), and the scoping run of 5♦↔8♦ sits on the prediction. Two swaps only, one
mix round only, independent uniform keys only; the real PassKey schedule is not measured
here, and nothing here is proved.

## 4. Not measured, not proved

* Any numeric bound on the full-cipher differential (independent or real keys); more than
  one mix round before the final round; any γ ≠ α after the final round in §3.
* Anything under the real PassKey schedule beyond what M5/M6 already record.
