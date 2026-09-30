# v12 whole cipher and final no-mix round: measurements (roadmap milestone M7)

**EMPIRICAL ONLY.** Everything in this note is sampled. No theorem uses it, and no
number here is proved. **No numeric bound on the full-cipher differential is proved**
anywhere. Not a bit-security claim. These measurements found no weakness.

## 0. What is proved (pointer)

The statements are in the header of `security/DoubleDealSecurity/FullCipher.lean`
(status: security README, "Roadmap", M7). This note holds only the measurements that are
new in M7. The SumRanks survival figures (a same-suit swap survives SumRanks alone on
≈ 1/221 of the decks, the same-suit 3-cycle on exactly 9/1105) have their home in
[`../v10-sumranks/`](../v10-sumranks/) (`README.md`, `EXPERIMENTS.md`, `sbox-search/`);
the `P[γ = α]` column of `logs/final1.log` reproduces them and is not restated here.
The one-round DP values have their home in [`../v12-differential/NOTES.md`](../v12-differential/NOTES.md).

## 1. Method

C, reusing `../v12-differential/ddiff.h` (the v12 round, its stem and inverse; see that
note, §1, for the cross-checks). `sh run.sh` rebuilds and rewrites both logs (about
12 min on the dev box; not run by CI; binaries go to `$BUILD`, default
`/tmp/v12-fullcipher`). Card indices and difference specs are as in
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
  `fullDiffCount α α 1 y / (52!)^3`. 8 × 2.5·10^7 samples per spec
  (seeds 101–108 for A♣↔2♣, 111–118 for 5♦↔8♦).

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
(sampled frequency ≤ 3·10^-6 each; this is the resolution of the sample, not a bound). Measured, not proved;
Lean proves only that each row sums to `52!` (`sum_dpFCount`) and the `v10Sym` rows.

## 3. One mix round, then the final round (`logs/mixfinal.log`)

| α → α | DP (hits / 2·10^8) | hits via β = α | β = α after the mix round |
|---|---|---|---|
| A♣↔2♣ | 2.15e-7 [1.56, 2.90]e-7 (43) | 43 of 43 | 11 710 (5.86e-5) |
| 5♦↔8♦ | 2.10e-7 [1.51, 2.84]e-7 (42) | 42 of 42 | 11 403 (5.70e-5) |

Every hit came through the constant path β = α; no hit through any β ≠ α was seen. The
values are consistent with (one-round DP α → α) × (SumRanks survival of α): 5.86e-5 /
221 ≈ 2.65e-7 and 5.70e-5 / 221 ≈ 2.58e-7, both inside the intervals. Two swaps only,
one mix round only, independent uniform keys only; the real PassKey schedule is not
measured here, and nothing here is proved.

## 4. Not measured, not proved

* Any numeric bound on the full-cipher differential (independent or real keys); more than
  one mix round before the final round; any γ ≠ α after the final round in §3.
* Anything under the real PassKey schedule beyond what M5/M6 already record.
