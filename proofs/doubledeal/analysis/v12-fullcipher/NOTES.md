# v12 whole cipher and final no-mix round: measurements (roadmap milestone M7)

**EMPIRICAL ONLY.** Everything in this note is sampled or enumerated (§5). No theorem uses it, and no
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
"Mix round" and "final round" here are the proof's grouping (the proof's mix rounds and
its finalRound step; the mapping to SPEC's rounds is in the `FullCipher.lean` header), not
SPEC's round numbers.

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
  is identical to the committed one, so it is not an independent run. The seed alone fixes
  the decks, whatever α is (see the seeding caveat in §3).

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
expected column is (β = α count) / 221, i.e. predicted DP ≈ 2.65e-7 (A♣↔2♣), ≈ 2.54e-7
(5♦↔8♦ scoping) and ≈ 2.58e-7 (5♦↔8♦ rerun); ≈ 2.56e-7 is the pooled 5♦↔8♦ figure.
P(X ≤ hits) is the one-sided Poisson lower tail (the binomial tail agrees to 0.001). A♣↔2♣ together with the second 5♦↔8♦ run: 85 hits against 104.6
expected, one-sided p ≈ 0.03; all three runs: 136 against 155.4, p ≈ 0.06. So the runs sit
somewhat low against the exact 1/221. No bug has been found: the final-round test in
`mixfinal.c` on samples with β = α is the same test as in `final1.c`, whose survivor counts
match 1/221 (§2), and the scoping run of 5♦↔8♦ sits on the prediction.

Seeding caveat. `mixfinal.c` seeds its generator from the seed number alone (not from α),
and draws one `x` and one `w` per sample whatever happens. So the A♣↔2♣ run and the
5♦↔8♦ scoping run, both seeds 101–108, use identical `x` and `w` decks, sample for sample.
The pool over all three runs (136 against 155.4) is therefore not over independent
samples. The effect on p is negligible: hits are rare (about 2.5e-7 per sample) and the two
runs test different α, so a shared deck almost never gives a hit in both. The A♣↔2♣ +
rerun pool (seeds 101–108 and 111–118) and the 5♦↔8♦ pool do not share seeds. The runs
were not re-seeded, so the logs stay reproducible as committed. Two swaps only, one
mix round only, independent uniform keys only; the real PassKey schedule is not measured
here, and nothing here is proved.

## 4. Not measured, not proved

* Any numeric bound on the full-cipher differential (independent or real keys). Proved
  reduction only: for outputs γ outside `v10Sym`, 1/64 would follow from
  `64 · dpFCount β γ ≤ 52!` for every β outside `v10Sym` with β ≠ γ
  (`fullDiffCount_le_64_of_offDiag`); §2 samples single off-diagonal entries of a few rows
  at ≤ 3·10^-6, which is not a bound and not a column. `StemPosition` proves no part of
  that hypothesis: if the stem sends `(x, β·x)`, `x = permDeck π`, to a pair with
  difference γ (the filter predicate of `dpFCount β γ`), then γ⁻¹β is π-conjugate to the
  ratio of the two decks' position maps and moves exactly `52 − zRows · zCols` cards
  (`card_moved_eq`). That would give `dpFCount β γ = 0` only when the support size of γ⁻¹β
  is not of the form 52 − ab (a ≤ 4, b ≤ 13), e.g. 2 or 3 (not stated), and says nothing
  for any other β. `StemCoupling` and `StemSupportFour` (security library) prove it for
  every `β` with `γ⁻¹β` moving exactly 4 cards (`dpFCount_le_of_support_four`, §5), and
  supports 1–3 and 5–7 count no deck (`dpFCount_eq_zero_of_support`). The `β` with `γ⁻¹β`
  moving at least 8 cards are open; `fullDiffCount_le_64_of_support_ge_eight` takes exactly
  that case as its hypothesis.
  More than one mix round before the final round; any γ ≠ α after the final round in §3.
* Anything under the real PassKey schedule beyond what M5/M6 already record.

## 5. Coupling constants for the 4-card stem case (`rowmax.c`, `pairs.py`, `qtype.py`, `pairs5.py`, `union_crude.py`)

**ENUMERATION ONLY; no theorem uses these numbers.** Exact integer counts over finite
sets, but not checked in Lean. They size the constant in `StemCoupling.coupling`
(security library, research item (b), second slice) and check the counting in
`StemSupportFour` (third slice); the theorems use none of them.

Setting. When γ⁻¹β moves 4 cards (a 4-cycle or a double transposition; `(zRows, zCols) =
(4, 12)` in `StemPosition`), the ratio `q` of the two position maps is
`StemSupportFour.qPerm t c d` with `t = rowAmts x`, `c` the one column whose amounts differ
mod 4 and `d ≠ 0` that difference (`ratio_eq_qPerm_of_support_four`, PROVED; a 300-sample
check against `security/checks/ddport.py` had found the same shape first). It moves
`cmFlat ρ ((c + t_ρ) % 13)` to the same seat of row `ρ + d`, one position per row
(`ratio_moves_le_one_of_support_four`). By `StemCoupling.rowAmts_eq_iff`, "row amounts = t"
is four row conditions; row ρ's condition is a weighted rank sum mod 13 over row ρ with
weights `13 − j` (turned). The (at least 12) positions of row ρ that `q` fixes carry cards
fixed by δ, and any rearrangement of them keeps `π⁻¹ δ π = q`. The assembly
(`dpFCount_le_of_support_four`, PROVED) sums over the `13^5 · 4` cells `(t, c, d)`; over the
four `d` the conjugate sets hold at most `8 · 48!` decks for each `(t, c)`
(`sum_card_conjSet_le`: `≤ 4 · 48!` for each of `d = 1, 3` when δ² ≠ 1, `≤ 8 · 48!` for
`d = 2` alone when δ² = 1). So a per-cell fraction of decks with row amounts `t` of at most
`52!/(64 · 13^5 · 8 · 48!) = 1 624 350/47 525 504 ≈ 0.0342` suffices, for both cycle types.

* `rowmax.c` (`logs/rowmax.log`, 12–17 min on one core): for every multiset of 12 ranks
  mod 13 (each at most 4 times; 2 056 210 multisets) and the 12 weights left after one
  column is removed (translated to 1..12, which shifts only the target), the largest
  fraction of arrangements whose weighted sum hits one target. Maximum 2730/34650 =
  13/165 ≈ 0.0788, at three ranks with 4 cards each; every multiset's maximum lies in
  [0.075, 0.080). So one row alone cannot give 0.0342 (the largest fraction is at least
  the average over the 13 targets, 1/13 ≈ 0.077); as a product over independent rows, two rows give ≈ 0.0062 and
  four ≈ 3.9·10^-5. (The product bound for several rows follows because the four rows'
  rearrangement groups commute and each preserves the other rows; this is the argument
  `coupling` formalises with 3 swaps per row.)
* `pairs.py` (`logs/pairs.log`, seconds): `L(m)`, the largest number of the `2^m` subset
  sums of `m` nonzero residues mod 13 equal to one target. `L(3) = 3` of 8, so three swaps
  of cards with different ranks per row give at most `(3/8)^4 = 81/4096 ≈ 0.0198` over
  four rows, the constant in `coupling` (proved there directly, `card_hit_le_three`). With
  it the assembly above has a margin of about 1.73
  (`64 · 13^5 · 8 · 48! · 81/4096 ≈ 3.76·10^6 · 48!` against `52! = 6 497 400 · 48!`), for a
  4-cycle and for a double transposition alike.
  **Correction to the second slice (PR #163 text and the earlier version of this section).**
  That text counted `2·13^5` choices of `q` for both cycle types and concluded that 81/4096
  does not fit a double transposition (`≈ 7.52·10^6 · 48!`). A double transposition δ has
  δ² = 1, and `qPerm t c d` squares to 1 only for `d = 2`, so only the `13^5` cells with
  `d = 2` can hold a deck; with `8 · 48!` per cell that is the same `≈ 3.76·10^6 · 48!`.
  `StemSupportFour.sum_card_conjSet_le` proves this split without cycle types.
* `qtype.py` (`logs/qtype.log`, 20 s): over all `(t, c, d)`, `d = 1, 3` give 4-cycles and
  `d = 2` double transpositions; each `d` gives `13^4` distinct `q` (`q` depends on `(t, c)`
  only through the four columns `(c + t_ρ) % 13`). The Lean sum is over the `13^5` cells per
  `d`, not over the distinct `q`, since each cell carries its own row-amount condition; the
  log's margins (1.728) are for that sum.
* `pairs5.py` (`logs/pairs5.log`, 20 s), the premises of a 5-swap coupling that the corrected
  count makes unnecessary (not formalised): among 12 (or 13) cards with each rank at most 4
  times there are always 6 disjoint pairs of different ranks (largest-class-first matching),
  but an arbitrary greedy choice of pairs, as `StemCoupling.exists_good` makes, can be left
  with only 4 (`[4,1,…,1]`), so a 5-pair version would need a different choice lemma; and
  `L(5) = 10` of 32 over all `12^5` nonzero tuples without the scaling WLOG.
* `union_crude.py` (`logs/union_crude.log`, seconds; arithmetic, not proof), one candidate
  route for the open supports `s ≥ 8`: bound `#{π | π⁻¹ δ π = q}` by `s^⌊s/2⌋ · (52 − s)!`
  (`π` is fixed on the support of `q` by its values at one point of each cycle, and there
  are at most `s/2` cycles) and sum over the `q` parameters with `52 − zRows·zCols = s`
  (the count of `research-b-union-bound/allsupp.py`; that `q` depends on the amounts only
  through `(t, t', s' − s)` is a paper argument, not proved). The largest value of
  `64 · #q · s^⌊s/2⌋ · (52 − s)! / 52!` over `s ≥ 8` is 0.173 (at `s = 8`), so this route
  would close `hoff` if formalised; at `s = 4` it gives 175 and does not work (hence the
  coupling there). None of it is in Lean.
* A joint sampling check of all four rows (400 000 decks for each of three `(t, c, d)`,
  not committed) gave hit fractions 2.8·10^-5 to 4.8·10^-5, near 13^-4 ≈ 3.5·10^-5.
  Sampled, not a bound.
