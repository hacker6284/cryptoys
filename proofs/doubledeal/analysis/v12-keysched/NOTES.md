# DoubleDeal v12: the real PassKey schedule vs M2's independent keys (roadmap milestone M5)

Roadmap: [`security/README.md`, section "Roadmap"](../../security/README.md#roadmap).
Lean: `security/DoubleDealSecurity/RealSchedule.lean` (namespace
`DoubleDeal.Security.RealSchedule`) and `security/DoubleDealSecurityHeavy/RealSchedule.lean`.

Labels: **PROVED** = Lean, audited; **MEASURED** = sampling with a fixed seed (empirical
only; no theorem uses these numbers). Nothing here is a security or bit-security claim.

## 0. What is proved (summary; statements in RealSchedule.lean)

* Master key: a uniform π : Perm (Fin 52), injected into key decks by `masterList`
  (`masterList_injective`; its image is exactly the 52-card key decks,
  `exists_masterList_eq`).
* `encryptDeckFn_masterList`: the real round keys `roundKey i π` are the keys of `encryptDeckFn`.
* `card_roundKey`: each single round key is uniform (uniform master key).
* `card_image_roundKey_pair` / `_lt`: for any two rounds r ≠ s, the pair (K_r, K_s) takes
  exactly 52! of the (52!)^2 values, so the round keys are not independent (the theorems
  are stated for all r, s; for r = s they are trivial).
* `passKey_head_ne` / `card_roundKey_top_eq`: K_{r+1}[0] ≠ K_r[0] for every master key.
* `realTrail_card_le_64` (heavy) and `realTrail_card_le_26`, `_64_of_not_v10Sym`,
  `_64_of_check` (default): for every R ≥ 1, σ ≠ 1 and starting deck y, the constant-σ
  characteristic through R rounds of the REAL schedule has probability ≤ 1/64 over the
  master key. **The proved bound gains nothing beyond the proof's first mix round (key
  K_0)**: it is 1/64 for every R, weaker than M2's (1/64)^R, because in the proof's later
  mix rounds (keys K_1 …) the round key is not uniform given the state (§4). This is a
  limit of the proof, not a measured weakness; for R ≥ 2 nothing rules out the real
  schedule being more likely than (1/64)^R. One characteristic, not the differential. The
  final no-mix round is not covered, and `rounds` is not linked to `encryptN` (only the
  keys are); M7 (`FullCipher.lean`) adds both and gains nothing beyond the proof's first
  mix round (key K_0): the proof's later mix rounds (K_1 … K_4) and the proof's finalRound
  step (K_5, K_6) add no factor (the mapping to SPEC's rounds is in the `FullCipher`
  header). R ≤ 5 is the cipher's range: `Trail` step i (the proof's mix round i) is
  "Compose with K_i, then the round with mix", and the cipher has five such steps
  (K_0 … K_4); for R ≥ 6 the model uses K_5, K_6, … as keys before a mix, which the
  cipher never does (harmless, but not the cipher).

## 1. How the round keys depend on each other (PROVED where marked; the rest is a short argument)

* `expandKeys k0 = [passKeyIter r k0 | r = 0..6]`, `passKeyIter (n+1) k = F (passKeyIter n k)`,
  `F = passToKeyCutFallback` (Concrete.lean). Round key r of `encryptDeckFn` is
  `keyPos (F^r K0)`. F reads only the key deck (its controllers), never the message.
* F is a bijection on 52-card decks (`passKey_leftInverse` / `passKey_rightInverse`,
  content-preserving by `passToKeyCutFallback_perm`). Hence, for K0 uniform on the 52!
  decks: **each K_r alone is exactly uniform** (PROVED: `card_roundKey`), and the tuple
  (K_0, …, K_R) is uniform on the 52!-point set {(k, F k, …, F^R k)}, a vanishing fraction
  of the (52!)^(R+1) tuples. **No two round keys r ≠ s are independent**: K_s = F^(s-r)(K_r), so
  P[K_r = a, K_s = b] = [b = F^(s-r) a]/52!, never 1/(52!)^2 (argument; PROVED in the form
  "the pair takes exactly 52! values": `card_image_roundKey_pair`, `_lt`).
* One exact card-level consequence: the top card of F(K) is the last controller and
  the top card of K the first, so **P[K_{r+1}[0] = K_r[0]] = 0** (PROVED:
  `card_roundKey_top_eq`). For independent uniform keys it would be 1/52 (not a theorem).

## 2. Measured statistics of consecutive keys (MEASURED, `keystats.c`, `adjstats.c`)

K0 uniform (xorshift64 Fisher–Yates; the `% (i+1)` bias is < 2^-57 per draw).
N = 2·10^7 keys for the seat statistics (6 seeds), 2·10^6 for adjacency.

| pair | seat-transition chi² (df 2601; 99.9% point ≈ 2840) | extreme cell / uniform | mean fixed seats (random 1) | mean cycles of relative perm (random 4.538) | neighbour pairs kept (random 1.9615) |
|---|---|---|---|---|---|
| (K0, K1) | 827 333 | 0 (seat 0→0) … 1.213 (0→12) | 0.9825 | 4.5065 | 1.0930 |
| (K0, K2) | 3 124 | 1.027 (0→0) | 1.0007 | 4.5391 | 1.9862 |
| (K0, K3) | 2 532 (not significant) | 0.994 … 1.005 | 1.0004 | 4.5378 | 1.9619 |

Seat 0 carries 783k of the 827k chi² for (K0, K1); other seats deviate by ≤ 7%.
Per-card (s = 1) chi² over the 52×52 (seat in K0, seat in K1) table: 17 942 … 20 935.
0 repeated relative permutations (64-bit FNV hash) among 1.2·10^6 samples for each of s = 1, 2, 3 (no low-entropy structure seen at that size).
So one pass leaves strong, easily measured seat-level structure; two passes a small
but significant one (17σ at 0→0); three passes nothing at this resolution. None of
this is an attack: the schedule is public and deterministic by design, like AES's.

## 3. The constant-σ characteristic, real schedule vs independent keys (MEASURED, `trail.c`)

Model exactly as TrailBound.lean (`rounds`, `Trail`, `RoundChar`): the proof's mix round i
uses K_i, x_i = Compose(s_i, K_i), s_0 = y, and RC_i is the characteristic's event in it
(i = 0: the proof's first mix round, key K_0; i ≥ 1: the proof's later mix rounds). These
are the proof's mix rounds, not SPEC's rounds; the mapping is in the `FullCipher` header.
Real: K_i = F^i(K0). K0 uniform is sampled as x_0 uniform (a bijection for fixed y).
Control: fresh uniform K_1.
Same x_0 streams (seeds 1–6) for every y (common random numbers).

Conditioned runs: 6 × 3·10^8 = 1.8·10^9 uniform x_0 per row.

| σ | y | H0 = #RC_0 | P[RC_0] | H01 real (K_1 = F K0) | H01 control (K_1 fresh) | expected if the proof's second mix round (K_1) behaves like M2 (H0·P[RC_0]) | H012 real |
|---|---|---|---|---|---|---|---|
| A♣↔2♣ | identity | 107 098 | 5.95e-5 | 9 | 5 | 6.4 | 0 of 9 |
| A♣↔2♣ | random (seed 7) | 107 098 (same x_0) | 5.95e-5 | 7 | 5 (same control) | 6.4 | 0 of 7 |
| 5♦↔8♦ | identity | 101 942 | 5.66e-5 | 8 | 4 | 5.8 | 0 of 8 |

Poisson 95% interval for 9 hits: [4.1, 17.1], so P[RC_1 | RC_0] ∈ [3.8e-5, 1.6e-4] for the
first row, against 5.95e-5 unconditionally: **no sign of positive (or negative) correlation
between consecutive rounds' events, at a resolution of only about a factor 2–3** (9, 7 and
8 hits), from only two same-suit swaps and two starting decks. This does not bound R ≥ 2:
for R ≥ 2 nothing proved or measured here rules out the real schedule following the
characteristic with probability above (1/64)^R. The measured
two-round real-schedule probability is 9/1.8·10^9 = 5.0e-9 (95% upper bound 9.5e-9), far
below (1/64)^2 = 2.4e-4 and near the independent-model product (5.95e-5)^2 = 3.5e-9.
Three rounds: no hits, and no resolution (would need ~10^14 samples).

Marginal of RC_1, the event of the proof's second mix round (key K_1) (not conditioned;
σ = A♣↔2♣, y = identity, 6 × 10^7 x_0, seeds 101–106):
#RC_0 = 3 562 (5.94e-5), #RC_1 real = 3 530 (5.88e-5). Equal within noise (difference
−32 ± 84), consistent with the post-Compose state x_1 of the proof's second mix round
being close to uniform for this statistic. (Not a proof that it is uniform; that is not
known.)

Both σ are same-suit swaps (SumRanks alone: exactly 1/221 each, `../v10-sumranks/`).
The measured one-round value, ~1/17 000 for these two swaps, is far below the proved 1/64,
so a real-schedule probability above (1/64)^R would need consecutive rounds to be
correlated by a factor of order 10^2–10^3 per round. Nothing like that is seen at R = 2
for these two swaps and two starting decks (resolution about 2–3×); other σ, other decks
and R ≥ 3 are not measured at any useful resolution.
An exact two-round value is out of reach (a count over 52! master keys).

## 4. Where M2's proof uses independence and uniformity

* `card_keys_roundChar σ hy`: for a FIXED state y, the keys k with RoundChar(Compose y k)
  number `roundCharCount σ`. Needs the round key to range over all of `Key`
  independently of the state it is composed with (uniformity *conditional on the state*).
* `card_trail_succ`: the (R+1)-round count is a sum over the first key of the R-round
  count over ALL tail tuples `Fin R → Key`. This is the product structure (independence).
* `trail_card_le_of_round`, inductive step: applies the R-round bound at the new state
  `unkeyedWithMix (Compose y k)` with a fresh, full tail. Both uses meet here.

Real schedule: the proof's first mix round (key K_0) is fine (x_0 = Compose(y, K0), K0
uniform, y fixed). In the proof's second mix round the entering state
s_1 = GridCycle∘stem(Compose(y, K0)) and the key K_1 = F(K0) are both functions of K0;
given s_1 (and y), K_1 is a single key, not uniform. So the step `card_keys_roundChar` in
the proof's later mix rounds and the product split both fail; only the factor of the
proof's first mix round (key K_0) survives. The injectivity of K0 ↦ (K_0, …, K_{R-1})
only gives #real ≤ #independent, i.e. P_real ≤ (52!)^{R-1}·(1/64)^R, vacuous for
R ≥ 2.

## 5. Weakness check

No attack and no weakness beyond what is already documented was found.
Structural remarks, none measured as exploitable:
* One pass leaves strong seat-level structure between K_r and K_{r+1} (§2). The schedule
  is public, so this matters only through what it does to the cipher. The trail
  measurement (§3) shows no carry-over into the characteristic at R = 2, at a resolution
  of about 2–3×, for two same-suit swaps and two starting decks only.
* Slide / related-key structure: E_{F(K)} uses round keys K_1..K_7 where E_K uses
  K_0..K_6, so the mix rounds of the two encryptions line up shifted by one. The whitening
  and the no-mix final round break exact self-similarity. This is a related-key property
  only, of the same kind as the v11 finding, and was not measured here.

## Reproduce

All C is analysis-only scratch (no CI). `dd12.h` adds the v12 PassKey to the v11 round
layers of `../passkey-related-key/dd.h` (the v12 round function is v11's).

    gcc -O2 -o xcheck12 xcheck12.c && python3 xcheck12.py   # C vs ddport.py (300 decks) vs the committed vectors
    gcc -O2 -o keystats keystats.c
    for p in 1 2 3 4 5 6; do ./keystats 3333334 $p h$p.txt > ks$p.txt; done   # ~1 min on 6 cores
    python3 keystats.py ks*.txt > keystats.log; cat h*.txt | sort | uniq -d | wc -l
    gcc -O2 -o adjstats adjstats.c && ./adjstats 2000000 1 > adjstats.log
    gcc -O2 -o trail trail.c
    for cfg in "0,1 id" "0,1 7" "43,46 id"; do set -- $cfg
      for p in 1 2 3 4 5 6; do ./trail $1 $2 300000000 $p 0; done; done       # ~20 min per row on 6 cores
    for p in 1 2 3 4 5 6; do ./trail 0,1 id 10000000 $((p+100)) 1; done     # the marginal run

`trail.log` records every process line and the totals. The same seeds 1–6 were used for
every conditioned row, so the rows share their x_0 samples (common random numbers).
The raw count files (`ks*.txt`, `h*.txt`) are not committed (~150k lines each).
