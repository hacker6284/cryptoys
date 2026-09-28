# PassKey F: the suit+rank collision and what it does to v11 (related keys)

Analysis only. Nothing here changes the SPEC, the sudo, or the Lean. No bit-security claims. DoubleDeal makes no
cryptographic security claim. Every number below comes from a log in `logs/`. Each log starts with its producing
command, and `run_all.sh` regenerates all of them (~25 min on 8 cores; seeds fixed).

## Summary

* **Both earlier statements are true. They describe the same property of F in two places.** F is a data-dependent
  permutation, and its move at each step depends on the controller card only through **(suit + rank) mod hand size**
  (plus a key-pile cut when the rank does not fit in the hand). Swap two cards with the same suit + rank, e.g. 2♥ (1+2)
  and A♠ (2+1), and F makes exactly the same moves with the two labels exchanged, so F(τK) = τF(K).
  * **F as a mixing layer:** a swap passes unchanged at ≈0.887. That is what the gridcycle-bijective README called
    fatal.
  * **F as the key schedule:** keys K and τK give round keys that differ by exactly τ with that same probability per
    pass, and ≈0.48 for all six passes.
* **68 swaps collide**: the pairs with equal suit + rank. Each has an exact closed-form lower bound
  e(e−1)/2652 with e = 51 − max rank. The rates run from 196/221 ≈ 0.887 (2♣↔A♥, 2♥↔A♠, 2♠↔A♦) down to
  703/1326 ≈ 0.530 (pairs with a King). Measurements agree to about 1e-3. No other swap is above 1/64; the worst
  other swap is 9♥↔9♦ at 0.0028.
* **It does not carry through to v11 encryption.** A key difference τ reaches the state through Compose, where it
  becomes a swap of seats a and b of the round output. This happens again in every round, and the next unkeyed
  round turns a 2-seat difference into a full one. Over 10M related-key samples for 2♥↔A♠ (and 2M each for 3 more
  colliding pairs and 3 non-colliding controls):
  * the relations E_τK(P) = E_K(P), E_τK(P) = E_K(P)∘σ, and E_τK(τP) = τE_K(P) never held (0 hits; 95% upper
    bound 3e-7 for 2♥↔A♠);
  * the number of equal seats between the two ciphertexts is 0.9999 ± 0.0006, where unrelated decks give 1;
  * with the most favourable oracle-aligned plaintext (whitened states made equal, which needs the key), the
    difference is exactly 2 seats after round 1 and nearly full after round 2 (50.7 of 52 seats differ). From
    round 3 on it cannot be told apart from unrelated decks (51.000).
* **Verdict: related-key-only, and at full rounds harmless as far as measured.** The property exists only in a
  related-key model, where the attacker obtains encryptions under K and τK. On the key schedule alone it is a clean
  related-key property (τ-related round keys ≈48% of the time for six passes). On the 6-round cipher it gives no
  measurable distinguisher at 10M samples: it buys about one round (two in the oracle-aligned case) out of six. It
  is not a single-key attack and not a related-plaintext attack like the v8/v9 breaks. Nothing is deprecated here.

## 1. The mechanism (hand-checkable)

SPEC §3.7, step i (i = 0..51): pop the controller C. The hand now holds n = 51 − i cards and the key pile i cards.

1. Cut the hand by suit(C) mod n.
2. If rank(C) < n, cut the hand by rank(C). Otherwise, if rank(C) < i, cut the key pile by rank(C).
3. Put C on the key pile.

Steps 1 and 2 are both left rotations of the same packet, so they add. When rank(C) < n the move is "rotate the
hand by (suit + rank) mod n", and the card itself matters only through **v = suit + rank**. The positions of all
other cards evolve the same way whichever card is the controller. So if a and b have the same v, and both act at
steps where their ranks fit in the hand, every move of F is identical on K and on τK. The only difference is which
of the two labels sits where, so F(τK) = τF(K).

**Hand check for 2♥ vs A♠** (suits ♣0 ♥1 ♠2 ♦3, A = 1):

* 2♥: cut the hand by 1, then by 2, which is a cut of 3.
* A♠: cut the hand by 2, then by 1, which is also a cut of 3.

The moves are identical at every step with n ≥ 3, which is 49 of the 52 steps. They differ only in the last three:

| n | 2♥ | A♠ |
|---|---|---|
| 2 | hand cut 1, then key-pile cut 2 | hand cut 0 + 1 = 1 |
| 1 | key-pile cut 2 | key-pile cut 1 |
| 0 | key-pile cut 2 | key-pile cut 1 |

**Why the rate has a closed form.** Each step of F is a bijection on (hand, key) states of fixed sizes. So for a
uniform key the state after i steps is uniform, and the controller order is a uniform permutation of the 52 cards.
The steps at which a and b control are therefore a uniform ordered pair of distinct steps (52·51 = 2652 choices).
If both steps lie in the set E of steps where a and b would make the same move, F(τK) = τF(K). Hence

    P[F(τK) = τF(K)]  ≥  e(e − 1)/2652,   e = |E|.

Equality holds up to paths that diverge and later re-merge, which is measured to be negligible here. For
suit+rank-equal pairs, E is exactly the steps with n > max rank, so e = 51 − max(rank a, rank b), with no extra
steps (`colliders.py` enumerates the moves exactly). For 2♥↔A♠, e = 49 and the bound is 49·48/2652 = 196/221 ≈ 0.8869.

## 2. The colliding pairs and their rates

All 68 pairs with equal v = suit + rank. Per class, the lower bound depends only on the larger rank m in the pair:
LB = (51 − m)(50 − m)/2652. Full list: `logs/colliders.log`. Measured values: `logs/pass.log` (50k keys per swap
for all 1326 swaps; every measured value is within about 0.005 of its lower bound, i.e. within sampling error).

| larger rank m | e | closed-form LB | example pairs (measured) |
|---|---|---|---|
| 2 | 49 | 196/221 = 0.8869 | 2♣↔A♥ 0.8857, 2♥↔A♠ 0.8856, 2♠↔A♦ 0.8846 |
| 3 | 48 | 188/221 = 0.8507 | 3♣↔2♥, 3♣↔A♠, 3♥↔2♠, 3♥↔A♦, 3♠↔2♦ (0.850–0.853) |
| 4 | 47 | 1081/1326 = 0.8152 | 4♣↔3♥ … 4♥↔2♦ |
| 5 | 46 | 345/442 = 0.7805 | |
| 6 | 45 | 165/221 = 0.7466 | |
| 7 | 44 | 473/663 = 0.7134 | |
| 8 | 43 | 301/442 = 0.6810 | |
| 9 | 42 | 287/442 = 0.6493 | |
| 10 | 41 | 410/663 = 0.6184 | |
| 11 | 40 | 10/17 = 0.5882 | |
| 12 | 39 | 19/34 = 0.5588 | |
| 13 | 38 | 703/1326 = 0.5302 | K♣↔Q♥ 0.5338, K♠↔Q♦ 0.5324, … |

The classes are v = 2 (2♣ A♥), v = 3 (3♣ 2♥ A♠), v = 4..13 (four cards each, e.g. v = 13: K♣ Q♥ J♠ T♦), v = 14
(K♥ Q♠ J♦) and v = 15 (K♠ Q♦). That is 1 + 3 + 10·6 + 3 + 1 = 68 pairs. The non-colliding swaps have e ≤ 3 (their
moves only coincide at small n where different v agree mod n). Measured worst among them: 9♥↔9♦ at 0.0028; the
closed-form worst is K♥↔K♦ at 1/442.

## 3. The real key schedule (K_r = F(K_{r−1}), six passes)

`logs/sched_top.log` (5M keys per swap) and `logs/sched_all68.log` (500k keys per swap, all 68 pairs). K is uniform
and K' = τK.

| swap | pass 1 | later passes, given the earlier ones held | all six passes | (pass 1)^6 |
|---|---|---|---|---|
| 2♥↔A♠ | 0.8871 | 0.8847–0.8851 | **0.4814 ± 0.0004** | 0.487 |
| 2♣↔A♥ | 0.8869 | 0.8849–0.8853 | 0.4817 | 0.487 |
| 2♠↔A♦ | 0.8870 | 0.8847–0.8851 | 0.4813 | 0.487 |
| 3♣↔2♥ | 0.8510 | 0.848 | 0.3735 | 0.380 |
| K♠↔Q♦ | 0.5301 | 0.521–0.523 | 0.0206 | 0.022 |

Across all 68 colliding pairs the all-six rate runs from 0.020 (King pairs) to 0.481. Once the relation breaks it
essentially never comes back: 1 case in 5M for 2♣↔A♥, and 0 in the 68 × 500k run. Passes are close to
independent; given that earlier passes held, the rate is slightly lower (0.885 instead of 0.887).

## 4. Does it reach the full cipher?

**Why it should not.** Compose(M, K)[j] = M[pos_K(j)]. Swapping cards a and b in the key swaps their positions,
so Compose(M, τK) = Compose(M, K)∘σ, where σ swaps **seats a and b** of the output (seats 14 and 26 for
2♥↔A♠). A τ-related round key therefore injects a fixed 2-seat difference into the state in every round. It
does not relabel cards.

For the difference to cancel, the next unkeyed round (SumRanks, ShiftRows, GridCycle) would have to turn "swap
seats a, b" into "swap the two key-dependent seats that the next Compose maps back". For the relation to survive
as a label relation (E_τK(τP) = τE_K(P)), the unkeyed layers would have to commute with a label swap combined with
a seat swap, which they do not. Neither is a symmetry of the round.

**Measurements.** `logs/rk_main.log` has 10M (K, P) samples for 2♥↔A♠. `logs/rk_more.log` has 2M each for
2♣↔A♥, 2♠↔A♦, K♣↔Q♥, K♠↔Q♦ and the controls Q♦↔K♦, K♠↔K♦, A♣↔K♦. Full v11: whitening, 5 full rounds, final
round. The C port matches `ddport.py` and the committed vectors (`logs/xcheck.log`).

| test (2♥↔A♠, n = 10M; conditioned on all six keys τ-related: n = 4.81M) | hits | ciphertext equal seats (unrelated = 1) |
|---|---|---|
| E_τK(P) = E_K(P) | 0 | 0.9999 ± 0.0006 |
| E_τK(P) = E_K(P)∘σ (the final-Compose relation) | 0 | — |
| E_τK(τP) = τE_K(P) (label relation) | 0 | 1.0002 ± 0.0006 |
| oracle-aligned P' (whitened states equal; needs K), E_τK(P') = E_K(P) or E_K(P)∘σ | 0 | 0.9994 ± 0.0006 |

With 0 hits in 10M, the 95% upper bound on each relation is 3e-7. The conditioned subset gives the same picture
(0 hits; equal seats 0.9998 ± 0.0009).

**How far the difference gets (oracle-aligned case, the attacker's best case):**

| state after round | 0 (whitening) | 1 | 2 | 3 | 4–6 |
|---|---|---|---|---|---|
| mean seats differing, all samples | 0 | 7.50 (exactly 2 seats in 88.7%) | 50.72 | 51.000 | 51.000 |
| same, all six keys τ-related | 0 | 2.00 (always exactly σ) | 50.64 | 51.000 | 51.00 |
| control Q♦↔K♦ (not colliding) | 0 | 48.3 | 51.00 | 51.00 | 51.00 |

So a colliding pair keeps the difference to two seats for one extra round compared with a non-colliding pair.
After round 2 there is a small residue (about 1.3 equal seats instead of 1), and from round 3 on nothing is
visible. v11 has six rounds. The same holds for all four colliding pairs tested; the controls are flat from round 2.

## 5. Verdict

* **What it is:** a related-key property of the key schedule. For the 68 suit+rank-equal swaps τ, keys K and τK
  give round keys related by exactly τ in all six passes with probability between 0.02 and 0.48, with an exact
  closed form per pass.
* **What it is not:**
  * **Not a single-key attack.** F is a bijection, so there are no equivalent keys and the key space is not
    reduced.
  * **Not a related-plaintext distinguisher** (the model of the v8/v9 breaks).
  * **Not a related-key distinguisher on the 6-round cipher** at 10M samples.
* **Where it matters:** only if F is reused as a data layer (the gridcycle-bijective note), or if a future design
  lets round-key relations reach the state as label relations rather than seat swaps.
* **Status: harmless for v11 as far as measured, related-key-only.** It is not a working attack under the repo's
  usual (single-key, chosen/related-plaintext) rules. Nothing was deprecated; that is Zachary's call.

## 6. Fix idea (proposal only, not implemented)

The collision exists because both cuts of a step land on the same pile and therefore add. A hand-friendly change
that keeps the same two gestures: **cut the key pile by suit instead of the hand.** When rank(C) < n, cut the hand
by rank and the key pile by suit (mod its size); otherwise cut the key pile by rank and the hand by suit. This is
the PassMix-F rule from `analysis/gridcycle-bijective/` (branch `doubledeal-gridcycle-bijective`).

* **Collisions:** rank and suit then act on different piles, so two cards collide only if both their ranks and
  their suits act the same, which for distinct cards happens only at a few edge steps. As a single pass its worst
  swap has a closed form of 30/2652 ≈ 1/88 (6♣↔6♦) instead of 196/221. Not measured as a key schedule chain.
* **Proofs:** per step it is still a bijection readable from the controller, so the `PassKey.lean` proof shape
  carries over.
* **Cost:** it changes the key schedule, so every round key, every vector and the PassKey refinement proofs would
  change. Given section 4, there is no measured need for it in v11.

## Files

| file | what |
|---|---|
| `dd.h` | v11 in C: PassKey F / F⁻¹, SumRanks, ShiftRows, GridCycle v11, Compose, encrypt with per-round states |
| `vec.c`, `xcheck.py` | cross-check against `security/checks/ddport.py`, `dd_v8.passkey` and the committed v11 vectors |
| `colliders.py` | exact step-move enumeration: colliding pairs, e, closed-form lower bounds |
| `keysched.c` | `pass`: all 1326 swaps through one F; `sched`: τ-relation through the six real passes |
| `rk.c` | full-cipher related-key tests V1–V3 and per-round state distance |
| `run_all.sh` | rebuilds and regenerates every log |
