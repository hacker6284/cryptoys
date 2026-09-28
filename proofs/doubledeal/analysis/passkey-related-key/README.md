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
| `readings.c`, `readings_exact.py` | §7: alternative readings of the suit step (reversibility, one-pass swaps, six-pass chain; exact move sets) |
| `dealk_exact.py`, `dealk_check.c`, `logs/dealk*.log`, `logs/rk_dealk2mod.log` | §8: deal suit + k (k = 0..4, min vs mod), exact bounds, 1M refinements, full-cipher check (rk.c with env DEALK/DEALMOD) |
| `run_all.sh` | rebuilds and regenerates every log |

## 7. History of PassKey's F, and the "deal x cards" reading (follow-up)

### 7.1 Timeline (git log -S/-G on SPEC, sudo, Lean, demos, READMEs; `gh pr list/view`)

**Summary:** the suit rotation of the hand has been in F since the first commit of the cipher. No commit or PR
changed F's forward rule. The phrase "rotate x cards one by one" (or "one at a time", "one-card cut") appears
nowhere in the repository history (all refs) or in PR bodies. Any change from Zachary's intent therefore happened
before the cipher entered this repo. The first SPEC says its hand conventions "match `PLAYER_SHEET_ELEGANT_V8.md`"
and calls the rule `pass_to_key_cut_fallback` (the cipher was then "TDSPN elegant-v8"). That player sheet was never
committed, so it could not be checked.

| date | commit / PR | author | what happened to PassKey |
|---|---|---|---|
| 2026-09-23 | [`a2e9b70`](https://github.com/hacker6284/cryptoys/commit/a2e9b70) "Add TwoDeck, the first cryptoys cipher." (direct push, no PR) | Zach Mills | **Origin.** SPEC §3.7 pseudocode with `k ← suit(C) mod len(hand); hand ← left_rotate(hand, k)`, then the proper rank cut with key-pile fallback. §4.6 prose (quoted below). `twodeck.sudo` `passkey` is the same. The demo labels the step "suit cut, then rank cut on the hand". Injectivity "not claimed". |
| 2026-09-24 | [#2](https://github.com/hacker6284/cryptoys/pull/2) (`e621596` "Prove PassKey injectivity with a constructive inverse.") | Cursor Agent, merged by hacker6284 | Lean model `passKeyStep` = `maybeRotate` (hand by `suit c % hand.length`) then `maybeCut`. Proves the inverse. No rule change. |
| 2026-09-24 | [#3](https://github.com/hacker6284/cryptoys/pull/3) "PassKey is a bijection; decrypt un-passes from K6" (`bbb00b1`) | Cursor Agent / hacker6284 | Adds F⁻¹ and "undo the suit rotation" prose; decrypt un-passes. "Ciphertexts do not change". |
| 2026-09-24 | [#4](https://github.com/hacker6284/cryptoys/pull/4) (`1f1c0ea` "Correct teaching copy…") | Cursor Agent | Demo text "suit cut" → "suit-rotate hand". Wording only. |
| 2026-09-24 | [#11](https://github.com/hacker6284/cryptoys/pull/11) rename to DoubleDeal; [#13](https://github.com/hacker6284/cryptoys/pull/13) emit Lean from sudo; [#17](https://github.com/hacker6284/cryptoys/pull/17) `while` → bounded `for` | hacker6284 | The only diff to sudo `passkey` since the first commit is `while hand.length > 0` → `for i = 1 to n` (#17). |
| 2026-09-25 | [#23](https://github.com/hacker6284/cryptoys/pull/23), [#26](https://github.com/hacker6284/cryptoys/pull/26), [#28](https://github.com/hacker6284/cryptoys/pull/28), [#30](https://github.com/hacker6284/cryptoys/pull/30), [#33](https://github.com/hacker6284/cryptoys/pull/33) Link 2 | hacker6284 | Refinement proofs of the existing rule. |
| 2026-09-25 | [#29](https://github.com/hacker6284/cryptoys/pull/29) playroom | Zach Mills | Demo copy moved. |
| 2026-09-26 → 28 | [#75](https://github.com/hacker6284/cryptoys/pull/75), [#86](https://github.com/hacker6284/cryptoys/pull/86), [#91](https://github.com/hacker6284/cryptoys/pull/91), [#95](https://github.com/hacker6284/cryptoys/pull/95), [#96](https://github.com/hacker6284/cryptoys/pull/96) | hacker6284 | Version freezes copy §3.7 verbatim ("PassKey … unchanged"). The SPEC F pseudocode on main is byte-identical to `a2e9b70` (`diff` empty). |

**Original prose, verbatim** (`a2e9b70:primitives/cipher/twodeck/SPEC.md`, §4.6):

> 2. For each controller **C** dealt from the hand:
>    - Deal C (remove from top of hand).
>    - If cards remain in hand: rotate the hand **left** by C’s **suit** places (♣=0 ♥=1 ♠=2 ♦=3), wrapping; use suit **mod** how many cards are left.
>    - **Proper cut** only (count **strictly less** than packet size — do **not** wrap with mod):
>      - If the hand still has cards and C’s **rank** \(<\) hand size: cut the **hand** by that rank.
>      - Else if the key pile is nonempty and C’s rank \(<\) key-pile size: cut the **key pile** by that rank.
>      - Else skip the cut.
>    - Place C **on top** of the key pile.

The original §7 choreography says: "Controller card lifts and flashes **suit** (hand rotate) then **rank**".

**What the original text supports.**
* It says "rotate the hand left by C's suit places, wrapping". That is x = suit, on the **hand**, moving top
  cards to the bottom in order. x one-card top-to-bottom moves equal one cut of x, so this is the current rule and
  the collision is unchanged (reading SAME below is bit-identical to the current F).
* No written version in the repo describes a deal that reverses the cards, or moving them to the key pile.

### 7.2 Readings measured (`readings.c`, `readings_exact.py`; x = suit; rank cut and fallback unchanged)

Zachary's stated intent is a deal: the x cards move one at a time, so the moved packet ends up reversed. The
original says "rotate the **hand** … wrapping", so the natural deal version keeps the cards in the hand:

* **DEALB:** deal x cards off the top and put that reversed packet under the hand, then cut by rank.
* **DEAL:** deal them onto the key pile. Measured as the other pile choice.
* **REVT:** reverse them in place on top. Shown for completeness.
* **KEYP:** do the suit move on the key pile. Also for completeness.

One pass, uniform decks, 20k decks per swap for all 1326 swaps. Reversibility is a round trip on 200k decks each
way. Six passes are 200k keys for the worst pair. The closed-form bounds come from exact move comparison.

| reading | reversible | worst swap (one pass) | 2♥↔A♠ | pairs > 1/64 | worst pair, all six passes τ-related |
|---|---|---|---|---|---|
| CUR (SPEC F) | yes (0 fails) | 2♥↔A♠ 0.890 (exact bound 196/221) | 0.890 | 68 | 0.479 |
| SAME (x one-card top→bottom moves of the hand) | yes | identical to CUR on 200k/200k decks | — | 68 | — |
| **DEALB** (deal x off the hand, reversed, under the hand) | **yes** (0 fails) | **2♣↔A♥ 0.887** (bound 196/221) | **0.0153 ± 0.0009** | **12** | 0.482 |
| DEAL (deal x onto the key pile) | **no**: ≥2 preimages for 59% of outputs; dealt cards never act as controllers | 6♥↔6♠ 0.374 | 0.349 | 1326 | — |
| REVT (reverse the top x in place) | yes | A♣↔A♥ 1.000 | 0.000 | 25 | 1.000 |
| KEYP (suit moves on the key pile) | yes | K♥↔Q♠ 0.059 | 0.0006 | 35 | 0 of 200k |

What the table shows:
* **DEALB fixes 56 of the 68 collisions, including 2♥↔A♠, but not all.**
  * Dealing 0 or 1 card reverses nothing, so a ♣ card (deal 0) and a ♥ card (deal 1) are still plain
    rotations. The 12 pairs ♣(r+1)↔♥(r) (2♣↔A♥ … K♣↔Q♥) keep exactly the current rates, up to 0.887, and the
    same ≈0.48 six-pass related-key rate.
  * 2♥↔A♠ drops to 0.0153, just under 1/64. No step makes the same move for it (e = 0), so this rate comes
    entirely from paths that diverge and re-merge.
* **DEAL onto the key pile is not a bijection**, so it cannot be the key schedule's F.
* **REVT is worse:** ♣ and ♥ cards of the same rank make identical moves at every step.
* **KEYP** leaves a residue: late in the pass the rank cut also falls on the key pile, where suit and rank add
  again (King/Queen pairs up to 0.059).
* **Unmeasured hand-friendly idea for the ♣/♥ residue:** deal x = suit + 2 cards (2–5), so every suit reverses
  at least two cards. Not tested.

## 8. "Deal suit + k" for k = 0..4 (follow-up)

**Rule measured (analysis only; not the spec).** Pop the controller C; the hand now has n cards.

1. Deal m cards one at a time off the top of the hand. They land reversed. Put that small packet under the hand.
2. Do the existing rank cut with key-pile fallback, unchanged.
3. Put C on top of the key pile.

Here m = suit(C) + k (♣0 ♥1 ♠2 ♦3), reduced as below when the hand is short. The inverse gesture mirrors this:
lift C, undo the rank cut, then take the bottom m cards as a packet and deal them one at a time onto the top of
the hand (which reverses them back).

**Short hands: chosen rule `mod`.** If the count is not smaller than the hand, subtract the hand size until it
is, i.e. m = (suit + k) mod n. This only matters in the last suit + k steps of a pass (n ≤ 6 for k = 2), and it
is one small subtraction.

The obvious alternative is `min`: when the hand runs out, deal everything. It is also reversible, but late in
the pass every card with suit + k ≥ n then makes the same move (reverse the whole hand), so the two cards of a
same-rank pair act identically there. Measured, this makes the worst swap 3.5× worse at k = 2 (≈1/89 against
≈1/300), and at k = 3 and 4 it puts 5 and 29 pairs above 1/64. Both rules are in the table.

**Why it is reversible (both rules).**
* The inverse reads C from the top of the key pile. The hand size n at C's step is the inverse's current hand
  size, because neither the deal nor a hand cut changes it. So m can be recomputed, and so can the rank-cut
  branch (it depends only on rank(C) and the two pile sizes, exactly as in today's F⁻¹).
* "Reverse the top m, move them to the bottom" is a fixed permutation of the n hand seats once m is known.
  Undo it by moving the bottom m back to the top, then reversing them.
* So each step is a bijection on (hand, key) states of fixed sizes, and the pass is their composition. This is
  the same argument as `PassKey.lean`.
* Round trip: 0 failures in 200k decks each way, for every k and both rules (`logs/dealk.log`, `logs/dealk_mod.log`).

**Results.** One pass, all 1326 swaps at 20k decks each (seed 31). Top pairs were re-measured at 1M decks
(`logs/dealk_check.log`). The exact bound is the largest closed-form lower bound e(e−1)/2652 over all pairs
(`logs/dealk_exact.log`). The six-pass rate is for the worst pair, over 200k keys. Cards dealt per pass is exact
(the controller is uniform at each step).

| rule | reversible | worst swap, one pass | 2♥↔A♠ | pairs > 1/64 | exact bound (max) | six passes, worst pair | cards dealt per pass |
|---|---|---|---|---|---|---|---|
| current F | yes | 2♥↔A♠ 0.890 | 0.890 | 68 | 196/221 | 0.479 | 0 (one suit cut per step) |
| k=0 (min or mod) | yes | 2♣↔A♥ 0.887 | 0.0149 | 12 | 196/221 | 0.479 | 75.5 / 73.3 |
| k=1 min | yes | 2♣↔A♥ 0.0146 (1M) ≈ 1/69 | 0.0020 | 0 | 5/663 | 0 / 200k | 125.0 |
| k=1 mod | yes | 2♣↔A♥ 0.0146 (1M) ≈ 1/69 | 0.0016 | 0 | 1/442 | 0 / 200k | 120.5 |
| k=2 min | yes | 2♠↔2♦ 0.0112 (1M) ≈ 1/89 | 0.0006 | 0 | 5/442 | 0 / 200k | 173.5 |
| **k=2 mod** | **yes** | **A♥↔A♦ 0.0034, 3♥↔3♦ 0.0032 (1M) ≈ 1/300** | **0.0008 (1M)** | **0** | **1/442** | **0 / 200k** | **166.5** |
| k=3 min | yes | 7♠↔7♦ 0.0175 | 0.0006 | 5 | 7/442 | 0 / 200k | 221.0 |
| k=3 mod | yes | A♣↔A♠ 0.0032 (1M) ≈ 1/310 | 0.0004 | 0 | 1/442 | 0 / 200k | 210.3 |
| k=4 min | yes | 6♠↔6♦ 0.0225 | 0.0006 | 29 | 14/663 | 0 / 200k | 267.5 |
| k=4 mod | yes | 4♣↔4♦ 0.0023 (1M) ≈ 1/430 | 0.0010 | 0 | 1/442 | 0 / 200k | 253.0 |

Top 5 pairs (20k screen):

| rule | top 5 pairs |
|---|---|
| k=1 | 2♣↔A♥, 3♣↔2♥, 6♣↔5♥, 5♣↔4♥, 4♣↔3♥ (0.012–0.015) |
| k=2 mod | 3♥↔3♦, A♥↔A♦, J♣↔J♠, K♣↔K♦, 5♥↔5♦ (0.0029–0.0037) |
| k=3 mod | A♣↔A♠, 3♣↔3♠, 6♥↔6♦, Q♥↔Q♦, 8♣↔8♦ (≈0.003) |
| k=4 mod | 4♣↔4♦, 6♣↔6♦, 8♣↔8♦, A♥↔A♦, 8♥↔8♦ (≈0.003) |

Reading the results:
* **k=1** removes every exact collision, but the ♣↔♥ suit+rank pairs still pass at ≈1/69 through paths that
  split and rejoin. Dealing 1 card (a ♣) is a plain rotation, and dealing 2 (a ♥) differs from it only by one
  adjacent swap.
* **From k=2 up (mod)** every suit reverses at least two cards. The worst swap flattens at about 1/300–1/430,
  5–7× below the 1/64 bar and around 250× better than today's F. Beyond k=2 it gains nothing
  measurable, while each extra k costs about 44–48 more card deals per pass.

**Full-cipher sanity check with k=2 mod as the key schedule** (`logs/rk_dealk2mod.log`, 3M (K, P) samples per
swap, for 3♥↔3♦ (its worst), 2♥↔A♠ and 2♣↔A♥):
* The relations E_τK(P) = E_K(P), E_τK(P) = E_K(P)∘σ and E_τK(τP) = τE_K(P) had 0 hits (95% upper bound 1e-6).
* Ciphertext equal seats: 0.9989–1.0003 ± 0.0011, where unrelated decks give 1.
* No key reached six τ-related round keys, and in the oracle-aligned case the state already differs in
  50.3–50.5 seats after round 1 (7.5 with today's F). The related-key relation now dies in the first pass.

**Recommendation (proposal only).** If PassKey is changed to match the intended "deal" gesture, use **deal
suit + 2, reversed, under the hand, count taken mod the hand size, then the unchanged rank cut**.
* It is reversible by the same per-step argument that `PassKey.lean` already uses.
* It removes all 68 suit+rank collisions. The worst one-pass swap is ≈1/300, with 0 pairs above 1/64.
* The cost is about 3.2 cards dealt per controller, 166.5 per pass. That is roughly 1000 extra single-card deals
  per encryption, since there are six passes.
* Every round key, every vector and the PassKey Lean/Link 2 files would change. Section 4 found no measured
  full-cipher need, so this is a fidelity/cleanliness change, not a security fix.
* k=1 is cheaper (120 cards) but leaves the ♣↔♥ pairs at ≈1/69. k=3 and 4 cost more for no measured gain.
