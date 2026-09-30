# MegaDreifach hash: security review (reductions, proofs and cryptanalysis)

> **Status update.** Everything in this report is about **MegaDreifach v1**, which is now **deprecated** and frozen at `primitives/hash/megadreifach/v1/` (SPEC + `megadreifach.sudo`). "As published" and "current" below mean v1 as it was when this report was written. The current version is v2 (`primitives/hash/megadreifach/SPEC.md`), which this report does not analyse. `md.py` and `tables.py` model v1; `md.py` reads the v1 KAT file `kats/megaminx_hash_kats_v1.json` (renamed from `kats/megaminx_hash_kats.json`, contents unchanged). Card names use CHaSeD suit order (id % 4: 0 ♣, 1 ♥, 2 ♠, 3 ♦). The file count in §1 ("Files are in `proofs/megadreifach/lean/MegaDreifach/Security/`: 9 modules") and its audit count ("2,371 theorems audited") are v1-era snapshots.

Subject: MegaDreifach v1 (`primitives/hash/megadreifach/v1/`, deprecated). Its block map E_m uses the **v1 Recipe A grip rule**, called "v1 of the grip rule" (or just "v1") below. Recipe A re-grips by reading one corner cubie, after the card's held-face, noon and Front turns. ("v1" here names the grip rule only; it is unrelated to the v1 SPEC's "Public v1 Body" API name.)
Lean: the v1 results below are in the frozen package `proofs/deprecated/megadreifach-v1/lean` (Lean v4.14.0, namespace `MegaDreifachV1`, files in `MegaDreifachV1/Security/`); the rule-independent files of §1.5 were ported to v2 in the main package `proofs/megadreifach/lean`; the scripts are in this directory (`proofs/megadreifach/security/`), with their recorded outputs in `logs/` (§7).
**Note: this package has no Mathlib. It is core Lean plus the repo's `audit` package.** Every proof below uses core Lean only.

**How to read this report.**
* **Proved** means a kernel-checked Lean theorem: the v1 results (§1.3) are in `MegaDreifachV1` (`proofs/deprecated/megadreifach-v1/lean`), audited by `check_axioms.py megadreifach-v1-deprecated`; the rule-independent results are proved for v2 in the default library `MegaDreifach`, audited by `check_axioms.py megadreifach`; only `MDGeneric`, `MDReduction`, `StepWord` and `Parity` are also in `MegaDreifachV1` (`DigestInj` and `IdealCount` were not kept, so e.g. `v_Hash_collision_comp` is no longer proved for the v1 `v_Hash`).
* **Measured** means a seeded script run on the real hash (via the KAT-checked `md.py`), with the output committed under `logs/` and re-checked by `--check`. The swap attack F5 (§3) is measured: it gives concrete IV-anchored `Hash` collisions at about 2^12–2^13 compressions, and second preimages of long random targets. One collision is also kernel-checked in Lean (`MegaDreifachV1.Security.SwapCollision.v_Hash_swap_collision`).
* **Estimated** means a paper attack extrapolated from toy-scale runs (§4) under stated assumptions. This applies to F3 and F4 (§2). They were not run at full size. No preimage of `Hash` has been found.
* **The ideal-cipher bound does not apply.** §2 records the Black–Rogaway–Shrimpton ideal-cipher bounds only as the design target. E_m is not an ideal cipher: `emBlock_word` gives a 2-query distinguisher, and F5 a practical related-key one. So those bounds say nothing about MegaDreifach v1.
* **Two separate causes.** The v1 weaknesses have two different causes (§0, "Causes"): the corner-only read (F1–F4) and the read timing after the noon turn (F5). In-tree, a control run (§3.5) keeps Recipe A's corner-only read and moves only the read to before the noon turn: the swap collisions disappear (distance 2 from the IV: 15/35,175 → 0/35,175). That an edge-reading rule which still reads after the noon turn keeps them is out-of-tree evidence only. So a redesign should address both; fixing A alone is not expected to remove F5, but that half is not shown here. The MD reduction, the pad suffix-freeness, digest-encoding injectivity (`evenRank_inj` plus the parity invariant), the step lemmas and the ideal-model counting lemmas are independent of the grip rule (§1.5).

## 0. Summary

* **MD reduction, proved.** Take two different well-formed messages with the same digest. A computable function `extract` returns a collision of the compression step `dm(h, block) = h * E_block(h)`. The IV/length branch is proved impossible, because the padding has MD strengthening (a 64-bit bit length). The same holds for the generated `v_Hash`, via Link 2. Second-preimage versions are proved too, for `vhashAlg` and for `v_Hash`.
* **The reduction gives no security, because the compression function is broken (under v1).**
  * **F1 (corner-driven; proved).** For a fixed block, `E_m(h) = W * h`, where the word `W` depends only on the *corner* part of `h`. The corner chain is therefore an independent 90.2-bit MD hash, and the top ~90.2 bits of the digest depend only on that chain.
  * **F2 (universal pseudo-collisions).** For every block and every corner value, there are distinct legal chaining values with the same `dm` output. Finding them takes 3 block encryptions. Lean proves the reduction to a squaring collision (`dmStep_pseudo_collision`). That such pairs exist is a short paper argument (two edge involutions), checked by `pseudo_collision.py` on 50/50 random (corner, block) pairs.
* **F5, practical IV-anchored collisions of the full hash (measured; §3).**
  * In each G2 step the Recipe A read comes after the noon turn, which usually brings a piece from off the held face into the read slot. So for about 71.5% of cards the new grip does not depend on the suit, i.e. on the turn amount k.
  * Swapping two same-rank cards exactly two positions apart (cards i and i+2) is then a **3-card local collision** about **once in 2,800 tries**. The runs give 1/2,496 from the IV, 1/3,267 from a non-IV chaining value, and 1/2,933 in the reviewer's independent run; pooled, 80/220,116.
  * Other distances are much rarer: 3 apart 1/16,000 and 4 apart 1/38,000 (from the IV); adjacent same-rank cards 0/224,315.
  * Cost: about **2^12–2^13 compressions per full `Hash` collision**, a few seconds of Python, against a generic 2^113.
  * A concrete pair of 28-byte messages with digest `0084d6d1…c34e82` is verified by `suit_blind_collision.py` and kernel-checked in Lean for the generated `v_Hash`.
  * **Second preimages of long targets are practical too:** about 1 in 900 random blocks admits a colliding two- or three-apart swap. A second preimage was found for 65/100 random targets of 1,000 blocks (28 KB) and 30/30 of 3,000 blocks (84 KB), at about 4,300–6,200 compressions per target.
  * **Related-key distinguisher of E_m:** for a block m and its swap m′, `E_m(h) = E_m′(h)` with probability ≈ 1/2,800, against ≈ 2^−226 for an ideal cipher.
* **Effective security of v1. Generic figures use |G| = 2^225.90.**

| goal | generic | this analysis (v1 grip rule) |
|---|---|---|
| free-start / pseudo-collision of `dm` | 2^113 | **instant** (F2; reduction proved; demo on the real function) |
| full-hash collision (IV-anchored) | 2^113 | **practical: ≈ 2^12–2^13 compressions, measured** (F5, §3). A concrete pair is verified by script and kernel-checked in Lean |
| collision on the top ~90 digest bits | 2^45 | moot: implied by any full collision |
| second preimage, long targets | 2^226 (≈ 2^226/L for L-block targets) | **measured, practical:** found for 65/100 random 1,000-block targets and 30/30 3,000-block targets, ≈ 2^12–2^12.6 compressions per target (F5, §3.4) |
| second preimage, short targets | 2^226 | **estimate: ~2^93–2^96** (F4, paper). F5 applies only when the target has a vulnerable block, ≈ 1/900 per full block (a one-block target: ≈ 0.1%) |
| preimage | 2^226 | **estimate: ~2^93–2^96** compressions + 2^68 time/memory MitM (F4, paper). F5 gives no preimages |
| distinguishing E_m from an ideal cipher | — | 2 queries (F1, single key); ≈ 2^12 related-key query pairs (F5) |

The F4 figures are paper attacks. Only their toy-scale versions were run end to end (§4): every toy collision and preimage was checked by re-hashing, and the toy costs follow the predicted formulas. The full-size figures extrapolate those formulas (and the square-class, square-fraction and edge-tree trends measured for scaled edge groups with n ≤ 10 edges) to the real 30-edge group; they are not measurements. The earlier corner-based collision estimate (F3, §2) is no longer an estimate of anything useful, because F5 is far cheaper. It is kept in §2 only as the derivation F4 builds on.

**Causes: what is shown and what is unknown.**

| cause | findings | what is shown | what is not known |
|---|---|---|---|
| **A. The read sees only corners** (Recipe A reads a corner cubie; `recipeA_sameCorners`) | F1, F2, and the paper attacks F3 / F4 built on F1; top-90-bit structure (`digest_top_collision`) | F1 and the F2 reduction are proved in Lean; F2 is demonstrated on the real hash | whether a rule that also reads edges has other free-start weaknesses (an out-of-tree prototype found free-start pseudo-collisions via never-read pieces); F3 / F4 costs at full size |
| **B. The read comes after the noon turn** (so it usually ignores k) | F5: suit-blind re-grips, same-rank swap collisions, long-target second preimages, the related-key distinguisher | the suit-blind fraction, the swap collision rates per distance, and the second-preimage rates are measured; for the recorded pair the grips and positions are shown equal after card 7 (script and Lean). In-tree control (§3.5): with the read moved before the noon turn, and nothing else changed, no swap at distance 1–4 collides in 139,490 tries (Recipe A: 17) | an exact characterisation of which swaps rejoin (the rates are measured, not derived) |

Evidence that B, not A, causes F5:
* **In-tree (§3.5, `suit_blind_collision.py --variant pre-noon`).** Keep Recipe A (corner-only) and move only the read to right after the held-face turn. The suit-blind fraction drops from 0.715 to 0.000, and same-rank swaps at distances 1–4 from the IV go from 17/139,490 colliding (distance 2: 15/35,175) to 0/139,490 on the same blocks. So, under Recipe A, the read after the noon turn is what makes the swaps collide. This shows that, under Recipe A, B is necessary for F5; it does not show what an edge-reading rule does.
* **Out-of-tree only (not reproducible from this repository).** A candidate rule that alternates corner and edge reads but still reads after the noon turn had the same collisions: 36 in 264,115 swaps, against 41 for v1. The reviewer of this PR independently saw the pre-noon drop (distance 2: 19/35,588 → 0/35,588).

So a redesign that only makes the read see edges is expected to remove F1 but not F5; the second half of that sentence rests on the out-of-tree run. Whether a rule fixing both causes is secure is unknown.

## 1. What is proved in Lean

Files are in `proofs/megadreifach/lean/MegaDreifach/Security/`: 9 modules (~1,790 lines) plus the aggregator `MegaDreifach/Security.lean`.
* The aggregator is imported by `MegaDreifach.lean`, so `lake build MegaDreifach` builds and checks everything.
* Imports follow use: the step lemmas and `Word` are in the rule-independent `StepWord.lean`, which `Parity` and `CornerDriven` both import. So deleting the v1 files does not take M3 or `v_Hash_collision_comp` with it.
* The repo gate `python3 proofs/doubledeal/check_axioms.py megadreifach` passes: *2,371 theorems audited (the whole default library, Security included), all use only [Classical.choice, Quot.sound, propext], 0 failures*. The per-theorem axiom columns below are from that audit.
  * Its required-headline list is every theorem the MegaDreifach README cites by name, plus the Link 2 and Security headlines.
* There is no `sorry`, `admit` or `native_decide` (`scan_sorry.py`), and no axioms beyond those three (`check_axioms.py`).
* The heavy KAT library `MegaDreifachHeavy` is unchanged.

### 1.1 Generic Merkle–Damgård (`MDGeneric.lean`, any `dm : α → β → α`)
| theorem | content | axioms |
|---|---|---|
| `findR_collision` | Equal chains over block lists where neither is a suffix of the other ⇒ the computable `findR` returns a compression collision `(h,b) ≠ (h',b')` with `dm h b = dm h' b'` | propext |
| `findR_collision_or_iv` | Without strengthening: a collision **or** an IV preimage (`dm h b = IV`) | propext |
| `md_collision` | Forward-list form, stated with `<:+` (suffix) | propext, Quot.sound |

### 1.2 MegaDreifach instantiation (`MDReduction.lean`, `DigestInj.lean`)
| theorem | content | axioms |
|---|---|---|
| `pad_suffix_free` | `pad m1 <:+ pad m2 ⇒ m1 = m2` when `8·len < 2^64`. **The pad contains the length, so MD strengthening holds** | propext, Quot.sound |
| `extract_collision` | Distinct well-formed messages with equal chaining values ⇒ `extract m1 m2 = some b` with `b` a valid comp collision *or* digest-level "out" break | all three |
| `evenRank_inj` | `evenRank` is injective on even permutations of `0..n-1` (M3 glue; surjectivity / unrank stays open) | all three |
| `isLegal_chainMsg` (Parity.lean) | Every chaining value reachable from the IV is a legal position: even cp/ep, co sum ≡ 0 mod 3, eo sum even (the open "parity invariant for DM outputs") | all three |
| `positionToBytes_inj_legal` / `_reachable` | The digest encoding is injective on legal, and hence all reachable, positions | all three |
| **`extract_collision_comp`** | `PadWf m1, PadWf m2, m1 ≠ m2, vhashAlg m1 = vhashAlg m2 ⇒ ∃ c, extract m1 m2 = some (Break.comp c) ∧ valid`: a compression collision, with the out branch ruled out | all three |
| **`extract_second_preimage_comp`** | Same, and the first side is `(chainPre (pad m) i, blockAt (pad m) i)` for some `i`, i.e. it sits on the target message's own chain | all three |
| **`v_Hash_collision_comp`**, **`v_Hash_second_preimage_comp`** | The same two statements for the generated `Megadreifach.v_Hash (embed m)`, via Link 2 (`v_Hash_refines`, through `vhashAlg_eq_of_v_Hash`) | all three |
| `comp_collision_deals` | The collision lifts to deals and `Em.dmStep` | all three |

**Answer to the MD-strengthening question.** The padding appends the 8-byte big-endian bit length. The reduction therefore needs nothing beyond `8·|m| < 2^64`, which is part of `PadWf`, and the IV branch disappears. Without strengthening, `findR_collision_or_iv` shows that an IV preimage `dm(h,b) = IV` would also have to be allowed.

### 1.3 Weaknesses of v1, proved (`CornerDriven.lean`, `FreeStart.lean`, `SwapCollision.lean`)

The theorems of `CornerDriven` and `FreeStart` rest on cause A: Recipe A reads only corner cubies (`recipeA_sameCorners`). They document why the rule is being redesigned, and need not hold for a redesigned rule.

| theorem | content | axioms |
|---|---|---|
| `emBlock_word` | `SameCorners h h' ⇒ ∃ W, E_m(h) = W∘h ∧ E_m(h') = W∘h'`. The grips (Recipe A) read only corner stickers | propext, Quot.sound |
| `dmStep_word` | `dm(h,m) = h∘W∘h` with the same `W` for all `h` sharing corners | propext, Quot.sound |
| `corner_collision_extends` / `foldl_dmBlock_sameCorners` | A corner-only match propagates through any suffix | propext, Quot.sound |
| `digest_top_collision` | Same corners ⇒ `rank(digest) / edgeRadix` is equal: the top ≈ 90.2 bits of the digest depend only on the corner chain | all three |
| `dmStep_collision_of_sq` | Same `W` and `(hW)² = (h'W)² ⇒ dm(h,m) = dm(h',m)` | propext, Quot.sound |
| `dmStep_pseudo_collision` | For same corners there is a legal word `W` (a product of face moves) with that implication | all three |

The invariant `WordInv` carries `Word W` (the shared word is a product of face moves), so `emBlock_word` and `emBlock_word_legal` come from the same induction (`emBlock_wordInv`).

**A concrete IV-anchored collision, kernel-checked (`SwapCollision.lean`; cause B, §3).** It is about the v1 hash and does not use `recipeA_sameCorners`.

| theorem | content | axioms |
|---|---|---|
| **`MegaDreifachV1.Security.SwapCollision.v_Hash_swap_collision`** | `embed M ≠ embed M' ∧ ∃ d, Megadreifach.v_Hash (embed M) = .ok d ∧ Megadreifach.v_Hash (embed M') = .ok d` (both runs succeed, same digest) for the 28-byte pair of §3.3, about the **generated** `v_Hash` (via `v_Hash_refines`) | all three |
| `SwapCollision.vhashAlg_collision` | The same for the algebraic hash `vhashAlg` | propext, Quot.sound |
| `SwapCollision.dmBlock_iv_collision` | `dmBlock IV M = dmBlock IV M'`: the first compressions agree | propext, Quot.sound |
| `SwapCollision.prefixA` / `prefixB` | Both 7-card prefixes of the deals lead from (IV-COOK12, identity grip) to the same position and grip | propext, Quot.sound |

The proof is cheap. It evaluates only the two 7-card prefixes with plain `decide` (a few seconds), not whole blocks. `phiUnrank`, the padding and the block split are small `decide`s, and the rest is `List.foldl_append`. So it lives in the default library and does not need `MegaDreifachHeavy`. The digest value itself is not evaluated in Lean; the script prints it.

### 1.4 Ideal-model combinatorics (`IdealCount.lean`)
| theorem | content |
|---|---|
| `injective_surjective_fin` | Pigeonhole: an injective map on `Fin n` is surjective |
| `compose_left_cancel` | Left cancellation in the position group (right cancellation is `Group.leftMul_cancel`) |
| `dm_forward_bad_count` | For fixed `h`, at most \|Z\| cipher outputs `y` make `h∘y` land in a target set `Z` |
| `dm_inverse_bad_count` | For fixed `y`, at most \|Z\| keys `h` do |
| `reachable_rank_lt_group` | Every reachable digest rank is < \|G\|. (That the leading digest byte is therefore ≤ 0x03 is derived on paper: \|G\| < 4·2^224.) |

These are the counting cores of the Black–Rogaway–Shrimpton Davies–Meyer bound. The probabilistic step is paper-only (§2), since no probability library is available without Mathlib. The bound itself does not apply to MegaDreifach v1 (§2).

### 1.5 Which results depend on the grip rule

A transitive scan of constant dependencies over every theorem in `MegaDreifach.Security` (128 declared in the source; the axiom audit reports 165 theorem constants declared in the Security modules, counting the equation and match lemmas Lean generates) finds 15 that use `recipeA_sameCorners` (the corner-only read). All are in `CornerDriven.lean` and `FreeStart.lean`: `recipeA_sameCorners` itself, `wordInv_g2Step`, `wordInv_f3Step`, `wordInv_f3Iter`, `wordInv_foldl`, `emBlock_wordInv`, `emBlock_word`, `emBlock_is_leftMul`, `dmStep_word`, `dmStep_sameCorners`, `foldl_dmBlock_sameCorners`, `corner_collision_extends`, `digest_top_collision`, `emBlock_word_legal`, `dmStep_pseudo_collision`. `SwapCollision.lean` does not use it (it evaluates `Em` directly).

| file | grip rule | what needs repair if E_m changes |
|---|---|---|
| `MDGeneric.lean` | independent | nothing (generic in `dm`, `iv`) |
| `MDReduction.lean` | independent | `injPos_chR_from` / `injPos_chR` (via `Link2.injPos_dmStep`, which unfolds `Em`). The pad lemmas (`pad_suffix_free`, `blocks_suffix_free`) and `extract_*` need nothing. The Link 2 refinement of the new sudo E_m is separate work |
| `StepWord.lean` | independent | `g2Step_fst`, `f3Step_fst`, `word_g2Step`, `word_f3Iter`, `word_foldl_g2`, `word_emBlock`, which unfold the (v1) `Em` steps. They go through again if each step still left-multiplies by face moves |
| `Parity.lean` | independent | only through `StepWord`; `swC` / `swE` only if the face-move tables change |
| `DigestInj.lean` | independent | `evenRank_inj`, `positionToBytes_inj_legal`: nothing. `positionToBytes_inj_reachable`, `extract_*_comp`, `v_Hash_collision_comp`, `v_Hash_second_preimage_comp`: only through `isLegal_chR` and `injPos_chR` |
| `IdealCount.lean` | independent | counting lemmas: nothing. `reachable_rank_lt_group`: through `injPos_chR` |
| `CornerDriven.lean` | **v1** (cause A) | the weakness theorems are expected to fail for an edge-reading rule; delete or restate. The digest arithmetic (`rankPosition_split`, `edgeRank_lt`, `rankPosition_div`, `cornerRank_sameCorners`) does not depend on the rule |
| `FreeStart.lean` | **v1** (cause A) | `emBlock_word_legal`, `dmStep_pseudo_collision`: delete or restate. `dmStep_collision_of_sq` is plain group algebra (it assumes a shared word) |
| `SwapCollision.lean` | **v1** (cause B; v1 hash) | A concrete instance proved by evaluating the (v1) `Em.g2Step`. It fails as soon as E_m changes; delete it then (or replace it with a pair for the new rule, if one exists) |

## 2. Argued on paper (with assumptions)

**Effective output size.**
* |G| = (20!/2)·3^19·(30!/2)·2^29 ≈ 2^225.90. The digest is 29 bytes (232 bits), but only ranks < |G| occur (`reachable_rank_lt_group`), and `isLegal_chainMsg` plus the injective encoding show every reachable value is a legal position. So n = 225.90 bits. The parity restrictions are already inside |G|; there is no further shrinkage.
* The group is a direct product of the corner part Gc (2^90.19) and the edge part Ge (2^135.71).
* Blocks: 28 bytes = 2^224 < 52!, and φ is injective (already proved). The first card of every deal is always one of the first 18 values; this is harmless.

**Ideal-cipher bounds (design target only; shown inapplicable below).** Assume E is an ideal cipher on G, i.e. an independent random permutation of G for each block. At query i the answer is uniform over at least |G| − i values, and by the counting lemmas at most i of them are bad. This gives:
* Adv^coll(q) ≤ q(q+1)/(|G|−q), which is about q²/2^225.9 for q ≪ |G|. Collision security is ≈ 2^112.9.
* Adv^pre(q) ≤ q/(|G|−q), which is about q/2^225.9. Preimage security is ≈ 2^225.

The same forms are stated in the `IdealCount.lean` docstring. The per-query counting steps are `dm_forward_bad_count` and `dm_inverse_bad_count`; the averaging over the random permutation is paper math.

**The ideal-cipher bound is inapplicable to MegaDreifach v1: its assumption is false.**
* `emBlock_word` gives a 2-query distinguisher: two chaining values with the same corners and different edges are mapped by the same left multiplication, which an ideal cipher does with negligible probability.
* F5 gives a related-key distinguisher: `E_m(h) = E_m′(h)` for a same-rank two-apart swap m′ of m, with probability ≈ 1/2,800 (§3).
* For a fixed block, `h ↦ W(h_c)·h` is a permutation of G only if `h_c ↦ W_c(h_c)·h_c` is a permutation of Gc. That was not established and has no reason to hold.

So the ideal-cipher numbers are only what the design could at best achieve. They are not a bound on MegaDreifach v1's security, and this report does not use them as one.

**F3, corner-based collision attack (paper estimate, confirmed at toy scale only). Superseded:** F5 (§3) gives collisions at ≈ 2^13, so F3's ~2^59 (conservative 2^68) is no longer an estimate of MegaDreifach's collision security. It is kept because F4 reuses its corner multicollision and edge tree.
Assumption: the corner chain behaves like a random 90.2-bit compression function. It is itself an MD hash on corners: F1 means it ignores edges.
1. Build a Joux multicollision on corners with t stages, at about 1.25·2^45.1 per stage. This gives 2^t messages with identical corner chains.
2. Their edge values follow e → e·X_i·e, where X_i is known and depends only on the corner state and block. Find two leaves with equal edges; by F1 they then have equal full states and equal digests.
   * Two leaves also merge whenever (e·X)² values coincide. The collision probability per pair is c/|Ge|, where c = Σ r(y)²/|Ge| is the number of square classes (exact for n ≤ 8 in `exp_square_classes.py`, extrapolated c(30) ≈ 2^17.4).
   * So the edge tree first merges after about 2^{(135.7−17.4)/2} ≈ 2^59 leaves. The conservative figure, ignoring the squaring gain, is 2^67.9.
3. Cost: about 60 stages × 2^45.1 ≈ 2^51 compressions, plus 2^59 edge-group multiplications.
   * An edge multiplication is much cheaper than a compression; one compression is ~246 face turns.
   * Memory is 2^59, or low memory with a Pollard-rho walk over leaf selectors at a factor-t cost (~2^65 edge operations).

**F4, preimage / second preimage (paper estimate, confirmed at toy scale only).**
1. Build a corner multicollision of length L ≈ 137, about 2^52 compressions.
2. Find a last block (19 free bytes available after the padding) that maps the common corner value to the target corner: 2^90.2.
3. Run an edge meet-in-the-middle:
   * forward: 2^{L/2} edge values from the IV;
   * backward: from the target through the last block and the last L/2 stages using square roots (e X e = y ⇔ (eX)² = yX ⇔ e = r X⁻¹, r² = yX);
   * about 2^68 time and memory.
4. The backward tree can die out when yX is not a square. The fraction of squares is ~0.24–0.40 for n = 6..8 and ≈ 2^−3 for the n = 30 edge group (`exp_square_fraction.py`, B_n criterion). Step 2 is therefore repeated a few times: 6–7 times in the toy runs, estimated 2^3–2^6 at full size.
5. Total ≈ 2^93–2^96, against 2^226 generic. This works for second preimages too, since only the target digest is used. For second preimages of long targets it is moot: F5 finds them far more cheaply (§3.4).

**DM fixed points.** `dm(h,m) = h∘W∘h = h ⇔ W∘h = 1 ⇔ h = W⁻¹`. Because `W` depends on `h_c`, this is a corner fixed-point problem, `h_c = (W_c(h_c))⁻¹`, costing ~2^90. The edges are then forced: `h_e = W_e⁻¹`. This gives no advantage beyond F1/F4.

## 3. F5: suit-blind re-grips give practical IV-anchored collisions (measured)

Script: `suit_blind_collision.py`, on the repo's `md.py` (it re-runs the 8 KAT checks first). Recorded outputs: `logs/suit_blind_collision.log` (quick run, checked in CI with `--check`), `logs/suit_blind_collision_full.log` (the report-size runs below, `--check --full`) and `logs/suit_blind_collision_pre_noon.log` (the control of §3.5, `--check --variant pre-noon`). The script is derived from the scripts of an out-of-tree review of candidate grip rules, keeping only v1. F5 does not use F1 (cause A); it comes from *when* the grip is read (cause B).

### 3.1 Mechanism: the read ignores the suit

A non-King card of rank r and suit s (k = s + 1) runs these steps in v1:
1. turn the held face F by +k;
2. turn F's noon face N by +1;
3. turn Front by +1;
4. read the Recipe A corner (the slot between F, N and the next neighbour of F) and re-grip from its colours on F and N.

The read slot is on N. The noon turn in step 2 moves into it a corner that was on N but, in the usual case, not on F, so the F^k turn of step 1 never touched it. The new grip is then the same for all four suits, unless the Front turn of step 3 also moves the read slot. A King's grip always depends on k, because the grip is spun by +k.

Measured (3,000 uniformly random legal states, grips and ranks):
* P(all 4 suits give the same grip) = **0.715**, i.e. 1.86 distinct grips on average over the 4 suits.
* Per rank: A, 4–7 and 9–Q always (1.00); 8 in 0.16 of cases; 2 (held face = Front), 3 and K never.

### 3.2 Attack: swap two same-rank cards

Take cards i < j of the same rank and different suits, and swap them. With j = i + 2 this is a **3-card local collision** when two things hold:
* the grips agree in both orders (suit-blindness at cards i and j), so the middle card sees the same grip and turns the same faces;
* the held-face turns and the middle card's turns combine to the same group element in both orders (e.g. when they commute).

Then the position and grip after card j coincide, the remaining cards and the 12 F3 rounds are identical, and `dm(h, m) = dm(h, m')`. Distances 3 and 4 give 4- and 5-card local collisions, much more rarely. The swapped deal must still be the image of a 28-byte block (factoradic rank < 2^224); the script skips swaps where it is not, so every hit below is a real block.

Both messages have the same length, so the padding is the same, and a colliding block gives a `Hash` collision. The same holds for a swap in any full message block of a longer message: the rest of the chain is unchanged. So a colliding block inside a target is a second preimage of it.

These are local collisions of the kind the SPEC and STONES already record as existing ("L3 collisions exist"). What is new is that they occur at a practical rate in real blocks, from the standard IV and from reachable chaining values. The earlier small probes (§4: `exp_local_collisions.py`, `exp_corner_local.py`, `exp_related_blocks.py` (a)) were too small, or of the wrong shape, to see them: they used random cards, or adjacent swaps only.

Adjacent swaps (2-card, j = i + 1) never collided in any run: 0/119,824 from the IV, 0/59,595 from non-IV chaining values, 0/44,896 in the reviewer's run. This is evidence, not a proof. **M9 (no 2-card local collision) stays OPEN.**

### 3.3 Results

`logs/suit_blind_collision_full.log` has seed 99 and per-block seeds, so the results do not depend on the number of worker processes. Rates carry exact Poisson 95% intervals.

**From the IV** (40,000 random one-block messages):

| distance j − i | same-rank swaps tested | preserve `dm` (= `Hash` collisions) | rate (95% CI) |
|---|---|---|---|
| 1 (adjacent) | 119,824 | 0 | < 1/32,000 |
| 2 | 117,313 | **47** | **1/2,496** (1/1,877 – 1/3,397) |
| 3 | 114,778 | 7 | 1/16,397 (1/7,958 – 1/40,783) |
| 4 | 112,572 | 3 | 1/37,524 (1/12,840 – 1/181,957) |
| 5 | 110,625 | 0 | < 1/30,000 |
| 6 | 108,176 | 0 | < 1/29,000 |

**From a reachable non-IV chaining value** (20,000 random 2-block messages; the swap is in the second block): distance 1: 0/59,595; distance 2: **18/58,801 = 1/3,267** (1/2,067 – 1/5,512); distance 3: 8/57,563 = 1/7,195.

**Independent run by the reviewer:**
* distance 1: 0/44,896;
* distance 2: 15/44,002 = 1/2,933 (1/1,800 – 1/5,200);
* distance 3: 2/43,317;
* distance 4: 2/42,302;
* a same-rank pair chosen uniformly at any distance: about 1/39,000.

In that run too, all hits are real blocks, and several are at the IV.

**Summary.**
* **Two apart: about 1 in 2,800** (pooled 80/220,116; the three runs give 1/2,496, 1/3,267 and 1/2,933, with overlapping intervals).
* Every hit is re-verified as two distinct messages with equal `Hash`.
* Cost per collision:
  * testing distance 2 only from the IV: (117,313 + 40,000)/47 ≈ 2^11.7 compressions;
  * distances 2–3: (232,091 + 40,000)/54 ≈ 2^12.3;
  * distances 1–6 as run: 2^13.6.
* So ≈ 2^12–2^13 compressions, a few seconds of single-core Python per collision.
* Blocks with at least one colliding swap (distances 1–6): 57/40,000 = 1/702.

**The verified pair.** It is the first hit of the review's original seed-99 search. Its deals differ by swapping cards 5 and 7 (ids 46 and 47: Q♠ and Q♦ with suits named in CHaSeD order, id % 4 = 0 ♣, 1 ♥, 2 ♠, 3 ♦; their held face is Down):
```
M  = e132ebb03ed19b3949820c68d22d8b5004867c3c0ea79f44269e19fb
M' = e132ebd9724a3c582fca2e7f51a1a34dd82b8afcfcf71344269e19fb
Hash(M) = Hash(M') = 0084d6d1e0a4ddb231deb23ac0f4ead7b497eed17f997bfcefa7c34e82
```
* The grips after cards 5, 6 and 7 are (Up, Front) = (1, 0), (3, 9), (4, 3) in both orders, and the positions after card 7 are equal.
* `python3 suit_blind_collision.py` checks the pair. It exits non-zero if the digests differ, if the messages are equal, or if a KAT fails.
* `MegaDreifachV1.Security.SwapCollision.v_Hash_swap_collision` (§1.3) kernel-checks the same collision for the generated `v_Hash`.

### 3.4 What F5 changes, and what it does not

* **Collisions.** Full-hash collision resistance of v1 is broken in practice, at ≈ 2^12–2^13 compressions against the generic 2^113. The F3 estimate is superseded. The top-90-bit collision question is moot.
* **Second preimages: measured.**
  * Setup: random targets of L full 28-byte blocks (the padding adds one more block). Each block is tested for a same-rank swap at distance 2 or 3 that preserves `dm` from the block's own chaining value, and every found M′ is re-verified by hashing.

    | L | targets | second preimage found | first vulnerable block (median / max) | compressions per target (mean) |
    |---|---|---|---|---|
    | 1,000 (28 KB) | 100 | **65/100** | 371 / 980 | 4,346 |
    | 3,000 (84 KB) | 30 | **30/30** | 745 / 2,807 | 6,177 |

  * Per-block rate (vulnerable blocks / blocks tested): 1/980 and 1/904; about 1 in 900.
  * So a random target of L blocks has a second preimage found this way with probability ≈ 1 − (1 − 1/900)^L: about 67% at L = 1,000 (measured 65%) and 96% at L = 3,000 (measured 30/30).
  * The cost is at most ≈ 7 compressions per block scanned (1 for the chain plus ≈ 5.8 swap tests).
  * For short targets (a few blocks) this succeeds with probability ≈ L/900, and otherwise only the F4 estimate (~2^93–2^96) applies.
* **Preimages.** Not affected, as far as this analysis shows. F5 needs a known message whose block admits a colliding swap, and returns a *different* message with the *same* digest; it gives no way to reach a prescribed digest. The F4 estimate stands as an estimate.
* **Related-key distinguisher of E_m.** Take keys (blocks) m and m′ that differ by a same-rank two-apart swap. Then `E_m(h) = E_m′(h)` with probability ≈ 1/2,800 over random blocks, from the IV and from non-IV h; since `dm = h·E_m(h)`, equal `dm` means equal E_m. For an ideal cipher the probability is ≈ 2^−226. About 2^12 query pairs distinguish.
* **Pseudo-collisions (F2)** are unchanged.
* **Grip-rule redesign.** Cause B needs its own fix: every re-grip should depend on the suit. Under Recipe A, reading right after the held-face turn, before the noon and Front turns, removes the swap collisions (§3.5, in-tree). Reading edges as well as corners addresses cause A; that it leaves B in place is out-of-tree evidence (see "Causes" in §0).

### 3.5 Control: the same rule with the read before the noon turn (in-tree)

`suit_blind_collision.py --variant pre-noon` (log `logs/suit_blind_collision_pre_noon.log`, `--check --variant pre-noon`; ≈ 1 min on 8 cores). The variant changes one thing in the G2 step: the Recipe A corner (between the held face, its noon and the next neighbour, for the grip in force) is read right after the held-face turn (and the King spin); the noon and Front turns follow with the old grip, and then the grip becomes the remembered reading. F3 steps and everything else are unchanged. It is a control, not a proposed rule. Both rules are run on the same 12,000 random one-block messages from the IV (the first 12,000 blocks of the §3.3 search, seed 99) and the same same-rank swaps.

| | Recipe A (v1) | pre-noon read |
|---|---|---|
| suit-blind fraction (3,000 trials) | 0.715 | **0.000** (all 4 suits give 4 distinct grips) |
| distance 1 | 0/35,820 | 0/35,820 |
| distance 2 | **15/35,175** (1/2,345) | **0/35,175** (95% CI 0 to 1/9,535) |
| distance 3 | 1/34,597 | 0/34,597 |
| distance 4 | 1/33,898 | 0/33,898 |
| recorded pair (`e132…19fb`) | collides | does not collide |

What this shows: under Recipe A, the read position after the noon turn is what makes same-rank swaps collide; without it the grip always depends on the suit and no swap collided. What it does not show: rates below ≈ 1/9,500 per swap, chained (non-IV) blocks, or anything about other grip rules; the pre-noon variant is not claimed to be secure.

## 4. Attack results (reproducible scripts in this directory)

Only `md.py`, `exp_corner_driven.py`, `pseudo_collision.py`, `exp_related_blocks.py`, `exp_local_collisions.py`, `exp_corner_local.py` and `suit_blind_collision.py` run the real MegaDreifach functions (via `md.py`, checked against the v1 KATs). The other scripts use scaled edge groups H_n or a toy hash with the proved v1 structure; their results are the basis of the extrapolated estimates in §2. Every row is a committed log (`logs/<name>.log`, §7).

| script | what it checks | result |
|---|---|---|
| `md.py` | Python transliteration of the hash | **all 8 KATs, the IV digest and the group order match** |
| `exp_corner_driven.py` | F1: change only the edges of h | 200/200 identical face-turn words and corner outputs |
| `pseudo_collision.py` | F2 on the **real** compression function | **50/50** random (corner, block) pairs give distinct *legal* `h ≠ h'` with `dm(h,m) = dm(h',m)`. Example printed (block `ed69…440b`) |
| `exp_local_collisions.py`, `exp_corner_local.py` | small probe for 3-card local collisions (full state, resp. corners + grip): all 6 orderings of 3 *random* cards from 2,000 random mid-block states | 0 in 12,000 orderings each. **Too small to see the 3-card collisions of §3**: random cards rarely put a same-rank pair two apart, and such a pair collides only ≈ 1/2,800 |
| `suit_blind_collision.py` | F5 on the **real** hash (§3) | KATs 8/8; the recorded pair collides; suit-blind fraction 0.715; per-distance rates, second preimages (§3.3, §3.4). `--variant pre-noon`: the control of §3.5 (0.000; 0/139,490 swaps collide) |
| `exp_edge_tree.py`, `exp_edge_first_merge.py` | Joux edge tree vs ideal (scaled edge groups H_n) | first merge after 2^6.4 / 2^7.7 / 2^9.3 / 2^11.0 / 2^12.7 states for n = 6..10, vs ideal 2^8.0 … 2^16.2. The gain grows like √c(n), 2^1.6 → 2^3.5 |
| `exp_square_classes.py` | exact c(n) | c = 2, 7, 10, 21, 30, 54 for n = 3..8; c/p2(n) ≈ 0.3, giving c(30) ≈ 2^17.4 |
| `exp_square_fraction.py` | fraction of squares in H_n | 0.35 / 0.50 / 0.30 / 0.40 / 0.24 for n = 4..8. B_n criterion ≈ 0.126 at n = 30 |
| `toy_attacks.py coll` | full F3 attack on a toy (k-bit random corners, H_n edges) | k=20,n=6: 2^12.9 vs generic 2^16.7; k=24,n=7: 2^15.0 vs 2^20.6; k=28,n=8: 2^17.5 vs 2^24.6; k=32,n=8: 2^19.3 vs 2^26.6 (5/5 verified each) |
| `toy_attacks.py pre` | full F4 attack on a toy | k=16,n=6: 2^18.6 vs 2^29.5; k=16,n=7: 2^18.2 vs 2^33.3; k=20,n=7: 2^22.7 vs 2^37.3 (8/8 verified each; 6–7 last-block retries) |
| `exp_related_blocks.py` | related and degenerate blocks | (a) adjacent swaps of random cards: 0/1000 equal outputs; (b) single suit shifts: 0/1000; (c) E_m(h) = h in 0/1000; see note |

Notes on `exp_related_blocks.py`:
* (a) swaps *adjacent* cards of random rank. That is a 2-card change, the M9 shape, not the 3-card collisions that exist. Adjacent same-rank swaps also never collided in the large runs of §3.2, so this is consistent with M9 being open, and it does not contradict "3-card local collisions exist". It is far too small to say anything about rates.
* The total turn amount of every block word is the constant 246. This follows from the card→amount rule; it carries no information because every face turn is an even move in both factors.

**Not tested:** whole-puzzle rotation (conjugation) symmetry, i.e. whether `E_m(σhσ⁻¹)` relates to `σE_m(h)σ⁻¹`. The grip is reset to the identity at the start of each block, which probably breaks the symmetry after the first card, but this was not checked.

## 5. Effective security levels of v1 (plain language)

* **Compression function:** no collision resistance at all. A pseudo-collision is found instantly for any block (reduction proved in Lean; demo on the real function). The MD reduction is correct, but its hypothesis is false, so it proves nothing about the hash.
* **Hash collision (measured):** practical. About 2^12–2^13 compressions, a few seconds of Python, by swapping two same-rank cards two apart (F5). A concrete pair is verified by script and kernel-checked in Lean. The design target would be ~2^113.
* **Collision on the top 90 bits of the digest:** moot; any full collision is one.
* **Second preimage (measured for long targets):** practical for random targets of about 1,000 blocks (28 KB) or more: 65/100 at 1,000 blocks, 30/30 at 3,000, ≈ 2^12–2^12.6 compressions. For short targets only the F4 estimate of ~2^93–2^96 applies (plus ≈ L/900 odds via F5).
* **Preimage (estimate):** about 2^93–2^96, against a design target of ~2^226 (F4, extrapolated from toy runs; not run at full size). F5 does not change this.
* **Causes:** two separate flaws of v1 of the grip rule (see "Causes" in §0).
  * The grip is chosen from corner pieces only, while edges are only ever multiplied by corner-determined words (F1–F4).
  * The grip is read after the noon turn, so for most cards it ignores the suit (F5). Moving the read before the noon turn removes the swap collisions under Recipe A (§3.5, in-tree); that an edge-reading rule still has them is out-of-tree evidence.

## 6. Recommended next steps

1. **Fix the design (the grip rule is being redesigned). Both causes need a fix:**
   * **A:** make the grip choice depend on edges as well, or mix the full state into the control flow, e.g. derive the grip from a hash of the whole position.
   * **B:** make every re-grip depend on the card's suit, e.g. read right after the held-face turn, before the noon and Front turns.

   Then re-run `exp_corner_driven.py` and an adapted `suit_blind_collision.py`. Repair the rule-independent Lean files as listed in §1.5, and delete or restate `CornerDriven.lean` / `FreeStart.lean` / `SwapCollision.lean`.
2. Kernel-check one concrete pseudo-collision instance from `pseudo_collision.py` with `decide`. The IV-anchored collision is already kernel-checked (`SwapCollision.lean`), cheaply, because only 7-card prefixes are evaluated. A free-start pair needs whole blocks evaluated (about 25 s each), so it belongs in the heavy library, in a separate CI job. Do not run it alongside other builds; memory is limited.
3. Formalize the probabilistic half of the BRS bound. This needs a finite-probability library; Mathlib is not in this package.
4. Test rotation/conjugation symmetry. Measure the edge-root survival probability at n = 30 directly (implement B_n → H_n root counting) to tighten the 2^93–2^96 preimage estimate.
5. Existing roadmap items: M8/M9, Link 1, and the digest unrank (surjectivity; M3 proves injectivity only).

## 7. How to reproduce

From the repository root:
```
cd proofs/megadreifach/lean && lake build MegaDreifach          # incremental; do NOT build MegaDreifachHeavy concurrently
cd ../../.. && python3 proofs/doubledeal/check_axioms.py megadreifach
python3 proofs/doubledeal/security/checks/scan_sorry.py --root proofs/megadreifach/lean --exclude Generated
python3 proofs/megadreifach/security/logs.py --check                          # all other attack scripts vs logs/ (≈ 2.5 min)
python3 proofs/megadreifach/security/suit_blind_collision.py --check          # F5 quick run (≈ 10 s)
python3 proofs/megadreifach/security/suit_blind_collision.py --check --full   # F5 report-size runs (≈ 20 CPU-min; uses all cores)
python3 proofs/megadreifach/security/suit_blind_collision.py --check --variant pre-noon   # §3.5 control (≈ 4 CPU-min)
```
* The scripts need only Python 3 (standard library) and run from any directory.
* `md.py` reads the v1 KATs from `primitives/hash/megadreifach/kats/megaminx_hash_kats_v1.json` and exits non-zero on a mismatch; `tables.py` holds the E_m tables copied from `megadreifach.sudo`.
* Without `--check`, `logs.py` and `suit_blind_collision.py --log [--full | --variant pre-noon]` rewrite the logs (the `tools/gencheck.py` convention).
* CI runs `suit_blind_collision.py --check` in `proofs.yml` (megadreifach-lean). It runs `logs.py --check`, `suit_blind_collision.py --check --full` and `suit_blind_collision.py --check --variant pre-noon` in `proofs-heavy.yml` (megadreifach-attack-logs).
