# MegaDreifach hash: security review (reductions, proofs and cryptanalysis)

Subject: MegaDreifach as published (`primitives/hash/megadreifach/`), whose block map E_m uses **v1 of the grip rule**: Recipe A chooses grips by reading only corner cubies.
Lean package: `proofs/megadreifach/lean`, Lean v4.14.0. The Lean files are in `proofs/megadreifach/lean/MegaDreifach/Security/`; the scripts are in this directory (`proofs/megadreifach/security/`).
**Note: this package has no Mathlib. It is core Lean plus the repo's `audit` package.** Every proof below uses core Lean only.

**How to read this report.**
* **Proved** means a kernel-checked Lean theorem in the default library `MegaDreifach`, audited by `check_axioms.py megadreifach`.
* **Attack costs are estimates.** The costs of the collision and preimage attacks (F3, F4; §0, §2, §4) are paper estimates extrapolated from toy-scale runs (§3) under the stated assumptions. No attack was run at full size. No full-size collision, preimage or second preimage of `Hash` has been found.
* **The ideal-cipher bound does not apply.** §2 records the Black–Rogaway–Shrimpton ideal-cipher bounds only as the design target. E_m is shown not to be an ideal cipher (`emBlock_word` gives a 2-query distinguisher), so those bounds say nothing about MegaDreifach v1.
* **v1 versus rule-independent.** F1–F4 and the Lean files `CornerDriven.lean` and `FreeStart.lean` are results about v1 of the grip rule; they document why the rule is being redesigned. The MD reduction, the pad suffix-freeness, digest-encoding injectivity (`evenRank_inj` plus the parity invariant) and the ideal-model counting lemmas are independent of the grip rule (§1.5).

## 0. Summary

* **MD reduction, proved.** Take two different well-formed messages with the same digest. A computable function `extract` returns a collision of the compression step `dm(h, block) = h * E_block(h)`. The IV/length branch is proved impossible, because the padding has MD strengthening (a 64-bit bit length). The same holds for the generated `v_Hash`, via Link 2. A second-preimage version is also proved.
* **The reduction gives no security, because the compression function is broken (under v1). The structure is proved in Lean; the pseudo-collisions are demonstrated on the real function.**
  * **F1 (corner-driven).** For a fixed block, `E_m(h) = W * h`, where the word `W` depends only on the *corner* part of `h`.
    * The corner chain is therefore an independent 90.2-bit MD hash.
    * The top ~90.2 bits of the digest depend only on that chain.
  * **F2 (universal pseudo-collisions).** For every block and every corner value, there are distinct legal chaining values with the same `dm` output. Finding them takes 3 block encryptions. Lean proves the reduction to a squaring collision (`dmStep_pseudo_collision`); the existence of such pairs is a short paper argument (two edge involutions), checked by `pseudo_collision.py` on 50/50 random (corner, block) pairs.
* **Effective security of v1, estimated. Generic figures use |G| = 2^225.90.**

| goal | generic | this analysis (v1 grip rule) |
|---|---|---|
| free-start / pseudo-collision of `dm` | 2^113 | **instant** (reduction proved; demo on the real function) |
| collision on top ~90 digest bits | 2^45 (for 90 bits) | 2^45.1 (estimate: generic birthday on the corner chain) |
| full-hash collision | 2^113 | **estimate: ~2^51 compressions + ~2^59 edge-group operations** (conservative: 2^68) |
| preimage / second preimage | 2^226 | **estimate: ~2^93–2^96** compressions (2^90.2 × small retry factor) + 2^68 time/memory MitM |

The last three rows are estimates, and the last two are paper attacks. Only the toy-scale versions were run end to end (§3): every toy collision and preimage was checked by re-hashing, and the toy costs follow the predicted formulas. The full-size figures extrapolate those formulas (and, for F3/F4, the square-class, square-fraction and edge-tree trends measured for scaled edge groups with n ≤ 10 edges) to the real 30-edge group. They are not measurements.

## 1. What is proved in Lean

Files are in `proofs/megadreifach/lean/MegaDreifach/Security/`: 7 modules (~1600 lines) plus the aggregator `MegaDreifach/Security.lean`.
* The aggregator is imported by `MegaDreifach.lean`, so `lake build MegaDreifach` builds and checks everything.
* The repo gate `python3 proofs/doubledeal/check_axioms.py megadreifach` passes: *2364 theorems audited (the whole default library, Security included), all use only [Classical.choice, Quot.sound, propext], 0 failures*. The per-theorem axiom columns below are from that audit.
* There is no `sorry`, `admit` or `native_decide`, and no new axioms (`scan_sorry.py`).
* The heavy KAT library `MegaDreifachHeavy` is unchanged and was not rebuilt for this work.

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
| `evenRank_inj` | `evenRank` is injective on even permutations of `0..n-1` (open item M3) | all three |
| `isLegal_chainMsg` (Parity.lean) | Every chaining value reachable from the IV is a legal position: even cp/ep, co sum ≡ 0 mod 3, eo sum even (the open "parity invariant for DM outputs") | all three |
| `positionToBytes_inj_legal` / `_reachable` | The digest encoding is injective on legal, and hence all reachable, positions | all three |
| **`extract_collision_comp`** | `PadWf m1, PadWf m2, m1 ≠ m2, vhashAlg m1 = vhashAlg m2 ⇒ ∃ c, extract m1 m2 = some (Break.comp c) ∧ valid`: a compression collision, with the out branch ruled out | all three |
| **`extract_second_preimage_comp`** | Same, and the first side is `(chainPre (pad m) i, blockAt (pad m) i)` for some `i`, i.e. it sits on the target message's own chain | all three |
| **`v_Hash_collision_comp`** | Same statement for the generated `Megadreifach.v_Hash (embed m)`, via Link 2 (`v_Hash_refines`) | all three |
| `comp_collision_deals` | The collision lifts to deals and `Em.dmStep` | all three |

**Answer to the MD-strengthening question.** The padding appends the 8-byte big-endian bit length. The reduction therefore needs nothing beyond `8·|m| < 2^64`, which is part of `PadWf`, and the IV branch disappears. Without strengthening, `findR_collision_or_iv` shows that an IV preimage `dm(h,b) = IV` would also have to be allowed.

### 1.3 Structural weaknesses of v1, proved (`CornerDriven.lean`, `FreeStart.lean`)

These theorems are about v1 of the grip rule (Recipe A reads only corner cubies, `recipeA_sameCorners`). They document why the rule is being redesigned, and need not hold for a redesigned rule.

| theorem | content | axioms |
|---|---|---|
| `emBlock_word` | `SameCorners h h' ⇒ ∃ W, E_m(h) = W∘h ∧ E_m(h') = W∘h'`. The grips (Recipe A) read only corner stickers | propext, Quot.sound |
| `dmStep_word` | `dm(h,m) = h∘W∘h` with the same `W` for all `h` sharing corners | propext, Quot.sound |
| `corner_collision_extends` / `foldl_dmBlock_sameCorners` | A corner-only match propagates through any suffix | propext, Quot.sound |
| `digest_top_collision` | Same corners ⇒ `rank(digest) / edgeRadix` is equal: the top ≈ 90.2 bits of the digest depend only on the corner chain | all three |
| `dmStep_collision_of_sq` | Same `W` and `(hW)² = (h'W)² ⇒ dm(h,m) = dm(h',m)` | propext, Quot.sound |
| `dmStep_pseudo_collision` | For same corners there is a legal word `W` (a product of face moves) with that implication | all three |

### 1.4 Ideal-model combinatorics (`IdealCount.lean`)
| theorem | content |
|---|---|
| `injective_surjective_fin` | Pigeonhole: an injective map on `Fin n` is surjective |
| `compose_left_cancel`, `compose_right_cancel` | Cancellation in the position group |
| `dm_forward_bad_count` | For fixed `h`, at most \|Z\| cipher outputs `y` make `h∘y` land in a target set `Z` |
| `dm_inverse_bad_count` | For fixed `y`, at most \|Z\| keys `h` do |
| `reachable_rank_lt_group` | Every reachable digest rank is < \|G\|, so the leading digest byte is ≤ 0x03 |

These are the counting cores of the Black–Rogaway–Shrimpton Davies–Meyer bound. The probabilistic step is paper-only (§2), since no probability library is available without Mathlib. The bound itself does not apply to MegaDreifach v1 (§2).

### 1.5 Which results depend on the grip rule

A transitive scan of constant dependencies over every theorem in `MegaDreifach.Security` (119 declared; 145 with the equation lemmas Lean generates) finds 14 that use `recipeA_sameCorners` (the corner-only read). All 14 are in `CornerDriven.lean` and `FreeStart.lean`: `recipeA_sameCorners`, `wordInv_g2Step`, `wordInv_f3Step`, `wordInv_f3Iter`, `wordInv_foldl`, `emBlock_word`, `emBlock_is_leftMul`, `dmStep_word`, `dmStep_sameCorners`, `foldl_dmBlock_sameCorners`, `corner_collision_extends`, `digest_top_collision`, `emBlock_word_legal`, `dmStep_pseudo_collision`.

| file | grip rule | what needs repair if E_m changes |
|---|---|---|
| `MDGeneric.lean` | independent | nothing (generic in `dm`, `iv`) |
| `MDReduction.lean` | independent | `injPos_chR` (via `Link2.injPos_dmStep`, which unfolds `Em`); the pad lemmas (`pad_suffix_free`, `blocks_suffix_free`) and `extract_*` need nothing. The Link 2 refinement of the new sudo E_m is separate work |
| `Parity.lean` | independent | `word_g2Step`, `word_f3Iter`, `word_foldl_g2`, `word_emBlock` (and `CornerDriven.g2Step_fst`), which unfold the current `Em` steps. They go through again if each step still left-multiplies by face moves. `swC` / `swE` only if the face-move tables change |
| `DigestInj.lean` | independent | `evenRank_inj`, `positionToBytes_inj_legal`: nothing. `positionToBytes_inj_reachable`, `extract_*_comp`, `v_Hash_collision_comp`: only through `isLegal_chR` and `injPos_chR` |
| `IdealCount.lean` | independent | counting lemmas: nothing. `reachable_rank_lt_group`: through `injPos_chR` |
| `CornerDriven.lean` | **v1** | the weakness theorems are expected to fail for an edge-reading rule; delete or restate. The digest arithmetic (`rankPosition_split`, `edgeRank_lt`, `rankPosition_div`, `cornerRank_sameCorners`) does not depend on the rule |
| `FreeStart.lean` | **v1** | `emBlock_word_legal`, `dmStep_pseudo_collision`: delete or restate. `dmStep_collision_of_sq` is plain group algebra (it assumes a shared word) |

## 2. Argued on paper (with assumptions)

**Effective output size.**
* |G| = (20!/2)·3^19·(30!/2)·2^29 ≈ 2^225.90. The digest is 29 bytes (232 bits), but only ranks < |G| occur, and `isLegal_chainMsg` plus the injective encoding show every reachable value is a legal position. So n = 225.90 bits. The parity restrictions are already inside |G|; there is no further shrinkage.
* The group is a direct product of the corner part Gc (2^90.19) and the edge part Ge (2^135.71).
* Blocks: 28 bytes = 2^224 < 52!, and φ is injective (already proved). The first card of every deal is always one of the first 18 values; this is harmless.

**Ideal-cipher bounds (design target only; shown inapplicable below).** Assume E is an ideal cipher on G, i.e. an independent random permutation of G for each block. The standard BRS argument gives:
* Adv^coll(q) ≤ q(q+1)/|G|, which is about q²/2^225.9. Collision security is ≈ 2^112.9.
* Adv^pre(q) ≤ q/(|G|−q), which is about q/2^225.9. Preimage security is ≈ 2^225.

The per-query counting steps are `dm_forward_bad_count` and `dm_inverse_bad_count`; the averaging over the random permutation is paper math.

**The ideal-cipher bound is inapplicable to MegaDreifach v1: its assumption is false.**
* `emBlock_word` gives a 2-query distinguisher: two chaining values with the same corners and different edges are mapped by the same left multiplication, which an ideal cipher does with negligible probability.
* For a fixed block, `h ↦ W(h_c)·h` is a permutation of G only if `h_c ↦ W_c(h_c)·h_c` is a permutation of Gc. That was not established and has no reason to hold.

So the ideal-cipher numbers are only what the design could at best achieve. They are not a bound on MegaDreifach v1's security, and this report does not use them as one.

**F3, collision attack (paper estimate, confirmed at toy scale only).**
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
5. Total ≈ 2^93–2^96, against 2^226 generic. This works for second preimages too, since only the target digest is used.

**DM fixed points.** `dm(h,m) = h∘W∘h = h ⇔ W∘h = 1 ⇔ h = W⁻¹`. Because `W` depends on `h_c`, this is a corner fixed-point problem, `h_c = (W_c(h_c))⁻¹`, costing ~2^90. The edges are then forced: `h_e = W_e⁻¹`. This gives no advantage beyond F1/F4.

## 3. Attack results (reproducible scripts in this directory)

Only `md.py`, `exp_corner_driven.py`, `pseudo_collision.py` and `exp_related_blocks.py` run the real MegaDreifach functions (via `md.py`, checked against the published KATs). The other scripts use scaled edge groups H_n or a toy hash with the proved v1 structure; their results are the basis of the extrapolated estimates in §2 and §4.

| script | what it checks | result |
|---|---|---|
| `md.py` | Python transliteration of the hash | **all 8 KATs, the IV digest and the group order match** |
| `exp_corner_driven.py` | F1: change only the edges of h | 200/200 identical face-turn words and corner outputs |
| `pseudo_collision.py` | F2 on the **real** compression function | **50/50** random (corner, block) pairs give distinct *legal* `h ≠ h'` with `dm(h,m) = dm(h',m)`, 0.27 s total. Example printed (block `ed69…440b`) |
| `exp_local_collisions.py`, `exp_corner_local.py` | cheap 2–3-block local collisions | none found (5000 / 3000 / 2000 states) |
| `exp_edge_tree.py`, `exp_edge_first_merge.py` | Joux edge tree vs ideal (scaled edge groups H_n) | first merge after 2^6.4 / 2^7.7 / 2^9.3 / 2^11.0 / 2^12.7 states for n = 6..10, vs ideal 2^8.0 … 2^16.2. The gain grows like √c(n), 2^1.6 → 2^3.5 |
| `exp_square_classes.py` | exact c(n) | c = 2, 7, 10, 21, 30, 54 for n = 3..8; c/p2(n) ≈ 0.3, giving c(30) ≈ 2^17.4 |
| `exp_square_fraction.py` | fraction of squares in H_n | 0.35 / 0.50 / 0.30 / 0.40 / 0.24 for n = 4..8. B_n criterion ≈ 0.126 at n = 30 |
| `toy_attacks.py coll` | full F3 attack on a toy (k-bit random corners, H_n edges) | k=20,n=6: 2^12.9 vs generic 2^16.7; k=24,n=7: 2^15.0 vs 2^20.6; k=28,n=8: 2^17.5 vs 2^24.6; k=32,n=8: 2^19.3 vs 2^26.6 (5/5 verified each) |
| `toy_attacks.py pre` | full F4 attack on a toy | k=16,n=6: 2^18.6 vs 2^29.5; k=16,n=7: 2^18.2 vs 2^33.3; k=20,n=7: 2^22.7 vs 2^37.3 (8/8 verified each; 6–7 last-block retries) |
| `exp_related_blocks.py` | related and degenerate blocks | adjacent card swaps: 0/1000 equal outputs; single suit shifts: 0/1000; E_m(h) = h in 0/1000; see note |

Note on `exp_related_blocks.py`: the total turn amount of every block word is the constant 246. This follows from the card→amount rule; it carries no information because every face turn is an even move in both factors.

**Not tested:** whole-puzzle rotation (conjugation) symmetry, i.e. whether `E_m(σhσ⁻¹)` relates to `σE_m(h)σ⁻¹`. The grip is reset to the identity at the start of each block, which probably breaks the symmetry after the first card, but this was not checked.

## 4. Effective security levels of v1 (plain language)

* **Compression function:** no collision resistance at all. A pseudo-collision is found instantly for any block (reduction proved in Lean; demo on the real function). The MD reduction is correct, but its hypothesis is false, so it proves nothing about the hash.
* **Hash collision (estimate):** about 2^59 work (2^51 compressions + 2^59 cheap group operations); a conservative estimate is 2^68. The design target would be ~2^113.
* **Collision on the top 90 bits of the digest (estimate):** 2^45.
* **Preimage / second preimage (estimate):** about 2^93–2^96, against a design target of ~2^226.
* The three estimates are extrapolated from toy runs; none was run at full size.
* All of these follow from one design flaw in v1 of the grip rule: the round function's control flow (grip choice) reads only corner pieces, while edges are only ever multiplied by corner-determined words.

## 5. Recommended next steps

1. **Fix the design (the grip rule is being redesigned):** make Recipe A (grip choice) depend on edges as well, or mix the full state into the control flow, e.g. derive the grip from a hash of the whole position. Then re-run `exp_corner_driven.py`; F1–F4 should disappear. Repair the rule-independent Lean files as listed in §1.5, and delete or restate `CornerDriven.lean` / `FreeStart.lean`.
2. Kernel-check one concrete pseudo-collision instance from `pseudo_collision.py` in the heavy library, with `decide`, in a separate CI job. Do not run it alongside other builds; memory is limited.
3. Formalize the probabilistic half of the BRS bound. This needs a finite-probability library; Mathlib is not in this package.
4. Test rotation/conjugation symmetry. Measure the edge-root survival probability at n = 30 directly (implement B_n → H_n root counting) to tighten the 2^93–2^96 estimate.
5. Existing roadmap items: M8/M9 and Link 1.

## 6. How to reproduce

From the repository root:
```
cd proofs/megadreifach/lean && lake build MegaDreifach          # a few minutes; do NOT build MegaDreifachHeavy concurrently
cd ../../.. && python3 proofs/doubledeal/check_axioms.py megadreifach
python3 proofs/doubledeal/security/checks/scan_sorry.py --root proofs/megadreifach/lean --exclude Generated
cd proofs/megadreifach/security
python3 md.py; python3 pseudo_collision.py; python3 toy_attacks.py coll; python3 toy_attacks.py pre   # pre ≈ 1 min
```
The scripts need only Python 3 (standard library). They import `md.py` / `tables.py` from this directory and can also be run from elsewhere (`python3 proofs/megadreifach/security/md.py`). `md.py` reads the published KATs from `primitives/hash/megadreifach/kats/megaminx_hash_kats.json` and exits non-zero on a mismatch. `tables.py` holds the E_m tables copied from `megadreifach.sudo`.
