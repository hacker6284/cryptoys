# MegaDreifach

> **v1 is deprecated (broken)** and frozen at [`v1/`](v1/SPEC.md) (KATs: [`kats/megaminx_hash_kats_v1.json`](kats/megaminx_hash_kats_v1.json)). Why, with the #119 evidence: the banner of [`v1/SPEC.md`](v1/SPEC.md).

**This is MegaDreifach v2, the current version.** It is final in the sense that its definition and KATs (`kats/megaminx_hash_kats_v2.json`) are fixed; that is not a security claim (§8). One change from v1: the grip rule inside `E_m` (§5). Three parts:

1. **Visual noon** replaces the table noon everywhere (§5.2).
2. **Read at once, alternating.** The piece is read right after the held-face turn (King: after the Up counter-turn and the spin), before the noon and Front turns. Odd positions read the clockwise-noon **corner**, even positions the noon **edge** (§5.3).
3. **36 F3 rounds** (was 12): 3 × 12 faces, a deliberate nod to *drei*. The alternation continues through them (§5.4).

Pad, φ, card ids, the face-turn tables, chaining, Davies–Meyer, IV-COOK12 and the digest encoding are v1's, unchanged. All digests change (`kats/megaminx_hash_kats_v2.json`).

Naming. v2 is the grip rule called **C36** in the grip-rule review (2026-09-29, kept out of tree; its v2 scripts are ported into this repository, §8): the **v2 card rule** (visual noon, one piece read right after the held-face turn, corner/edge alternating; §5.2–§5.3) plus 36 F3 rounds. The review calls the v2 card rule with v1's 12 F3 rounds "A_vn"; this SPEC says "the v2 card rule with 12 F3 rounds" instead. Neither is v1's Recipe A (which reads a corner after all three turns, with the table noon). It is *not* the review's earlier rule also called "v2" (alternating, but read after all turns, with the table noon; review `megadreifach-v2/`), which the review found broken the same way as v1 (IV-anchored collisions at about 2^12.5–2^13; *out of tree*, not reproduced in this repository), nor its "v2e" (this rule with the table noon; the review's real IV-anchored `Hash` collision re-verifies in tree, §8). The evidence for v2 behind the choice is in [`proofs/megadreifach/security/v2/`](../../../proofs/megadreifach/security/v2/README.md) (§8).

This document is the normative specification. `megadreifach.sudo` is the conformance implementation. A mismatch is a bug in the implementation. MegaDreifach is a toy three-megaminx Merkle–Damgård hash. It makes no cryptographic security claim. It is not for protecting anything.

The product name **MegaDreifach** is locked. The puzzle, group, and library stay called **megaminx**.

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Use a keyed construction if you need to stop it. The in-tree keyed use is the **Sandwich MAC** of DoubleDeal-CBC-Sandwich v2 (`primitives/aead/doubledeal-cbc-hmac/`, not a second hash): `HashDecksBody` over the key deck, the message decks and the key deck turned over. Its security argument needs this compression to be a PRF keyed through the data block with the chaining value chosen by the adversary, which the free-start weakness of §8 refutes; see that SPEC's §8. The frozen DoubleDeal-CBC-HMAC v1 (`primitives/aead/doubledeal-cbc-hmac/v1/`) used HMAC-MegaDreifach (standard HMAC with this `Hash`, \(B=28\)); its vectors were regenerated when this v2 became current. A green Lean build is not a security claim. What the Lean covers: §7. Hand-written Lean is not a proof that the sudo text equals the Lean model.

---

# 1. Scope and non-goals

## In scope

- A general byte hash `Hash` / `MegaDreifach`.
- `HashDeck` / `MegaDreifachDeck`: `Hash(φ⁻¹(deal))` when the deal is in the image of φ.
- `HashDeckBody` / `MegaDreifachBody`: one Davies–Meyer compression on a required 52-card permutation, from IV-COOK12.
- `HashDecksBody`: the Davies–Meyer cascade of that compression over a non-empty list of 52-card permutations, from IV-COOK12 (no pad, no φ).
- `HashDeckBodyFrom` / `MegaDreifachBodyFrom`: the same compression from a caller chaining value (free-start analysis surface; broken).
- Pad B=28, factoradic φ, v2 abs-G2 + F3 t=36, IV-COOK12, 29-byte digest rank.
- A hand procedure that a person can run from the puzzle alone: no sheet, no lookup table, no colour-to-number arithmetic (§5).

## Non-goals

- No collision resistance, preimage resistance, or ideal-cipher-on-G claim.
- No AES-class numbers. Birthday ≈ 2^113 is honesty about `|G| ≈ 2^{225.9}`, not a theorem.
- No proof that mid-block local collisions are absent, beyond one narrow case: 2-card windows at the same deal positions, from an `InjPos` position on a `GripOk` grip (§7, Lean coverage, gives the exact hypotheses). Longer windows and block-level collisions are open. Free-start `HashDeckBodyFrom` is broken (§8).
- Relative reorient recipes are rejected (research disproof). Absolute re-grip only.
- No claim that Lean equals this sudo text. That is a future emitter proof.
- A keyed use (the Sandwich MAC, or v1's HMAC-MegaDreifach) does not make `Hash` collision-resistant, and inherits this toy compression.

---

# 2. Public API

| Function | Meaning |
| --- | --- |
| `Hash(msg)` / `MegaDreifach(msg)` | Byte hash. The only public message domain. |
| `HashDeck(deal)` / `MegaDreifachDeck(deal)` | `Hash(φ⁻¹(deal))` when the deal’s factoradic rank is `< 2^{224}`. Often two MD blocks after the outer pad. |
| `HashDeckBody(deal)` / `MegaDreifachBody(deal)` | Public Body. One DM compression on a **52-card permutation** from **IV-COOK12**. No outer pad, no φ. Non-permutations are rejected. |
| `HashDecksBody(deals)` | The DM cascade of `HashDeckBody`'s compression over a non-empty list of **52-card permutations**, from **IV-COOK12**: `h ← DM(h, deal)` for each deal, then the digest. No outer pad, no φ, no length. Non-permutations and the empty list are rejected. `HashDecksBody([d])` = `HashDeckBody(d)`. The block interface of the Sandwich MAC. |
| `HashDeckBodyFrom(deal, h)` / `MegaDreifachBodyFrom(deal, h)` | Free-start analysis surface. Same DM from caller chaining value `h`. **Broken** (pseudo-collisions are easy, §8). Not a security API. |

Sudocode has no optional parameters, so the soft-lock prose `HashDeckBody(deal[, h])` splits: omit `h` → `HashDeckBody(deal)` (always IV-COOK12); supply `h` → `HashDeckBodyFrom(deal, h)`. Identically, `HashDeckBody(deal)` is `HashDeckBodyFrom(deal, IV-COOK12)`.

Cards appear after φ, or as deal bodies for `HashDeckBody` / `HashDecksBody`. There is no arbitrary-card public message API. The API is v1's plus `HashDecksBody`, added for the Sandwich MAC of DoubleDeal-CBC-Sandwich v2; it changes no digest (v1 called the Body "Public v1 Body"; that "v1" named the API, not this version).

---

# 3. Parameters (locked)

| Item | Value |
| --- | --- |
| Version | **v2** (current). v1 deprecated (broken), frozen at `v1/` |
| Pad | SHA-2-style **B=28**: `M ‖ 0x80 ‖ 0x00^z ‖ 8-byte BE bit length` |
| φ | Each 28-byte chunk → BE integer `n < 2^{224} < 52!` → Lehmer unrank → 52-card deal |
| Card ids | `0..51` → `(rank = id // 4, suit = id % 4)`. Amount `k = suit + 1 ∈ {1,2,3,4}`. Ranks 0–12 are A, 2, …, 10, J, Q, K. Suits are named in **CHaSeD** order: 0 = Clubs ♣, 1 = Hearts ♥, 2 = Spades ♠, 3 = Diamonds ♦, so `k` is ♣ 1, ♥ 2, ♠ 3, ♦ 4 (e.g. id 46 = Q♠, id 47 = Q♦). The names are new in v2's text (v1 left suits unnamed); they change no digest |
| E_m | v2 abs-G2 (§5): turn the held face `+k` (**King = king_up**: `−k` on Up, then spin the grip `+k`); **read at once**, odd position corner / even position edge, at the **visual noon**; noon+1; Front+1; absolute re-grip. Body = 52. **F3 t = 36**, alternation continued |
| Chaining | Final position `g` only. Discard grip `o` after each block |
| IV | **IV-COOK12**: from solved, faces `0..11` each +1 CW (unchanged; it does not use `E_m`) |
| DM | `h' = compose(h, E_m(h))` (3-solve hand) |
| Digest | `position_to_bytes(g)` → **29 bytes**. Intended as a bijection legal G ↔ `[0, \|G\|)`; only injectivity is proved (M3); surjectivity / unrank is OPEN |

`z = (28 − ( |M| + 1 + 8 ) mod 28) mod 28`. Bit length is `8 · |M|`.

---

# 4. The megaminx group

Fixed centres. A **position** is corner permutation and orientation (`cp[20]`, `co[20]` with `co[i] ∈ {0,1,2}`) plus edge permutation and orientation (`ep[30]`, `eo[30]` with `eo[i] ∈ {0,1}`).

Legal (reachable) positions:

- `cp` and `ep` are even permutations
- `∑ co ≡ 0 (mod 3)`
- `∑ eo ≡ 0 (mod 2)`

`compose(g, h)` applies `h` first, then `g` (function composition / left action):

\[
\begin{aligned}
\mathrm{cp}[s] &= h.\mathrm{cp}[g.\mathrm{cp}[s]], \\
\mathrm{co}[s] &= (h.\mathrm{co}[g.\mathrm{cp}[s]] + g.\mathrm{co}[s]) \bmod 3,
\end{aligned}
\]

and the same shape for edges with `mod 2`. Face turns are 72° clockwise looking at the face from outside. They act by left multiplication.

Face adjacency (CW from outside), opposites, the 20 corner triples and the 60 grips are the tables in `megadreifach.sudo` (unchanged from v1). v2 adds one table of **software data**, the 30 edge slots (`edge_faces_flat`, §5.6). No step of the hand procedure needs any table.

Colours are the centre ids `0..11`: a sticker's colour is the id of the centre it matches. A grip `o` lists which physical face is held in each of the 12 hold positions (0 = Up, 1 = Front, 2–5 = the rest of the upper ring, 6–10 = the lower ring, 11 = Down); the identity grip is the **home grip**, in which the face with centre `i` is at hold position `i`.

---

# 5. Compression

1. φ(chunk) → a 52-card deal.
2. `e ← E_m(h)`: start at position `h` in the home grip. Run one card step per card (§5.3), then 36 F3 rounds (§5.4). Discard the grip.
3. `h ← compose(h, e)`.
4. After the last block, the digest is the 29-byte rank of `h`.

Merkle–Damgård: `h₀ = IV-COOK12`; for each chunk `hᵢ = DM(hᵢ₋₁, mᵢ)`.

§5.1–§5.4 are the hand procedure, written so that it can be done from the puzzle alone. §5.5 states the same rule in grip terms for software; §5.6 is software data. If they ever disagree, §5.5 and the sudo are normative and the prose is a bug.

## 5.1 Words

- **Up** is the face on top, **Front** the face toward you. The **upper ring** is the five faces around Up; the **lower ring** is the five faces around Down. **Down** is the bottom face.
- **Home grip**: centre 0 on Up and centre 1 on Front. Every block starts in the home grip.
- A **click** is one fifth of a turn. **Turn X +n** means turn face X by n clicks clockwise, looking straight at X from outside. Up `−k` means k clicks counter-clockwise seen from above.
- **Held face** of a card, in the grip you are holding:
  - A: Up. 2: Front.
  - 3, 4, 5, 6: the other four upper-ring faces, going clockwise seen from above, starting with the face to the left of Front (3 = left of Front, 6 = right of Front).
  - 7, 8, 9, 10, J: the lower-ring faces, going clockwise seen from above, starting with the face below and to the right of Front (7 = below-right of Front, 8 = below-left of Front).
  - Q: Down.
  - K: see the King step (§5.3).
- **k**, the number of clicks, comes from the suit. The suits go in the order of the capital letters of **CHaSeD**: **C**lubs 1, **H**earts 2, **S**pades 3, **D**iamonds 4. (This is `k = suit + 1` of §3.)
- **Re-grip c1/c2**: turn the whole puzzle so that centre c1 is on top, then spin it about the vertical axis until centre c2 faces you. This is always possible: the two colours of a piece are always neighbouring centres.

## 5.2 Visual noon

The **noon** of a face is the neighbouring face it points to:

- **Up** points toward **Front**.
- An **upper-ring face** points toward **Up**.
- A **lower-ring face** points toward its **upper-left neighbour**, looking straight at it with Up on top.
- **Down** points toward the lower-ring face **below and to the right of Front** (the rank-7 face).

The **noon edge** is the edge the face shares with its noon. The **noon corner** (clockwise-noon corner) is the corner at the clockwise end of the noon edge: looking straight at the face with its noon edge at the top, the right-hand end. Spelled out (the same rule, not a table):

| Face | Noon corner | Noon edge |
| --- | --- | --- |
| Up | where Up, Front and the face left of Front meet | Up–Front |
| upper-ring face | its top-right corner (Up on top) | its top edge |
| lower-ring face | its top point | its upper-left edge |
| Down | where Down, the rank-7 face and the lower-ring face to its right meet (the rank-7 face's bottom-right corner) | Down–rank-7 face |

**Reading** the noon piece: **c1** is the colour of its sticker on the face you just turned; **c2** the colour of its sticker on the noon face.

## 5.3 Card step (card number i = 1 … 52)

1. **Turn** the held face **+k**.
   **King (king_up):** turn Up **−k**, then spin the whole puzzle k clicks about the Up–Down axis, each click bringing the face on your left round to the front. Up is now the held face.
2. **Read at once**, before any other turn, the held face's noon piece: for **odd i the noon corner**, for **even i the noon edge**. Remember c1 and c2.
3. **Turn the noon face +1.**
4. **Turn Front +1** (the Front you are holding now; for a King, the Front after the spin).
5. **Re-grip c1/c2.**

When the noon face is Front (card A, card 7, and every King) Front gets +1 twice, so +2 in total. When the held face is Front (card 2) the noon is Up, so step 3 turns Up and step 4 turns the held face again.

The corner/edge choice depends only on the card's position i in the deal, never on the card or the state.

## 5.4 F3 blank rounds (t = 36, round r = 1 … 36)

1. **Turn Up +1.**
2. **Read** Up's noon piece (Up's noon is Front): for **odd r the noon corner** (Up, Front, left of Front), for **even r the Up–Front edge**. c1 is on Up, c2 on Front.
3. **Re-grip c1/c2.**

The alternation simply continues from the deal (52 is even, so round r is position 52 + r). Keep a tally for the 36 rounds, for example three passes of twelve counters.

## 5.5 Software form (normative, equal to §5.1–§5.4)

The grip is `o` (hold position → physical face). `held_up = 0`, `held_front = 1`. `face_nbrs(f)` lists `f`'s five neighbours clockwise from outside.

- **Held face.** Non-King (`rank < 12`): `phys = o[rank]`; turn `phys` by `k`. King: turn `o[0]` by `5 − k`; `o ← spin_about_up(o, k)`; `phys = o[0]`.
- **Visual noon** of `phys = o[p]`: `p = 0` → `o[1]`; `1 ≤ p ≤ 5` → `o[0]`; `6 ≤ p ≤ 10` → `o[p − 5]`; `p = 11` → `o[6]`.
- **Read** with the grip then in force, on the position right after the held-face turn: odd `pos` reads the corner `{phys, noon, next}` where `next` follows `noon` in `face_nbrs(phys)`; even `pos` reads the edge `{phys, noon}`. `c1` = colour on `phys`, `c2` = colour on `noon`. New grip = `abs_reorient(c1, c2)`, the unique rotation with `o[0] = c1`, `o[1] = c2`.
- Then turn `noon` by 1 and `o[1]` by 1 (same grip), and install the new grip.
- **F3 round r**: turn `o[0]` by 1; read at `phys = o[0]`, `noon = o[1]`, parity of `r`; install the new grip.

v1 differed in exactly three places: its noon was the table noon (`noon_phys`: Front for Up; Up for faces touching Up; otherwise the first neighbour in `face_nbrs` order that touches Up, or `face_nbrs[0]` for Down); it read the corner at every position, after all three turns; and `f3_t = 12`.

## 5.6 Edge slots (software data only)

Edge slot `s` lies between the two faces `edge_faces(s)` below; the first is its reference face. `eo[s] = 0` iff the piece's reference colour (its lower-numbered colour) is on the slot's reference face. The table is derived from the unchanged v1 face-turn tables: each slot is moved by exactly its two faces, and a face turn keeps the turned face's colour on that face; the sudo tests check both. A person never uses this table: on the puzzle you simply look at the stickers.

| s | faces | s | faces | s | faces | s | faces | s | faces | s | faces |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 0,1 | 5 | 1,5 | 10 | 2,8 | 15 | 4,9 | 20 | 6,10 | 25 | 8,11 |
| 1 | 0,2 | 6 | 1,6 | 11 | 2,3 | 16 | 4,10 | 21 | 6,11 | 26 | 8,9 |
| 2 | 0,3 | 7 | 1,7 | 12 | 3,8 | 17 | 4,5 | 22 | 6,7 | 27 | 9,11 |
| 3 | 0,4 | 8 | 1,2 | 13 | 3,9 | 18 | 5,10 | 23 | 7,11 | 28 | 9,10 |
| 4 | 0,5 | 9 | 2,7 | 14 | 3,4 | 19 | 5,6 | 24 | 7,8 | 29 | 10,11 |

## 5.7 Hand details unchanged from v1

**IV-COOK12 by hand.** From solved, in the home grip, turn each face +1 once, in card order A, 2, 3, …, Q (Up, Front, the upper ring, the lower ring, Down). No re-grip.

**3-solve hand (informal).** Between blocks, puzzles `(A,B,C) = (h, h⁻¹, id)`. Run E_m on A; solve B onto A; solve A onto B and C; solve C onto A. Software is `compose(h, e)`.

**Cost per block** (v1 → v2): 168 → 192 face turns (246 → 270 clicks), 64 → 88 pieces read, 64 → 88 whole-puzzle re-grips. These are exact for every block, since every deal holds each card once ([`cost.log`](../../../proofs/megadreifach/security/v2/logs/cost.log)).

---

# 6. Digest encoding

`position_to_bytes` is the 29-byte big-endian mixed-radix rank:

`even cp (20!/2) | co[0..18] (3^19) | even ep (30!/2) | eo[0..28] (2^29)`.

Last orientations are completed by the parity rules. Parse rejects integers `≥ |G|`. Encoding is injective on legal positions. It is not surjective onto `{0,1}^{232}`.

A sudocode `int` is 64-bit and overflow traps. `|G|` and `52!` do not fit. `std.bigint` cannot cross a module boundary; the conformance file pastes the limb arithmetic it needs (same limitation DoubleDeal records for 52-card ranks).

---

# 7. Test vectors

`kats/megaminx_hash_kats_v2.json` holds the **v2** vectors: the same inputs and layout as the v1 file, with `"version": "v2"` and `f3_t = 36`. The pad lengths, block counts, IV-COOK12 digest and `|G|` are unchanged; every digest differs from v1. They were produced by an independent Python transliteration of the sudo and agree with the sudoc JS build of `megadreifach.sudo` and with the review engine's rule C36 (both Python programs are out of tree). In tree, the engine of [`proofs/megadreifach/security/v2/`](../../../proofs/megadreifach/security/v2/README.md) reproduces all eight digests and the `HashDeck` vector, and `proofs/megadreifach/m9/m9_search.py` the eight digests.

The sudo tests assert pad lengths, block counts, the IV-COOK12 digest, φ on zero, the permutation domain, the public API, the edge-slot table (§5.6), the visual noon on all 60 grips, and **all eight v2 `Hash` digests plus the `HashDeck` vector** of that file.

`kats/megaminx_hash_kats_v1.json` is the **v1** KAT file (for the deprecated `v1/megadreifach.sudo`), renamed from `kats/megaminx_hash_kats.json` with identical contents.

**Lean coverage.** The Lean proof package [`proofs/megadreifach/`](../../../proofs/megadreifach/README.md) models **v2**: its `Generated/` is emitted from this `megadreifach.sudo` (`proofs/emit_lean.sh` target `megadreifach`), and its model (`Em.lean`), Link 2 and `Security/` are about v2. Proved there, sorry-free and axiom-audited: the emitted `Hash` equals the algebraic Merkle–Damgård fold of the typed E_m transliteration on well-formed messages (`v_Hash_refines`; this includes visual noon on all 60 grips, the edge and corner reads and 36 F3 rounds), and all eight v2 `Hash` digests of `kats/megaminx_hash_kats_v2.json` as kernel-checked theorems about the emitted `v_Hash`. Also proved there: the emitted `HashDeck` equals `Hash` of the deal's 28-byte Lehmer rank on permutations (`v_HashDeck_refines`); the 60×52 v2 one-card nets are pairwise distinct per grip, so from an `InjPos` position, on a `GripOk` grip, at the same deal position, one card step is injective in the card for cards `< 52` (M8, `nets_nodup`, `net2_ne`, `g2Step_ne`); and from an `InjPos` position, on a `GripOk` grip, at the same deal positions (any two, so both read parities), two different 2-card windows of cards `< 52` never reach the same state (M9 for 2-card windows, `twoCard_ne`: the same-first-card half `twoCard_same_first_ne`, and the different-first-card half `twoCard_diff_first_ne`, by rotation covariance of the card step, `g2Step_cov`, and a kernel-checked decoder certificate at the identity grip, `m9_canon`; proof route and costs in [`proofs/megadreifach/m9/`](../../../proofs/megadreifach/m9/README.md)). This is local to 2-card windows: it says nothing about longer windows or block-level collisions. The package also has correctness and grip-rule-independent lemmas. **No Lean theorem is a security claim about v2**, and that the sudo text equals the emitted Lean (the emitter) is trusted, not proved; the ledger (what is proved, what is open) is that README. The v1 weakness proofs are kept, frozen and about v1 only, in [`proofs/deprecated/megadreifach-v1/`](../../../proofs/deprecated/megadreifach-v1/README.md).

---

# 8. Security status

Nothing here is a security claim. "Tested" means a structured search found nothing at the stated detection threshold; it does not mean secure. Evidence: [`proofs/megadreifach/security/v2/`](../../../proofs/megadreifach/security/v2/README.md), the grip-rule review's scripts ported and re-run from its seeds, with logs checked in CI (which log backs each statement: that README). Every v2 number below is re-run there unless it is marked *out of tree*.

**Known to be easy (v2 does not fix this).**

- **Free-start / pseudo-collisions** of the compression function. For a fixed block, `E_m(h) = W·h` where the face-turn word `W` depends only on the pieces the block reads. A C36 block reads 88 pieces and leaves on average 2.08 ± 0.02 corners and 6.71 ± 0.03 edges unread (mean ± standard error over 3,000 blocks from uniform random `h`), and changing unread pieces never changes `W` (3000/3000 re-randomisations). A "same read class" recipe (flip two unread edges, arranged so that the flip commutes with `h·W`) gives distinct legal `h ≠ h'` with equal `dm` output about once per 2 `(h, m)` draws (711/1500, 95% CI 45–50%; 20 of 40 draws in a second run, every pair re-verified with the slow reference in [`engine.py`](../../../proofs/megadreifach/security/v2/engine.py), built on m9_search's Em.lean transliteration; it shares the fast engine's tables and read primitives, so it is not an independent check, see [Limits of the self-check](../../../proofs/megadreifach/security/v2/README.md#limits-of-the-self-check)), and a 2-edge flip of `h` alone leaves `W` unchanged 143/3000 times. `HashDeckBodyFrom` is broken.
- For comparison, the review's rule C76 (the v2 card rule with 76 F3 rounds) reads more (on average 0.75 corners and 3.40 edges unread per block) and has fewer such pseudo-collisions (125/1500 = 8.3% of draws, 95% CI 7.0–9.8%, against C36's 47%), at 232 face turns and 128 pieces read per block against C36's 192 and 88 (1.21× and 1.45×; against v1's 168 and 64, 1.38× and 2×). The C76 engine has no KAT and no review digest prefix: it is anchored only by agreeing with the slow reference and by reproducing every coverage statistic the review printed for it ([Limits of the self-check](../../../proofs/megadreifach/security/v2/README.md#limits-of-the-self-check)). v2 is C36 by the designer's choice.

**Untested beyond structured searches.** The status of IV-anchored collisions, second preimages and preimages of v2 is **empirically untested** beyond these structured searches (one block from IV-COOK12 unless stated, 95% one-sided upper bounds when 0 hits):

| Test | Trials | Hits | Rate would have been seen above |
| --- | --- | --- | --- |
| same-rank swap at distance 1, 2, 3, 4 (1.2M messages) | 3.60M, 3.53M, 3.46M, 3.38M | 0 | 1/1.20M, 1/1.18M, 1/1.15M, 1/1.13M |
| same-rank swap at a random distance ≥ 5 | 1.20M | 0 | 1/399k |
| different-rank swap at distance 1, 2 | 1.18M each | 0 | 1/395k |
| suit change alone (the changed deal is not a permutation, so this probes `E_m` outside the `Hash` domain) | 1.20M | 0 | 1/401k |
| local reorderings of 2, 3, 4 random or rank-structured cards, mid-block from a uniform random state and grip (not from the IV) | 0.3M, 1.5M, 6.9M ordering pairs for k = 2, 3, 4, for random and for rank-structured cards each | 0 | 1/100k, 1/501k, 1/2.30M per pair |
| window reorderings (k = 2, 3, 4) in IV blocks | 240k each | 0 | 1/80k |
| 32-bit truncated birthday (200k messages) | — | 6 | expected 4.7 (exact Poisson 95% range 1–9) |

On the blocks and swaps of the v1 measurement (40,000 IV blocks, every same-rank swap at distance 1–6; v1: 47 of 117,313 swaps collide at distance 2, 57 of 683,288 in all), v2 has 0 hits in all 683,288.

Card-phase tests run on the v2 card rule with 12 F3 rounds, whose 52 card steps are identical to v2's (v2 only adds F3 rounds after them, and a card-phase collision survives any F3 tail): telescoping card pairs (A♠K♥, A♥K♠, A♠7♠) 0/2.0M (1/668k); a T card next to a same-rank swap at distance 2 or 3, 0/1.0M each (1/334k each); exact count, over all grips, cards and read parities, of pairs of different grips that make identical turns and read the same slot, 0. These 12-round tests do not rule out collisions that would first arise in C36's extra 24 F3 rounds (states that differ after the card phase and merge later). (The review's table-noon variant of the same card rule, which it calls "A" or "v2e", has 192 such cases, all rank T, and the same targeted search finds real IV-anchored `Hash` collisions: 3 in 999,873 trials at distance 2, about 1 per 333,000 ≈ 2^18.3 trials (exact Clopper–Pearson 95% CI [6.2e-7, 8.8e-6] per trial, about 2^16.8–2^20.6 trials per collision; the log prints the Wilson interval [1.0e-6, 8.8e-6]); the collision the review found first, a same-rank swap at distance 3, also re-verifies. Visual noon removes that mechanism.) Suit dependence: another suit of the same card never gives the same grip, from any state. For every grip, read parity and rank, the four suits bring pieces from four different slots to the read slot, and the read piece fixes the grip one-to-one (exhaustive check; the review's sampled test T3 also gives 0).

What these do **not** cover: no second-preimage or preimage search was run on the real v2 at all (only the review's toy models, which were generic; *out of tree*, not reproduced here); no swap search from non-IV chaining values; no multi-block, longer telescoping-word (3+ cards), King-spin or puzzle-automorphism attacks; no rates below the thresholds above (about 2^16–2^21 structured trials). There are no human trials of error rates. The searches are the review's own, re-run in tree from its seeds (except the v1-blocks run and the exhaustive suit check, which are new): that checks its numbers, it is not an independent choice of tests.

**v1, for comparison** (PR #119): IV-anchored collisions ≈2^12–2^13 (measured), long-target second preimages practical (measured), preimage ≈2^93–2^96 (estimate).

# 9. What this does not claim

- Ideal-cipher-on-G / PRF of `E_m`
- Collision resistance of `Hash`
- IV-anchored collision resistance (for v2: empirically untested beyond §8; for v1: false, collisions from the standard IV are practical via same-rank card swaps, see `proofs/megadreifach/security/suit_blind_collision.py` and §3 of `REPORT.md` there)
- Second-preimage or preimage resistance (for v2: untested)
- Absence of local collisions (v1: L3 collisions exist and occur at a practical rate in real blocks; v2: not claimed beyond the same-first-card 2-card case in §7, and free-start pseudo-collisions are easy, §8)
- Birthday ≈ 2^113 as a theorem
- PRESSURE.md tables as theorems
- Lean model = this sudo text (the emitter is trusted), or any Lean security result about v2 (§7)
