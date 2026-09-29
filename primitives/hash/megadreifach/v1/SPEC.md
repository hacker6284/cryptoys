# MegaDreifach v1 (deprecated, broken, frozen)

> **Deprecated and broken.** This is the frozen v1 specification. It is kept verbatim below this banner so the published v1 vectors (`../kats/megaminx_hash_kats_v1.json`, formerly `kats/megaminx_hash_kats.json`) and the write-ups keep a fixed target. Do not change its behavior. The current version is v2 (`../SPEC.md`, `../megadreifach.sudo`, KATs `../kats/megaminx_hash_kats_v2.json`).
>
> **Why deprecated.** The v1 grip rule (Recipe A: read the clockwise-noon corner *after* the held-face, noon and Front turns, with the table noon; 12 F3 rounds) has two separate flaws, both documented in PR #119 (merged; `proofs/megadreifach/security/REPORT.md`):
>
> * **The read comes after the noon turn** (cause B). For about 71.5% of cards the new grip ignores the suit, so swapping two same-rank cards two apart is a 3-card local collision about once in 2,800 tries. That gives **practical IV-anchored `Hash` collisions at about 2^12–2^13 compressions** (measured; one pair is kernel-checked against the generated `v_Hash`, `SwapCollision.v_Hash_swap_collision`) and practical second preimages of long targets (65/100 random 1,000-block targets). Report §3.
> * **The read sees only corners** (cause A). `E_m(h) = W·h` with `W` a function of the corner part of `h` alone (`emBlock_word`, proved), so the top ≈90.2 digest bits depend only on a corner chain, and the compression function has pseudo-collisions for every block (reduction proved, pairs demonstrated). Preimage and short-target second preimage are estimated at ≈2^93–2^96 (paper, toy-scale runs). Report §1.3, §2.
>
> In addition, the *table noon* below ("the first neighbour in table order") cannot be performed from the puzzle alone: for lower-ring faces it matches a visual rule in only 48 of the 60 grips, and for Down it can be any of 5 faces. v2 replaces it with a visual noon.
>
> The conformance implementation for this frozen text is `megadreifach.sudo` next to this file (`v1/megadreifach.sudo`; it keeps the v1 file name so that the Lean emitted from it is still the module `Megadreifach`). It differs from the last v1 `megadreifach.sudo` on main (bbc26cb) only in comment lines 1 and 6. Relative links in the body below point at the v1-era tree (`megadreifach.sudo` there means `v1/megadreifach.sudo` here; `kats/megaminx_hash_kats.json` there is the v1 KAT file, now renamed `kats/megaminx_hash_kats_v1.json` with identical contents). The body below is the v1 SPEC as of main bbc26cb (after PR #119), verbatim.
>
> **Lean.** The Lean proof package `proofs/megadreifach/` is pinned to this v1: its `Generated/` is emitted from `v1/megadreifach.sudo`, and its vectors are the v1 KATs. Its proofs are about v1, not v2.
>
> **Suit names.** The v1 text numbers suits (`suit = id % 4`) but never names them. The repository now names them in **CHaSeD** order for both versions: 0 = Clubs ♣, 1 = Hearts ♥, 2 = Spades ♠, 3 = Diamonds ♦ (turn amounts 1, 2, 3, 4). This is a naming only; no v1 digest or behaviour depends on it.

---

# MegaDreifach

This document is the normative specification. `megadreifach.sudo` is the conformance implementation. A mismatch is a bug in the implementation. MegaDreifach is a toy three-megaminx Merkle–Damgård hash. It makes no cryptographic security claim. It is not for protecting anything.

The product name **MegaDreifach** is locked. The puzzle, group, and library stay called **megaminx**.

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Use a keyed construction if you need to stop it. **HMAC-MegaDreifach** is that construction: standard HMAC with this `Hash`, block size \(B=28\), tag = the 29-byte digest. It lives in `primitives/aead/doubledeal-cbc-hmac/` as part of DoubleDeal-CBC-HMAC (not a second hash). A green Lean build is not a security claim. Hand-written Lean is not a proof that the sudo text equals the Lean model.

---

# 1. Scope and non-goals

## In scope

- A general byte hash `Hash` / `MegaDreifach`.
- `HashDeck` / `MegaDreifachDeck`: `Hash(φ⁻¹(deal))` when the deal is in the image of φ.
- `HashDeckBody` / `MegaDreifachBody`: one Davies–Meyer compression on a required 52-card permutation, from IV-COOK12.
- `HashDeckBodyFrom` / `MegaDreifachBodyFrom`: the same compression from a caller chaining value (free-start analysis surface; broken).
- Pad B=28, factoradic φ, abs-G2 + F3 t=12, IV-COOK12, 29-byte digest rank.

## Non-goals

- No collision resistance, preimage resistance, or ideal-cipher-on-G claim.
- No AES-class numbers. Birthday ≈ 2^113 is honesty about `|G| ≈ 2^{225.9}`, not a theorem.
- No proof that mid-block L3 collisions are absent. They exist. Free-start `HashDeckBodyFrom` is broken.
- Relative reorient recipes are rejected (research disproof). Absolute Recipe A only.
- No claim that Lean equals this sudo text. That is a future emitter proof.
- HMAC-MegaDreifach does not make `Hash` collision-resistant. It is a correctly wired HMAC over this toy hash.

---

# 2. Public API

| Function | Meaning |
| --- | --- |
| `Hash(msg)` / `MegaDreifach(msg)` | Byte hash. The only public message domain. |
| `HashDeck(deal)` / `MegaDreifachDeck(deal)` | `Hash(φ⁻¹(deal))` when the deal’s factoradic rank is `< 2^{224}`. Often two MD blocks after the outer pad. |
| `HashDeckBody(deal)` / `MegaDreifachBody(deal)` | Public v1 Body. One DM compression on a **52-card permutation** from **IV-COOK12**. No outer pad, no φ. Non-permutations are rejected. |
| `HashDeckBodyFrom(deal, h)` / `MegaDreifachBodyFrom(deal, h)` | Free-start analysis surface. Same DM from caller chaining value `h`. **Broken** (collisions exist). Not a security API. |

Sudocode has no optional parameters, so the soft-lock prose `HashDeckBody(deal[, h])` splits: omit `h` → `HashDeckBody(deal)` (always IV-COOK12); supply `h` → `HashDeckBodyFrom(deal, h)`. Identically, `HashDeckBody(deal)` is `HashDeckBodyFrom(deal, IV-COOK12)`.

Cards appear after φ, or as a deal body for `HashDeckBody`. There is no arbitrary-card public message API.

---

# 3. Parameters (locked)

| Item | Value |
| --- | --- |
| Pad | SHA-2-style **B=28**: `M ‖ 0x80 ‖ 0x00^z ‖ 8-byte BE bit length` |
| φ | Each 28-byte chunk → BE integer `n < 2^{224} < 52!` → Lehmer unrank → 52-card deal |
| Card ids | `0..51` → `(rank = id // 4, suit = id % 4)`. Amount `k = suit + 1 ∈ {1,2,3,4}` |
| E_m | abs-G2: non-King turns the held face by `+k`; **King = king_up** (`−k` on Up, then spin the grip `+k`); noon+1; Front+1; abs reorient Recipe A; body=52; F3 t=12 |
| Chaining | Final position `g` only. Discard grip `o` after each block |
| IV | **IV-COOK12**: from solved, faces `0..11` each +1 CW |
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

Face adjacency (CW from outside), opposites, and the 20 corner triples are the tables in `megadreifach.sudo`.

---

# 5. Compression

1. φ(chunk) → a 52-card deal.
2. `e ← E_m(h)`: start at position `h` and grip = identity. Run one G2 step per card, then twelve F3 blank rounds. Discard the grip.
3. `h ← compose(h, e)`.
4. After the last block, the digest is the 29-byte rank of `h`.

Merkle–Damgård: `h₀ = IV-COOK12`; for each chunk `hᵢ = DM(hᵢ₋₁, mᵢ)`.

## G2 step (one card)

Held faces at the identity grip: rank A=Up=0, 2=Front=1, then CW around Up, then around Down, Q=Down=11. King is special.

**Non-King.** Turn the held face named by the rank by `+k`. Turn its noon neighbour by `+1`. Turn held-Front by `+1`. Read the clockwise-noon corner of the face just turned: colour on the turned face is `c1`, colour on the noon side is `c2`. Tip-and-spin absolutely: put centre `c1` on Up and centre `c2` on Front (Recipe A).

**King (king_up).** Turn held-Up by `−k` (same as `5−k` CW). Spin the grip about Up by `+k`. Noon of Up is Front, so Front then receives `+2` total. Read Up; tip-and-spin absolutely.

**Noon.** On face X, the edge toward held-Up; if X is Up, the edge toward held-Front.

## F3 (t = 12)

Twelve times: turn Up once CW; read the clockwise-noon corner of Up; tip-and-spin absolutely.

## 3-solve hand (informal)

Between blocks, puzzles `(A,B,C) = (h, h⁻¹, id)`. Run E_m on A; solve B onto A; solve A onto B and C; solve C onto A. Software is `compose(h, e)`.

---

# 6. Digest encoding

`position_to_bytes` is the 29-byte big-endian mixed-radix rank:

`even cp (20!/2) | co[0..18] (3^19) | even ep (30!/2) | eo[0..28] (2^29)`.

Last orientations are completed by the parity rules. Parse rejects integers `≥ |G|`. Encoding is injective on legal positions. It is not surjective onto `{0,1}^{232}`.

A sudocode `int` is 64-bit and overflow traps. `|G|` and `52!` do not fit. `std.bigint` cannot cross a module boundary; the conformance file pastes the limb arithmetic it needs (same limitation DoubleDeal records for 52-card ranks).

---

# 7. Test vectors

`kats/megaminx_hash_kats.json` is the published KAT file from the soft-lock reference (`hash_ref.py`). A copy lives at `proofs/megadreifach/vectors/` for Lean metadata checks. Sudo tests assert pad lengths, block counts, IV-COOK12 digest, φ on zero, the permutation domain, and that the public Hash API returns 29 bytes.

Full `Hash` digest equality against the hex strings in that JSON is not asserted by the sudo tests: those digests are not re-exported from this file's test block. It is proved outside the sudo, for the emitted Lean of this file: `proofs/megadreifach/lean/MegaDreifachHeavy/Kat.lean` kernel-checks `v_Hash(msg) = digest` for all 8 vectors (proof package, not part of this normative spec; the sudo → Lean emitter is trusted).

---

# 8. What this does not claim

- Ideal-cipher-on-G / PRF of `E_m`
- Collision resistance of `Hash`
- IV-anchored collision resistance. Answered (negatively) for the current Recipe A grip rule of this specification: collisions from the standard IV are practical via same-rank card swaps. See `proofs/megadreifach/security/suit_blind_collision.py` (and §3 of `REPORT.md` there).
- L3 absence (L3 collisions exist)
- Birthday ≈ 2^113 as a theorem
- PRESSURE.md tables as theorems
- Lean model = this sudo text
