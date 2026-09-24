# MegaDreifach

This document is the normative specification. `megadreifach.sudo` is the conformance implementation. A mismatch is a bug in the implementation. MegaDreifach is a toy three-megaminx Merkle–Damgård hash. It makes no cryptographic security claim. It is not for protecting anything.

The product name **MegaDreifach** is locked. The puzzle, group, and library stay called **megaminx**.

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Use a keyed construction if you need to stop it. A green Lean build is not a security claim. Hand-written Lean is not a proof that the sudo text equals the Lean model.

---

# 1. Scope and non-goals

## In scope

- A general byte hash `Hash` / `MegaDreifach`.
- `HashDeck` / `MegaDreifachDeck`: `Hash(φ⁻¹(deal))` when the deal is in the image of φ.
- `HashDeckBody` / `MegaDreifachBody`: one Davies–Meyer compression on a required 52-card permutation.
- Pad B=28, factoradic φ, abs-G2 + F3 t=12, IV-COOK12, 29-byte digest rank.

## Non-goals

- No collision resistance, preimage resistance, or ideal-cipher-on-G claim.
- No AES-class numbers. Birthday ≈ 2^113 is honesty about `|G| ≈ 2^{225.9}`, not a theorem.
- No proof that mid-block L3 collisions are absent. They exist. Free-start `HashDeckBody` is broken.
- Relative reorient recipes are rejected (research disproof). Absolute Recipe A only.
- No claim that Lean equals this sudo text. That is a future emitter proof.

---

# 2. Public API

| Function | Meaning |
| --- | --- |
| `Hash(msg)` / `MegaDreifach(msg)` | Byte hash. The only public message domain. |
| `HashDeck(deal)` / `MegaDreifachDeck(deal)` | `Hash(φ⁻¹(deal))` when the deal’s factoradic rank is `< 2^{224}`. Often two MD blocks after the outer pad. |
| `HashDeckBody(deal[, h])` / `MegaDreifachBody(deal[, h])` | One DM compression on a **52-card permutation** from chaining value `h` (default IV-COOK12). No outer pad, no φ. Non-permutations are rejected. |

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
| Digest | `position_to_bytes(g)` → **29 bytes**, bijective on legal G ↔ `[0, \|G\|)` |

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

A sudocode `int` is 64-bit and overflow traps. `|G|` and `52!` do not fit. `std.bigint` cannot cross a module boundary; the conformance file pastes the limb arithmetic it needs (same limitation TwoDeck records for 52-card ranks).

---

# 7. Test vectors

`kats/megaminx_hash_kats.json` is the published KAT file from the soft-lock reference (`hash_ref.py`). A copy lives at `proofs/megadreifach/vectors/` for Lean metadata checks. Sudo tests assert pad lengths, block counts, IV-COOK12 digest, φ on zero, the permutation domain, and that the public Hash API returns 29 bytes.

Full `Hash` digest equality against the research hex strings in that JSON is **evidence to finish**. This sudo is the conformance runner; those hexes are not sudo-asserted until they are re-exported from it.

---

# 8. What this does not claim

- Ideal-cipher-on-G / PRF of `E_m`
- Collision resistance of `Hash`
- IV-anchored collision (empirically open)
- L3 absence (L3 collisions exist)
- Birthday ≈ 2^113 as a theorem
- PRESSURE.md tables as theorems
- Lean model = this sudo text
