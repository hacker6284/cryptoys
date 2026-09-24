# MegaDreifach

MegaDreifach is a toy Merkle–Damgård hash on the megaminx group. The product name is locked. The puzzle, group, and library stay called **megaminx**.

This is not a security claim. Length extension on bare `Hash` is accepted (SHA-2-shaped). A green Lean build is not collision resistance.

## What is in this directory

| File | Role |
| --- | --- |
| `megaminx.py` | Megaminx group: positions, face turns, compose/inverse, 29-byte rank |
| `front.py` | Pad B=28, factoradic φ, `require_permutation`, IV-COOK12 |
| `selfcheck.py` | Pad / φ / domain / IV-COOK12 vs `proofs/megadreifach/vectors/` |
| `SPEC.md` | This file |

`hash_bytes` / `E_m` (abs-G2 + F3 t=12) are **not** landed here. The research runner `em_spike_r4` is not in this tree. Full KAT digest regeneration is a follow-up.

## Parameters (LOCKED)

| Item | Value |
| --- | --- |
| Pad | SHA-2-style **B=28**: `M ‖ 0x80 ‖ 0x00*z ‖ 8-byte BE bit length` |
| φ | Each 28B chunk → BE int `n < 2^224 < 52!` → Lehmer unrank → 52-card deal |
| Card ids | `0..51` → `(rank = id // 4, suit = id % 4)` |
| E_m | abs-G2: king_up, noon+1, Front+1, Recipe A; body=52; F3 t=12 (**follow-up**) |
| IV | **IV-COOK12**: solved, faces `0..11` each +1 CW |
| DM | `h' = compose(h, E_m(h))` (3-solve hand) |
| Digest | `position_to_bytes(g)` → **29 bytes**, bijective on legal G ↔ `[0, \|G\|)` |

## Public API (names)

| Function | Meaning | In this drop |
| --- | --- | --- |
| `Hash(bytes)` / `hash_bytes` | General byte hash | Follow-up (`E_m`) |
| `HashDeck(deal)` | `Hash(φ⁻¹(deal))` when the deal is in the image of φ | Follow-up |
| `HashDeckBody(deal[, h])` | One DM compression; **require** a 52-perm | Domain + IV landed; compression follow-up |

## Correctness ledger

Algebraic obligations live in `proofs/megadreifach/`. See `STONES.md`. Lean targets correctness, not bit-security.

Out of scope: collision resistance, ideal-cipher-on-G, L3 absence (L3 collisions exist), PRESSURE.md tables as theorems, relative reorient recipes.

## Test

```sh
python3 primitives/hash/megadreifach/selfcheck.py
```
