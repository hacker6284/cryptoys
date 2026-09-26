# Link 2: algebraic Lean ≃ Generated Lean

Link 2 is a **refinement** goal: on the well-formed domain, the
handwritten algebraic ledger (`proofs/*/lean/<Name>/`) equals the
emitted implementation (`proofs/*/lean/Generated/`). Algebraic
theorems then transfer to Generated — and to sudo — **modulo emitter
bugs**.

This is **not** Link 1. Link 1 (sudo → Generated via `emit`) stays
**trusted-not-proved**. `proofs/emit_lean.sh --check` is the living
alarm. A green Link 2 theorem is not emitter soundness, not a KAT/TAP
substitute, and not bit-security / MDS / collision-resistance / AEAD
security.

Sudo remains normative. Never hand-edit `lean/Generated/`.

## Why a bridge

`Generated/` is a standalone Lake package. Emitted functions are
fuel-total `Except SudoRt.Trap` over `Array Int`. Stones are `Fin` /
`List Nat` algebra. Those types do not match. The bridge interprets
one side into the other **without editing Generated sources**.

Well-formedness is the domain where Trap does not fire and the
`Array Int` value is in the image of the algebraic embedding (Nats
that fit the i64 index arithmetic the emitter uses). PassKey does not
need the Fin-52 packet; encrypt uses `CardBound` and `Perm52`
(`encrypt_refines`).

```text
List Nat  --embed-->  Array Int
   |                      |
   | algebraic            | Generated (Except Trap)
   v                      v
List Nat  <--decode--  Array Int     (on success, no Trap)
```

## This drop (DoubleDeal S3/S4 on Except Trap)

Builds on #26/#28/#30 (`passkey_refines`, `passkey_inv_refines`, twin
`runLoopOn`) and #32 (`encrypt_refines`). On the well-formed domain —
`FitsLen` lists, and `WellFormed` for emitted `Array Int` — algebraic
S3/S4 hold for `Doubledeal.passkey` and `Doubledeal.passkey_inv`
(`Except SudoRt.Trap`): card multiset (`List.Perm`), `passkey_inv`
after `passkey` is the identity, `passkey` after `passkey_inv` is the
identity, and both are injective. The proofs are the two passkey glues
plus the list algebra. They do not re-induct on `runLoopOn`. Algebraic
Link 2 only — not bit-security, not emitter soundness.

| Item | Status |
| --- | --- |
| Scaffolding + well-formedness + embed/decode | Landed (`DoubleDeal/Link2/Embed.lean`) |
| `suit_of` / `rank_of` refine the stones | Landed |
| `Generated.drop_front` ≃ algebraic `uncons` (nonempty, `FitsLen`) | Landed |
| `Generated.push_front` ≃ algebraic `cons` (`FitsLen`) | Landed |
| `Generated.left_rotate` ≃ algebraic `rotL` (`FitsLen`) | Landed (`Link2/Rotate.lean`) |
| `Generated.right_rotate` ≃ algebraic `rotR` (`FitsLen`) | Landed (`right_rotate_refines`; via `left_rotate` + `rotR_eq_rotL`) |
| One generated PassKey body ≃ `passKeyStep` (rotate / cut / push) | Landed (`maybeRotate_refines`, `maybeCut_push_refines`, `passKeyStep_refines`) |
| Twin `runLoopOn` inducts to `passKeyGoN` on every well-formed list | Landed (`passkey_loop_refines`, `passkey_twin_refines`) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on length ≤ 1 | Landed (`passkey_nil`, `passkey_singleton`) |
| Residual stepper of `Doubledeal.passkey` = `passkeyStepGen` | **CLOSED** (`passkey_step_eq`, `passkey_inlined_cut_eq`; nested suit-rotate / do-elaboration, not a second algorithm) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on every well-formed list | **CLOSED** (`passkey_eq_twin_loop`, `passkey_refines`) |
| One generated inverse body ≃ `invPassKeyStep` | Landed (`maybeCutInv_refines`, `maybeRotateInv_refines`, `invPassKeyStep_refines`) |
| Twin inverse `runLoopOn` inducts to `passKeyInvGoN` | Landed (`passkey_inv_loop_refines`, `passkey_inv_twin_refines`) |
| Residual stepper of `Doubledeal.passkey_inv` = `passkeyInvStepGen` | **CLOSED** (`passkey_inv_step_eq`, `passkey_inv_eq_twin_loop`; nested undo-cut / do-elaboration, not a second algorithm) |
| `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list | **CLOSED** (`passkey_inv_refines`) |
| `Generated.encrypt` ≃ `encryptDeck` / `encrypt6` | **CLOSED** (`encrypt_refines`; `CardBound` message, `Perm52` key, length 52) |
| `mix_columns` ≃ `mixColumns` | **CLOSED** (`mix_columns_refines`) |
| `full_round` / `final_round` ≃ `fullRound` / `fullRoundNoMix` | **CLOSED** (`full_round_refines`, `final_round_refines`) |
| S3/S4 transfer onto `Except Trap` (multiset, inverse, injectivity) | **CLOSED** (`passkey_perm`, `passkey_inv_perm`, `passkey_leftInverse`, `passkey_rightInverse`, `passkey_injective`, `passkey_inv_injective`, and the `WellFormed` Array forms in `Link2/PassKeyTransfer.lean`) |
| MegaDreifach `pad_message` ≃ algebraic `pad` | **CLOSED** (`pad_message_refines`, `pad_message_refines_array`, `pad_z_refines`). Domain `PadWf`: bytes `≤ 255` and `8 * length` fits in an i64. Not `v_Hash`. |
| MegaDreifach `compose` ≃ algebraic `compose` | **CLOSED** (`compose_refines`, `compose_refines_array`). Domain `PosWf`: lengths 20/20/30/30, nonnegative in-range indices, orientations `< 3` / `< 2` (trap-free, i64-safe). Not `v_Hash`. |
| MegaDreifach `require_permutation` ≃ algebraic `requirePermutation` | **CLOSED** (`require_permutation_refines`, `require_permutation_refines_array`). Domain `DealWf` / `isPermutation52`: length 52, nonnegative card ids `< 52`, no duplicates (trap-free, i64-safe). Not `v_Hash`. |
| MegaDreifach `pack_ori2` ≃ algebraic `packOri2` | **CLOSED** (`pack_ori2_refines`, `pack_ori2_refines_array`). Domain `Ori2Wf`: length 30, entries `< 2`. Horner value `< 2^29`, one limb, trap-free i64 arithmetic. Not `v_Hash`. |
| MegaDreifach `pack_ori3` ≃ algebraic `packOri3` | **CLOSED** (`pack_ori3_refines`, `pack_ori3_refines_array`). Domain `Ori3Wf`: length 20, entries `< 3`. Horner value `< 3^19`, at most two base-10^9 limbs, trap-free i64 arithmetic. Not `v_Hash`. |
| MegaDreifach `even_perm_rank_big` ≃ algebraic `evenRank` | **CLOSED** (`even_perm_rank_big_refines`, `even_perm_rank_big_refines_array`). Domain `Rank20Wf`: length 20, permutation of `0..19`, Lehmer rank `< 2·10^9` (one-limb accumulator, two-limb sum, trap-free i64). Not every corner rank (`20!/2` is three limbs). Not length 30. Not M3 injectivity. Not `v_Hash`. |
| MegaDreifach `position_to_bytes` ≃ algebraic `positionToBytes` | **CLOSED** on `PosBytesWf` (`position_to_bytes_refines`, `position_to_bytes_refines_array`). Corner `evenRank = 0`, corner-ori `packOri3 = 0`, edge prefix `0..27` (`EdgeZero` / `evenRank = 0`), edge ori any `Ori2Wf`. Digest is `toBE 29 (packOri2 eo)`. `even30` = `30!/2` multiplies a zero accumulator. Not every legal position. Not `v_Hash`. |
| MegaDreifach `big_from_be` on zero bytes ≃ `fromBE` | **CLOSED** (`big_from_be_zeros`, `big_from_be_zeros_fromBE`, `big_from_be_zero_pad`). Domain: `k` zero bytes, `k` fits in an i64, including `0` and the 28-byte pad block. Value is `0`; the emitted bigint is the empty limb list. Not a general pad block. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_factorial` ≃ algebraic `factorial` for `n ≤ 13` | **CLOSED** (`big_factorial_refines`). `12! < 10^9` (one limb). `13! = 12! · 13` is the last product of the proved one-limb multiply; the value is two limbs. `14!` needs a two-limb accumulator. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of the zero bigint | **CLOSED** (`peel_leading_zero`, `peel_leading_zero_digit`). Domain `d ≤ 13`: divisors `2..d` stay on the empty limb list. The factoradic digit is `0 / d! = 0` and the remainder is `0`. The emitter still builds `d!` and multiplies it by that digit; the product is zero. Not a positive rank. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_from_be` ≃ `fromBE` on short byte strings | **CLOSED** (`big_from_be_short`, `big_from_be_short_array`, `big_from_be_byte`, `fromBE_short_lt_limb`). Domain `BeShortWf`: length `≤ 3`, each byte `≤ 255`. `fromBE < 256^3 < 10^9`, one limb (empty if zero). Each Horner step `acc * 256 + b` stays in the proved one-limb multiply and add. Not length 4 (`256^4 > 10^9`). Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `big_from_be` ≃ `fromBE` on two-limb byte strings | **CLOSED** (`big_from_be_limb2`, `big_from_be_limb2_array`, `big_add_byte`, `fromBE_limb2_lt_sq`). Domain `BeLimb2Wf`: length `≤ 7`, each byte `≤ 255`. `fromBE < 256^7 < 10^18`, at most two limbs. Prefixes of length `≤ 3` stay in one limb; a fourth byte may carry. Multiply by 256 is the proved one-limb or two-limb product (below `10^18`). Not length 8 (`256^8 > 10^18`). Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `peel_leading` on a one-limb rank | **CLOSED** (`peel_leading_limb`, `peel_leading_factorial`, `divmod_limb`, `limb_to_small_limb`). Domain: `d ≤ 12` and `n < 10^9`. `d!` and every quotient `n / k!` (`k ≤ d`) are one limb. The pair is `(n % d!, n / d!)`. The digit is positive when `d! ≤ n`; `peel_leading (bigNat (d!)) d = (0, 1)`. Not `d ≥ 13` (a positive digit times a two-limb factorial). Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_factorial` ≃ `factorial` for `n ≤ 19` | **CLOSED** (`big_factorial_two`, `big_mul_two`). `12!` is one limb. `13!` through `19!` are two limbs (`19! < 10^18`). Each step multiplies that accumulator by `i ≤ 19` and the product stays below `10^18` (the scratch third limb is zero). `20!` is three limbs. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of zero for `d ≤ 19` | **CLOSED** (`peel_leading_zero_two`, `peel_leading_zero_digit_two`). Domain `d ≤ 19` on the zero bigint. The factoradic digit is `0 / d! = 0` and the remainder is `0`. For `d ≥ 13` the factorial is two limbs; the closing multiply is the zero coefficient, which short-circuits. Not a positive rank. Not `d ≥ 20`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of `d!` for `d ≤ 19` | **CLOSED** (`peel_leading_factorial_two`, `divmod_sq`, `big_mul_one`). The factoradic digit is `d! / d! = 1` and the remainder is `0`. For `d ≥ 13`, `d!` is two limbs (`19! < 10^18`). `divmod_sq` divides any `a < 10^18` by a positive one-limb divisor; the running remainder stays below `10^18`. The closing product is the digit `1` times that factorial. Not an arbitrary positive two-limb rank. Not `20!` (three limbs). Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_factorial` ≃ algebraic `factorial` for `n ≤ 20` | **CLOSED** (`big_factorial_three`, `big_mul_three`, `big_mul_three_limbs`, `bigNat_three`). `12!` is one limb. `13!` through `19!` are two limbs (`19! < 10^18`). `20! = 19! · 20` is the first three-limb factorial (`10^18 ≤ 20! < 10^27`). `big_mul_three` multiplies a two-limb value by a one-limb factor when the product needs a third limb. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_factorial` ≃ algebraic `factorial` for `n ≤ 26` | **CLOSED** (`big_factorial_acc3`, `big_mul_acc3`, `big_mul_acc3_limbs`). `21!` through `26!` multiply a three-limb accumulator by a one-limb factor `i ≤ 26`. The product stays below `10^27`; the fourth scratch limb is zero and trims away. Not `27!` (four limbs). Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of `d!` for `d ≤ 26` | **CLOSED** (`peel_leading_factorial_three`, `divmod_cube`, `big_mul_one_three`). The factoradic digit is `d! / d! = 1` and the remainder is `0`. For `d ≥ 20`, `d!` is three limbs (`10^18 ≤ 20!` and `26! < 10^27`). `divmod_cube` divides any value below `10^27` by a positive one-limb divisor. The closing product is the digit `1` times that factorial. Not an arbitrary positive three-limb rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of zero for `d ≤ 26` | **CLOSED** (`peel_leading_zero_three`, `peel_leading_zero_digit_three`). Domain `d ≤ 26` on the zero bigint. The factoradic digit is `0 / d! = 0` and the remainder is `0`. For `d ≥ 20` the factorial is three limbs (`26! < 10^27`); the closing multiply is the zero coefficient, which short-circuits. Not a positive rank. Not `d ≥ 27`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of a rank strictly below `d!` for `d ≤ 26` | **CLOSED** (`peel_leading_below`, `peel_leading_below_digit`, `mag_sub_zero_right`). Domain `n < d!` and `d ≤ 26`. The factoradic digit is `n / d! = 0` and the remainder is `n`. For `13 ≤ d` a positive rank `10^9 ≤ n < d!` is two limbs; for `20 ≤ d` a rank `10^18 ≤ n < d!` is three limbs (`26! < 10^27`). Not `d!` itself (digit `1`). Not an arbitrary rank `n ≥ d!`. Not a positive digit. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of a rank in `[d!, 2·d!)` for `d ≤ 19` | **CLOSED** (`peel_leading_one`, `peel_leading_one_digit`, `mag_sub_two_le`). The factoradic digit is `n / d! = 1` and the remainder is `n - d!`. `d!` itself stays the old remainder-0 corner. Every larger rank in the interval has a positive remainder. For `13 ≤ d` the rank is two limbs (`2·19! < 10^18`); `mag_sub` may borrow. Not `d ≥ 20`. Not a digit `q ≥ 2`. Not `n ≥ 2·d!`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of a rank in `[d!, 2·d!)` for `d ≤ 26` | **CLOSED** (`peel_leading_one_three`, `peel_leading_one_three_digit`, `mag_sub_three_le`). The factoradic digit is `n / d! = 1` and the remainder is `n - d!`, which may be positive. For `20 ≤ d` both the rank and `d!` are three limbs (`10^18 ≤ 20!` and `2·26! < 10^27`); `mag_sub` may borrow. `d ≤ 19` reuses the two-limb theorem. Not a digit `q ≥ 2`. Not `n ≥ 2·d!`. Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` of every rank below `limbCap d` for `d ≤ 26` | **CLOSED** (`peel_leading_cap`, `peel_leading_cube`, `peel_leading_sq`, `big_mul_small_three`, `big_mul_small_two`). The pair is `(n % d!, n / d!)`, every digit including `q ≥ 2`. `limbCap` is `10^9` for `d ≤ 12`, `10^18` for `13 ≤ d ≤ 19`, and `10^27` for `20 ≤ d ≤ 26`. On that cap `d!` forces the digit into one limb. The emitted product is the digit times `d!`; `mag_sub` may borrow. Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_divmod_small` on any width, divisor one limb | **CLOSED** (`big_divmod_small_refines`, `big_divmod_nat`, `natLimbs_length_le`). A canonical base-`10^9` limb string divided by `0 < d < 10^9` returns `(natLimbs (value / d), value % d)`. The countdown stacks `divGenStep_at`. Each `rem * 10^9 + digit` stays below `10^18`. Not `big_mul`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_mul` of a wide left factor by one limb | **PARTIAL** (`big_mul_wide_open`, `mulAcc`, `mulAcc_succ`, `kLoop_write`, `kLoop_idle`). The emitted outer loop is the schoolbook product. The accumulator after `i` limbs is `mulAcc`, and the carry walk writes one extra limb. The induction that turns one outer digit into `natLimbs (q * n)` is not closed, so `big_factorial` through `51!` is not closed. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach full `v_Hash` / Scramble algebraic ≃ Generated | **OPEN** (`v_Hash` is M13; Scramble has little ledger). The pad, compose, `require_permutation`, `pack_ori2`, `pack_ori3`, length-20 `even_perm_rank_big`, zero-rank `position_to_bytes`, zero-byte `big_from_be`, short `big_from_be` (`BeShortWf`, length `≤ 3`), two-limb `big_from_be` (`BeLimb2Wf`, length `≤ 7`), `big_factorial` (`n ≤ 26`), and `peel_leading` of every rank below `limbCap d` for `d ≤ 26` (every digit `q`, three limbs once `d ≥ 20`) are closed. `big_divmod_small` now agrees with `natLimbs (n / d)` at arbitrary width for a one-limb divisor. `big_mul` of a wide accumulator by one limb is reduced to its schoolbook loop; the digit induction into `natLimbs (q * n)` is not closed, so `51!`, a 28-byte `big_from_be`, `peel_leading` for `d ≤ 51`, and `phi_chunk` / `phi_inv` stay open. Positive `range_list` (`0 < n`, `FitsLen`, including 52) is already `range_list_refines` in `EvenRank.lean`. Full `v_Hash` remains OPEN. |
| DoubleDeal-CBC-HMAC algebraic ≃ Generated | OPEN. Generated TAP exists (`#22`); no algebraic ledger. Not AEAD security. |
| sudo text = generated Lean (deep embedding) | OPEN — Link 1, not this file |
| Bit-security, MDS, collision-resistance, AEAD | Not a Link 2 claim |

## What stays trusted-not-proved

- The Lean emitter (`backends/lean/emit.py` at the pin in
  [`ANTI_DRIFT.md`](ANTI_DRIFT.md)).
- Generated TAP and JSON KATs as **evidence**, not Link 2 theorems.

Edit `.sudo` and regenerate `Generated/` to change the algorithm.
Edit stones / `Link2/` to change the ledger or the refinement.
