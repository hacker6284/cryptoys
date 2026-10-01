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
`FitsLen` lists whose cards are also `FitsLen` (v12: the deal count
`suit + 2` is an i64 addition), and `WellFormed` for emitted `Array Int`
(which now carries the same card bound) — algebraic
S3/S4 hold for `Doubledeal.passkey` and `Doubledeal.passkey_inv`
(`Except SudoRt.Trap`): card multiset (`List.Perm`), `passkey_inv`
after `passkey` is the identity, `passkey` after `passkey_inv` is the
identity, and both are injective. The proofs are the two passkey glues
plus the list algebra. They do not re-induct on `runLoopOn`. Algebraic
Link 2 only — not bit-security, not emitter soundness.

MegaDreifach rows: v2 (Generated from [`megadreifach.sudo`](../primitives/hash/megadreifach/megadreifach.sudo)); see [`megadreifach/README.md`](megadreifach/README.md). The v1 rows, frozen with the v1 weakness proofs they support, are in [`deprecated/megadreifach-v1/`](deprecated/megadreifach-v1/README.md).

| Item | Status |
| --- | --- |
| Scaffolding + well-formedness + embed/decode | Landed (`DoubleDeal/Link2/Embed.lean`) |
| `suit_of` / `rank_of` refine the stones | Landed |
| `Generated.drop_front` ≃ algebraic `uncons` (nonempty, `FitsLen`) | Landed |
| `Generated.push_front` ≃ algebraic `cons` (`FitsLen`) | Landed |
| `Generated.left_rotate` ≃ algebraic `rotL` (`FitsLen`) | Landed (`Link2/Rotate.lean`) |
| `Generated.right_rotate` ≃ algebraic `rotR` (`FitsLen`) | Landed (`right_rotate_refines`; via `left_rotate` + `rotR_eq_rotL`) |
| `Generated.deal_under` / `undeal_under` / `deal_step` / `undeal_step` ≃ `dealUnder` / `undealUnder` / `maybeDeal` / `maybeDealInv` (v12) | Landed (`Link2/Deal.lean`: `deal_under_refines`, `undeal_under_refines`, `deal_step_refines`, `undeal_step_refines`; `FitsLen` card and piles) |
| One generated PassKey body ≃ `passKeyStep` (deal / cut / push) | Landed (`deal_step_refines`, `maybeCut_push_refines`, `passKeyStep_refines`) |
| Twin `runLoopOn` inducts to `passKeyGoN` on every well-formed list | Landed (`passkey_loop_refines`, `passkey_twin_refines`) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on length ≤ 1 | Landed (`passkey_nil`, `passkey_singleton`; the singleton needs its card `FitsLen` since v12) |
| Residual stepper of `Doubledeal.passkey` = `passkeyStepGen` | **CLOSED** (inside `passkey_eq_twin_loop`; do-elaboration only, not a second algorithm. v12 re-proof: `deal_step` then the cut / push body) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on every well-formed list | **CLOSED** (`passkey_eq_twin_loop`, `passkey_refines`) |
| One generated inverse body ≃ `invPassKeyStep` | Landed (`maybeCutInv_refines`, `undeal_step_refines`, `invPassKeyStep_refines`) |
| Twin inverse `runLoopOn` inducts to `passKeyInvGoN` | Landed (`passkey_inv_loop_refines`, `passkey_inv_twin_refines`) |
| Residual stepper of `Doubledeal.passkey_inv` = `passkeyInvStepGen` | **CLOSED** (inside `passkey_inv_eq_twin_loop`; undo-cut then `undeal_step`, do-elaboration only, not a second algorithm) |
| `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list | **CLOSED** (`passkey_inv_refines`). v12: both refinements also assume every card `FitsLen` (v11 did not need it) |
| `Generated.encrypt` ≃ `encryptDeck` / `encrypt6` | **CLOSED for v12** (`encrypt_refines`, unchanged in statement; `CardBound` message, `Perm52` key, length 52; the new card bound for PassKey comes from `Perm52`). Re-proved for v9 in stage 2, for v10 with the new SumRanks, for v11 with the new GridCycle, and for v12 with the new PassKey deal; see "v12 changes", "v11 changes" and "v10 changes" in `doubledeal/README.md` |
| `sum_ranks` ≃ `sumRanksV10` | **CLOSED for v10, v11 and v12** (`sum_ranks_refines`; v11 and v12 keep v10 SumRanks). Every emitted helper has its own refinement lemma (`row_total`, `row_turn`, `sum_rows`, `suit_label`, `gf_add`, `gf_times_w`, `column_value`, `column_suits`, `column_turn`, `turn_column`, `sum_columns`). Domain: every grid (v9 needed `CardBound` cells; v10 turn amounts stay small) |
| `mix_columns` ≃ `mixColumns` | **CLOSED for v11 and v12** (v12 keeps the v11 GridCycle; `mix_columns_refines`, `CardBound` hand; re-proved for the ghost finger and blocker-directed scan: the emitted loop state carries the finger `fr`/`fc`, the blocker is read from the emitted grid, and the emitted `overflow_seat` refines `overflowSeat` via `scan_row_refines`). Previously closed for v9 and v10 |
| `full_round` / `final_round` ≃ `fullRound` / `fullRoundNoMix` | **CLOSED for v11 and v12** (`full_round_refines`, `final_round_refines`; unchanged in statement) |
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
| MegaDreifach `big_mul` of a wide left factor by one limb | **CLOSED** (`big_mul_wide_refines`, `big_mul_nat`). Any canonical base-`10^9` digit string times `q < 10^9` is `natLimbs (q * value)`. The accumulator is on the left (`big_factorial`, Horner `* 256`). Each cell stays below `10^18`. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `big_mul` of one limb on the left by a wide digit string | **CLOSED** (`big_mul_left_refines`, `big_mul_left_nat`). The factoradic digit sits on the left and the wide factorial on the right, which is what `peel_leading` emits. The product is `natLimbs (q * value)`. Each cell `digit * q + carry` stays below `10^18`. Not `mag_sub`. Not `peel_leading` for `d > 26`. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `big_factorial` ≃ `factorial` for `n ≤ 51` | **CLOSED** (`big_factorial_51`). `51! < 10^72`, at most eight limbs. Each step is `big_mul_nat`. Not `peel_leading` for `d > 26`. Not the 28-byte `big_from_be`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `mag_sub` at arbitrary width | **CLOSED** (`mag_sub_nat`). Canonical base-`10^9` limbs, subtrahend at most the minuend. The trimmed digits are `natLimbs (n - m)`. The final borrow is `0`. Not `phi_chunk`. Not `v_Hash`. |
| MegaDreifach `mag_add` / `big_add` at arbitrary width | **CLOSED** (`mag_add_limbs`, `mag_add_nat`, `big_add_nat`). Canonical base-`10^9` limbs. Trimmed digits are `natLimbs (n + m)`. `FitsLen` of the longer string plus one covers the final carry limb. Not the 28-byte `big_from_be`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `big_from_be` ≃ `fromBE` on length ≤ 28 (the pad block) | **CLOSED** (`big_from_be_pad`, `big_from_be_pad_array`, `fromBE_pad_lt_limb8`, `pow256_28_lt_limb8`). Domain `BePadWf` / `WellFormedBePad`: length `≤ 28`, each byte `≤ 255`. `256^28 < 10^72 = limbBase^8`, so every Horner prefix is at most eight base-`10^9` limbs; the value is `bigOf (natLimbs (fromBE bs))`. Each step `acc * 256 + b` is `big_mul_nat` then `big_add_nat`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `peel_leading` for `d ≤ 51` when the digit is one limb | **CLOSED** (`peel_leading_51`). Domain `d ≤ 51` and `n / d! < 10^9`. The pair is `(n % d!, n / d!)`. `limb_to_small` and `big_mul_left` take the digit; `mag_sub_nat` subtracts the product. `n < 10^81`. Not a two-limb digit. Not `big_from_be` past length 7. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `phi_chunk` ≃ `phiUnrank (fromBE bs)` on the 28-byte pad | **CLOSED** (`phi_chunk_refines`, `phi_chunk_refines_array`, plus `phiChunkStep_lt`, `phiChunkStep_51`). Domain `PhiChunkWf` / `WellFormedPhiChunk`: length 28, each byte `≤ 255`. The outer `chain_loop` runs `phiState` from `0` to `51`; each step peels `(rank % d!, rank / d!)` and erases the drawn card, and the last step breaks at `phiState rank 52`, whose `out` is `embed (phiUnrank rank)`. Not `phi_inv`. Not `v_Hash`. |
| MegaDreifach `phi_inv` ≃ Lehmer rank of a 52-card deal, emitted `toBE 28` | **CLOSED** (`phi_inv_refines`, `phi_inv_refines_array`, plus `phiInvStep_lt`, `phiInvStep_51`, `phiInvFind_breaks`, `mag_cmp_eq`, `magCmp_lt_natLimbs`, and `ToBePad.big_to_be_pad`). Domain `PhiInvWf` / `WellFormedPhiInv`: length 52, a permutation of `0..51` (`Nodup`, ids `< 52`), and `lehmerRank deal < 2^224` (`phiMax`). The outer `chain_loop` runs `phiState` from `0` to `51`, folding `n := n * (52 - i) + idx` (`big_from_int` / `big_mul` / `big_add`), erasing `idx`, asserting `n < 2^224` (`mag_cmp` on canonical limbs) and emitting `big_to_be n 28`. Result is `embed (toBE 28 (lehmerRank deal))`. Not `v_HashDeck`. |
| MegaDreifach full `v_Hash` ≃ algebraic Merkle–Damgård fold | **CLOSED** on `PadWf` (bytes `≤ 255`, `8 · length` fits in an i64): `v_Hash_refines`, `v_Hash_refines_array`, `v_MegaDreifach_refines`, `v_Hash_eq_hashBlocks` (`Link2/VHash.lean`), built from `em_block_refines`, `position_to_bytes_refines_gen` (every `InjPos` position), `even_perm_rank_big_refines_gen` and `big_mul_gen_refines` (arbitrary limb lists), `phi_chunk_refines`, `pad_message_refines`. The algebraic side `Em` (`Em.lean`) is a typed transliteration of the v2 sudo `E_m` (visual noon, the corner / edge read right after the held-face turn, 36 F3 rounds) with the tables copied verbatim, not an independent specification. All 8 exported v2 KATs (M13) are kernel-checked `v_Hash` theorems in the non-default lib `MegaDreifachHeavy` (`kat_<name> : v_Hash (embed (hexBytes Vectors.vec_<name>.msgHex)) = .ok (embed (hexBytes Vectors.vec_<name>.digestHex))`; `Vectors.lean` is generated from the v2 KAT JSON and checked in CI). `v_Hash` never calls `phi_inv`. Not `v_HashDeck`. Not collision resistance. |
| MegaDreifach `v_HashDeck` ≃ algebraic hash of the deal's Lehmer rank | **CLOSED** on `PhiInvWf` / `WellFormedPhiInv` (`v_HashDeck_eq_v_Hash`, `v_HashDeck_refines`, `v_HashDeck_refines_array`, `v_MegaDreifachDeck_refines`; `megadreifach/lean/MegaDreifach/Link2/VHashDeck.lean`), built from `require_permutation_refines`, `phi_inv_refines` and `v_Hash_refines`. `v_HashDeck deal = v_Hash (toBE 28 (lehmerRank deal))`. The digest is `positionToBytes (dmBlock (Em.dmStep Em.ivCook12 deal) deckPadBlock)` (`v_HashDeck_two_blocks`, using the φ round trip `phiUnrank_lehmerRank`). Not collision resistance. |
| Scramble algebraic ≃ Generated | **CLOSED** (correctness of the emitted code only): the v2 digest path, digest-only and traced, one or several updates, and the v1 digest-only path refine a hand-written model; statements and what is not claimed in [`scramble/README.md`](scramble/README.md#link-2-leanscramblev2). Not collision resistance. |
| DoubleDeal-CBC-HMAC algebraic ≃ Generated | **CLOSED** on byte inputs whose lengths fit the i64 bounds, one theorem per exported sudo function (`proofs/doubledeal-cbc-hmac/lean/DoubleDealCbcHmac/Link2/`; table in [`doubledeal-cbc-hmac/README.md`](doubledeal-cbc-hmac/README.md#link-2)): `xor_bytes_refines`, `hmac_normalize_key_refines`, `v_HMAC_refines`, `v_HMAC_MegaDreifach_refines`, `pad_iso7816_refines`, `unpad_iso7816_char` (succeeds exactly where the model `unpad` does, with the same bytes; traps otherwise; corollaries `unpad_iso7816_refines`, `unpad_iso7816_rejects`), `mac_input_refines`, `derive_keys_refines`, `cbc_chain_from_cipher_block_refines`, `tags_equal_refines`. The model (`DoubleDealCbcHmac/Spec.lean`) is written from SPEC with the hash as a parameter, instantiated at MegaDreifach's `vhashAlg` via `v_Hash_refines`, re-checked against CBC-HMAC's own emitted `Megadreifach` module. For HMAC and the KDF, the theorems prove the HMAC / KDF wiring around the hash; the hash itself is only as independent as `vhashAlg`, which is a transliteration of the MegaDreifach sudo, not an independent specification. Not the byte-domain CBC encrypt / decrypt (JS). Not AEAD security. |
| sudo text = generated Lean (deep embedding) | OPEN — Link 1, not this file; plan in [`LINK1.md`](LINK1.md) |
| Bit-security, MDS, collision-resistance, AEAD | Not a Link 2 claim |

## What stays trusted-not-proved

- The Lean emitter (`backends/lean/emit.py` at the pin in
  [`ANTI_DRIFT.md`](ANTI_DRIFT.md)).
- Generated TAP and JSON KATs as **evidence**, not Link 2 theorems.

Edit `.sudo` and regenerate `Generated/` to change the algorithm.
Edit stones / `Link2/` to change the ledger or the refinement.
