/-
  LINK 2. Algebraic MegaDreifach ≃ Generated on the pad and compose domains.

  Not emitter soundness (Link 1 stays trusted-not-proved).
  Not bit-security, collision resistance, or `v_Hash`.
  Do not edit lean/Generated/. Sudo remains normative.

  See proofs/LINK2.md.
-/
import MegaDreifach.Link2.Embed
import MegaDreifach.Link2.Bytes
import MegaDreifach.Link2.Sudo
import MegaDreifach.Link2.Loop
import MegaDreifach.Link2.Big
import MegaDreifach.Link2.Be
import MegaDreifach.Link2.PadRef
import MegaDreifach.Link2.Compose
import MegaDreifach.Link2.RequirePerm
import MegaDreifach.Link2.PackOri
import MegaDreifach.Link2.EvenRank
import MegaDreifach.Link2.PosBytes
import MegaDreifach.Link2.FromBe
import MegaDreifach.Link2.FromBeShort
import MegaDreifach.Link2.FromBeLimb2
import MegaDreifach.Link2.Factorial
import MegaDreifach.Link2.PeelLimb
import MegaDreifach.Link2.FactTwo
import MegaDreifach.Link2.FactThree
import MegaDreifach.Link2.AccThree
import MegaDreifach.Link2.PeelFact
import MegaDreifach.Link2.PeelCube
import MegaDreifach.Link2.PeelZeroThree
import MegaDreifach.Link2.PeelBelow
import MegaDreifach.Link2.PeelOne
import MegaDreifach.Link2.PeelOneThree

namespace MegaDreifach.Link2

/-!
  CLOSED: `pad_z_refines`, `pad_message_refines`, `pad_message_refines_array`.
  Domain `PadWf`: every byte `≤ 255`, and `8 * length` fits in an i64
  (`FitsBitlen`). Generated `pad_message` equals algebraic `pad`.

  CLOSED: `compose_refines`, `compose_refines_array`.
  Domain `PosWf`: table lengths 20/20/30/30, nonnegative in-range indices,
  orientations `< 3` / `< 2` (trap-free, i64-safe). Generated `compose`
  equals algebraic `compose`.

  CLOSED: `require_permutation_refines`, `require_permutation_refines_array`.
  Domain `DealWf` / `isPermutation52`: length 52, nonnegative card ids `< 52`,
  no duplicates (trap-free, i64-safe). Generated `require_permutation` equals
  algebraic `requirePermutation`.

  CLOSED: `pack_ori2_refines`, `pack_ori2_refines_array`.
  Domain `Ori2Wf`: length 30, every entry `< 2`. Generated `pack_ori2` equals
  algebraic `packOri2` (Horner / mixed-radix). The value stays below `2^29`,
  inside one base-10^9 limb.

  CLOSED: `pack_ori3_refines`, `pack_ori3_refines_array`.
  Domain `Ori3Wf`: length 20, every entry `< 3`. Generated `pack_ori3` equals
  algebraic `packOri3`. The Horner value stays below `3^19`, so it fits in
  two base-10^9 limbs (the last step may carry).

  CLOSED: `even_perm_rank_big_refines`, `even_perm_rank_big_refines_array`.
  Domain `Rank20Wf`: length 20, a permutation of `0..19`, and `evenRank < 2·10^9`.
  Generated `even_perm_rank_big` equals algebraic `evenRank` (Lehmer prefix).
  The bound keeps every Horner step in the one-limb multiply / two-limb add.
  Not every corner rank (`20!/2` is three limbs). Not length 30. Not M3 glue.

  CLOSED: `position_to_bytes_refines`, `position_to_bytes_refines_array`.
  Domain `PosBytesWf` / `BytesWf`: corner `evenRank = 0`, corner-ori `packOri3 = 0`,
  edge Lehmer prefix `0..27` (`EdgeZero`, so `evenRank = 0`), edge ori any `Ori2Wf`.
  The 29 bytes are `toBE 29 (packOri2 eo)`. `even30` equals `30!/2` and multiplies
  a zero accumulator. Not every legal position. Not `v_Hash`.

  CLOSED: `big_from_be_zeros`, `big_from_be_zeros_fromBE`, `big_from_be_zero_pad`.
  Domain: `k` zero bytes with `k` fitting in an i64, including the empty
  string and the 28-byte pad block. The Horner value is `0` (`fromBE`),
  so the emitted bigint is the empty limb list. Not a general pad block
  (`2^224` is many limbs). Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `big_factorial_refines`. Domain `n ≤ 13`. `12! < 10^9` (one limb);
  `13! = 12! · 13` is the last product of the proved one-limb multiply.
  Not `51!`.

  CLOSED: `peel_leading_zero`, `peel_leading_zero_digit`. Domain `d ≤ 13`
  on the zero bigint. Divisors `2..d` stay on the empty limb list. The
  factoradic digit is `0 / d! = 0` and the remainder is `0`. Not a positive
  rank. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `big_from_be_short`, `big_from_be_short_array`, `big_from_be_byte`.
  Domain `BeShortWf`: length `≤ 3`, every byte `≤ 255`. `fromBE < 256^3 < 10^9`,
  one limb (empty if zero). Each step `acc * 256 + b` uses the one-limb
  multiply and add. Not length 4 (`256^4 > 10^9`). Not the 28-byte pad block.
  Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `big_from_be_limb2`, `big_from_be_limb2_array`, `big_add_byte`.
  Domain `BeLimb2Wf`: length `≤ 7`, every byte `≤ 255`. `fromBE < 256^7 < 10^18`,
  at most two limbs. A prefix of length `≤ 3` is still one limb; the fourth
  byte may carry. Each step is the proved one-limb or two-limb multiply by
  256 (product below `10^18`) plus `big_add_byte`. Not length 8
  (`256^8 > 10^18`). Not the 28-byte pad block. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_limb`, `peel_leading_factorial`.
  Domain: `d ≤ 12` and `n < 10^9`. `d!` is one limb, and so is every quotient
  of `n`. Generated `peel_leading` returns `(n % d!, n / d!)`. The digit is
  positive when `d! ≤ n`; peeling `d!` itself yields `(0, 1)`. Not `d ≥ 13`
  (a positive digit times a two-limb factorial). Not `51!`. Not `phi_chunk`.
  Not `phi_inv`.

  CLOSED: `big_factorial_two`, `big_mul_two`. Domain `n ≤ 19`. `12!` is one
  limb. `13!` through `19!` are two limbs (`19! < 10^18`); each step multiplies
  that accumulator by `i ≤ 19` and the product stays below `10^18`. `20!` is
  three limbs. Not `51!`.

  CLOSED: `peel_leading_zero_two`, `peel_leading_zero_digit_two`. Domain
  `d ≤ 19` on the zero bigint. The factoradic digit is `0 / d! = 0`. The
  closing multiply is the zero coefficient times `d!` (two limbs for `d ≥ 13`),
  which short-circuits. Not a positive rank. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_factorial_two`, `divmod_sq`, `big_mul_one`.
  Domain `d ≤ 19`: peeling `d!` yields digit `1` and remainder `0`
  (`d! / d!`). For `d ≥ 13` the factorial is two limbs. `divmod_sq` divides
  any value below `10^18` by a positive one-limb divisor. The closing product
  is the digit `1` times that factorial. Not an arbitrary positive two-limb
  rank. Not `20!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `big_factorial_three`, `big_mul_three`, `big_mul_three_limbs`.
  Domain `n ≤ 20`. `12!` is one limb; `13!` through `19!` are two limbs.
  `20! = 19! · 20` is the first three-limb factorial
  (`10^18 ≤ 20! < 10^27`). `big_mul_three` is the two-limb × one-limb product
  whose third limb is nonzero. Not `21!` (that multiplies a three-limb
  accumulator). Not `51!`. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `big_factorial_acc3`, `big_mul_acc3`, `big_mul_acc3_limbs`.
  Domain `n ≤ 26`. `21!` through `26!` multiply a three-limb accumulator by
  a one-limb factor `i ≤ 26`. The product stays below `10^27`, so the fourth
  scratch limb is zero. Not `27!` (four limbs). Not `51!`. Not `phi_chunk`.
  Not `phi_inv`.

  CLOSED: `peel_leading_factorial_three`, `divmod_cube`, `big_mul_one_three`.
  Domain `d ≤ 26`: peeling `d!` yields digit `1` and remainder `0`
  (`d! / d!`). For `d ≥ 20` the factorial is three limbs
  (`10^18 ≤ 20!` and `26! < 10^27`). `divmod_cube` divides any value below
  `10^27` by a positive one-limb divisor. The closing product is the digit
  `1` times that factorial. Not an arbitrary positive three-limb rank.
  Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_zero_three`, `peel_leading_zero_digit_three`.
  Domain `d ≤ 26` on the zero bigint. The factoradic digit is `0 / d! = 0`
  and the remainder is `0`. For `d ≥ 20` the factorial is three limbs; the
  closing multiply is the zero coefficient, which short-circuits. Not a
  positive rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_below`, `peel_leading_below_digit`, `mag_sub_zero_right`.
  Domain `n < d!` and `d ≤ 26`. The factoradic digit is `n / d! = 0` and the
  remainder is `n`. For `13 ≤ d` a positive rank `10^9 ≤ n < d!` is two limbs;
  for `20 ≤ d` a rank `10^18 ≤ n < d!` is three limbs (`26! < 10^27`).
  `divmod_cube` divides each prefix quotient. The closing multiply is the
  zero coefficient, and `mag_sub` copies the rank. Not `d!` itself (digit `1`).
  Not an arbitrary rank `n ≥ d!`. Not a positive digit. Not `27!`. Not `51!`.
  Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_one`, `peel_leading_one_digit`, `mag_sub_two_le`.
  Domain `d! ≤ n < 2·d!` and `d ≤ 19`. The factoradic digit is `1` and the
  remainder is `n - d!`. For `13 ≤ d` the rank is two limbs (`2·19! < 10^18`);
  the remainder may be positive, so this is not the pure `d!` corner.
  `mag_sub` may borrow. Not `d ≥ 20`. Not a digit `q ≥ 2`. Not `27!`.
  Not `51!`. Not `phi_chunk`. Not `phi_inv`.

  CLOSED: `peel_leading_one_three`, `peel_leading_one_three_digit`,
  `mag_sub_three_le`. Domain `d! ≤ n < 2·d!` and `d ≤ 26`. The factoradic
  digit is `1` and the remainder is `n - d!`, which may be positive.
  For `20 ≤ d` the rank and `d!` are three limbs (`2·26! < 10^27`);
  `mag_sub` may borrow. `d ≤ 19` reuses the two-limb theorem. Not a digit
  `q ≥ 2`. Not `n ≥ 2·d!`. Not `27!`. Not `51!`. Not `phi_chunk`.
  Not `phi_inv`.

  OPEN: full `v_Hash` refinement. `phi_chunk` / `phi_inv` are still open
  (a positive chunk still peels `d!` up to `51!`, and the pad block is 28
  bytes; zero peel and the strict-below peel reach `d ≤ 26`, peeling `d!`
  itself yields digit `1` through `d ≤ 26`, digit `1` on `[d!, 2·d!)` reaches
  `d ≤ 26` (three limbs from `d ≥ 20`, positive remainder allowed), and
  `big_factorial` reaches `26!`, not `27!` and not 51;
  `big_from_be` reaches length `≤ 7`, not the 28-byte pad block). A digit
  `q ≥ 2` on a multi-limb rank is still open. Positive `range_list`
  (`0 < n`, `FitsLen`, including 52) is already `range_list_refines` in
  `EvenRank.lean`. A positive corner or edge rank is outside this limb fragment.
-/

end MegaDreifach.Link2
