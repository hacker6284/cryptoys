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

  OPEN: full `v_Hash` refinement. `phi_chunk` / `phi_inv` are still open
  (`peel_leading` still builds `d!` up to `51!`). Positive `range_list`
  (`0 < n`, `FitsLen`, including 52) is already `range_list_refines` in
  `EvenRank.lean`. A positive corner or edge rank is outside this limb fragment.
-/

end MegaDreifach.Link2
