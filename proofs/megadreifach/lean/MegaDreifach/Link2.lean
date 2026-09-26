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

  OPEN: full `v_Hash` refinement.
-/

end MegaDreifach.Link2
