/-
  LINK 2. Algebraic MegaDreifach ≃ Generated on the pad domain.

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

namespace MegaDreifach.Link2

/-!
  CLOSED: `pad_z_refines`, `pad_message_refines`, `pad_message_refines_array`.
  Domain `PadWf`: every byte `≤ 255`, and `8 * length` fits in an i64
  (`FitsBitlen`). Generated `pad_message` equals algebraic `pad`.

  OPEN: full `v_Hash` refinement. Scramble is next, not this slice.
-/

end MegaDreifach.Link2
