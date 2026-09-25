/-
  LINK 2 (start). Proof-only refinement: algebraic DoubleDeal ≃ Generated
  Doubledeal on the well-formed domain.

  Not emitter soundness (Link 1 stays trusted-not-proved).
  Not bit-security, MDS, collision-resistance, or AEAD security.
  Do not edit lean/Generated/. Sudo remains normative.

  See proofs/LINK2.md.
-/
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.PassKey
import DoubleDeal.Link2.PassKeyInv
import DoubleDeal.Link2.Encrypt

namespace DoubleDeal.Link2

/-!
  This drop: encrypt refinement on the well-formed domain.
  `Generated.encrypt` equals algebraic `encryptDeck` / `encrypt6`
  (`encrypt_refines`) when the message has length 52, every card id is
  `CardBound` (so `step_seat` does not Trap), and the key is `Perm52`.
  The bridge is the same twin `runLoopOn` used for passkey (#26/#28/#30):
  lay / sum / shift / scoop, `mix_columns_refines`, `full_round_refines`,
  `final_round_refines`. Algebraic Link 2 only — not bit-security.

  OPEN: S3/S4 Except Trap transfer. Not MegaDreifach, Scramble, or
  CBC-HMAC.
-/

end DoubleDeal.Link2
