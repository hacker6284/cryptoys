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
import DoubleDeal.Link2.PassKeyTransfer

namespace DoubleDeal.Link2

/-!
  This drop: S3/S4 on `Except Trap`. Emitted `Doubledeal.passkey` and
  `Doubledeal.passkey_inv` inherit card-multiset preservation, mutual
  inversion, and injectivity on `FitsLen` / `WellFormed`
  (`passkey_perm`, `passkey_inv_perm`, `passkey_leftInverse`,
  `passkey_rightInverse`, `passkey_injective`, `passkey_inv_injective`,
  and the `WellFormed` Array forms). The proofs ride `passkey_refines`
  and `passkey_inv_refines`. Algebraic Link 2 only — not bit-security.

  OPEN: MegaDreifach / Scramble algebraic ≃ Generated. Not CBC-HMAC.
-/

end DoubleDeal.Link2
