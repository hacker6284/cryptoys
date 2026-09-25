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
import DoubleDeal.Link2.PassKey

namespace DoubleDeal.Link2

/-!
  NEXT (not this PR): general `passkey_refines` on every well-formed list
  (length ≤ 1 is `passkey_refines_nil_and_singleton`). Needs one generated
  PassKey step ≃ `passKeyStep`, then induction on `passKeyGoN`.

  NEXT (not this PR): encrypt refinement on the Fin-52 / Perm52 domain.

  ```
  theorem encrypt_refines (message key : List Nat)
      (hm : message.length = 52) (hk : Perm52 key) :
      Doubledeal.encrypt (embed message) (embed key)
        = .ok (embed (encryptDeck message key))
  ```

  Needs helper refinements for compose / unkeyed / mix_columns / expand_keys
  on top of `passkey_refines`. Stay on the well-formed domain (length 52,
  Trap does not fire). Still not emitter soundness.
-/

end DoubleDeal.Link2
