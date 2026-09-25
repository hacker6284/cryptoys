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

namespace DoubleDeal.Link2

/-!
  This drop: `left_rotate` ≃ `rotL`; one PassKey step ≃ `passKeyStep`;
  induction of the proof-side twin loop (`passkey_loop_refines`,
  `passkey_twin_refines`). Length ≤ 1 still ties `Doubledeal.passkey` itself
  (`passkey_refines_nil_and_singleton`). Connecting the emitted residual
  stepper to `passkeyStepGen` (do-elaboration / nested suit-rotate) is OPEN.

  NEXT: that residual glue, then `passkey_inv`, then encrypt on Fin-52.

  ```
  theorem encrypt_refines (message key : List Nat)
      (hm : message.length = 52) (hk : Perm52 key) :
      Doubledeal.encrypt (embed message) (embed key)
        = .ok (embed (encryptDeck message key))
  ```

  Needs helper refinements for compose / unkeyed / mix_columns / expand_keys
  on top of a glued `passkey_refines`. Stay on the well-formed domain
  (length 52, Trap does not fire). Still not emitter soundness.
-/

end DoubleDeal.Link2
