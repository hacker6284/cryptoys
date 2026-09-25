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

namespace DoubleDeal.Link2

/-!
  This drop: full `passkey_inv` glue. On the well-formed domain,
  `Generated.passkey_inv` equals algebraic `passToKeyCutFallbackInv`
  (`passkey_inv_refines`), via residual stepper `passkey_inv_step_eq`
  and `passkey_inv_eq_twin_loop`. Nested undo-cut / suit-rotate after
  `dsimp` is the emitted shape; `passkeyInvStepGen` is the sequential
  twin, not a second algorithm. Reuses #26/#28 `runLoopOn` /
  `right_rotate_refines`. Algebraic correctness only — not bit-security.

  NEXT: encrypt refinement (same well-formed domain). S3/S4 Except Trap
  transfer rides on the two passkey glues after that.

  ```
  theorem encrypt_refines (message key : List Nat)
      (hm : message.length = 52) (hk : Perm52 key) :
      Doubledeal.encrypt (embed message) (embed key)
        = .ok (embed (encryptDeck message key))
  ```

  Needs helper refinements for compose / unkeyed / mix_columns / expand_keys
  on top of glued `passkey` / `passkey_inv`. Stay on the well-formed domain
  (length 52, Trap does not fire). Still not emitter soundness.
-/

end DoubleDeal.Link2
