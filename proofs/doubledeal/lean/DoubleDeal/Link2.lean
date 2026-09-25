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
  This drop: full passkey induction glue. On the well-formed domain,
  `Generated.passkey` equals algebraic `passToKeyCutFallback` for every
  well-formed length (`passkey_refines`), via residual stepper
  `passkey_step_eq` / `passkey_inlined_cut_eq` and
  `passkey_eq_twin_loop`. Nested suit-rotate after `dsimp` is the emitted
  shape; `passkeyStepGen` is the sequential twin, not a second algorithm.

  NEXT: `passkey_inv` (same twin / `runLoopOn` pattern; needed before
  injectivity transfers onto `Except Trap`). Encrypt refinement stays
  after that; S3/S4 transfer after that.

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
