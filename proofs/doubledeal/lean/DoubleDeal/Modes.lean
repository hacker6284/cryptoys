/-
  Mode lemmas at the Compose algebra layer (SPEC §6 S11).
  Correctness: ECB determinism of Compose; CTR KP uniqueness; nonce prefix.
  Not a bit-security claim.
-/
import DoubleDeal.Compose
import DoubleDeal.Factoradic

namespace DoubleDeal

/-- ECB identical-block observation at the Compose layer: equal messages
    under the same `pos` give equal ciphertexts. -/
theorem compose_ecb_equal_blocks {n : Nat} {α : Type _}
    {M₁ M₂ : Fin n → α} (pos : Fin n → Fin n) (h : M₁ = M₂) :
    DoubleDeal.composeVec n α M₁ pos = DoubleDeal.composeVec n α M₂ pos :=
  h ▸ rfl

/-- Re-export KP uniqueness (S11 / CTR nonce-reuse). -/
theorem ctr_kp_unique_52 {α} (M : Fin 52 → α) (pos : Fin 52 → Fin 52)
    (C : Fin 52 → α)
    (hC : C = DoubleDeal.composeVec 52 α M pos)
    (hInj : ∀ i j, M i = M j → i = j) :
    ∀ j i, M i = C j → i = pos j :=
  DoubleDeal.compose_kp_unique_52 α M pos C hC hInj

/-- CTR counter decks with same nonce agree on prefix (from Factoradic). -/
theorem ctr_nonce_prefix_stable (nonce : List Nat) (i j : Nat) :
    (counterDeck nonce i).take nonce.length =
    (counterDeck nonce j).take nonce.length := by
  simp [counterDeck_nonce_prefix]

end DoubleDeal
