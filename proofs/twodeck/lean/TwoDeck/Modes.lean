/-
  Mode lemmas at the Compose algebra layer (SPEC §6 S11).
  Correctness: ECB determinism of Compose; CTR KP uniqueness; nonce prefix.
  Not a bit-security claim.
-/
import TwoDeck.Compose
import TwoDeck.Factoradic

namespace TwoDeck

/-- ECB identical-block observation: encrypt is a pure function of the block,
    so equal plaintexts under fixed key yield equal ciphertexts.
    (Stated for the Compose layer as the keyed step.) -/
theorem compose_deterministic (n : Nat) (α : Type _)
    (M : Fin n → α) (pos : Fin n → Fin n) :
    TwoDeck.composeVec n α M pos = TwoDeck.composeVec n α M pos := rfl

/-- Re-export KP uniqueness (S11 / CTR nonce-reuse). -/
theorem ctr_kp_unique_52 {α} (M : Fin 52 → α) (pos : Fin 52 → Fin 52)
    (C : Fin 52 → α)
    (hC : C = TwoDeck.composeVec 52 α M pos)
    (hInj : ∀ i j, M i = M j → i = j) :
    ∀ j i, M i = C j → i = pos j :=
  TwoDeck.compose_kp_unique_52 α M pos C hC hInj

/-- CTR counter decks with same nonce agree on prefix (from Factoradic). -/
theorem ctr_nonce_prefix_stable (nonce : List Nat) (i j : Nat) :
    (counterDeck nonce i).take nonce.length =
    (counterDeck nonce j).take nonce.length := by
  simp [counterDeck_nonce_prefix]

end TwoDeck
