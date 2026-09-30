/-
  GridCycle parity write-up (deprecated DoubleDeal v10 only).

  A kernel-checked single-deck witness: on the recorded packet `deck`, the
  transposition sigma = K♣↔K♦ commutes with the emitted frozen v10
  `mix_columns` (GridCycle):

      mix_columns (sigma · deck) = sigma · mix_columns deck,

  and sigma really moves the output (it is not the identity on it). Each
  `mix_columns` evaluation is checked by `decide!` (kernel reduction), never
  the compiler-trusting tactic.

  Scope: this is ONE deck. It illustrates the per-layer measurement in
  ../README.md (K♣↔K♦ survives v10 GridCycle on about 26% of uniform decks);
  it is not a probability bound and not an attack on the full cipher.
-/
import Doubledeal_v10
import DoubleDealV10.WitnessData

namespace DoubleDealV10.Witness

set_option maxRecDepth 100000

/-- `decide!` states facts about `Except` through `toOption` (`SudoRt.Trap` has no
    `DecidableEq`); this turns them back into `= .ok`. -/
theorem ok_of_toOption {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-- `deck` is a deck: 52 distinct card ids below 52. -/
theorem deck_is_deck : deck.length = 52 ∧ deck.Nodup ∧ ∀ x ∈ deck, x < 52 := by decide

/-- The JSON's sigma-images are sigma applied pointwise. -/
theorem deckSigma_eq : deckSigmaJson = deck.map sw := by decide
theorem mixSigma_eq : mixSigmaJson = mix.map sw := by decide

/-- Emitted v10 GridCycle on `deck` (kernel evaluation). -/
theorem mix_columns_deck : Doubledeal_v10.mix_columns (embed deck) = .ok (embed mix) :=
  ok_of_toOption (by decide!)

/-- Emitted v10 GridCycle on sigma · `deck` (kernel evaluation). -/
theorem mix_columns_deck_sigma :
    Doubledeal_v10.mix_columns (embed deckSigmaJson) = .ok (embed mixSigmaJson) :=
  ok_of_toOption (by decide!)

/-- sigma moves the output: both swapped cards are in it. -/
theorem sigma_moves_mix : mix.map sw ≠ mix := by decide

/-- **Headline.** On `deck`, K♣↔K♦ commutes with the emitted frozen v10 GridCycle,
    and the relation is not trivial. -/
theorem v10_KC_KD_swap_commutes_with_gridcycle :
    Doubledeal_v10.mix_columns (embed (deck.map sw)) = .ok (embed (mix.map sw)) ∧
      Doubledeal_v10.mix_columns (embed deck) = .ok (embed mix) ∧
      mix.map sw ≠ mix := by
  refine ⟨?_, mix_columns_deck, sigma_moves_mix⟩
  rw [← deckSigma_eq, ← mixSigma_eq]
  exact mix_columns_deck_sigma

end DoubleDealV10.Witness
