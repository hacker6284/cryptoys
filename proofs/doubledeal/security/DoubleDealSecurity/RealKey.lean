/-
  Real key schedule: the light half of
  `generated_encrypt_realKey_not_v9Sym_equivariant`
  (the heavy kernel witnesses live in `DoubleDealSecurityHeavy.RealKey`).

  `realE m = encryptDeckFn m (List.range 52)` is the model encrypt under ONE
  master key, the identity deck, expanded by the real PassKey chain
  (`passKeyIter`), exactly as `Doubledeal.encrypt` does (`Link2.encrypt_refines`).

  - The relabellings that commute with a fixed deck map on all decks are closed
    under composition, so under powers (`commutesOnDecks_pow`).
  - v9Sym is cyclic of order 52. Every nontrivial element has a power equal to
    `v9Sym 0 2` (the unique involution) or `v9Sym 1 0` (order 13)
    (`v9Sym_iter_hits`, kernel `decide!`, cheap). So two witnesses cover all 51.
  - `commutesOnDecks_realE_of_generated` pulls commutation back from the
    emitted `Doubledeal.encrypt` to the model (`generated_encrypt_relabel_iff`).
-/
import DoubleDealSecurity.PermKeys
import DoubleDealSecurity.Link
import Batteries.Data.Array.OfFn
import Mathlib.Data.List.OfFn

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## Commuting relabellings are closed under composition -/

theorem commutesOnDecks_mul {σ τ : Relabel} {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (hσ : CommutesOnDecks σ F) (hτ : CommutesOnDecks τ F) : CommutesOnDecks (σ * τ) F := by
  intro m hm
  rw [rel_mul, hσ _ (isDeck_rel τ hm), hτ m hm, rel_mul]

theorem commutesOnDecks_pow {σ : Relabel} {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (h : CommutesOnDecks σ F) : ∀ n : Nat, CommutesOnDecks (σ ^ n) F
  | 0 => by rw [pow_zero]; exact commutesOnDecks_one F
  | n + 1 => by rw [pow_succ']; exact commutesOnDecks_mul h (commutesOnDecks_pow h n)

/-! ## Every nontrivial v9Sym has a power in {v9Sym 0 2, v9Sym 1 0} -/

/-- Exponent for `v9Sym a b`, at index `4 a + b` (from `checks/realkeys/v9sym_subgroup.py`). -/
def v9SymWitnessExp : List Nat :=
  [0, 2, 1, 2, 1, 26, 13, 26, 7, 20, 13, 20, 9, 26, 13, 26, 10, 26, 10, 26, 8, 8, 8, 8,
   11, 24, 13, 24, 2, 26, 2, 26, 5, 26, 13, 26, 3, 16, 13, 16, 4, 4, 4, 4, 6, 26, 6, 26,
   12, 12, 12, 12]

/-- (PROVED, kernel `decide!`) -/
theorem v9Sym_iter_hits : ∀ (a : Fin 13) (b : Fin 4), (a, b) ≠ (0, 0) →
    (∀ c, (v9SymFn a b)^[v9SymWitnessExp.getD (4 * a.val + b.val) 0] c = v9SymFn 0 2 c) ∨
    (∀ c, (v9SymFn a b)^[v9SymWitnessExp.getD (4 * a.val + b.val) 0] c = v9SymFn 1 0 c) := by
  decide!

/-- (PROVED) If a nontrivial `v9Sym a b` commutes with a deck map on all decks,
    then so does `v9Sym 0 2` or `v9Sym 1 0`. -/
theorem commutesOnDecks_v9Sym_reduce {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (a : Fin 13) (b : Fin 4) (hab : (a, b) ≠ (0, 0)) (h : CommutesOnDecks (v9Sym a b) F) :
    CommutesOnDecks (v9Sym 0 2) F ∨ CommutesOnDecks (v9Sym 1 0) F := by
  have hn := commutesOnDecks_pow h (v9SymWitnessExp.getD (4 * a.val + b.val) 0)
  have key : ∀ τ : Relabel, (∀ c, (v9SymFn a b)^[v9SymWitnessExp.getD (4 * a.val + b.val) 0] c = τ c) →
      CommutesOnDecks τ F := by
    intro τ hw
    have e : v9Sym a b ^ v9SymWitnessExp.getD (4 * a.val + b.val) 0 = τ :=
      Equiv.ext fun c => by rw [Equiv.Perm.coe_pow]; exact hw c
    exact e ▸ hn
  exact (v9Sym_iter_hits a b hab).imp (key _) (key _)

/-! ## The real schedule under the identity master key -/

/-- Model encrypt under the identity master key and the real PassKey schedule. -/
def realE (m : Fin 52 → Nat) : Fin 52 → Nat := encryptDeckFn m (List.range 52)

theorem perm52_toDeck {m : Fin 52 → Nat} (hm : IsDeck m) : Perm52 (toDeck m) where
  length := length_toDeck m
  nodup := by
    simp only [toDeck, Array.toList_ofFn]
    exact List.nodup_ofFn.mpr hm.2
  bounded := by
    intro x hx
    simp only [toDeck, Array.toList_ofFn, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hm.1 i
  complete := by
    intro j
    obtain ⟨i, hi⟩ := (deckPerm m hm).surjective j
    simp only [toDeck, Array.toList_ofFn, List.mem_ofFn]
    exact ⟨i, by simpa using congrArg Fin.val hi⟩

/-- (PROVED) If the emitted `Doubledeal.encrypt` under the identity master key
    commutes with σ on every deck message, the model `realE` commutes with σ on
    all decks. -/
theorem commutesOnDecks_realE_of_generated (σ : Relabel)
    (H : ∀ message : List Nat, Perm52 message →
      Doubledeal.encrypt (Link2.embed (message.map σ.app)) (Link2.embed (List.range 52)) =
        .ok (Link2.embed ((encryptDeck message (List.range 52)).map σ.app))) :
    CommutesOnDecks σ realE := by
  intro m hm
  have hp := perm52_toDeck hm
  have h := (generated_encrypt_relabel_iff σ (toDeck m) (List.range 52) (length_toDeck m)
    perm52_range (fun x hx => hp.bounded x hx)).1 (H _ hp)
  simpa only [realE, Link2.ofDeck_toDeck] using h

/-! ## Witness plumbing (the heavy library supplies the kernel evaluations) -/

/-- The identity deck `A♣, 2♣, …, K♦`. -/
def idDeck : Fin 52 → Nat := fun i => i.val

theorem isDeck_idDeck : IsDeck idDeck := ⟨fun i => i.isLt, fun _ _ h => Fin.ext h⟩

theorem realE_toDeck (m : Fin 52 → Nat) :
    toDeck (realE m) = encryptDeck (toDeck m) (List.range 52) := by
  rw [encryptDeck_eq_encryptDeckFn _ _ (length_toDeck m), Link2.ofDeck_toDeck]; rfl

theorem not_commutesOnDecks_of_witness (σ : Relabel)
    (h : encryptDeck (toDeck (rel σ idDeck)) (List.range 52) ≠
      (encryptDeck (toDeck idDeck) (List.range 52)).map σ.app) :
    ¬ CommutesOnDecks σ realE := by
  intro hc
  apply h
  rw [← realE_toDeck, ← realE_toDeck, hc idDeck isDeck_idDeck]
  exact toDeck_map σ.app (realE idDeck)

end DoubleDeal.Security
