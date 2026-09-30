/-
  Real key schedule: the light half of
  `generated_encrypt_realKey_not_v10Sym_equivariant`
  (the heavy kernel witnesses live in `DoubleDealSecurityHeavy.RealKey`).

  `realE m = encryptDeckFn m (List.range 52)` is the model encrypt under ONE
  master key, the identity deck, expanded by the real PassKey chain
  (`passKeyIter`), exactly as `Doubledeal.encrypt` does (`Link2.encrypt_refines`).

  - The relabellings that commute with a fixed deck map on all decks are closed
    under composition, so under powers (`commutesOnDecks_pow`).
  - v10Sym is `ℤ/13 × (ℤ/2)²` (not cyclic; v9Sym was `ℤ/52`). Every nontrivial
    element has a power equal to `v10Sym 1 0` (order 13) or one of the three
    involutions `v10Sym 0 x` (`v10Sym_iter_hits`, kernel `decide!`, cheap). So
    four witnesses cover all 51 (v9 needed two).
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

/-! ## Every nontrivial v10Sym has a power in {v10Sym 1 0, v10Sym 0 x}

`v10Sym` is `ℤ/13 × (ℤ/2)²`: for `x ≠ 0` the 13th power of `v10Sym a x` is the
involution `v10Sym 0 x`; for `x = 0` a power of `v10Sym a 0` is `v10Sym 1 0`.
So four witnesses cover all 51 (`checks/realkeys/v10sym_subgroup.py`). -/

/-- Inverse of `a` mod 13 (`0 ↦ 0`), as a table. -/
def inv13 : List Nat := [0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12]

/-- Exponent taking `v10Sym a x` to its witness. -/
def v10SymWitnessExp (a : Fin 13) (x : Fin 4) : Nat :=
  if x.val = 0 then inv13.getD a.val 0 else 13

/-- The witness reached: `v10Sym 1 0` if `x = 0`, else `v10Sym 0 x`. -/
def v10SymWitness (x : Fin 4) : Fin 13 × Fin 4 :=
  if x.val = 0 then (1, 0) else (0, x)

/-- (PROVED, kernel `decide!`) -/
theorem v10Sym_iter_hits : ∀ (a : Fin 13) (x : Fin 4), (a, x) ≠ (0, 0) →
    ∀ c, (v10SymFn a x)^[v10SymWitnessExp a x] c =
      v10SymFn (v10SymWitness x).1 (v10SymWitness x).2 c := by
  decide!

/-- (PROVED) If a nontrivial `v10Sym a x` commutes with a deck map on all decks,
    then so does its witness (`v10Sym 1 0` or `v10Sym 0 x`). -/
theorem commutesOnDecks_v10Sym_reduce {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (a : Fin 13) (x : Fin 4) (hax : (a, x) ≠ (0, 0)) (h : CommutesOnDecks (v10Sym a x) F) :
    CommutesOnDecks (v10Sym (v10SymWitness x).1 (v10SymWitness x).2) F := by
  have hn := commutesOnDecks_pow h (v10SymWitnessExp a x)
  have e : v10Sym a x ^ v10SymWitnessExp a x =
      v10Sym (v10SymWitness x).1 (v10SymWitness x).2 :=
    Equiv.ext fun c => by rw [Equiv.Perm.coe_pow]; exact v10Sym_iter_hits a x hax c
  exact e ▸ hn

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

-- `idDeck` is in `Decks.lean`, `isDeck_idDeck` in `Relabel.lean`.

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
