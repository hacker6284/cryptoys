/-
  T1 — card relabellings versus the DoubleDeal layers (Mathlib side): basics.

  A relabelling `σ : Equiv.Perm (Fin 52)` permutes card values and acts on every
  card of a deck (value-wise, not positional) through the bridge `Relabel.app`
  on the model's `Nat` cells. All statements in `Relabel`, `SumRanks`,
  `GridCycle`, `Rounds` and `PermKeys` are about the proof-only algebraic model
  (`Round.lean`, `GridCycle.lean`, `SumRanks.lean` in ../lean). The transfer to
  the emitted `Doubledeal.encrypt` (Link 2, `encrypt_refines`) is in
  `Link.lean`. Link 1 (sudo = Generated) stays open.

  There is no `sorry`. The covariant round statement `roundBody_covariant_iff_id` (only the
  identity is covariant for the unkeyed round; a one-round symmetry result, not a security
  bound) is proved in the heavy library (`DoubleDealSecurityHeavy/V10Sym.lean`, finite checks
  by kernel `decide!`; also checked numerically by `checks/check_covariant.py`); the default
  library has the `_of_covariant` reductions (`fullRound_commutes_iff_id_of_covariant`,
  `encrypt6_commutes_iff_id_of_covariant`). `../check_axioms.py security` audits the axioms
  of every theorem in these modules. Structural facts, not a security proof.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Fintype.Card
import DoubleDeal.Round
import DoubleDealSecurity.Decks

namespace DoubleDeal.Security

open DoubleDeal

/-! ## Relabellings -/

/-- A relabelling: a permutation of the card values `0..51` (Mathlib `Equiv.Perm`). -/
abbrev Relabel := Equiv.Perm (Fin 52)

namespace Relabel

/-- Bridge to the model's `Nat` cells: cards `< 52` are relabelled, anything
    else is fixed. -/
def app (σ : Relabel) (n : Nat) : Nat :=
  if h : n < 52 then (σ ⟨n, h⟩).val else n

/-- The transposition of two card values (Mathlib `Equiv.swap`). -/
abbrev swap (a b : Fin 52) : Relabel := Equiv.swap a b

theorem app_fin (σ : Relabel) (c : Fin 52) : σ.app c.val = (σ c).val := by
  simp [app, c.isLt]

theorem app_lt (σ : Relabel) {n : Nat} (h : n < 52) : σ.app n < 52 := by
  simp [app, h]

theorem app_inj (σ : Relabel) {a b : Nat} (h : σ.app a = σ.app b) : a = b := by
  unfold app at h
  by_cases ha : a < 52 <;> by_cases hb : b < 52 <;> simp only [ha, hb, ↓reduceDIte] at h
  · exact congrArg Fin.val (σ.injective (Fin.ext h))
  · have := (σ ⟨a, ha⟩).isLt; omega
  · have := (σ ⟨b, hb⟩).isLt; omega
  · exact h

theorem app_one (n : Nat) : app 1 n = n := by
  unfold app; split <;> rfl

end Relabel

open Relabel

/-- Relabel every card of a deck. -/
def rel (σ : Relabel) (m : Fin 52 → Nat) : Fin 52 → Nat := fun i => σ.app (m i)

theorem rel_one (x : Fin 52 → Nat) : rel 1 x = x := funext fun _ => app_one _

theorem app_mul (σ τ : Relabel) (n : Nat) : (σ * τ).app n = σ.app (τ.app n) := by
  unfold app
  by_cases h : n < 52
  · simp [h, (τ ⟨n, h⟩).isLt, Equiv.Perm.mul_apply]
  · simp [h]

theorem rel_mul (σ τ : Relabel) (m : Fin 52 → Nat) : rel (σ * τ) m = rel σ (rel τ m) :=
  funext fun i => app_mul σ τ (m i)

/-- Relabel every card of a grid. -/
def relG (σ : Relabel) (g : Grid Nat) : Grid Nat := fun r c => σ.app (g r c)

/-- Every cell is a card value. -/
def Cards (m : Fin 52 → Nat) : Prop := ∀ i, m i < 52
def CardsG (g : Grid Nat) : Prop := ∀ r c, g r c < 52

/-- A well-formed deck: 52 distinct card values. -/
def IsDeck (m : Fin 52 → Nat) : Prop := Cards m ∧ Function.Injective m

/-- The identity deck (`Decks.lean`) is a deck. -/
theorem isDeck_idDeck : IsDeck idDeck := ⟨fun i => i.isLt, fun _ _ h => Fin.ext h⟩

/-- A deck as a permutation of `Fin 52`. -/
noncomputable def deckPerm (d : Fin 52 → Nat) (hd : IsDeck d) : Equiv.Perm (Fin 52) :=
  Equiv.ofBijective (fun i => ⟨d i, hd.1 i⟩)
    (Finite.injective_iff_bijective.1 (fun _ _ h => hd.2 (congrArg Fin.val h)))

@[simp] theorem deckPerm_val (d : Fin 52 → Nat) (hd : IsDeck d) (i : Fin 52) :
    (deckPerm d hd i).val = d i := rfl

/-- On a deck `x`, a relabelling is determined by its action: `α·x = β·x` iff `α = β`
    (the deck holds every card). -/
theorem rel_left_inj {x : Fin 52 → Nat} (hx : IsDeck x) {α β : Relabel} :
    rel α x = rel β x ↔ α = β := by
  refine ⟨fun h => Equiv.ext fun c => ?_, fun h => h ▸ rfl⟩
  have hi : x ((deckPerm x hx).symm c) = c.val := by
    rw [← deckPerm_val x hx, Equiv.apply_symm_apply]
  have e := congrFun h ((deckPerm x hx).symm c)
  simp only [rel, hi, app_fin] at e
  exact Fin.ext e

/-- `σ` commutes with a deck map on every card-valued deck. -/
def Commutes (σ : Relabel) (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : Prop :=
  ∀ m, Cards m → F (rel σ m) = rel σ (F m)

/-- `σ` commutes with a deck map on every well-formed deck (weaker hypothesis). -/
def CommutesOnDecks (σ : Relabel) (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : Prop :=
  ∀ m, IsDeck m → F (rel σ m) = rel σ (F m)

def CommutesG (σ : Relabel) (F : Grid Nat → Grid Nat) : Prop :=
  ∀ g, CardsG g → F (relG σ g) = relG σ (F g)

/-- Grid version on well-formed decks (read column-major). -/
def CommutesOnDecksG (σ : Relabel) (F : Grid Nat → Grid Nat) : Prop :=
  ∀ g, IsDeck (scoopColumnMajor g) → F (relG σ g) = relG σ (F g)

/-- The identity relabelling commutes with every deck map. -/
theorem commutesOnDecks_one (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : CommutesOnDecks 1 F :=
  fun m _ => by rw [rel_one, rel_one]

/-- (PROVED) If every cell of the deck `x` occurs in `y`, then `y` is a deck
    too (52 distinct values fill all 52 cells). -/
theorem isDeck_of_cells {x y : Fin 52 → Nat} (hx : IsDeck x) (h : ∀ k, ∃ i, x k = y i) :
    IsDeck y := by
  classical
  choose ρ hρ using h
  have hinj : Function.Injective ρ := fun k k' e => hx.2 (by rw [hρ k, hρ k', e])
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨fun i => ?_, fun i j e => ?_⟩
  · obtain ⟨k, rfl⟩ := hsurj i
    rw [← hρ k]; exact hx.1 k
  · obtain ⟨k, rfl⟩ := hsurj i
    obtain ⟨k', rfl⟩ := hsurj j
    rw [← hρ k, ← hρ k'] at e
    rw [hx.2 e]

theorem Commutes.onDecks {σ F} (h : Commutes σ F) : CommutesOnDecks σ F :=
  fun m hm => h m hm.1

theorem CommutesG.onDecks {σ F} (h : CommutesG σ F) : CommutesOnDecksG σ F := by
  intro g hg
  apply h
  intro r c
  have := hg.1 (cmFlat r c)
  simpa [scoopColumnMajor, (cm_cmFlat r c).1, (cm_cmFlat r c).2] using this

/-! ## Bridge to the cell-map lemmas of `Link.lean` -/

/-- `σ.app` is a card map in the sense of the Link-side transfer theorems. -/
theorem app_cardMap (σ : Relabel) : CardMap σ.app := ⟨fun _ h => σ.app_lt h⟩

/-- A transposition acts on cells as the Link-side `swapNat`. -/
theorem swap_app_eq (a b : Fin 52) : (swap a b).app = swapNat a.val b.val := by
  funext x
  unfold Relabel.app swapNat
  by_cases hx : x < 52
  · simp only [hx, ↓reduceDIte]
    by_cases ha : x = a.val
    · subst ha; simp [Equiv.swap_apply_left]
    · by_cases hb : x = b.val
      · subst hb; simp [Equiv.swap_apply_right, ha]
      · have ha' : (⟨x, hx⟩ : Fin 52) ≠ a := fun e => ha (congrArg Fin.val e)
        have hb' : (⟨x, hx⟩ : Fin 52) ≠ b := fun e => hb (congrArg Fin.val e)
        simp [Equiv.swap_apply_of_ne_of_ne ha' hb', ha, hb]
  · have ha : x ≠ a.val := fun e => hx (e ▸ a.isLt)
    have hb : x ≠ b.val := fun e => hx (e ▸ b.isLt)
    simp [hx, ha, hb]

/-- `swap K♣ K♦` acts on cells as the Link-side `swapNat 12 51`. -/
theorem swap_KC_KD_app : (swap KC KD).app = swapNat 12 51 := swap_app_eq KC KD

theorem cards_firstDeck : Cards (firstDeck 51) := firstDeck_lt

/-! ## 1. Positional layers commute with every relabelling

Compose/AddRoundKey is `C[j] = M[keyPos K j]`: the key only supplies
positions. So the right form is `E_K(σM) = σ E_K(M)` with the key NOT
relabelled. Relabelling the key instead permutes the output positions
(`keyPos_relabel_key` in `Link.lean`), and PassKey is value-dependent, so neither
`E_{σK}(M)` nor `E_{σK}(σM)` is related to `σ E_K(M)` in general. -/

theorem compose_rel (σ : Relabel) (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) :
    composeVec 52 Nat (rel σ m) pos = rel σ (composeVec 52 Nat m pos) := rfl

theorem compose_commutes (σ : Relabel) (pos : Fin 52 → Fin 52) :
    Commutes σ (fun m => composeVec 52 Nat m pos) := fun _ _ => rfl

theorem layColumnMajor_rel (σ : Relabel) (m : Fin 52 → Nat) :
    layColumnMajor (rel σ m) = relG σ (layColumnMajor m) := rfl

theorem scoopColumnMajor_rel (σ : Relabel) (g : Grid Nat) :
    scoopColumnMajor (relG σ g) = rel σ (scoopColumnMajor g) := rfl

theorem layRowMajor_rel (σ : Relabel) (m : Fin 52 → Nat) :
    layRowMajor (rel σ m) = relG σ (layRowMajor m) := rfl

theorem scoopRowMajor_rel (σ : Relabel) (g : Grid Nat) :
    scoopRowMajor (relG σ g) = rel σ (scoopRowMajor g) := rfl

theorem shiftRows_rel (σ : Relabel) (g : Grid Nat) :
    shiftRows (relG σ g) = relG σ (shiftRows g) := rfl

theorem shiftRows_commutes (σ : Relabel) : CommutesG σ shiftRows := fun _ _ => rfl

end DoubleDeal.Security
