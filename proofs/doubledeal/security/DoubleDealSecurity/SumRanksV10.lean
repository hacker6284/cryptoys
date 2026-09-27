/-
  T1 for v10 SumRanks (SPEC §3.3, `DoubleDeal.sumRanksV10`).

  PROVED ("if" direction only): the 52 relabellings `v10Sym a x` — rank index
  `+a (mod 13)` and GF(4) suit label `⊕ x` — commute with v10 SumRanks on
  every card-valued grid. Why: a rank shift adds `a · (13 + 12 + … + 1) = 91 a
  ≡ 0 (mod 13)` to every row total; a label shift adds `x ⊕ x ⊕ x ⊕ x = 0` to
  every column's own suit sum and `(1 ⊕ w ⊕ w²) x = 0` to the previous
  column's weighted value.

  The converse (these are the only relabellings that commute on decks) is
  proved in `SumRanksV10Iff.lean`: `sumRanksV10_commutes_iff`.
  The group is `ℤ/13 × (ℤ/2)²`, not cyclic (v9's was `ℤ/52`).
-/
import DoubleDealSecurity.SumRanks
import Mathlib.Tactic.Ring

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## The group `v10Sym` -/

/-- GF(4) label → suit index (inverse of `suitLabel` on suits):
    0 → ♣ (0), 1 → ♦ (3), 2 → ♥ (1), 3 → ♠ (2). -/
def suitOfLabel (l : Nat) : Nat := if l = 0 then 0 else (l + 1) % 3 + 1

/-- `v10Sym a x`: rank index `+a (mod 13)`, suit label `⊕ x`. -/
def v10SymFn (a : Fin 13) (x : Fin 4) (c : Fin 52) : Fin 52 :=
  ⟨13 * (suitOfLabel (gfAdd (suitLabel c.val) x.val) % 4) + (c.val % 13 + a.val) % 13, by omega⟩

theorem v10SymFn_left : ∀ (a : Fin 13) (x : Fin 4) (c : Fin 52),
    v10SymFn (neg13 a) x (v10SymFn a x c) = c := by decide!

theorem v10SymFn_right : ∀ (a : Fin 13) (x : Fin 4) (c : Fin 52),
    v10SymFn a x (v10SymFn (neg13 a) x c) = c := by decide!

def v10Sym (a : Fin 13) (x : Fin 4) : Relabel where
  toFun := v10SymFn a x
  invFun := v10SymFn (neg13 a) x
  left_inv := v10SymFn_left a x
  right_inv := v10SymFn_right a x

theorem v10SymFn_rank : ∀ (a : Fin 13) (x : Fin 4) (c : Fin 52),
    cardRank (v10SymFn a x c).val % 13 = (cardRank c.val + a.val) % 13 := by decide!

theorem v10SymFn_label : ∀ (a : Fin 13) (x : Fin 4) (c : Fin 52),
    suitLabel (v10SymFn a x c).val = gfAdd (suitLabel c.val) x.val := by decide!

theorem v10SymFn_fixed : ∀ (a : Fin 13) (x : Fin 4) (c : Fin 52),
    v10SymFn a x c = c → a = 0 ∧ x = 0 := by decide!

theorem v10SymFn_zero (c : Fin 52) : v10SymFn 0 0 c = c := by
  revert c; decide!

theorem v10Sym_app_rank (a : Fin 13) (x : Fin 4) {n : Nat} (h : n < 52) :
    rank ((v10Sym a x).app n) % 13 = (rank n + a.val) % 13 := by
  have := v10SymFn_rank a x ⟨n, h⟩
  rw [show n = (⟨n, h⟩ : Fin 52).val from rfl, app_fin]
  exact this

theorem v10Sym_app_label (a : Fin 13) (x : Fin 4) {n : Nat} (h : n < 52) :
    suitLabel ((v10Sym a x).app n) = gfAdd (suitLabel n) x.val := by
  have := v10SymFn_label a x ⟨n, h⟩
  rw [show n = (⟨n, h⟩ : Fin 52).val from rfl, app_fin]
  exact this

/-! ## Row turns are invariant under a rank shift -/

/-- `Σ_{j<n} (13 - j)`; `rowWeightTotal 13 = 91 = 7 · 13`. -/
def rowWeightTotal : Nat → Nat
  | 0 => 0
  | n + 1 => rowWeightTotal n + (13 - n)

theorem rowPref_shift (xs ys : List Nat) (a : Nat)
    (h : ∀ j, j < 13 → rank (ys.getD j 0) % 13 = (rank (xs.getD j 0) + a) % 13) :
    ∀ n, n ≤ 13 → rowPref ys n % 13 = (rowPref xs n + a * rowWeightTotal n) % 13 := by
  intro n hn
  induction n with
  | zero => simp [rowPref, rowWeightTotal]
  | succ n ih =>
    have ih := ih (by omega)
    simp only [rowPref, rowWeightTotal]
    have e1 : (13 - n) * rank (ys.getD n 0) % 13 = (13 - n) * (rank (xs.getD n 0) + a) % 13 := by
      rw [Nat.mul_mod, h n (by omega), ← Nat.mul_mod]
    calc (rowPref ys n + (13 - n) * rank (ys.getD n 0)) % 13
        = (rowPref ys n % 13 + (13 - n) * rank (ys.getD n 0) % 13) % 13 := Nat.add_mod _ _ _
      _ = ((rowPref xs n + a * rowWeightTotal n) % 13 +
            (13 - n) * (rank (xs.getD n 0) + a) % 13) % 13 := by rw [ih, e1]
      _ = (rowPref xs n + a * rowWeightTotal n + (13 - n) * (rank (xs.getD n 0) + a)) % 13 :=
            (Nat.add_mod _ _ _).symm
      _ = (rowPref xs n + (13 - n) * rank (xs.getD n 0) +
            a * (rowWeightTotal n + (13 - n))) % 13 := by congr 1; ring

theorem getD_toList13_map (x : Fin 13 → Nat) (f : Nat → Nat) (j : Nat) (hj : j < 13) :
    (toList13 (fun i => f (x i))).getD j 0 = f ((toList13 x).getD j 0) := by
  match j, hj with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl
  | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl

theorem getD_toList13_lt (x : Fin 13 → Nat) (hx : ∀ j, x j < 52) (j : Nat) (hj : j < 13) :
    (toList13 x).getD j 0 < 52 := by
  match j, hj with
  | 0, _ => exact hx _ | 1, _ => exact hx _ | 2, _ => exact hx _ | 3, _ => exact hx _
  | 4, _ => exact hx _ | 5, _ => exact hx _ | 6, _ => exact hx _ | 7, _ => exact hx _
  | 8, _ => exact hx _ | 9, _ => exact hx _ | 10, _ => exact hx _ | 11, _ => exact hx _
  | 12, _ => exact hx _

theorem rowTurnV10_rel (a : Fin 13) (x : Fin 4) (row : Fin 13 → Nat) (hrow : ∀ j, row j < 52) :
    rowTurnV10 (fun j => (v10Sym a x).app (row j)) = rowTurnV10 row := by
  unfold rowTurnV10 rowTotal
  have hs := rowPref_shift (toList13 row) (toList13 (fun j => (v10Sym a x).app (row j))) a.val
    (fun j hj => by
      rw [getD_toList13_map row _ j hj]
      exact v10Sym_app_rank a x (getD_toList13_lt row hrow j hj)) 13 (Nat.le_refl _)
  have h91 : rowWeightTotal 13 = 91 := rfl
  rw [hs, h91]
  omega

/-! ## Column turns are invariant under a label shift -/

theorem colValue_core : ∀ l1, l1 < 4 → ∀ l2, l2 < 4 → ∀ l3, l3 < 4 → ∀ x, x < 4 →
    gfAdd (gfAdd (gfAdd l1 x) (gfTimesW (gfAdd l2 x))) (gfTimesW (gfTimesW (gfAdd l3 x))) =
      gfAdd (gfAdd l1 (gfTimesW l2)) (gfTimesW (gfTimesW l3)) := by decide

theorem colSuits_core : ∀ l0, l0 < 4 → ∀ l1, l1 < 4 → ∀ l2, l2 < 4 → ∀ l3, l3 < 4 →
    ∀ x, x < 4 →
    gfAdd (gfAdd (gfAdd (gfAdd l0 x) (gfAdd l1 x)) (gfAdd l2 x)) (gfAdd l3 x) =
      gfAdd (gfAdd (gfAdd l0 l1) l2) l3 := by decide

theorem colValue_rel (a : Fin 13) (x : Fin 4) (p : Fin 4 → Nat) (hp : ∀ r, p r < 52) :
    colValue (fun r => (v10Sym a x).app (p r)) = colValue p := by
  unfold colValue
  simp only [v10Sym_app_label a x (hp _)]
  exact colValue_core _ (suitLabel_lt _) _ (suitLabel_lt _) _ (suitLabel_lt _) _ x.isLt

theorem colSuits_rel (a : Fin 13) (x : Fin 4) (y : Fin 4 → Nat) (hy : ∀ r, y r < 52) :
    colSuits (fun r => (v10Sym a x).app (y r)) = colSuits y := by
  unfold colSuits
  simp only [v10Sym_app_label a x (hy _)]
  exact colSuits_core _ (suitLabel_lt _) _ (suitLabel_lt _) _ (suitLabel_lt _) _ (suitLabel_lt _)
    _ x.isLt

theorem colTurnV10_rel (a : Fin 13) (x : Fin 4) (p y : Fin 4 → Nat)
    (hp : ∀ r, p r < 52) (hy : ∀ r, y r < 52) :
    colTurnV10 (fun r => (v10Sym a x).app (p r)) (fun r => (v10Sym a x).app (y r)) =
      colTurnV10 p y := by
  unfold colTurnV10
  rw [colValue_rel a x p hp, colSuits_rel a x y hy]

/-! ## Generic: invariant turn functions make the chain commute -/

theorem turnRow_rel (σ : Relabel) (g : Grid Nat) (i : Fin 4) (k : Nat) :
    turnRow (relG σ g) i k = relG σ (turnRow g i k) :=
  rowRotate_rel σ g _ _ (fun _ => rfl)

theorem turnCol_rel (σ : Relabel) (g : Grid Nat) (j : Fin 13) (k : Nat) :
    turnCol (relG σ g) j k = relG σ (turnCol g j k) :=
  colRotate_rel σ g _ _ (fun _ => rfl)

theorem sumRanksChain_commutes (σ : Relabel) (rt : (Fin 13 → Nat) → Nat)
    (ct : (Fin 4 → Nat) → (Fin 4 → Nat) → Nat)
    (hrt : ∀ row : Fin 13 → Nat, (∀ j, row j < 52) → rt (fun j => σ.app (row j)) = rt row)
    (hct : ∀ p y : Fin 4 → Nat, (∀ r, p r < 52) → (∀ r, y r < 52) →
      ct (fun r => σ.app (p r)) (fun r => σ.app (y r)) = ct p y) :
    CommutesG σ (sumRanksChain rt ct) := by
  intro g hg
  have hrows : ∀ n, rowsDone rt (relG σ g) n = relG σ (rowsDone rt g n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show rowStep rt (rowsDone rt (relG σ g) n) _ = relG σ (rowStep rt (rowsDone rt g n) _)
      rw [ih]
      unfold rowStep
      have hb := rowsDone_bound rt (· < 52) g hg n
      rw [show relG σ (rowsDone rt g n) (prevRow _) =
          fun j => σ.app (rowsDone rt g n (prevRow _) j) from rfl,
        hrt _ (fun j => hb _ j)]
      exact turnRow_rel σ _ _ _
  have hcols : ∀ h : Grid Nat, CardsG h → ∀ n,
      colsDone ct (relG σ h) n = relG σ (colsDone ct h n) := by
    intro h hh n
    induction n with
    | zero => rfl
    | succ n ih =>
      show colStep ct (colsDone ct (relG σ h) n) _ = relG σ (colStep ct (colsDone ct h n) _)
      rw [ih]
      unfold colStep
      have hb := colsDone_bound ct (· < 52) h hh n
      rw [show column (relG σ (colsDone ct h n)) (prevCol _) =
          fun r => σ.app (column (colsDone ct h n) (prevCol _) r) from rfl,
        show column (relG σ (colsDone ct h n)) _ =
          fun r => σ.app (column (colsDone ct h n) _ r) from rfl,
        hct (column (colsDone ct h n) (prevCol _)) (column (colsDone ct h n) _)
          (fun r => hb r _) (fun r => hb r _)]
      exact turnCol_rel σ _ _ _
  unfold sumRanksChain
  rw [hrows 4, hcols _ (rowsDone_bound rt (· < 52) g hg 4) 13]

/-- **v10 SumRanks, "if"** (PROVED): every `v10Sym a x` commutes with v10
    SumRanks on every card-valued grid. The converse is
    `v10Sym_of_sumRanksV10_commutes` (`SumRanksV10Iff.lean`). -/
theorem sumRanksV10_commutes_v10Sym (a : Fin 13) (x : Fin 4) :
    CommutesG (v10Sym a x) sumRanksV10 :=
  sumRanksChain_commutes _ _ _ (rowTurnV10_rel a x) (colTurnV10_rel a x)

end DoubleDeal.Security
