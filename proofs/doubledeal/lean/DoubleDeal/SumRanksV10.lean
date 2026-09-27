/-
  v10 SumRanks (SPEC §3.3): chained, position-aware rows and GF(4) suit columns.
  Correctness only (zero sorry): the forward and inverse maps undo each other.

  Rows turn in the order 1, 2, 3, 0; row `i` turns left by a function `rt` of
  row `i - 1` as it is at that moment. Columns turn in the order 1, …, 12, 0;
  column `j` turns top→bottom by `ct (column j-1) (column j)`. The generic
  chain (`sumRanksChain rt ct`) is invertible for any `rt` and any `ct` whose
  value does not change when column `j` itself is rotated (`OwnInvariant`).
  The cipher uses `rowTurnV10` / `colTurnV10` (sudo `row_turn`, `column_turn`).
-/
import DoubleDeal.Basic
import DoubleDeal.SumRanks

namespace DoubleDeal

theorem rotL_zero (xs : List α) : rotL xs 0 = xs := by
  unfold rotL; split <;> simp

theorem rotR_zero (xs : List α) : rotR xs 0 = xs := by
  unfold rotR; split <;> simp

/-! ## One row / one column -/

/-- Row `i` rotated left by `k`; every other row unchanged. -/
def turnRow (g : Grid α) (i : Fin 4) (k : Nat) : Grid α :=
  rowRotate g (fun r => if r = i then k else 0)

def turnRowBack (g : Grid α) (i : Fin 4) (k : Nat) : Grid α :=
  rowRotateInv g (fun r => if r = i then k else 0)

/-- Column `j` rotated top→bottom by `k`; every other column unchanged. -/
def turnCol (g : Grid α) (j : Fin 13) (k : Nat) : Grid α :=
  colRotate g (fun c => if c = j then k else 0)

def turnColBack (g : Grid α) (j : Fin 13) (k : Nat) : Grid α :=
  colRotateInv g (fun c => if c = j then k else 0)

theorem turnRowBack_turnRow (g : Grid α) (i : Fin 4) (k : Nat) :
    turnRowBack (turnRow g i k) i k = g := rowRotateInv_rowRotate _ _

theorem turnRow_turnRowBack (g : Grid α) (i : Fin 4) (k : Nat) :
    turnRow (turnRowBack g i k) i k = g := rowRotate_rowRotateInv _ _

theorem turnColBack_turnCol (g : Grid α) (j : Fin 13) (k : Nat) :
    turnColBack (turnCol g j k) j k = g := colRotateInv_colRotate _ _

theorem turnCol_turnColBack (g : Grid α) (j : Fin 13) (k : Nat) :
    turnCol (turnColBack g j k) j k = g := colRotate_colRotateInv _ _

theorem turnRow_other (g : Grid α) (i : Fin 4) (k : Nat) {r : Fin 4} (h : r ≠ i) :
    turnRow g i k r = g r := by
  unfold turnRow rowRotate
  exact (ofList13_eq _ (length_toList13 _) (by
    show rotL _ (if r = i then k else 0) = _
    rw [if_neg h, rotL_zero])).trans (ofList13_toList13 _)

theorem turnRowBack_other (g : Grid α) (i : Fin 4) (k : Nat) {r : Fin 4} (h : r ≠ i) :
    turnRowBack g i k r = g r := by
  unfold turnRowBack rowRotateInv
  exact (ofList13_eq _ (length_toList13 _) (by
    show rotR _ (if r = i then k else 0) = _
    rw [if_neg h, rotR_zero])).trans (ofList13_toList13 _)

theorem turnCol_other (g : Grid α) (j : Fin 13) (k : Nat) (r : Fin 4) {c : Fin 13} (h : c ≠ j) :
    turnCol g j k r c = g r c := by
  unfold turnCol colRotate
  simp only [if_neg h, rotR_zero, ofList4_toList4]

theorem turnColBack_other (g : Grid α) (j : Fin 13) (k : Nat) (r : Fin 4) {c : Fin 13}
    (h : c ≠ j) :
    turnColBack g j k r c = g r c := by
  unfold turnColBack colRotateInv
  simp only [if_neg h, rotL_zero, ofList4_toList4]

/-- Column `c` read top to bottom. -/
def column (g : Grid α) (c : Fin 13) : Fin 4 → α := fun r => g r c

/-- A column rotated top→bottom / bottom→top by `k`. -/
def rotDown (y : Fin 4 → α) (k : Nat) : Fin 4 → α :=
  ofList4 (rotR (toList4 y) k) (by rw [length_rotR, length_toList4])

def rotUp (y : Fin 4 → α) (k : Nat) : Fin 4 → α :=
  ofList4 (rotL (toList4 y) k) (by rw [length_rotL, length_toList4])

theorem column_turnCol (g : Grid α) (j : Fin 13) (k : Nat) :
    column (turnCol g j k) j = rotDown (column g j) k := by
  funext r
  unfold column turnCol colRotate rotDown
  simp only [↓reduceIte]

theorem column_turnColBack (g : Grid α) (j : Fin 13) (k : Nat) :
    column (turnColBack g j k) j = rotUp (column g j) k := by
  funext r
  unfold column turnColBack colRotateInv rotUp
  simp only [↓reduceIte]

def prevRow (i : Fin 4) : Fin 4 := ⟨(i.val + 3) % 4, Nat.mod_lt _ (by decide)⟩
def prevCol (j : Fin 13) : Fin 13 := ⟨(j.val + 12) % 13, Nat.mod_lt _ (by decide)⟩

theorem prevRow_ne : ∀ i : Fin 4, prevRow i ≠ i := by decide
theorem prevCol_ne : ∀ j : Fin 13, prevCol j ≠ j := by decide

/-! ## Chained steps (generic turn functions) -/

section Chain
variable (rt : (Fin 13 → α) → Nat) (ct : (Fin 4 → α) → (Fin 4 → α) → Nat)

/-- Row `i` turns by `rt` of row `i - 1`. -/
def rowStep (g : Grid α) (i : Fin 4) : Grid α := turnRow g i (rt (g (prevRow i)))
def rowStepBack (g : Grid α) (i : Fin 4) : Grid α := turnRowBack g i (rt (g (prevRow i)))

/-- Column `j` turns by `ct (column j-1) (column j)`. -/
def colStep (g : Grid α) (j : Fin 13) : Grid α :=
  turnCol g j (ct (column g (prevCol j)) (column g j))
def colStepBack (g : Grid α) (j : Fin 13) : Grid α :=
  turnColBack g j (ct (column g (prevCol j)) (column g j))

/-- The column turn ignores how its own column is rotated. -/
def OwnInvariant : Prop :=
  ∀ (p y : Fin 4 → α) (k : Nat), ct p (rotDown y k) = ct p y ∧ ct p (rotUp y k) = ct p y

theorem rowStepBack_rowStep (g : Grid α) (i : Fin 4) :
    rowStepBack rt (rowStep rt g i) i = g := by
  unfold rowStepBack rowStep
  rw [turnRow_other _ _ _ (prevRow_ne i)]
  exact turnRowBack_turnRow _ _ _

theorem rowStep_rowStepBack (g : Grid α) (i : Fin 4) :
    rowStep rt (rowStepBack rt g i) i = g := by
  unfold rowStepBack rowStep
  rw [turnRowBack_other _ _ _ (prevRow_ne i)]
  exact turnRow_turnRowBack _ _ _

theorem column_prev_turnCol (g : Grid α) (j : Fin 13) (k : Nat) :
    column (turnCol g j k) (prevCol j) = column g (prevCol j) := by
  funext r; exact turnCol_other g j k r (prevCol_ne j)

theorem column_prev_turnColBack (g : Grid α) (j : Fin 13) (k : Nat) :
    column (turnColBack g j k) (prevCol j) = column g (prevCol j) := by
  funext r; exact turnColBack_other g j k r (prevCol_ne j)

theorem colStepBack_colStep (hct : OwnInvariant ct) (g : Grid α) (j : Fin 13) :
    colStepBack ct (colStep ct g j) j = g := by
  unfold colStepBack colStep
  rw [column_prev_turnCol, column_turnCol, (hct _ _ _).1]
  exact turnColBack_turnCol _ _ _

theorem colStep_colStepBack (hct : OwnInvariant ct) (g : Grid α) (j : Fin 13) :
    colStep ct (colStepBack ct g j) j = g := by
  unfold colStepBack colStep
  rw [column_prev_turnColBack, column_turnColBack, (hct _ _ _).2]
  exact turnCol_turnColBack _ _ _

/-- Rows after `n` steps of the forward order 1, 2, 3, 0. -/
def rowsDone (g : Grid α) : Nat → Grid α
  | 0 => g
  | n + 1 => rowStep rt (rowsDone g n) ⟨(n + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- Rows after `n` steps of the inverse order 0, 3, 2, 1. -/
def rowsUndo (g : Grid α) : Nat → Grid α
  | 0 => g
  | n + 1 => rowStepBack rt (rowsUndo g n) ⟨(4 - n) % 4, Nat.mod_lt _ (by decide)⟩

/-- Columns after `n` steps of the forward order 1, …, 12, 0. -/
def colsDone (g : Grid α) : Nat → Grid α
  | 0 => g
  | n + 1 => colStep ct (colsDone g n) ⟨(n + 1) % 13, Nat.mod_lt _ (by decide)⟩

/-- Columns after `n` steps of the inverse order 0, 12, …, 1. -/
def colsUndo (g : Grid α) : Nat → Grid α
  | 0 => g
  | n + 1 => colStepBack ct (colsUndo g n) ⟨(13 - n) % 13, Nat.mod_lt _ (by decide)⟩

/-- Chained SumRanks: all rows, then all columns. -/
def sumRanksChain (g : Grid α) : Grid α := colsDone ct (rowsDone rt g 4) 13

/-- Inverse: columns in reverse order, then rows in reverse order. -/
def invSumRanksChain (g : Grid α) : Grid α := rowsUndo rt (colsUndo ct g 13) 4

theorem rowsUndo_rowsDone (g : Grid α) :
    ∀ k, k ≤ 4 → rowsUndo rt (rowsDone rt g 4) k = rowsDone rt g (4 - k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, 4 - k = m + 1 := ⟨3 - k, by omega⟩
    have hidx : (⟨(4 - k) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
        ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by simp only [hm])
    show rowStepBack rt (rowsUndo rt (rowsDone rt g 4) k) _ = _
    rw [ih (by omega), hidx, hm]
    show rowStepBack rt (rowStep rt (rowsDone rt g m) _) _ = _
    rw [rowStepBack_rowStep, show 4 - (k + 1) = m by omega]

theorem rowsDone_rowsUndo (g : Grid α) :
    ∀ k, k ≤ 4 → rowsDone rt (rowsUndo rt g 4) k = rowsUndo rt g (4 - k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, 4 - k = m + 1 := ⟨3 - k, by omega⟩
    have hidx : (⟨(k + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
        ⟨(4 - m) % 4, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by
          show (k + 1) % 4 = (4 - m) % 4
          rw [show 4 - m = k + 1 by omega])
    show rowStep rt (rowsDone rt (rowsUndo rt g 4) k) _ = _
    rw [ih (by omega), hidx, hm]
    show rowStep rt (rowStepBack rt (rowsUndo rt g m) _) _ = _
    rw [rowStep_rowStepBack, show 4 - (k + 1) = m by omega]

theorem colsUndo_colsDone (hct : OwnInvariant ct) (g : Grid α) :
    ∀ k, k ≤ 13 → colsUndo ct (colsDone ct g 13) k = colsDone ct g (13 - k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, 13 - k = m + 1 := ⟨12 - k, by omega⟩
    have hidx : (⟨(13 - k) % 13, Nat.mod_lt _ (by decide)⟩ : Fin 13) =
        ⟨(m + 1) % 13, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by simp only [hm])
    show colStepBack ct (colsUndo ct (colsDone ct g 13) k) _ = _
    rw [ih (by omega), hidx, hm]
    show colStepBack ct (colStep ct (colsDone ct g m) _) _ = _
    rw [colStepBack_colStep ct hct, show 13 - (k + 1) = m by omega]

theorem colsDone_colsUndo (hct : OwnInvariant ct) (g : Grid α) :
    ∀ k, k ≤ 13 → colsDone ct (colsUndo ct g 13) k = colsUndo ct g (13 - k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, 13 - k = m + 1 := ⟨12 - k, by omega⟩
    have hidx : (⟨(k + 1) % 13, Nat.mod_lt _ (by decide)⟩ : Fin 13) =
        ⟨(13 - m) % 13, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by
          show (k + 1) % 13 = (13 - m) % 13
          rw [show 13 - m = k + 1 by omega])
    show colStep ct (colsDone ct (colsUndo ct g 13) k) _ = _
    rw [ih (by omega), hidx, hm]
    show colStep ct (colStepBack ct (colsUndo ct g m) _) _ = _
    rw [colStep_colStepBack ct hct, show 13 - (k + 1) = m by omega]

theorem invSumRanksChain_sumRanksChain (hct : OwnInvariant ct) (g : Grid α) :
    invSumRanksChain rt ct (sumRanksChain rt ct g) = g := by
  unfold invSumRanksChain sumRanksChain
  rw [colsUndo_colsDone ct hct _ 13 (Nat.le_refl _)]
  show rowsUndo rt (rowsDone rt g 4) 4 = g
  rw [rowsUndo_rowsDone rt g 4 (Nat.le_refl _)]
  rfl

theorem sumRanksChain_invSumRanksChain (hct : OwnInvariant ct) (g : Grid α) :
    sumRanksChain rt ct (invSumRanksChain rt ct g) = g := by
  unfold invSumRanksChain sumRanksChain
  rw [rowsDone_rowsUndo rt _ 4 (Nat.le_refl _)]
  show colsDone ct (colsUndo ct g 13) 13 = g
  rw [colsDone_colsUndo ct hct g 13 (Nat.le_refl _)]
  rfl

/-! Cell predicates survive (every step only moves cells). -/

theorem rowsDone_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ n r c, P (rowsDone rt g n r c) := by
  intro n
  induction n with
  | zero => exact hb
  | succ n ih => exact rowRotate_bound P _ _ ih

theorem colsDone_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ n r c, P (colsDone ct g n r c) := by
  intro n
  induction n with
  | zero => exact hb
  | succ n ih => exact colRotate_bound P _ _ ih

theorem rowsUndo_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ n r c, P (rowsUndo rt g n r c) := by
  intro n
  induction n with
  | zero => exact hb
  | succ n ih => exact rowRotateInv_bound P _ _ ih

theorem colsUndo_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ n r c, P (colsUndo ct g n r c) := by
  intro n
  induction n with
  | zero => exact hb
  | succ n ih => exact colRotateInv_bound P _ _ ih

theorem sumRanksChain_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ r c, P (sumRanksChain rt ct g r c) :=
  colsDone_bound ct P _ (rowsDone_bound rt P g hb 4) 13

theorem invSumRanksChain_bound (P : α → Prop) (g : Grid α) (hb : ∀ r c, P (g r c)) :
    ∀ r c, P (invSumRanksChain rt ct g r c) :=
  rowsUndo_bound rt P _ (colsUndo_bound ct P g hb 13) 4

end Chain

/-! ## The v10 turn functions -/

/-- Weighted rank total of the first `n` cells: `Σ_{j<n} (13 - j) · rank`. -/
def rowPref (xs : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rowPref xs n + (13 - n) * rank (xs.getD n 0)

/-- `U(x) = Σ_j (13 - j) · rank(x_j)` (sudo `row_total`). -/
def rowTotal (x : Fin 13 → Nat) : Nat := rowPref (toList13 x) 13

/-- Row turn: `U mod 13` (sudo `row_turn`). -/
def rowTurnV10 (x : Fin 13 → Nat) : Nat := rowTotal x % 13

/-- GF(4) label of a card's suit: clubs 0, hearts w = 2, spades w² = 3, diamonds 1. -/
def suitLabel (c : Nat) : Nat := if suit c = 0 then 0 else suit c % 3 + 1

/-- GF(4) addition on two-bit labels (XOR). -/
def gfAdd (a b : Nat) : Nat := (a % 2 + b % 2) % 2 + 2 * ((a / 2 + b / 2) % 2)

/-- GF(4) multiplication by `w`: 1 → 2 → 3 → 1, 0 fixed. -/
def gfTimesW (x : Nat) : Nat := if x = 0 then 0 else x % 3 + 1

/-- `V(y) = 0·ℓ(y₀) ⊕ ℓ(y₁) ⊕ w ℓ(y₂) ⊕ w² ℓ(y₃)` (sudo `column_value`). -/
def colValue (y : Fin 4 → Nat) : Nat :=
  gfAdd (gfAdd (suitLabel (y 1)) (gfTimesW (suitLabel (y 2))))
    (gfTimesW (gfTimesW (suitLabel (y 3))))

/-- `S(y) = ℓ(y₀) ⊕ ℓ(y₁) ⊕ ℓ(y₂) ⊕ ℓ(y₃)` (sudo `column_suits`). -/
def colSuits (y : Fin 4 → Nat) : Nat :=
  gfAdd (gfAdd (gfAdd (suitLabel (y 0)) (suitLabel (y 1))) (suitLabel (y 2))) (suitLabel (y 3))

/-- Column turn: `V(previous column) ⊕ S(own column)` (sudo `column_turn`). -/
def colTurnV10 (p y : Fin 4 → Nat) : Nat := gfAdd (colValue p) (colSuits y)

/-- v10 SumRanks. -/
def sumRanksV10 : Grid Nat → Grid Nat := sumRanksChain rowTurnV10 colTurnV10
def invSumRanksV10 : Grid Nat → Grid Nat := invSumRanksChain rowTurnV10 colTurnV10

theorem gfAdd_comm (a b : Nat) : gfAdd a b = gfAdd b a := by
  unfold gfAdd; omega

theorem gfAdd_assoc (a b c : Nat) : gfAdd (gfAdd a b) c = gfAdd a (gfAdd b c) := by
  unfold gfAdd; omega

instance : Std.Commutative gfAdd := ⟨gfAdd_comm⟩
instance : Std.Associative gfAdd := ⟨gfAdd_assoc⟩

theorem gfAdd_lt (a b : Nat) : gfAdd a b < 4 := by unfold gfAdd; omega

theorem suitLabel_lt (c : Nat) : suitLabel c < 4 := by
  unfold suitLabel; split <;> omega

theorem gfTimesW_lt (x : Nat) : gfTimesW x < 4 := by
  unfold gfTimesW; split <;> omega

theorem colTurnV10_lt (p y : Fin 4 → Nat) : colTurnV10 p y < 4 := gfAdd_lt _ _

theorem rotDown_cases (y : Fin 4 → α) (k : Nat) :
    (rotDown y k 0 = y 0 ∧ rotDown y k 1 = y 1 ∧
      rotDown y k 2 = y 2 ∧ rotDown y k 3 = y 3) ∨
    (rotDown y k 0 = y 3 ∧ rotDown y k 1 = y 0 ∧
      rotDown y k 2 = y 1 ∧ rotDown y k 3 = y 2) ∨
    (rotDown y k 0 = y 2 ∧ rotDown y k 1 = y 3 ∧
      rotDown y k 2 = y 0 ∧ rotDown y k 3 = y 1) ∨
    (rotDown y k 0 = y 1 ∧ rotDown y k 1 = y 2 ∧
      rotDown y k 2 = y 3 ∧ rotDown y k 3 = y 0) := by
  have hk : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have hr : rotDown y k = rotDown y (k % 4) := by
    unfold rotDown
    apply ofList4_eq
    exact rotR_congr_mod _ (by simp [length_toList4, Nat.mod_mod])
  rw [hr]
  generalize k % 4 = m at hk
  match m, hk with
  | 0, _ => left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 1, _ => right; left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 2, _ => right; right; left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 3, _ => right; right; right; exact ⟨rfl, rfl, rfl, rfl⟩

theorem rotUp_cases (y : Fin 4 → α) (k : Nat) :
    (rotUp y k 0 = y 0 ∧ rotUp y k 1 = y 1 ∧ rotUp y k 2 = y 2 ∧ rotUp y k 3 = y 3) ∨
    (rotUp y k 0 = y 1 ∧ rotUp y k 1 = y 2 ∧ rotUp y k 2 = y 3 ∧ rotUp y k 3 = y 0) ∨
    (rotUp y k 0 = y 2 ∧ rotUp y k 1 = y 3 ∧ rotUp y k 2 = y 0 ∧ rotUp y k 3 = y 1) ∨
    (rotUp y k 0 = y 3 ∧ rotUp y k 1 = y 0 ∧ rotUp y k 2 = y 1 ∧ rotUp y k 3 = y 2) := by
  have hk : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have hr : rotUp y k = rotUp y (k % 4) := by
    unfold rotUp
    apply ofList4_eq
    exact rotL_congr_mod _ (by simp [length_toList4, Nat.mod_mod])
  rw [hr]
  generalize k % 4 = m at hk
  match m, hk with
  | 0, _ => left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 1, _ => right; left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 2, _ => right; right; left; exact ⟨rfl, rfl, rfl, rfl⟩
  | 3, _ => right; right; right; exact ⟨rfl, rfl, rfl, rfl⟩

theorem colSuits_rotDown (y : Fin 4 → Nat) (k : Nat) : colSuits (rotDown y k) = colSuits y := by
  unfold colSuits
  rcases rotDown_cases y k with
    ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
    rw [h0, h1, h2, h3] <;> ac_rfl

theorem colSuits_rotUp (y : Fin 4 → Nat) (k : Nat) : colSuits (rotUp y k) = colSuits y := by
  unfold colSuits
  rcases rotUp_cases y k with
    ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
    rw [h0, h1, h2, h3] <;> ac_rfl

theorem colTurnV10_ownInvariant : OwnInvariant colTurnV10 := fun p y k =>
  ⟨by unfold colTurnV10; rw [colSuits_rotDown], by unfold colTurnV10; rw [colSuits_rotUp]⟩

theorem invSumRanksV10_sumRanksV10 (g : Grid Nat) : invSumRanksV10 (sumRanksV10 g) = g :=
  invSumRanksChain_sumRanksChain rowTurnV10 colTurnV10 colTurnV10_ownInvariant g

theorem sumRanksV10_invSumRanksV10 (g : Grid Nat) : sumRanksV10 (invSumRanksV10 g) = g :=
  sumRanksChain_invSumRanksChain rowTurnV10 colTurnV10 colTurnV10_ownInvariant g

theorem sumRanksV10_bound (P : Nat → Prop) (g : Grid Nat) (hb : ∀ r c, P (g r c)) :
    ∀ r c, P (sumRanksV10 g r c) :=
  sumRanksChain_bound rowTurnV10 colTurnV10 P g hb

theorem invSumRanksV10_bound (P : Nat → Prop) (g : Grid Nat) (hb : ∀ r c, P (g r c)) :
    ∀ r c, P (invSumRanksV10 g r c) :=
  invSumRanksChain_bound rowTurnV10 colTurnV10 P g hb

/-! ## Compiled evaluation (`@[csimp]`)

The chained definitions above build each grid as a closure over the previous
one, so compiled code (the vector-check executable) would recompute earlier
steps on every cell read, exponentially in the number of steps. The `@[csimp]`
lemmas below make compiled code materialise the grid as lists after every step.
They are proved equal, so proofs and the kernel are unaffected. -/

/-- A grid as its four rows. -/
def toRows (g : Grid Nat) : List (List Nat) :=
  [toList13 (g 0), toList13 (g 1), toList13 (g 2), toList13 (g 3)]

/-- Rows back to a grid (`0` pads out-of-range reads). -/
def ofRows (L : List (List Nat)) : Grid Nat := fun r c => (L.getD r.val []).getD c.val 0

theorem getD_toList13_fin (f : Fin 13 → Nat) (c : Fin 13) : (toList13 f).getD c.val 0 = f c := by
  match c with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl

theorem getD_toRows (g : Grid Nat) (r : Fin 4) : (toRows g).getD r.val [] = toList13 (g r) := by
  match r with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl

theorem ofRows_toRows (g : Grid Nat) : ofRows (toRows g) = g := by
  funext r c
  simp only [ofRows, getD_toRows, getD_toList13_fin]

section LL
variable (rt : (Fin 13 → Nat) → Nat) (ct : (Fin 4 → Nat) → (Fin 4 → Nat) → Nat)

def rowsDoneLL (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | n + 1 =>
    toRows (rowStep rt (ofRows (rowsDoneLL L n)) ⟨(n + 1) % 4, Nat.mod_lt _ (by decide)⟩)

def rowsUndoLL (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | n + 1 =>
    toRows (rowStepBack rt (ofRows (rowsUndoLL L n)) ⟨(4 - n) % 4, Nat.mod_lt _ (by decide)⟩)

def colsDoneLL (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | n + 1 =>
    toRows (colStep ct (ofRows (colsDoneLL L n)) ⟨(n + 1) % 13, Nat.mod_lt _ (by decide)⟩)

def colsUndoLL (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | n + 1 =>
    toRows (colStepBack ct (ofRows (colsUndoLL L n))
      ⟨(13 - n) % 13, Nat.mod_lt _ (by decide)⟩)

theorem rowsDone_LL (g : Grid Nat) : ∀ n, rowsDone rt g n = ofRows (rowsDoneLL rt (toRows g) n)
  | 0 => (ofRows_toRows g).symm
  | n + 1 => by rw [rowsDone, rowsDone_LL g n, rowsDoneLL, ofRows_toRows]

theorem rowsUndo_LL (g : Grid Nat) : ∀ n, rowsUndo rt g n = ofRows (rowsUndoLL rt (toRows g) n)
  | 0 => (ofRows_toRows g).symm
  | n + 1 => by rw [rowsUndo, rowsUndo_LL g n, rowsUndoLL, ofRows_toRows]

theorem colsDone_LL (g : Grid Nat) : ∀ n, colsDone ct g n = ofRows (colsDoneLL ct (toRows g) n)
  | 0 => (ofRows_toRows g).symm
  | n + 1 => by rw [colsDone, colsDone_LL g n, colsDoneLL, ofRows_toRows]

theorem colsUndo_LL (g : Grid Nat) : ∀ n, colsUndo ct g n = ofRows (colsUndoLL ct (toRows g) n)
  | 0 => (ofRows_toRows g).symm
  | n + 1 => by rw [colsUndo, colsUndo_LL g n, colsUndoLL, ofRows_toRows]

end LL

/-- `sumRanksV10` with list snapshots (compiled implementation). -/
def sumRanksV10LL (g : Grid Nat) : Grid Nat :=
  -- `toRows (ofRows …)` pads the row lists to a full 4×13 grid.
  ofRows (colsDoneLL colTurnV10 (toRows (ofRows (rowsDoneLL rowTurnV10 (toRows g) 4))) 13)

def invSumRanksV10LL (g : Grid Nat) : Grid Nat :=
  -- `toRows (ofRows …)` pads the row lists to a full 4×13 grid.
  ofRows (rowsUndoLL rowTurnV10 (toRows (ofRows (colsUndoLL colTurnV10 (toRows g) 13))) 4)

@[csimp] theorem sumRanksV10_eq_LL : @sumRanksV10 = @sumRanksV10LL := by
  funext g
  unfold sumRanksV10 sumRanksChain sumRanksV10LL
  rw [rowsDone_LL, colsDone_LL]

@[csimp] theorem invSumRanksV10_eq_LL : @invSumRanksV10 = @invSumRanksV10LL := by
  funext g
  unfold invSumRanksV10 invSumRanksChain invSumRanksV10LL
  rw [colsUndo_LL, rowsUndo_LL]

end DoubleDeal
