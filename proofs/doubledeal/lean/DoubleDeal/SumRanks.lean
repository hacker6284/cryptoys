/-
  SumRanks / inv SumRanks on 4×13 grids — correctness, zero sorry.
  Row-then-column; inverse undoes columns then rows (SPEC §3.3).
  Rows and columns take separate weights (`rowW`, `colW`): the cipher uses
  rank for rows and rank + suit for columns. The inverse theorems hold for
  any pair of weights.
-/
import DoubleDeal.Grid
import DoubleDeal.Rotate

namespace DoubleDeal

def toList13 (f : Fin 13 → α) : List α :=
  [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12]

def toList4 (f : Fin 4 → α) : List α :=
  [f 0, f 1, f 2, f 3]

theorem length_toList13 (f : Fin 13 → α) : (toList13 f).length = 13 := rfl
theorem length_toList4 (f : Fin 4 → α) : (toList4 f).length = 4 := rfl

def ofList13 (xs : List α) (h : xs.length = 13) : Fin 13 → α :=
  fun i => xs[i.val]'(by omega)

def ofList4 (xs : List α) (h : xs.length = 4) : Fin 4 → α :=
  fun i => xs[i.val]'(by omega)

theorem getElem_toList13 (f : Fin 13 → α) (i : Fin 13) :
    (toList13 f)[i.val]'(by rw [length_toList13]; exact i.isLt) = f i := by
  revert i; intro ⟨v, hv⟩
  match v with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
  | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl
  | n+13 => omega

theorem getElem_toList4 (f : Fin 4 → α) (i : Fin 4) :
    (toList4 f)[i.val]'(by rw [length_toList4]; exact i.isLt) = f i := by
  revert i; intro ⟨v, hv⟩
  match v with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | n+4 => omega

theorem ofList13_toList13 (f : Fin 13 → α) :
    ofList13 (toList13 f) (length_toList13 f) = f := by
  funext i; exact getElem_toList13 f i

theorem ofList4_toList4 (f : Fin 4 → α) :
    ofList4 (toList4 f) (length_toList4 f) = f := by
  funext i; exact getElem_toList4 f i

theorem toList13_ofList13 (xs : List α) (h : xs.length = 13) :
    toList13 (ofList13 xs h) = xs := by
  apply List.ext_getElem
  · simp [length_toList13, h]
  · intro i hi _
    have hi13 : i < 13 := by simp [h] at hi; exact hi
    simpa [ofList13] using getElem_toList13 (ofList13 xs h) ⟨i, hi13⟩

theorem toList4_ofList4 (xs : List α) (h : xs.length = 4) :
    toList4 (ofList4 xs h) = xs := by
  apply List.ext_getElem
  · simp [length_toList4, h]
  · intro i hi _
    have hi4 : i < 4 := by simp [h] at hi; exact hi
    simpa [ofList4] using getElem_toList4 (ofList4 xs h) ⟨i, hi4⟩

theorem ofList13_eq {xs ys : List α} (hx : xs.length = 13) (hy : ys.length = 13)
    (h : xs = ys) : ofList13 xs hx = ofList13 ys hy := by
  cases h; rfl

theorem ofList4_eq {xs ys : List α} (hx : xs.length = 4) (hy : ys.length = 4)
    (h : xs = ys) : ofList4 xs hx = ofList4 ys hy := by
  cases h; rfl

def rowRotate (g : Grid α) (t : Fin 4 → Nat) : Grid α :=
  fun r => ofList13 (rotL (toList13 (g r)) (t r))
    (by rw [length_rotL, length_toList13])

def rowRotateInv (g : Grid α) (t : Fin 4 → Nat) : Grid α :=
  fun r => ofList13 (rotR (toList13 (g r)) (t r))
    (by rw [length_rotR, length_toList13])

def colRotate (g : Grid α) (s : Fin 13 → Nat) : Grid α :=
  fun r c => ofList4 (rotR (toList4 (fun r' => g r' c)) (s c))
    (by rw [length_rotR, length_toList4]) r

def colRotateInv (g : Grid α) (s : Fin 13 → Nat) : Grid α :=
  fun r c => ofList4 (rotL (toList4 (fun r' => g r' c)) (s c))
    (by rw [length_rotL, length_toList4]) r

theorem rowRotateInv_rowRotate (g : Grid α) (t : Fin 4 → Nat) :
    rowRotateInv (rowRotate g t) t = g := by
  funext r
  have hlist : toList13 (rowRotate g t r) = rotL (toList13 (g r)) (t r) := by
    unfold rowRotate; exact toList13_ofList13 _ _
  unfold rowRotateInv
  have heq : rotR (toList13 (rowRotate g t r)) (t r) = toList13 (g r) := by
    rw [hlist, rotR_rotL]
  rw [ofList13_eq _ (length_toList13 (g r)) heq, ofList13_toList13]

theorem colRotateInv_colRotate (g : Grid α) (s : Fin 13 → Nat) :
    colRotateInv (colRotate g s) s = g := by
  funext r c
  have hlist : toList4 (fun r' => colRotate g s r' c) =
      rotR (toList4 (fun r' => g r' c)) (s c) := by
    unfold colRotate; exact toList4_ofList4 _ _
  unfold colRotateInv
  have heq : rotL (toList4 (fun r' => colRotate g s r' c)) (s c) =
      toList4 (fun r' => g r' c) := by
    rw [hlist, rotL_rotR]
  rw [ofList4_eq _ (length_toList4 (fun r' => g r' c)) heq]
  exact congrFun (ofList4_toList4 (fun r' => g r' c)) r

theorem rowRotate_rowRotateInv (g : Grid α) (t : Fin 4 → Nat) :
    rowRotate (rowRotateInv g t) t = g := by
  funext r
  have hlist : toList13 (rowRotateInv g t r) = rotR (toList13 (g r)) (t r) := by
    unfold rowRotateInv; exact toList13_ofList13 _ _
  unfold rowRotate
  have heq : rotL (toList13 (rowRotateInv g t r)) (t r) = toList13 (g r) := by
    rw [hlist, rotL_rotR]
  rw [ofList13_eq _ (length_toList13 (g r)) heq, ofList13_toList13]

theorem colRotate_colRotateInv (g : Grid α) (s : Fin 13 → Nat) :
    colRotate (colRotateInv g s) s = g := by
  funext r c
  have hlist : toList4 (fun r' => colRotateInv g s r' c) =
      rotL (toList4 (fun r' => g r' c)) (s c) := by
    unfold colRotateInv; exact toList4_ofList4 _ _
  unfold colRotate
  have heq : rotR (toList4 (fun r' => colRotateInv g s r' c)) (s c) =
      toList4 (fun r' => g r' c) := by
    rw [hlist, rotR_rotL]
  rw [ofList4_eq _ (length_toList4 (fun r' => g r' c)) heq]
  exact congrFun (ofList4_toList4 (fun r' => g r' c)) r

def rowWeightSum (w : α → Nat) (g : Grid α) (r : Fin 4) : Nat :=
  weightSum w (toList13 (g r))

def colWeightSum (w : α → Nat) (g : Grid α) (c : Fin 13) : Nat :=
  weightSum w (toList4 (fun r => g r c))

theorem rowWeightSum_rowRotate (w : α → Nat) (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) :
    rowWeightSum w (rowRotate g t) r = rowWeightSum w g r := by
  dsimp [rowWeightSum, rowRotate]
  rw [toList13_ofList13, weightSum_rotL]

theorem rowWeightSum_rowRotateInv (w : α → Nat) (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) :
    rowWeightSum w (rowRotateInv g t) r = rowWeightSum w g r := by
  dsimp [rowWeightSum, rowRotateInv]
  rw [toList13_ofList13, weightSum_rotR]

theorem colWeightSum_colRotate (w : α → Nat) (g : Grid α) (s : Fin 13 → Nat) (c : Fin 13) :
    colWeightSum w (colRotate g s) c = colWeightSum w g c := by
  dsimp [colWeightSum, colRotate]
  rw [toList4_ofList4, weightSum_rotR]

theorem colWeightSum_colRotateInv (w : α → Nat) (g : Grid α) (s : Fin 13 → Nat) (c : Fin 13) :
    colWeightSum w (colRotateInv g s) c = colWeightSum w g c := by
  dsimp [colWeightSum, colRotateInv]
  rw [toList4_ofList4, weightSum_rotL]

def applyRowRotates (w : α → Nat) (g : Grid α) : Grid α :=
  rowRotate g (fun r => rowWeightSum w g r)

def applyRowRotatesInv (w : α → Nat) (g : Grid α) : Grid α :=
  rowRotateInv g (fun r => rowWeightSum w g r)

def applyColRotates (w : α → Nat) (g : Grid α) : Grid α :=
  colRotate g (fun c => colWeightSum w g c)

def applyColRotatesInv (w : α → Nat) (g : Grid α) : Grid α :=
  colRotateInv g (fun c => colWeightSum w g c)

/-- Row stage by `rowW` sums, then column stage by `colW` sums. -/
def sumRanks (rowW colW : α → Nat) (g : Grid α) : Grid α :=
  applyColRotates colW (applyRowRotates rowW g)

def invSumRanks (rowW colW : α → Nat) (g : Grid α) : Grid α :=
  applyRowRotatesInv rowW (applyColRotatesInv colW g)

theorem applyRowRotatesInv_applyRowRotates (w : α → Nat) (g : Grid α) :
    applyRowRotatesInv w (applyRowRotates w g) = g := by
  dsimp [applyRowRotatesInv, applyRowRotates]
  have ht : (fun r => rowWeightSum w (rowRotate g (fun r => rowWeightSum w g r)) r) =
            (fun r => rowWeightSum w g r) := by
    funext r; exact rowWeightSum_rowRotate w g _ r
  rw [ht]
  exact rowRotateInv_rowRotate g _

theorem applyColRotatesInv_applyColRotates (w : α → Nat) (g : Grid α) :
    applyColRotatesInv w (applyColRotates w g) = g := by
  dsimp [applyColRotatesInv, applyColRotates]
  have hs : (fun c => colWeightSum w (colRotate g (fun c => colWeightSum w g c)) c) =
            (fun c => colWeightSum w g c) := by
    funext c; exact colWeightSum_colRotate w g _ c
  rw [hs]
  exact colRotateInv_colRotate g _

theorem applyRowRotates_applyRowRotatesInv (w : α → Nat) (g : Grid α) :
    applyRowRotates w (applyRowRotatesInv w g) = g := by
  dsimp [applyRowRotates, applyRowRotatesInv]
  have ht : (fun r => rowWeightSum w (rowRotateInv g (fun r => rowWeightSum w g r)) r) =
            (fun r => rowWeightSum w g r) := by
    funext r; exact rowWeightSum_rowRotateInv w g _ r
  rw [ht]
  exact rowRotate_rowRotateInv g _

theorem applyColRotates_applyColRotatesInv (w : α → Nat) (g : Grid α) :
    applyColRotates w (applyColRotatesInv w g) = g := by
  dsimp [applyColRotates, applyColRotatesInv]
  have hs : (fun c => colWeightSum w (colRotateInv g (fun c => colWeightSum w g c)) c) =
            (fun c => colWeightSum w g c) := by
    funext c; exact colWeightSum_colRotateInv w g _ c
  rw [hs]
  exact colRotate_colRotateInv g _

theorem invSumRanks_sumRanks (rowW colW : α → Nat) (g : Grid α) :
    invSumRanks rowW colW (sumRanks rowW colW g) = g := by
  dsimp [invSumRanks, sumRanks]
  rw [applyColRotatesInv_applyColRotates, applyRowRotatesInv_applyRowRotates]

theorem sumRanks_invSumRanks (rowW colW : α → Nat) (g : Grid α) :
    sumRanks rowW colW (invSumRanks rowW colW g) = g := by
  dsimp [invSumRanks, sumRanks]
  rw [applyRowRotates_applyRowRotatesInv, applyColRotates_applyColRotatesInv]

theorem weightSum_row_invariant (w : α → Nat) (g : Grid α) (r : Fin 4) :
    rowWeightSum w (applyRowRotates w g) r = rowWeightSum w g r :=
  rowWeightSum_rowRotate w g _ r

theorem weightSum_col_invariant (w : α → Nat) (g : Grid α) (c : Fin 13) :
    colWeightSum w (applyColRotates w g) c = colWeightSum w g c :=
  colWeightSum_colRotate w g _ c


/-! ## Cell predicates survive the rotations

Rotations only move cells, so any predicate that holds on every cell of the
input holds on every cell of the output. -/

theorem rowRotate_bound (P : α → Prop) (g : Grid α) (t : Fin 4 → Nat)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (rowRotate g t r c) := by
  intro r c
  unfold rowRotate ofList13
  have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
  have hget := rotL_get_eq (toList13 (g r)) (t r) c.val hne c.isLt
  rw [hget]
  simp only [length_toList13]
  have hj : (c.val + t r % 13) % 13 < 13 := Nat.mod_lt _ (by decide)
  rw [getElem_toList13 (g r) ⟨(c.val + t r % 13) % 13, hj⟩]
  exact hb r ⟨(c.val + t r % 13) % 13, hj⟩

theorem colRotate_bound (P : α → Prop) (g : Grid α) (s : Fin 13 → Nat)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (colRotate g s r c) := by
  intro r c
  unfold colRotate ofList4
  have hne : (toList4 (fun r' => g r' c)).length ≠ 0 := by simp [length_toList4]
  have hget := getElem_rotR (toList4 (fun r' => g r' c)) (s c) r.val hne r.isLt
  rw [hget]
  have hj : (r.val + (4 - s c % 4)) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcell := getElem_toList4 (fun r' => g r' c) ⟨(r.val + (4 - s c % 4)) % 4, hj⟩
  simpa [length_toList4, hcell] using hb ⟨(r.val + (4 - s c % 4)) % 4, hj⟩ c

theorem applyRowRotates_bound (P : α → Prop) (w : α → Nat) (g : Grid α)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (applyRowRotates w g r c) :=
  rowRotate_bound P g _ hb

theorem applyColRotates_bound (P : α → Prop) (w : α → Nat) (g : Grid α)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (applyColRotates w g r c) :=
  colRotate_bound P g _ hb

theorem sumRanks_bound (P : α → Prop) (rowW colW : α → Nat) (g : Grid α)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (sumRanks rowW colW g r c) :=
  applyColRotates_bound P colW _ (applyRowRotates_bound P rowW g hb)

end DoubleDeal
