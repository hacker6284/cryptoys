/-
  SumRanks / inv SumRanks on 4×13 grids — correctness, zero sorry.
  Row-then-column; inverse undoes columns then rows (SPEC §3.3).
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

def rowRankSum (rank : α → Nat) (g : Grid α) (r : Fin 4) : Nat :=
  rankSum rank (toList13 (g r))

def colRankSum (rank : α → Nat) (g : Grid α) (c : Fin 13) : Nat :=
  rankSum rank (toList4 (fun r => g r c))

theorem rowRankSum_rowRotate (rank : α → Nat) (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) :
    rowRankSum rank (rowRotate g t) r = rowRankSum rank g r := by
  dsimp [rowRankSum, rowRotate]
  rw [toList13_ofList13, rankSum_rotL]

theorem rowRankSum_rowRotateInv (rank : α → Nat) (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) :
    rowRankSum rank (rowRotateInv g t) r = rowRankSum rank g r := by
  dsimp [rowRankSum, rowRotateInv]
  rw [toList13_ofList13, rankSum_rotR]

theorem colRankSum_colRotate (rank : α → Nat) (g : Grid α) (s : Fin 13 → Nat) (c : Fin 13) :
    colRankSum rank (colRotate g s) c = colRankSum rank g c := by
  dsimp [colRankSum, colRotate]
  rw [toList4_ofList4, rankSum_rotR]

theorem colRankSum_colRotateInv (rank : α → Nat) (g : Grid α) (s : Fin 13 → Nat) (c : Fin 13) :
    colRankSum rank (colRotateInv g s) c = colRankSum rank g c := by
  dsimp [colRankSum, colRotateInv]
  rw [toList4_ofList4, rankSum_rotL]

def applyRowRotates (rank : α → Nat) (g : Grid α) : Grid α :=
  rowRotate g (fun r => rowRankSum rank g r)

def applyRowRotatesInv (rank : α → Nat) (g : Grid α) : Grid α :=
  rowRotateInv g (fun r => rowRankSum rank g r)

def applyColRotates (rank : α → Nat) (g : Grid α) : Grid α :=
  colRotate g (fun c => colRankSum rank g c)

def applyColRotatesInv (rank : α → Nat) (g : Grid α) : Grid α :=
  colRotateInv g (fun c => colRankSum rank g c)

def sumRanks (rank : α → Nat) (g : Grid α) : Grid α :=
  applyColRotates rank (applyRowRotates rank g)

def invSumRanks (rank : α → Nat) (g : Grid α) : Grid α :=
  applyRowRotatesInv rank (applyColRotatesInv rank g)

theorem applyRowRotatesInv_applyRowRotates (rank : α → Nat) (g : Grid α) :
    applyRowRotatesInv rank (applyRowRotates rank g) = g := by
  dsimp [applyRowRotatesInv, applyRowRotates]
  have ht : (fun r => rowRankSum rank (rowRotate g (fun r => rowRankSum rank g r)) r) =
            (fun r => rowRankSum rank g r) := by
    funext r; exact rowRankSum_rowRotate rank g _ r
  rw [ht]
  exact rowRotateInv_rowRotate g _

theorem applyColRotatesInv_applyColRotates (rank : α → Nat) (g : Grid α) :
    applyColRotatesInv rank (applyColRotates rank g) = g := by
  dsimp [applyColRotatesInv, applyColRotates]
  have hs : (fun c => colRankSum rank (colRotate g (fun c => colRankSum rank g c)) c) =
            (fun c => colRankSum rank g c) := by
    funext c; exact colRankSum_colRotate rank g _ c
  rw [hs]
  exact colRotateInv_colRotate g _

theorem applyRowRotates_applyRowRotatesInv (rank : α → Nat) (g : Grid α) :
    applyRowRotates rank (applyRowRotatesInv rank g) = g := by
  dsimp [applyRowRotates, applyRowRotatesInv]
  have ht : (fun r => rowRankSum rank (rowRotateInv g (fun r => rowRankSum rank g r)) r) =
            (fun r => rowRankSum rank g r) := by
    funext r; exact rowRankSum_rowRotateInv rank g _ r
  rw [ht]
  exact rowRotate_rowRotateInv g _

theorem applyColRotates_applyColRotatesInv (rank : α → Nat) (g : Grid α) :
    applyColRotates rank (applyColRotatesInv rank g) = g := by
  dsimp [applyColRotates, applyColRotatesInv]
  have hs : (fun c => colRankSum rank (colRotateInv g (fun c => colRankSum rank g c)) c) =
            (fun c => colRankSum rank g c) := by
    funext c; exact colRankSum_colRotateInv rank g _ c
  rw [hs]
  exact colRotate_colRotateInv g _

theorem invSumRanks_sumRanks (rank : α → Nat) (g : Grid α) :
    invSumRanks rank (sumRanks rank g) = g := by
  dsimp [invSumRanks, sumRanks]
  rw [applyColRotatesInv_applyColRotates, applyRowRotatesInv_applyRowRotates]

theorem sumRanks_invSumRanks (rank : α → Nat) (g : Grid α) :
    sumRanks rank (invSumRanks rank g) = g := by
  dsimp [invSumRanks, sumRanks]
  rw [applyRowRotates_applyRowRotatesInv, applyColRotates_applyColRotatesInv]

theorem rankSum_row_invariant (rank : α → Nat) (g : Grid α) (r : Fin 4) :
    rowRankSum rank (applyRowRotates rank g) r = rowRankSum rank g r :=
  rowRankSum_rowRotate rank g _ r

theorem rankSum_col_invariant (rank : α → Nat) (g : Grid α) (c : Fin 13) :
    colRankSum rank (applyColRotates rank g) c = colRankSum rank g c :=
  colRankSum_colRotate rank g _ c

end DoubleDeal
