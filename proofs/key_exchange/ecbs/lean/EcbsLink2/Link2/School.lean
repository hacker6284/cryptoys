/-
  One schoolbook row: lay `first` from hole `i`, columns `0 .. n`, mirroring when `mir`.
  The six inlined copies in `Ecbs.mul` are this loop. Proof-only.
-/
import EcbsLink2.Link2.Loop
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def withMoves (b : Ecbs.Board) (m : Int) : Ecbs.Board :=
  { b with sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_5moves := m } }

/-- Columns `0 .. k` of one schoolbook row, starting from `strip`. -/
def rowAt (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) : Nat → List Nat
  | 0 => strip
  | k + 1 => schoolStep a i mir (rowAt a i mir strip k) k

theorem rowAt_zero (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) :
    rowAt a i mir strip 0 = strip := by
  rfl

theorem rowAt_succ (a : List Nat) (i mirK : Nat) (mir : Bool) (strip : List Nat) :
    rowAt a i mir strip (mirK + 1) = schoolStep a i mir (rowAt a i mir strip mirK) mirK := by
  rfl

theorem rowAt_eq_foldl (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) (k : Nat) :
    rowAt a i mir strip k = (List.range k).foldl (fun s j => schoolStep a i mir s j) strip := by
  induction k with
  | zero => simp [rowAt, List.range_zero]
  | succ k ih =>
    rw [rowAt_succ, List.range_succ, List.foldl_append, ih]
    simp

theorem schoolRow_eq_rowAt (n : Nat) (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) :
    schoolRow n a i mir strip = rowAt a i mir strip n := by
  unfold schoolRow
  exact (rowAt_eq_foldl a i mir strip n).symm

/-- How many of the first `k` coefficients of `a` are nonzero. Each one is a move. -/
def laidCount (a : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => laidCount a k + if coeff a k = 0 then 0 else 1

theorem laidCount_zero (a : List Nat) : laidCount a 0 = 0 := rfl

theorem laidCount_succ (a : List Nat) (k : Nat) :
    laidCount a (k + 1) = laidCount a k + if coeff a k = 0 then 0 else 1 := rfl

def allTritList (xs : List Nat) : Prop := ∀ x ∈ xs, x ≤ 2

theorem trit_get {xs : List Nat} (h : allTritList xs) {j : Nat} (hj : j < xs.length) :
    xs[j] ≤ 2 := h xs[j] (List.getElem_mem hj)

theorem embed_set (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    (embed xs).set ⟨i, by rw [size_embed]; exact h⟩ (Int.ofNat v) = embed (xs.set i v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro j hj hj'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem modI_three (a : Nat) :
    SudoRt.modI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a % 3)) :=
  modI_ofNat a (by decide)

private theorem coeff_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    coeff xs j = xs[j] := by
  unfold coeff
  simp [hj]

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_id (b : Ecbs.Board)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) :
    withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

private theorem flipTrit_le {c : Nat} (h : c ≤ 2) : flipTrit c ≤ 2 := by
  have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases this with h0 | h1 | h2
  · simp [flipTrit, h0]
  · simp [flipTrit, h1]
  · simp [flipTrit, h2]

private theorem tritAdd_le (a b : Nat) : tritAdd a b ≤ 2 := by
  unfold tritAdd
  have : (a + b) % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

private theorem allTritList_set {xs : List Nat} (h : allTritList xs) {i v : Nat}
    (hi : i < xs.length) (hv : v ≤ 2) : allTritList (xs.set i v) := by
  intro x hx
  cases Nat.decLt i xs.length with
  | isFalse hne => exact absurd hi hne
  | isTrue hlt =>
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hlen : (xs.set i v).length = xs.length := by rw [List.length_set]
    have hj' : j < xs.length := by rw [← hlen]; exact hj
    rw [List.getElem_set]
    by_cases hij : i = j
    · simp [hij, hv]
    · simp [hij]
      exact h _ (List.getElem_mem hj')

private theorem schoolStep_length (xs strip : List Nat) (i j : Nat) (mir : Bool) :
    (schoolStep xs i mir strip j).length = strip.length := by
  unfold schoolStep layCell
  by_cases hz : coeff xs j = 0
  · simp [hz]
  · simp [hz, List.length_set]

private theorem schoolStep_trits {xs strip : List Nat} (hs : allTritList strip)
    (i j : Nat) (mir : Bool) (hidx : coeff xs j = 0 ∨ i + j < strip.length) :
    allTritList (schoolStep xs i mir strip j) := by
  unfold schoolStep layCell
  by_cases hz : coeff xs j = 0
  · simp [hz, hs]
  · have hlt : i + j < strip.length := by
      cases hidx with
      | inl h => exact absurd h hz
      | inr h => exact h
    simp only [hz, ite_false]
    exact allTritList_set hs hlt (tritAdd_le _ _)

theorem laidCount_le (a : List Nat) (k : Nat) : laidCount a k ≤ k := by
  induction k with
  | zero => simp [laidCount_zero]
  | succ k ih =>
    rw [laidCount_succ]
    have : (if coeff a k = 0 then 0 else 1) ≤ 1 := by
      by_cases h0 : coeff a k = 0
      · simp [h0]
      · simp [h0]
    omega

/-- One emitted column, in the shape shared by every inlined copy in `Ecbs.mul`.
    `i` is the outer hole, `mir` is that peg's mirror bit, and the index is added twice
    because the emitter binds the cell and the read separately. -/
def layDo (a strip : Array Int) (i j : Int) (mir : Bool) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board) :=
  do
    let d ← SudoRt.atL a j
    if !(SudoRt.SEq.beq d (0 : Int)) then
      do
        if mir then
          do
            let d ← Ecbs.flip d
            let ix ← SudoRt.addI i j
            let t ← SudoRt.addI i j
            let cur ← SudoRt.atL strip t
            let sum ← SudoRt.addI cur d
            let r ← SudoRt.modI sum (3 : Int)
            let strip ← SudoRt.putL strip ix r
            let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
            let b := withMoves b mv
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (strip, b))
        else
          do
            let ix ← SudoRt.addI i j
            let t ← SudoRt.addI i j
            let cur ← SudoRt.atL strip t
            let sum ← SudoRt.addI cur d
            let r ← SudoRt.modI sum (3 : Int)
            let strip ← SudoRt.putL strip ix r
            let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
            let b := withMoves b mv
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (strip, b))
    else
      do
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (strip, b))

private theorem layDo_zero (xs strip : List Nat) (i j : Nat) (mir : Bool) (b : Ecbs.Board)
    (hj : j < xs.length) (hz : xs[j] = 0) :
    layDo (embed xs) (embed strip) (Int.ofNat i) (Int.ofNat j) mir b =
      .ok (.cont (embed strip, b)) := by
  unfold layDo
  rw [atL_embed xs j hj, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

private theorem lay_sum_fit (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) : FitsLen (a + b) :=
  fits_small (by omega)

/-- Nonzero column: the cell `i + j` and one move. Both `addI i j` binds are the emitter's. -/
private theorem layDo_nz (xs strip : List Nat) (i j moves : Nat) (mir : Bool) (b : Ecbs.Board)
    (hj : j < xs.length) (hidx : i + j < strip.length) (hz : xs[j] ≠ 0)
    (hxs : allTritList xs) (hs : allTritList strip)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfi : FitsLen (i + j)) (hfm : FitsLen (moves + 1)) :
    layDo (embed xs) (embed strip) (Int.ofNat i) (Int.ofNat j) mir b =
      .ok (.cont (embed (schoolStep xs i mir strip j),
        withMoves b (Int.ofNat (moves + 1)))) := by
  unfold layDo
  rw [atL_embed xs j hj, ok_bind, sEq_ofNat_zero]
  simp only [hz, decide_False, Bool.not_false, if_true, ok_bind]
  have hd : xs[j] ≤ 2 := trit_get hxs hj
  have hcell : strip[i + j] ≤ 2 := hs _ (List.getElem_mem hidx)
  by_cases hmIr : mir = true
  · simp only [hmIr, ite_true]
    rw [flip_refines _ hd, ok_bind, addI_ofNat i j hfi, ok_bind, ok_bind,
      atL_embed strip (i + j) hidx, ok_bind,
      addI_ofNat _ _ (lay_sum_fit _ _ hcell (flipTrit_le hd)), ok_bind,
      modI_three, ok_bind, embed_put strip (i + j) _ hidx, ok_bind, hm,
      addI_ofNat_one moves hfm, ok_bind, pure_eq_ok]
    simp [schoolStep, layCell, coeff_get xs j hj, coeff_get strip (i + j) hidx, hz, hmIr,
      tritAdd, withMoves]
  · have hf : mir = false := eq_false_of_ne_true hmIr
    simp only [hf, Bool.false_eq_true, if_false, ok_bind]
    rw [addI_ofNat i j hfi, ok_bind, ok_bind,
      atL_embed strip (i + j) hidx, ok_bind,
      addI_ofNat _ _ (lay_sum_fit _ _ hcell hd), ok_bind,
      modI_three, ok_bind, embed_put strip (i + j) _ hidx, ok_bind, hm,
      addI_ofNat_one moves hfm, ok_bind, pure_eq_ok]
    simp [schoolStep, layCell, coeff_get xs j hj, coeff_get strip (i + j) hidx, hz, hf,
      tritAdd, withMoves]

private theorem layDo_refines (xs strip : List Nat) (i j moves : Nat) (mir : Bool)
    (b : Ecbs.Board) (hj : j < xs.length) (hidx : i + j < strip.length)
    (hxs : allTritList xs) (hs : allTritList strip)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfi : FitsLen (i + j)) (hfm : FitsLen (moves + 1)) :
    layDo (embed xs) (embed strip) (Int.ofNat i) (Int.ofNat j) mir b =
      .ok (.cont (embed (schoolStep xs i mir strip j),
        withMoves b (Int.ofNat (moves + if xs[j] = 0 then 0 else 1)))) := by
  by_cases hz : xs[j] = 0
  · have h0 := layDo_zero xs strip i j mir b hj hz
    rw [h0, schoolStep, coeff_get xs j hj, hz, if_pos rfl, if_pos rfl, Nat.add_zero,
      withMoves_id b hm]
  · have h1 := layDo_nz xs strip i j moves mir b hj hidx hz hxs hs hm hfi hfm
    rw [h1, if_neg hz]

/-- Ascending `for j = 0 to n - 1` column loop. Parameterised by the first number,
    the outer hole, and the mirror bit, so each of the six inlined copies is this stepper. -/
def colStep (a : Array Int) (i toV : Int) (mir : Bool)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board) :=
  let j := σ.1
  let strip := σ.2.1
  let b := σ.2.2
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, (strip, b)))
    else
      match ← layDo a strip i j mir b with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
      | .cont fs => do
          if j == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
          else do
            let j' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))

private theorem colStep_hit (xs strip : List Nat) (i j toN moves : Nat) (mir : Bool)
    (b : Ecbs.Board) (hj : j ≤ toN) (hx : j < xs.length) (hidx : i + j < strip.length)
    (hxs : allTritList xs) (hs : allTritList strip)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfi : FitsLen (i + j)) (hfm : FitsLen (moves + 1)) (hfj : FitsLen (j + 1)) :
    colStep (embed xs) (Int.ofNat i) (Int.ofNat toN) mir
        (Int.ofNat j, (embed strip, b)) =
      (if j = toN then .ok (.brk (Int.ofNat j, (embed (schoolStep xs i mir strip j),
            withMoves b (Int.ofNat (moves + if xs[j] = 0 then 0 else 1)))))
        else .ok (.cont (Int.ofNat (j + 1), (embed (schoolStep xs i mir strip j),
            withMoves b (Int.ofNat (moves + if xs[j] = 0 then 0 else 1)))))) := by
  unfold colStep
  dsimp
  conv =>
    lhs
    rw [show (i : Int) = Int.ofNat i from rfl, show (j : Int) = Int.ofNat j from rfl,
      show (toN : Int) = Int.ofNat toN from rfl]
  have hngt : ¬ (Int.ofNat j > Int.ofNat toN) := not_gt_cast hj
  rw [if_neg hngt, layDo_refines xs strip i j moves mir b hx hidx hxs hs hm hfi hfm, ok_bind]
  exact asc_tail toN j hfj _

/-- Inner schoolbook loop: columns `0 .. n` of hole `i`, plus one move per nonzero cell. -/
theorem schoolCol_refines (xs strip : List Nat) (i moves n : Nat) (mir : Bool) (b : Ecbs.Board)
    (hn : 0 < n) (hi : i < n) (hx : n ≤ xs.length) (hspan : i + (n - 1) < strip.length)
    (hxs : allTritList xs) (hs : allTritList strip)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfi : FitsLen (i + (n - 1))) (hfm : FitsLen (moves + n)) (hfn : FitsLen n) :
    SudoRt.runLoopOn (ρ := Ecbs.Board) (Int.ofNat 0, (embed strip, b))
      (fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)))
      (colStep (embed xs) (Int.ofNat i) (Int.ofNat (n - 1)) mir)
      (fun σ => pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (σ.2.2, σ.2.1)))
      (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)) =
      .ok (SudoRt.Flow.cont (ρ := Ecbs.Board)
        (withMoves b (Int.ofNat (moves + laidCount xs n)),
          embed (schoolRow n xs i mir strip))) := by
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun j (st : Array Int × Ecbs.Board) =>
      st.1 = embed (rowAt xs i mir strip j) ∧
      st.2 = withMoves b (Int.ofNat (moves + laidCount xs j)) ∧
      allTritList (rowAt xs i mir strip j) ∧
      (rowAt xs i mir strip j).length = strip.length)
    (Nat.zero_le _) ?_ ?_ ?_
  · refine ⟨rfl, ?_, hs, rfl⟩
    rw [laidCount_zero, Nat.add_zero]
    exact (withMoves_id b hm).symm
  · intro j st _ hj hI
    have hi0 : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
    have hjx : j < xs.length := by omega
    have hidx : i + j < (rowAt xs i mir strip j).length := by
      have := hi0
      rw [hI.2.2.2]; omega
    have hfi' : FitsLen (i + j) := FitsLen.of_le hfi (by omega)
    have hlc : laidCount xs j ≤ j := laidCount_le xs j
    have hfm' : FitsLen (moves + laidCount xs j + 1) := FitsLen.of_le hfm (by omega)
    have hfj : FitsLen (j + 1) := FitsLen.of_le hfn (by omega)
    have hm' := withMoves_moves b (Int.ofNat (moves + laidCount xs j))
    rw [← hI.2.1] at hm'
    have hstep := colStep_hit xs (rowAt xs i mir strip j) i j (n - 1)
      (moves + laidCount xs j) mir st.2 hj hjx hidx hxs hI.2.2.1 hm' hfi' hfm' hfj
    have hpair : st = (embed (rowAt xs i mir strip j), st.2) := Prod.ext hI.1 rfl
    rw [hpair]
    refine ⟨(embed (schoolStep xs i mir (rowAt xs i mir strip j) j),
        withMoves st.2 (Int.ofNat (moves + laidCount xs j +
          if xs[j] = 0 then 0 else 1))), ?_, hstep⟩
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hI.2.1, withMoves_withMoves, laidCount_succ, coeff_get xs j hjx, Nat.add_assoc]
    · exact schoolStep_trits hI.2.2.1 i j mir (Or.inr hidx)
    · rw [rowAt_succ, schoolStep_length, hI.2.2.2]
  · intro st hI
    have hn1 : n - 1 + 1 = n := by omega
    rw [pure_eq_ok, hI.1, hI.2.1, hn1, schoolRow_eq_rowAt]

/-- One outer peg: skip a zero, otherwise lay `schoolRow` with the red-peg mirror. -/
def schoolAt (n : Nat) (first second : List Nat) (mirror : Bool) (i : Nat)
    (st : List Nat) : List Nat :=
  let c := coeff second i
  if c = 0 then st else schoolRow n first i (decide (c = 2) != mirror) st

/-- `k` descending steps, highest hole first. `k = 0` has not started; `k = n` is `school`. -/
def schoolDown (first second : List Nat) (mirror : Bool) (n : Nat) (strip : List Nat) :
    Nat → List Nat
  | 0 => strip
  | k + 1 => schoolAt n first second mirror (n - (k + 1)) (schoolDown first second mirror n strip k)

/-- Moves charged for those `k` steps: one to lift the peg, then one per nonzero cell laid. -/
def schoolMoves (first second : List Nat) (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let c := coeff second (n - (k + 1))
    schoolMoves first second n k + if c = 0 then 0 else 1 + laidCount first n

private theorem schoolDown_step (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) (k : Nat) :
    schoolDown first second mirror n strip (k + 1) =
      schoolAt n first second mirror (n - (k + 1)) (schoolDown first second mirror n strip k) :=
  rfl

private theorem schoolMoves_step (first second : List Nat) (n k : Nat) :
    schoolMoves first second n (k + 1) =
      schoolMoves first second n k +
        if coeff second (n - (k + 1)) = 0 then 0 else 1 + laidCount first n :=
  rfl

private theorem schoolDown_at (first second : List Nat) (mirror : Bool) (n i : Nat)
    (strip : List Nat) (hi : i < n) :
    schoolDown first second mirror n strip (n - i) =
      schoolAt n first second mirror i (schoolDown first second mirror n strip (n - (i + 1))) := by
  have hk : n - (i + 1) + 1 = n - i := by omega
  rw [← hk, schoolDown_step]
  have hidx : n - (n - (i + 1) + 1) = i := by omega
  rw [hidx]

private theorem schoolMoves_at (first second : List Nat) (n i : Nat) (hi : i < n) :
    schoolMoves first second n (n - i) =
      schoolMoves first second n (n - (i + 1)) +
        if coeff second i = 0 then 0 else 1 + laidCount first n := by
  have hk : n - (i + 1) + 1 = n - i := by omega
  rw [← hk, schoolMoves_step]
  have hidx : n - (n - (i + 1) + 1) = i := by omega
  rw [hidx]

private theorem range_succ_cons : ∀ k, List.range (k + 1) = 0 :: (List.range k).map Nat.succ
  | 0 => by simp [List.range_succ, List.range_zero]
  | k + 1 => by
    conv =>
      lhs
      rw [List.range_succ (k + 1), range_succ_cons k]
    conv =>
      rhs
      rw [List.range_succ k]
    simp [List.map_append, List.cons_append]

private theorem sub_succ_idx (n k d : Nat) (hk : k + 1 ≤ n) :
    n - (k + 1) + (d + 1) = n - k + d := by
  omega

private theorem map_high (n k : Nat) (hk : k + 1 ≤ n) :
    (List.range (k + 1)).map (fun d => n - (k + 1) + d) =
      (n - (k + 1)) :: (List.range k).map (fun d => n - k + d) := by
  rw [range_succ_cons]
  simp only [List.map_cons, Nat.add_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  exact sub_succ_idx n k d hk

private theorem schoolDown_high (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) (k : Nat) (hk : k ≤ n) :
    schoolDown first second mirror n strip k =
      ((List.range k).map (fun d => n - k + d)).foldr (schoolAt n first second mirror) strip := by
  induction k with
  | zero => simp [schoolDown, List.range_zero]
  | succ k ih =>
    have hk0 : k + 1 ≤ n := hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    rw [schoolDown, ih hk', map_high n k hk0, List.foldr_cons]

private theorem school_fold (n : Nat) (first second strip : List Nat) (mirror : Bool) :
    school n first second strip mirror =
      (List.range n).foldr (schoolAt n first second mirror) strip := by
  unfold school schoolAt
  rfl

theorem schoolDown_school (first second strip : List Nat) (mirror : Bool) (n : Nat) :
    schoolDown first second mirror n strip n = school n first second strip mirror := by
  rw [schoolDown_high first second mirror n strip n (Nat.le_refl n), school_fold]
  have hmap : (List.range n).map (fun d => n - n + d) = (List.range n).map id := by
    apply List.map_congr_left
    intro d _
    simp
  simp [hmap]

private theorem rowAt_length (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) :
    ∀ k, (rowAt a i mir strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by rw [rowAt_succ, schoolStep_length, rowAt_length a i mir strip k]

private theorem rowAt_trits {a strip : List Nat} (hs : allTritList strip) (i : Nat) (mir : Bool) :
    ∀ k, (∀ j, j < k → i + j < strip.length) → allTritList (rowAt a i mir strip k)
  | 0, _ => hs
  | k + 1, hspan => by
    rw [rowAt_succ]
    have hprev := rowAt_trits (a := a) hs i mir k (fun j hj => hspan j (Nat.lt_succ_of_lt hj))
    apply schoolStep_trits hprev i k mir
    by_cases hz : coeff a k = 0
    · exact Or.inl hz
    · exact Or.inr (by rw [rowAt_length]; exact hspan k (Nat.lt_succ_self k))

private theorem schoolDown_length (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) : ∀ k, (schoolDown first second mirror n strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by
    rw [schoolDown, schoolAt]
    by_cases hz : coeff second (n - (k + 1)) = 0
    · simp [hz, schoolDown_length first second mirror n strip k]
    · simp [hz, schoolRow_eq_rowAt, rowAt_length, schoolDown_length first second mirror n strip k]

private theorem schoolDown_trits (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) (hs : allTritList strip)
    (hbench : ∀ i, i < n → i + (n - 1) < strip.length) :
    ∀ k, k ≤ n → allTritList (schoolDown first second mirror n strip k)
  | 0, _ => hs
  | k + 1, hk => by
    rw [schoolDown, schoolAt]
    have hprev := schoolDown_trits first second mirror n strip hs hbench k (Nat.le_of_succ_le hk)
    by_cases hz : coeff second (n - (k + 1)) = 0
    · simp only [hz, ite_true]
      exact hprev
    · simp only [hz, ite_false, schoolRow_eq_rowAt]
      refine rowAt_trits (a := first) hprev (n - (k + 1))
        (decide (coeff second (n - (k + 1)) = 2) != mirror) n
        ?_
      intro j hj
      rw [schoolDown_length]
      have hi : n - (k + 1) < n := by omega
      have hjn : j ≤ n - 1 := Nat.le_sub_one_of_lt hj
      have : n - (k + 1) + j ≤ n - (k + 1) + (n - 1) := Nat.add_le_add_left hjn _
      exact Nat.lt_of_le_of_lt this (hbench _ hi)

private theorem schoolMoves_le (first second : List Nat) (n k : Nat) :
    schoolMoves first second n k ≤ k * (n + 1) := by
  induction k with
  | zero => simp [schoolMoves]
  | succ k ih =>
    rw [schoolMoves]
    have hstep : (if coeff second (n - (k + 1)) = 0 then 0 else 1 + laidCount first n) ≤ n + 1 := by
      by_cases h0 : coeff second (n - (k + 1)) = 0
      · simp [h0]
      · have hl := laidCount_le first n
        simp [h0]
        omega
    have hsum := Nat.add_le_add ih hstep
    rw [← Nat.succ_mul] at hsum
    exact hsum

private theorem not_lt_zero (i : Nat) : ¬ ((i : Int) < (0 : Int)) :=
  Int.not_lt.mpr (Int.ofNat_zero_le i)

private theorem mir_bit (c : Nat) (mirror : Bool) :
    (!(SudoRt.SEq.beq (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) mirror)) =
      (decide (c = 2) != mirror) := by
  have h2 : SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat]
  rw [h2]
  cases h : decide (c = 2) <;> cases mirror <;> rfl

/-- Body of `for i = n - 1 downto 0` when the coefficient is nonzero: lift, then the column loop.
    The six copies differ only in the arrays and the mirror flag closed over here. -/
def rowBody (a s : Array Int) (mirror : Bool) (nB i : Int) (b : Ecbs.Board) (strip : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board) :=
  do
    let c ← SudoRt.atL s i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
        let b := withMoves b mv
        let mir := !(SudoRt.SEq.beq (SudoRt.SEq.beq c (2 : Int)) mirror)
        let toJ ← SudoRt.subI nB (1 : Int)
        let fromV := (0 : Int)
        let fuel : Nat := if fromV > toJ then 1 else (toJ - fromV).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, (strip, b)) fuel
          (colStep a i toJ mir)
          (fun σ => pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (σ.2.2, σ.2.1)))
          (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
        pure out
    else
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (b, strip))

/-- Descending outer stepper. Every inlined schoolbook in `Ecbs.mul` is this loop. -/
def rowStep (a s : Array Int) (mirror : Bool) (nB toV : Int)
    (σ : Int × (Ecbs.Board × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Ecbs.Board × Array Int)) Ecbs.Board) :=
  let i := σ.1
  let b := σ.2.1
  let strip := σ.2.2
  do
    if i < toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, (b, strip)))
    else
      match ← rowBody a s mirror nB i b strip with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.subI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem move_budget (moves n i s : Nat) (hi : i < n)
    (hs : s ≤ (n - (i + 1)) * (n + 1)) :
    moves + s + 1 + n ≤ moves + n * (n + 1) := by
  have hk : n - (i + 1) ≤ n - 1 := by omega
  have hs' : s ≤ (n - 1) * (n + 1) := Nat.le_trans hs (Nat.mul_le_mul_right (n + 1) hk)
  have hstep : s + 1 + n ≤ (n - 1) * (n + 1) + (n + 1) := by omega
  have hn : n = (n - 1) + 1 := by omega
  have heq : (n - 1) * (n + 1) + (n + 1) = n * (n + 1) := by
    rw [hn, Nat.add_mul]
    simp
  rw [heq] at hstep
  have heq' : moves + s + 1 + n = moves + (s + 1 + n) := by omega
  rw [heq']
  exact Nat.add_le_add_left hstep moves

private theorem rowBody_zero (xs ys prev : List Nat) (i : Nat) (mirror : Bool) (nB : Int)
    (b : Ecbs.Board) (hy : i < ys.length) (hz : ys[i] = 0) :
    rowBody (embed xs) (embed ys) mirror nB (Int.ofNat i) b (embed prev) =
      .ok (.cont (b, embed prev)) := by
  unfold rowBody
  rw [atL_embed ys i hy, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

/-- Nonzero outer peg: one lift, then `schoolCol_refines` for that mirror bit. -/
private theorem rowBody_pos (xs ys prev : List Nat) (i m n : Nat) (mirror : Bool)
    (b : Ecbs.Board) (hn : 0 < n) (hi : i < n) (hx : n ≤ xs.length) (hy : i < ys.length)
    (hz : ys[i] ≠ 0) (hspan : i + (n - 1) < prev.length)
    (hxs : allTritList xs) (hp : allTritList prev)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat m)
    (hfn : FitsLen n) (hfi : FitsLen (i + (n - 1))) (hf1 : FitsLen (m + 1))
    (hfm : FitsLen (m + 1 + n)) :
    rowBody (embed xs) (embed ys) mirror (Int.ofNat n) (Int.ofNat i) b (embed prev) =
      .ok (.cont (withMoves b (Int.ofNat (m + 1 + laidCount xs n)),
        embed (schoolRow n xs i (decide (ys[i] = 2) != mirror) prev))) := by
  unfold rowBody
  rw [atL_embed ys i hy, ok_bind, sEq_ofNat_zero]
  simp only [hz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [hm, addI_ofNat_one m hf1, ok_bind, mir_bit (ys[i]) mirror, subI_ofNat_one n hn hfn, ok_bind]
  have hfuel : (if (0 : Int) > Int.ofNat (n - 1) then 1
      else (Int.ofNat (n - 1) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel, show (0 : Int) = Int.ofNat 0 from rfl]
  have hm1 : (withMoves b (Int.ofNat (m + 1))).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (m + 1) := withMoves_moves _ _
  rw [schoolCol_refines xs prev i (m + 1) n (decide (ys[i] = 2) != mirror)
      (withMoves b (Int.ofNat (m + 1))) hn hi hx hspan hxs hp hm1 hfi hfm hfn,
    except_bind_pure, withMoves_withMoves, Nat.add_assoc]

/-- Descending schoolbook. The state at the end is `school` and the moves charged along the way. -/
theorem school_loop_refines {β}
    (xs ys strip : List Nat) (moves n : Nat) (mirror : Bool) (b : Ecbs.Board)
    (after : Int × (Ecbs.Board × Array Int) → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : 0 < n) (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (hbench : 2 * (n - 1) < strip.length)
    (hxs : allTritList xs) (hs : allTritList strip)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfn : FitsLen n) (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    SudoRt.runLoopOn (ρ := Ecbs.Board) (Int.ofNat (n - 1), (b, embed strip))
      (fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0))
      (rowStep (embed xs) (embed ys) mirror (Int.ofNat n) (0 : Int))
      after onRet =
      after (Int.ofNat 0,
        (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys strip mirror))) := by
  refine desc_goal
    (fun t (st : Ecbs.Board × Array Int) =>
      st.2 = embed (schoolDown xs ys mirror n strip (n - t)) ∧
      st.1 = withMoves b (Int.ofNat (moves + schoolMoves xs ys n (n - t))) ∧
      allTritList (schoolDown xs ys mirror n strip (n - t)) ∧
      (schoolDown xs ys mirror n strip (n - t)).length = strip.length)
    (Nat.zero_le (n - 1)) ?_ ?_ ?_
  · have hz : n - (n - 1 + 1) = 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hz, schoolDown]
    · simp [hz, schoolMoves, Nat.add_zero]
      exact (withMoves_id b hm).symm
    · simpa [hz, schoolDown] using hs
    · simp [hz, schoolDown]
  · intro i st hlo hiI hI
    have hi : i < n := by omega
    have hk : n - (i + 1) + 1 = n - i := by omega
    have hlen := schoolDown_length xs ys mirror n strip (n - (i + 1))
    have hprevT := hI.2.2.1
    have hprevL := hI.2.2.2
    have hyi : i < ys.length := by omega
    have hm0 := withMoves_moves b (Int.ofNat (moves + schoolMoves xs ys n (n - (i + 1))))
    rw [← hI.2.1] at hm0
    have hfiti : FitsLen i := FitsLen.of_le hfn (Nat.le_of_lt hi)
    unfold rowStep
    dsimp
    have hng : ¬ ((i : Int) < (0 : Int)) := not_lt_zero i
    rw [if_neg hng]
    have hnI : (n : Int) = Int.ofNat n := rfl
    have hiI : (i : Int) = Int.ofNat i := rfl
    rw [hnI, hiI]
    by_cases hz : ys[i] = 0
    · have hbody := rowBody_zero xs ys (schoolDown xs ys mirror n strip (n - (i + 1))) i mirror
        (Int.ofNat n) st.fst hyi hz
      rw [← hI.1] at hbody
      simp only [hbody, ok_bind]
      refine ⟨(st.fst, st.snd), ?_, desc_tail i hfiti (st.fst, st.snd)⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hI.1, schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, hz,
            if_pos rfl]
        · rw [hI.2.1, schoolMoves_at xs ys n i hi, coeff_get ys i hyi, hz, if_pos rfl, Nat.add_zero]
          rfl
        · rw [schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, hz, if_pos rfl]
          exact hprevT
        · rw [schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, hz, if_pos rfl]
          exact hprevL
    · have hspan0 : i + (n - 1) < strip.length := by
        have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
        have hsum : i + (n - 1) ≤ (n - 1) + (n - 1) := Nat.add_le_add_right hi' (n - 1)
        rw [← Nat.two_mul] at hsum
        exact Nat.lt_of_le_of_lt hsum hbench
      have hspan : i + (n - 1) < (schoolDown xs ys mirror n strip (n - (i + 1))).length := by
        rw [hprevL]; exact hspan0
      have hfi' : FitsLen (i + (n - 1)) := FitsLen.of_le hfi (by
        have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
        have hsum : i + (n - 1) ≤ (n - 1) + (n - 1) := Nat.add_le_add_right hi' (n - 1)
        rw [← Nat.two_mul] at hsum
        exact hsum)
      have hmv : schoolMoves xs ys n (n - (i + 1)) ≤ (n - (i + 1)) * (n + 1) :=
        schoolMoves_le xs ys n _
      have hbud := move_budget moves n i _ hi hmv
      have hf1 : FitsLen (moves + schoolMoves xs ys n (n - (i + 1)) + 1) :=
        FitsLen.of_le hfm (Nat.le_trans (Nat.le_add_right _ n) hbud)
      have hfm' : FitsLen (moves + schoolMoves xs ys n (n - (i + 1)) + 1 + n) :=
        FitsLen.of_le hfm hbud
      have hbody := rowBody_pos xs ys (schoolDown xs ys mirror n strip (n - (i + 1))) i
        (moves + schoolMoves xs ys n (n - (i + 1))) n mirror st.fst hn hi hx hyi hz hspan hxs
        hprevT hm0 hfn hfi' hf1 hfm'
      rw [← hI.1] at hbody
      simp only [hbody, ok_bind]
      refine ⟨(withMoves st.fst (Int.ofNat (moves + schoolMoves xs ys n (n - (i + 1)) + 1 +
            laidCount xs n)),
          embed (schoolRow n xs i (decide (ys[i] = 2) != mirror)
            (schoolDown xs ys mirror n strip (n - (i + 1))))), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, if_neg hz,
            schoolRow_eq_rowAt]
        · rw [hI.2.1, withMoves_withMoves, schoolMoves_at xs ys n i hi, coeff_get ys i hyi, if_neg hz]
          simp [Nat.add_assoc]
        · rw [schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, if_neg hz,
            schoolRow_eq_rowAt]
          refine rowAt_trits (a := xs) hprevT i (decide (ys[i] = 2) != mirror) n ?_
          intro j hj
          rw [hprevL]
          have : i + j ≤ i + (n - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) i
          exact Nat.lt_of_le_of_lt this hspan0
        · rw [schoolDown_at xs ys mirror n i strip hi, schoolAt, coeff_get ys i hyi, if_neg hz,
            schoolRow_eq_rowAt, rowAt_length, hprevL]
      · exact desc_tail i hfiti _
  · intro st hI
    rw [Nat.sub_zero] at hI
    rw [schoolDown_school] at hI
    have hst : st = (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)),
        embed (school n xs ys strip mirror)) := by
      apply Prod.ext
      · exact hI.2.1
      · exact hI.1
    rw [hst]

theorem school_length (first second strip : List Nat) (mirror : Bool) (n : Nat) :
    (school n first second strip mirror).length = strip.length := by
  rw [← schoolDown_school first second strip mirror n]
  exact schoolDown_length first second mirror n strip n

theorem school_trits (first second strip : List Nat) (mirror : Bool) (n : Nat)
    (hs : allTritList strip)
    (hbench : ∀ i, i < n → i + (n - 1) < strip.length) :
    allTritList (school n first second strip mirror) := by
  rw [← schoolDown_school first second strip mirror n]
  exact schoolDown_trits first second mirror n strip hs hbench n (Nat.le_refl n)

theorem schoolMoves_bound (first second : List Nat) (n : Nat) :
    schoolMoves first second n n ≤ n * (n + 1) :=
  schoolMoves_le first second n n

end EcbsLink2.Link2

