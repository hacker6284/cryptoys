/-
  `Ecbs.mirror` flips every nonzero coefficient of a held home.
  The loop is `runLoopOn` from `0` through `n - 1`. After `i` coefficients
  the local array is `mirrorPrefix L i`, and the move counter has grown by
  the nonzero count of that prefix. At `i = n` the array is `Spec.mirrorTrits`.
  `set_number` writes it back. Held, the other homes, the ladder, the tally
  length, and the bench are the board the loop started from.
-/
import EcbsLink2.Link2.School
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.SetCongr

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Coefficients `0 .. i` flipped, the rest still the input. -/
def mirrorPrefix (xs : List Nat) (i : Nat) : List Nat :=
  (xs.take i).map flipTrit ++ xs.drop i

theorem mirrorTrits_flip (xs : List Nat) : mirrorTrits xs = xs.map flipTrit := by
  unfold mirrorTrits flipTrit
  rfl

theorem mirrorPrefix_zero (xs : List Nat) : mirrorPrefix xs 0 = xs := by
  simp [mirrorPrefix]

theorem mirrorPrefix_length (xs : List Nat) (i : Nat) (hi : i ≤ xs.length) :
    (mirrorPrefix xs i).length = xs.length := by
  simp [mirrorPrefix, List.length_take, Nat.min_eq_left hi, List.length_drop]
  omega

theorem mirrorPrefix_all (xs : List Nat) : mirrorPrefix xs xs.length = mirrorTrits xs := by
  simp [mirrorPrefix, mirrorTrits_flip]

private theorem getD_eq_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.getD j 999 = xs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem mirrorPrefix_cons (c : Nat) (xs : List Nat) (i : Nat) :
    mirrorPrefix (c :: xs) (i + 1) = flipTrit c :: mirrorPrefix xs i := by
  simp [mirrorPrefix, List.take_succ_cons, List.drop_succ_cons, List.map_cons]

private theorem mirrorPrefix_getD (xs : List Nat) (i j : Nat) (hi : i ≤ xs.length)
    (hj : j < xs.length) :
    (mirrorPrefix xs i).getD j 999 = if j < i then flipTrit xs[j] else xs[j] := by
  induction xs generalizing i j with
  | nil => cases hj
  | cons c xs ih =>
    cases i with
    | zero =>
      simp [mirrorPrefix, Nat.not_lt_zero j, List.getElem?_eq_getElem hj, Option.getD_some]
    | succ i =>
      have hi' : i ≤ xs.length := by
        rw [List.length_cons] at hi
        exact Nat.le_of_succ_le_succ hi
      have hlist := mirrorPrefix_cons c xs i
      cases j with
      | zero =>
        simp [hlist, List.getElem_cons_zero]
      | succ j =>
        have hj' : j < xs.length := by
          rw [List.length_cons] at hj
          exact Nat.lt_of_succ_lt_succ hj
        by_cases hlt : j < i
        · rw [hlist, List.getD_cons_succ, ih i j hi' hj']
          have hlt1 : j + 1 < i + 1 := Nat.succ_lt_succ hlt
          simp [if_pos hlt, if_pos hlt1, List.getElem_cons_succ]
        · have hge : ¬ j + 1 < i + 1 := fun h => hlt (Nat.lt_of_succ_lt_succ h)
          rw [hlist, List.getD_cons_succ, ih i j hi' hj']
          simp [if_neg hlt, if_neg hge, List.getElem_cons_succ]

theorem mirrorPrefix_get (xs : List Nat) (i j : Nat) (hi : i ≤ xs.length) (hj : j < xs.length) :
    (mirrorPrefix xs i)[j]'(by rw [mirrorPrefix_length xs i hi]; exact hj) =
      if j < i then flipTrit xs[j] else xs[j] := by
  rw [← getD_eq_get (mirrorPrefix xs i) j (by rw [mirrorPrefix_length xs i hi]; exact hj)]
  exact mirrorPrefix_getD xs i j hi hj

theorem mirrorPrefix_cell (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (mirrorPrefix xs i)[i]'(by rw [mirrorPrefix_length xs i (Nat.le_of_lt hi)]; exact hi) =
      xs[i] := by
  rw [mirrorPrefix_get xs i i (Nat.le_of_lt hi) hi]
  simp

theorem mirrorPrefix_succ (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    mirrorPrefix xs (i + 1) = (mirrorPrefix xs i).set i (flipTrit xs[i]) := by
  have hi0 : i ≤ xs.length := Nat.le_of_lt hi
  have hi1 : i + 1 ≤ xs.length := Nat.succ_le_of_lt hi
  apply List.ext_getElem
  · rw [List.length_set, mirrorPrefix_length xs i hi0, mirrorPrefix_length xs (i + 1) hi1]
  · intro j hj1 hj2
    have hjL : j < xs.length := by
      rw [← mirrorPrefix_length xs (i + 1) hi1]
      exact hj1
    rw [mirrorPrefix_get xs (i + 1) j hi1 hjL]
    by_cases hji : j = i
    · subst hji
      simp [List.getElem_set_self]
    · have hne : i ≠ j := fun h => hji h.symm
      rw [List.getElem_set_ne hne]
      rw [mirrorPrefix_get xs i j hi0 hjL]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · simp [hlt, show ¬ j < i + 1 by omega]

private theorem list_set_same (xs : List Nat) (i v : Nat) (hi : i < xs.length)
    (hv : xs[i] = v) : xs.set i v = xs := by
  apply List.ext_getElem
  · simp [List.length_set]
  · intro j hj1 hj2
    by_cases h : j = i
    · subst h
      simp [List.getElem_set_self, hv]
    · simp [List.getElem_set_ne (Ne.symm h)]

theorem mirrorPrefix_skip (xs : List Nat) (i : Nat) (hi : i < xs.length) (hz : xs[i] = 0) :
    mirrorPrefix xs (i + 1) = mirrorPrefix xs i := by
  rw [mirrorPrefix_succ xs i hi, flipTrit, hz]
  have hidx : i < (mirrorPrefix xs i).length := by
    rw [mirrorPrefix_length xs i (Nat.le_of_lt hi)]; exact hi
  have hcell := mirrorPrefix_cell xs i hi
  rw [hz] at hcell
  exact list_set_same (mirrorPrefix xs i) i 0 hidx hcell

private theorem take_succ_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.take]
    | succ i =>
      have hi' : i < xs.length := by
        rw [List.length_cons] at hi
        omega
      simp [List.take, List.getElem_cons_succ, ih i hi']

private theorem pegCount_append_one (xs : List Nat) (c : Nat) :
    pegCount (xs ++ [c]) = pegCount xs + if c = 0 then 0 else 1 := by
  unfold pegCount
  simp only [List.filter_append, List.length_append]
  by_cases h : c = 0
  · simp [h, List.filter]
  · simp [h, List.filter]

theorem pegCount_take_succ (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    pegCount (xs.take (i + 1)) =
      pegCount (xs.take i) + if xs[i] = 0 then 0 else 1 := by
  rw [take_succ_get xs i hi, pegCount_append_one]

theorem pegCount_take_zero (xs : List Nat) : pegCount (xs.take 0) = 0 := by
  simp [pegCount]

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_id (b : Ecbs.Board)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) : withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

/-- Held home: `get_number` is that home's array. -/
theorem get_number_held (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true) :
    Ecbs.get_number b (home : Int) = .ok (b.sudo_5Board_4home[home]) := by
  unfold Ecbs.get_number Ecbs.where_bench
  rw [show (home : Int) = Int.ofNat home from ofNat_eq_natCast home,
    atL_ofNat _ home hD, hheld]
  simp only [ok_bind, ite_true, pure_eq_ok, Bool.false_eq_true, if_false]
  rw [atL_ofNat _ home hH, ok_bind]

/-- Held home: `set_number` writes that home and leaves every other field. -/
theorem set_number_held (b : Ecbs.Board) (home : Nat) (v : Array Int)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true) :
    Ecbs.set_number b (home : Int) v =
      .ok { b with sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ v } := by
  unfold Ecbs.set_number Ecbs.where_bench
  rw [show (home : Int) = Int.ofNat home from ofNat_eq_natCast home,
    atL_ofNat _ home hD, hheld]
  simp only [ok_bind, ite_true, pure_eq_ok, Bool.false_eq_true, if_false]
  rw [putL_ofNat _ home v hH, ok_bind]

/-- The board `mirror` returns: home `home` is `arr`, and moves grew by the
    nonzero count. Nothing else moves. -/
def mirrorHome (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) : Ecbs.Board :=
  { withMoves b (Int.ofNat mv) with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ arr }

theorem mirrorHome_held (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_4held = b.sudo_5Board_4held := rfl

theorem mirrorHome_bench_on (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := rfl

theorem mirrorHome_bench (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_5bench = b.sudo_5Board_5bench := rfl

theorem mirrorHome_tier (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_1t = b.sudo_5Board_1t := rfl

theorem mirrorHome_ladder (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_6ladder = b.sudo_5Board_6ladder := rfl

theorem mirrorHome_tally (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := rfl

theorem mirrorHome_row (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_3row = b.sudo_5Board_3row := rfl

theorem mirrorHome_moves (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (mirrorHome b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
  simp [mirrorHome, withMoves]

theorem mirrorHome_at (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (hH' : home < (mirrorHome b home hH arr mv).sudo_5Board_4home.size) :
    (mirrorHome b home hH arr mv).sudo_5Board_4home[home] = arr := by
  simp [mirrorHome, withMoves, Array.getElem_set]

theorem mirrorHome_other (b : Ecbs.Board) (home j : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (hne : j ≠ home)
    (hj : j < b.sudo_5Board_4home.size)
    (hj' : j < (mirrorHome b home hH arr mv).sudo_5Board_4home.size) :
    (mirrorHome b home hH arr mv).sudo_5Board_4home[j] = b.sudo_5Board_4home[j] := by
  simp [mirrorHome, withMoves, Array.getElem_set, show home ≠ j from Ne.symm hne]

/-- One coefficient of `Ecbs.mirror`. A zero stays, and costs nothing. A nonzero
    trit is `flip`, and the move counter grows by one. The second `atL` is the
    one the emitter writes before `flip`. -/
def mirrorCell (v : Array Int) (i : Int) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board) :=
  do
    let c ← SudoRt.atL v i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let ix := i
        let c2 ← SudoRt.atL v i
        let f ← Ecbs.flip c2
        let v ← SudoRt.putL v ix f
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (v, b))
    else
      do
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (v, b))

/-- `for i = 0 to n - 1` around `mirrorCell`. Breaks on the last index. -/
def mirrorStep (toV : Int) (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board) :=
  let i := σ.1
  let v := σ.2.1
  let b := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, (v, b)))
    else
      match ← mirrorCell v i b with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem mirrorCell_zero (L : List Nat) (i : Nat) (b : Ecbs.Board)
    (hi : i < L.length) (hz : L[i] = 0) :
    mirrorCell (embed (mirrorPrefix L i)) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont (embed (mirrorPrefix L i), b)) := by
  have hpref : i < (mirrorPrefix L i).length := by
    rw [mirrorPrefix_length L i (Nat.le_of_lt hi)]; exact hi
  unfold mirrorCell
  rw [atL_embed _ i hpref, mirrorPrefix_cell L i hi, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

private theorem mirrorCell_nz (L : List Nat) (i moves : Nat) (b : Ecbs.Board)
    (hi : i < L.length) (hz : L[i] ≠ 0) (hc : L[i] ≤ 2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) :
    mirrorCell (embed (mirrorPrefix L i)) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont (embed (mirrorPrefix L (i + 1)),
        withMoves b (Int.ofNat (moves + 1)))) := by
  have hpref : i < (mirrorPrefix L i).length := by
    rw [mirrorPrefix_length L i (Nat.le_of_lt hi)]; exact hi
  unfold mirrorCell
  rw [atL_embed _ i hpref, mirrorPrefix_cell L i hi, ok_bind, sEq_ofNat_zero]
  simp only [hz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [flip_refines _ hc, ok_bind, embed_put _ i (flipTrit L[i]) hpref, ok_bind]
  rw [mirrorPrefix_succ L i hi]
  rw [hm, addI_ofNat_one moves hfm, ok_bind, pure_eq_ok]
  simp [withMoves]

private theorem mirrorStep_hit (L : List Nat) (i n moves : Nat) (b : Ecbs.Board)
    (hi : i < L.length) (hto : i ≤ n - 1) (hc : L[i] ≤ 2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) (hfi : FitsLen (i + 1)) :
    mirrorStep (Int.ofNat (n - 1))
        (Int.ofNat i, (embed (mirrorPrefix L i), b)) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            (embed (mirrorPrefix L (i + 1)),
              withMoves b (Int.ofNat (moves + if L[i] = 0 then 0 else 1)))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            (embed (mirrorPrefix L (i + 1)),
              withMoves b (Int.ofNat (moves + if L[i] = 0 then 0 else 1)))))) := by
  unfold mirrorStep
  dsimp
  split
  · next hgt => exact absurd hgt (not_gt_cast hto)
  · rw [(ofNat_eq_natCast i).symm, (ofNat_eq_natCast (n - 1)).symm]
    by_cases hz : L[i] = 0
    · rw [mirrorCell_zero L i b hi hz, ok_bind, mirrorPrefix_skip L i hi hz]
      rw [hz, if_pos (rfl : (0 : Nat) = 0), Nat.add_zero]
      have hm' : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
        rw [hm, ofNat_eq_natCast]
      rw [withMoves_id b hm']
      exact asc_tail (n - 1) i hfi _
    · rw [mirrorCell_nz L i moves b hi hz hc hm hfm, ok_bind]
      simp only [if_neg hz]
      exact asc_tail (n - 1) i hfi _

/-- Held home `home` stores `embed L`, a trit list of length `n`. `Ecbs.mirror`
    returns that home as `embed (mirrorTrits L)`. The move counter grows by the
    nonzero count, which fits because `moves + n` does: each coefficient adds
    at most one, and `pegCount L ≤ n`. -/
theorem mirror_refines (b : Ecbs.Board) (home : Nat) (L : List Nat) (n moves : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed L)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : L.length = n)
    (hpos : 0 < n)
    (htri : allTritList L)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    Ecbs.mirror b (home : Int) =
      .ok (mirrorHome b home hH (embed (mirrorTrits L)) (moves + pegCount L)) := by
  have hfitn : FitsLen n := FitsLen.of_le hfit (Nat.le_add_left n moves)
  have hmI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hm, ofNat_eq_natCast]
  unfold Ecbs.mirror
  rw [get_number_held b home hH hD hheld, harr, ok_bind]
  rw [hn, show (n : Int) = Int.ofNat n from ofNat_eq_natCast n,
    subI_ofNat_one n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
    change mirrorStep (Int.ofNat (n - 1))
  rw [except_bind_pure]
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Array Int × Ecbs.Board) =>
      st.1 = embed (mirrorPrefix L i) ∧
      st.2 = withMoves b (Int.ofNat (moves + pegCount (L.take i))))
    (Nat.zero_le _) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · simp [mirrorPrefix_zero]
    · rw [pegCount_take_zero, Nat.add_zero]
      exact (withMoves_id b hmI).symm
  · intro i st _ hi hI
    have hii : i < L.length := by omega
    have hc : L[i] ≤ 2 := trit_get htri hii
    have hin : i < n :=
      Nat.lt_of_le_of_lt hi (Nat.sub_lt hpos (Nat.succ_pos 0))
    have hpc : pegCount (L.take i) + 1 ≤ n :=
      Nat.le_trans (Nat.succ_le_succ (pegCount_take_le L i)) (Nat.succ_le_of_lt hin)
    have hfm : FitsLen (moves + pegCount (L.take i) + 1) :=
      FitsLen.of_le hfit (by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left hpc moves)
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfitn (Nat.succ_le_of_lt hin)
    let nxtArr := embed (mirrorPrefix L (i + 1))
    let nxtMv := moves + pegCount (L.take i) + if L[i] = 0 then 0 else 1
    have hpegS : pegCount (L.take (i + 1)) = pegCount (L.take i) + if L[i] = 0 then 0 else 1 :=
      pegCount_take_succ L i hii
    refine ⟨(nxtArr, withMoves b (Int.ofNat nxtMv)), ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      simp [nxtMv, hpegS, Nat.add_assoc]
    · have hstep := mirrorStep_hit L i n (moves + pegCount (L.take i))
        (withMoves b (Int.ofNat (moves + pegCount (L.take i))))
        hii hi hc (withMoves_moves _ _) hfm hfi
      have hpair :
          (embed (mirrorPrefix L i),
            withMoves b (Int.ofNat (moves + pegCount (L.take i)))) = st :=
        Prod.ext hI.1.symm hI.2.symm
      rw [hpair] at hstep
      simpa [nxtArr, nxtMv, withMoves_withMoves, hpegS, Nat.add_assoc] using hstep
  · intro st hs
    have hdone : mirrorPrefix L n = mirrorTrits L := by
      rw [← hlen, mirrorPrefix_all]
    have htake : L.take n = L := by rw [← hlen, List.take_length]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), hdone, htake] at hs
    conv =>
      lhs
      zeta
    rw [hs.1, hs.2]
    have hHw : home < (withMoves b (Int.ofNat (moves + pegCount L))).sudo_5Board_4home.size := hH
    have hDw : home < (withMoves b (Int.ofNat (moves + pegCount L))).sudo_5Board_4held.size := hD
    have hheldW : (withMoves b (Int.ofNat (moves + pegCount L))).sudo_5Board_4held[home] = true :=
      hheld
    rw [set_number_held _ home _ hHw hDw hheldW, ok_bind, pure_eq_ok]
    unfold mirrorHome
    have hhome :
        (withMoves b (Int.ofNat (moves + pegCount L))).sudo_5Board_4home =
          b.sudo_5Board_4home := rfl
    rw [Array.set_congr_arr hhome hHw (embed (mirrorTrits L))]

end EcbsLink2.Link2
