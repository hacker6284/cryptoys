/-
  LINK 2. Bridge `sum_ranks` to algebraic `sumRanks`.
  The twin follows the emitted loop nesting so it is definitionally the
  generated function; the refinement is proved on that twin.
-/
import Doubledeal
import DoubleDeal.Round
import DoubleDeal.SumRanks
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.Shift

namespace DoubleDeal.Link2

def fuel13 : Nat := if (0 : Int) > 12 then 1 else ((12 : Int) - 0).natAbs + 1
def fuel4 : Nat := if (0 : Int) > 3 then 1 else ((3 : Int) - 0).natAbs + 1

def rankAddStep (row : Array Int) (toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Array (Array Int))) :=
  let j := σ.1
  let total := σ.2
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, total))
    else
      match ← ((do
        let cell ← SudoRt.atL row j
        let rk ← Doubledeal.rank_of cell
        let total ← SudoRt.addI total rk
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) total)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, fs))
      | .cont fs =>
          if (j == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, fs))
          else do
            let j' ← SudoRt.addI j 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (j', fs))

/-- One row: sum ranks, rotate left by the sum mod 13, write the row back. -/
def sumRowStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let i := σ.1
  let g := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, g))
    else
      match ← ((do
        let row ← SudoRt.atL g i
        let fl ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (0 : Int)) fuel13
          (rankAddStep row 12)
          (fun σ => do
            let total := σ.2
            let amt ← SudoRt.modI total 13
            let row' ← Doubledeal.left_rotate row amt
            let g' ← SudoRt.putL g i row'
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g'))
          (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
        pure fl
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def colCollectStep (g : Array (Array Int)) (j toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array (Array Int))) :=
  let i := σ.1
  let col := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, col))
    else
      match ← ((do
        let row ← SudoRt.atL g i
        let cell ← SudoRt.atL row j
        let _mb := SudoRt.appendL col cell
        let ⟨col, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) col)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def colRankStep (col : Array Int) (toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Array (Array Int))) :=
  let i := σ.1
  let total := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, total))
    else
      match ← ((do
        let cell ← SudoRt.atL col i
        let rk ← Doubledeal.rank_of cell
        let total ← SudoRt.addI total rk
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) total)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def freshStep (col : Array Int) (s toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array (Array Int))) :=
  let i := σ.1
  let fresh := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fresh))
    else
      match ← ((do
        let d ← SudoRt.subI i s
        let ix ← SudoRt.modI d 4
        let cell ← SudoRt.atL col ix
        let _mb := SudoRt.appendL fresh cell
        let ⟨fresh, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) fresh)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def writeColStep (fresh : Array Int) (j toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let i := σ.1
  let g := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, g))
    else
      match ← ((do
        let row ← SudoRt.atL g i
        let cell ← SudoRt.atL fresh i
        let row ← SudoRt.putL row j cell
        let g ← SudoRt.putL g i row
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

/-- One column of SumRanks: gather, rank-sum, right-rotate by the sum mod 4, write back. -/
def sumColStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let j := σ.1
  let g := σ.2
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, g))
    else
      match ← ((do
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
          (colCollectStep g j 3)
          (fun σ => do
            let col := σ.2
            let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (0 : Int)) fuel4
              (colRankStep col 3)
              (fun σ => do
                let total := σ.2
                let s ← SudoRt.modI total (4 : Int)
                let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
                  (freshStep col s 3)
                  (fun σ => do
                    let fresh := σ.2
                    let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), g) fuel4
                      (writeColStep fresh j 3)
                      (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
                      (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
                    pure _out)
                  (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
                pure _out)
              (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
            pure _out)
          (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
        pure _out
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, fs))
      | .cont fs =>
          if (j == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (j, fs))
          else do
            let j' ← SudoRt.addI j 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (j', fs))

theorem fits169 : FitsLen 169 := by
  unfold FitsLen i64MaxNat
  decide

def rankPref (xs : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rankPref xs n + rank (xs.getD n 0)

theorem take_succ_append {α : Type} (xs : List α) (n : Nat) (h : n < xs.length) :
    xs.take (n + 1) = xs.take n ++ [xs[n]'h] := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h' : n < xs.length :=
        Nat.lt_of_succ_lt_succ (by simpa [List.length_cons] using h)
      simp only [List.take, List.getElem_cons_succ]
      rw [ih n h']
      simp

theorem rankPref_take (xs : List Nat) (n : Nat) (hn : n ≤ xs.length) :
    rankPref xs n = sumNats ((xs.take n).map rank) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < xs.length := by omega
    have hget : xs.getD n 0 = xs[n] := by
      rw [List.getD, List.get?_eq_get hn']
      rfl
    rw [rankPref, ih (Nat.le_of_lt hn'), hget, take_succ_append xs n hn',
      List.map_append, sumNats_append]
    simp [sumNats]

theorem rankPref_full (xs : List Nat) :
    rankPref xs xs.length = rankSum rank xs := by
  rw [rankPref_take xs xs.length (Nat.le_refl _), List.take_length]
  rfl

theorem rowsSummed_zero (g : Grid Nat) : g = g := rfl

/-- Rows `0 .. n-1` already sum-rotated; the rest still original. -/
def rowsSummed (g : Grid Nat) (n : Nat) : Grid Nat :=
  fun r => if r.val < n then applyRowRotates cardRank g r else g r

theorem rowsSummed_four (g : Grid Nat) : rowsSummed g 4 = applyRowRotates cardRank g := by
  funext r
  simp [rowsSummed, r.isLt]

theorem rankAdd_hit (xs : List Nat) (j : Nat) (hj : j ≤ 12) (hlen : xs.length = 13)
    (hsum : rankPref xs j ≤ 156) :
    rankAddStep (embed xs) 12 (Int.ofNat j, Int.ofNat (rankPref xs j)) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, Int.ofNat (rankPref xs (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), Int.ofNat (rankPref xs (j + 1)))) := by
  unfold rankAddStep
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  have hat := atL_embed xs j (by omega)
  rw [hat]
  simp only [ok_bind]
  have hcell : xs[j]'(by omega) = xs.getD j 0 := by simp [List.getD, show j < xs.length by omega]
  rw [show Int.ofNat (xs[j]'(by omega)) = Int.ofNat (xs.getD j 0) from by simp [hcell]]
  rw [rank_of_refines (xs.getD j 0)]
  simp only [ok_bind]
  have hadd := addI_ofNat (rankPref xs j) (rank (xs.getD j 0))
    (FitsLen.of_le fits169 (by
      have hr : rank (xs.getD j 0) ≤ 13 := by
        simp [rank]
        omega
      omega))
  rw [hadd]
  simp only [ok_bind, rankPref]
  by_cases heq : j = 12
  · subst heq
    simp only [ok_bind]
    have hbeq : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat j) == (12 : Int)) = false := by
      cases hb : (Int.ofNat j) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one j (fits_succ_lt (by omega : j < 12) (by decide))]
    simp [ok_bind, heq]

theorem fuel13_eq : fuel13 = fuelRange (Int.ofNat 0) (Int.ofNat 12) := by
  rw [fuel13, fuelRange_le (Nat.zero_le _)]
  decide

theorem fuel4_eq : fuel4 = fuelRange (Int.ofNat 0) (Int.ofNat 3) := by
  rw [fuel4, fuelRange_le (Nat.zero_le _)]
  decide

theorem rotL_mod (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0) :
    rotL xs (k % xs.length) = rotL xs k := by
  simp [rotL, hne, Nat.mod_mod]

theorem rankPref_le (xs : List Nat) (n : Nat) : rankPref xs n ≤ 13 * n := by
  induction n with
  | zero => simp [rankPref]
  | succ n ih =>
    simp [rankPref, rank]
    omega

theorem sum_ranks_as_loop (g : Array (Array Int)) :
    Doubledeal.sum_ranks g =
      (do
        let _fromV := (0 : Int)
        let _toV := (3 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) (_fromV, g) fuel
          (sumRowStep _toV)
          (fun σ => do
            let g := σ.2
            let _fromV := (0 : Int)
            let _toV := (12 : Int)
            let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
            let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) (_fromV, g) fuel
              (sumColStep _toV)
              (fun σ => pure σ.2)
              (fun r => pure r))
            pure _out)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.sum_ranks
  rfl

theorem toList13_rowRot (g : Grid Nat) (r : Fin 4) :
    toList13 (applyRowRotates cardRank g r) =
      rotL (toList13 (g r)) (rowRankSum cardRank g r) := by
  simp [applyRowRotates, rowRotate, toList13_ofList13, cardRank]

theorem rowRank_pref (g : Grid Nat) (r : Fin 4) :
    rowRankSum cardRank g r = rankPref (toList13 (g r)) 13 := by
  rw [rowRankSum]
  have hr : rankSum cardRank (toList13 (g r)) = rankSum rank (toList13 (g r)) := by
    unfold rankSum cardRank
    rfl
  rw [hr, ← rankPref_full (toList13 (g r)), length_toList13]

theorem rowsSummed_succ (g : Grid Nat) (i : Nat) (hi : i < 4) :
    (fun r c => if r = ⟨i, hi⟩ then applyRowRotates cardRank g r c else rowsSummed g i r c) =
      rowsSummed g (i + 1) := by
  funext r c
  by_cases heq : r = ⟨i, hi⟩
  · simp [heq, rowsSummed, hi]
  · have hne : r.val ≠ i := fun h => heq (Fin.ext h)
    by_cases hlt : r.val < i
    · simp [rowsSummed, heq, hlt, Nat.lt_succ_of_lt hlt]
    · simp [rowsSummed, heq, hlt, show ¬ r.val < i + 1 by omega]

/-- Summing one original row and rotating it updates `rowsSummed`. -/
theorem sumRowStep_hit (g : Grid Nat) (i : Nat) (hi : i ≤ 3) :
    sumRowStep 3 (Int.ofNat i, embedGrid (rowsSummed g i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (rowsSummed g (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (rowsSummed g (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold sumRowStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hsame : rowsSummed g i ⟨i, hi4⟩ = g ⟨i, hi4⟩ := by
    funext c; simp [rowsSummed, show ¬ i < i from Nat.lt_irrefl i]
  have hat := atL_ofNat (embedGrid (rowsSummed g i)) i
    (by rw [embedGrid_size]; exact hi4)
  have hget := embedGrid_get (rowsSummed g i) ⟨i, hi4⟩
  have hat' :
      (embedGrid (rowsSummed g i))[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 (rowsSummed g i ⟨i, hi4⟩)) := by simpa using hget
  rw [hat'] at hat
  simp only [hat, hsame, ok_bind]
  let xs := toList13 (g ⟨i, hi4⟩)
  have hlen : xs.length = 13 := length_toList13 _
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      rankAddStep (embed xs) 12 (Int.ofNat j, Int.ofNat (rankPref xs j)) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, Int.ofNat (rankPref xs (j + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), Int.ofNat (rankPref xs (j + 1)))) :=
    fun j _ hj => rankAdd_hit xs j hj hlen (by
      have := rankPref_le xs j
      omega)
  have hsum : rankPref xs 13 = rowRankSum cardRank g ⟨i, hi4⟩ := by
    simpa [xs, length_toList13] using (rowRank_pref g ⟨i, hi4⟩).symm
  -- The rank loop's after rotates; discharge it on the final total.
  have hrot : rotL xs (rankPref xs 13 % 13) = rotL xs (rankPref xs 13) :=
    rotL_mod xs _ (by simp [hlen])
  have hafter :
      (do
        let amt ← SudoRt.modI (Int.ofNat (rankPref xs 13)) 13
        let row' ← Doubledeal.left_rotate (embed xs) amt
        let g' ← SudoRt.putL (embedGrid (rowsSummed g i)) (Int.ofNat i) row'
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g')) =
      .ok (SudoRt.Flow.cont (embedGrid (rowsSummed g (i + 1)))) := by
    rw [show (13 : Int) = Int.ofNat 13 from rfl, modI_ofNat (rankPref xs 13) (by decide)]
    simp only [ok_bind]
    rw [left_rotate_refines xs (rankPref xs 13 % 13) (fits52 (by rw [hlen]; decide))]
    simp only [ok_bind, hrot]
    have hlist : rotL xs (rankPref xs 13) = toList13 (applyRowRotates cardRank g ⟨i, hi4⟩) := by
      rw [hsum, toList13_rowRot]
    rw [hlist]
    have hsz : i < (embedGrid (rowsSummed g i)).size := by rw [embedGrid_size]; exact hi4
    rw [putL_ofNat _ _ _ hsz]
    have hrowlen : (toList13 (applyRowRotates cardRank g ⟨i, hi4⟩)).length = 13 :=
      length_toList13 _
    rw [embedGrid_setRow (rowsSummed g i) i hi4 _ hrowlen]
    have hfun :
        (fun r c =>
          if r = ⟨i, hi4⟩ then
            ofList13 (toList13 (applyRowRotates cardRank g ⟨i, hi4⟩)) hrowlen c
          else rowsSummed g i r c) =
          rowsSummed g (i + 1) := by
      have hrow : ofList13 (toList13 (applyRowRotates cardRank g ⟨i, hi4⟩)) hrowlen =
          applyRowRotates cardRank g ⟨i, hi4⟩ := ofList13_toList13 _
      have hswap :
          (fun r c =>
            if r = ⟨i, hi4⟩ then applyRowRotates cardRank g ⟨i, hi4⟩ c
            else rowsSummed g i r c) =
            (fun r c =>
              if r = ⟨i, hi4⟩ then applyRowRotates cardRank g r c
              else rowsSummed g i r c) := by
        funext r c
        by_cases hr : r = ⟨i, hi4⟩ <;> simp [hr]
      rw [hrow, hswap]
      exact rowsSummed_succ g i hi4
    rw [hfun]
    simp [ok_bind, Pure.pure, Except.pure]
  let afterRank := fun (σ : Int × Int) => do
    let amt ← SudoRt.modI σ.2 13
    let row' ← Doubledeal.left_rotate (embed xs) amt
    let g' ← SudoRt.putL (embedGrid (rowsSummed g i)) (Int.ofNat i) row'
    pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g')
  have hrun := chain_loop (rankAddStep (embed xs) 12) afterRank
    (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r))
    (fun j => (Int.ofNat (rankPref xs j))) 0 12 (Nat.zero_le _) hstep
    (.ok (SudoRt.Flow.cont (embedGrid (rowsSummed g (i + 1)))))
    (by simpa [afterRank] using hafter)
  have h0 : rankPref xs 0 = 0 := rfl
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (0 : Int)) fuel13 (rankAddStep (embed xs) 12) afterRank
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)) =
      SudoRt.runLoopOn (Int.ofNat 0, Int.ofNat (rankPref xs 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12)) (rankAddStep (embed xs) 12) afterRank
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)) := by
    rw [fuel13_eq, h0]
    rfl
  simp only [hcast, hrun, except_bind_pure, ok_bind]
  by_cases heq : i = 3
  · subst heq
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    have hneI : (i : Int) ≠ (3 : Int) := by
      intro h
      exact heq (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h))
    simp [hbeq, hneI, Pure.pure, Except.pure, ok_bind]
    rw [← ofNat_eq_natCast i]
    rw [addI_ofNat_one i (fits_succ_lt hi4 (by decide : 4 ≤ 52))]
    simp [ok_bind, heq]

theorem rowsSummed_base (g : Grid Nat) : rowsSummed g 0 = g := by
  funext r c
  simp [rowsSummed]

/-- Columns `0 .. n-1` already sum-rotated; the rest still original. -/
def colsSummed (g : Grid Nat) (n : Nat) : Grid Nat :=
  fun r c => if c.val < n then applyColRotates cardRank g r c else g r c

theorem colsSummed_zero (g : Grid Nat) : colsSummed g 0 = g := by
  funext r c
  simp [colsSummed]

theorem colsSummed_all (g : Grid Nat) : colsSummed g 13 = applyColRotates cardRank g := by
  funext r c
  simp [colsSummed, c.isLt]

/-- Column `j` while its first `n` rows have been written back. -/
def colsWriting (g : Grid Nat) (j n : Nat) : Grid Nat :=
  fun r c =>
    if c.val < j then applyColRotates cardRank g r c
    else if c.val = j ∧ r.val < n then applyColRotates cardRank g r c
    else g r c

theorem colsWriting_zero (g : Grid Nat) (j : Nat) :
    colsWriting g j 0 = colsSummed g j := by
  funext r c
  simp [colsWriting, colsSummed]

theorem colsWriting_four (g : Grid Nat) (j : Nat) :
    colsWriting g j 4 = colsSummed g (j + 1) := by
  funext r c
  have hr : r.val < 4 := r.isLt
  by_cases hlt : c.val < j
  · simp [colsWriting, colsSummed, hlt, hr, Nat.lt_succ_of_lt hlt]
  · by_cases heq : c.val = j
    · simp [colsWriting, colsSummed, hlt, heq, hr, show c.val < j + 1 by omega]
    · simp [colsWriting, colsSummed, hlt, heq, show ¬ c.val < j + 1 by omega]

theorem colsWriting_succ (g : Grid Nat) (j i : Nat) (hj : j < 13) (hi : i < 4) :
    (fun r c =>
      if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then applyColRotates cardRank g r c
      else colsWriting g j i r c) =
      colsWriting g j (i + 1) := by
  funext r c
  by_cases hr : r = ⟨i, hi⟩
  · by_cases hc : c = ⟨j, hj⟩
    · simp [hr, hc, colsWriting, hi, hj]
    · have hcne : c.val ≠ j := by
        intro h
        exact hc (Fin.ext h)
      simp [colsWriting, hr, hc, hcne]
  · have hrne : r.val ≠ i := by
      intro h
      exact hr (Fin.ext h)
    by_cases hlt : c.val < j
    · simp [colsWriting, hr, hlt]
    · by_cases hc : c.val = j
      · have hiff : r.val < i + 1 ↔ r.val < i := by
          constructor
          · intro hlt'
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') hrne
          · exact fun h => Nat.lt_succ_of_lt h
        simp [colsWriting, hr, hlt, hc, hiff]
      · simp [colsWriting, hr, hlt, hc]

theorem subI_bounded (a b : Nat) (ha : a ≤ 4) (hb : b ≤ 4) :
    SudoRt.subI (Int.ofNat a) (Int.ofNat b) = .ok ((a : Int) - (b : Int)) := by
  unfold SudoRt.subI SudoRt.narrowI
  have hmin : ¬ ((a : Int) - (b : Int)) < SudoRt.i64Min := by
    have : SudoRt.i64Min < (-4 : Int) := by decide
    omega
  have hmax : ¬ ((a : Int) - (b : Int)) > SudoRt.i64Max := by
    have : (4 : Int) ≤ SudoRt.i64Max := by decide
    have : (a : Int) - (b : Int) ≤ 4 := by omega
    omega
  simp [hmin, hmax]

theorem modI_sub_small (a b n : Nat) (ha : a < n) (hb : b < n) (hn : 0 < n) :
    SudoRt.modI ((a : Int) - (b : Int)) (Int.ofNat n) =
      .ok (Int.ofNat ((a + (n - b)) % n)) := by
  unfold SudoRt.modI
  have hb0 : ((Int.ofNat n) == (0 : Int)) = false := by
    cases hbv : (Int.ofNat n) == (0 : Int) with
    | false => rfl
    | true =>
      exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv))
        (Nat.ne_of_gt hn)
  rw [hb0]
  exact congrArg Except.ok (fmod_sub_small a b n ha hb hn)

theorem getElem_rotR {α : Type} (xs : List α) (k i : Nat)
    (hne : xs.length ≠ 0) (hi : i < xs.length) :
    (rotR xs k)[i]'(by rw [length_rotR]; exact hi) =
      xs[(i + (xs.length - k % xs.length)) % xs.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero hne)) := by
  unfold rotR
  simp only [hne, ↓reduceIte]
  have hk : k % xs.length < xs.length := Nat.mod_lt _ (Nat.pos_of_ne_zero hne)
  have hdrop : (xs.drop (xs.length - k % xs.length)).length = k % xs.length := by
    rw [List.length_drop]
    omega
  by_cases hi' : i < k % xs.length
  · have hidx : i < (xs.drop (xs.length - k % xs.length)).length := by rw [hdrop]; exact hi'
    rw [List.getElem_append_left hidx, List.getElem_drop]
    have hlt : i + (xs.length - k % xs.length) < xs.length := by omega
    have hadd : xs.length - k % xs.length + i = i + (xs.length - k % xs.length) :=
      Nat.add_comm _ _
    simp [Nat.mod_eq_of_lt hlt, hadd]
  · have hge : (xs.drop (xs.length - k % xs.length)).length ≤ i := by rw [hdrop]; omega
    rw [List.getElem_append_right hge]
    simp only [hdrop]
    rw [List.getElem_take]
    have hmod : (i + (xs.length - k % xs.length)) % xs.length = i - k % xs.length := by
      have : i + (xs.length - k % xs.length) = xs.length + (i - k % xs.length) := by omega
      rw [this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    simp [hmod]

theorem colRank_pref (g : Grid Nat) (c : Fin 13) :
    colRankSum cardRank g c = rankPref (toList4 (fun r => g r c)) 4 := by
  rw [colRankSum]
  have hr :
      rankSum cardRank (toList4 (fun r => g r c)) =
        rankSum rank (toList4 (fun r => g r c)) := by
    unfold rankSum cardRank
    rfl
  rw [hr, ← rankPref_full, length_toList4]

theorem colCollectStep_hit (grid : Grid Nat) (j : Nat) (hj : j < 13) (i : Nat) (hi : i ≤ 3) :
    colCollectStep (embedGrid grid) (Int.ofNat j) 3
      (Int.ofNat i, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i,
          embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold colCollectStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hat := atL_ofNat (embedGrid grid) i (by rw [embedGrid_size]; exact hi4)
  have hrow := embedGrid_get grid ⟨i, hi4⟩
  have hat' :
      (embedGrid grid)[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 (grid ⟨i, hi4⟩)) := by simpa using hrow
  rw [hat'] at hat
  simp only [hat, ok_bind]
  have hget := getElem_toList13 (grid ⟨i, hi4⟩) ⟨j, hj⟩
  have hatC := atL_embed (toList13 (grid ⟨i, hi4⟩)) j (by rw [length_toList13]; exact hj)
  rw [hatC]
  have hpush :
      (embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)).push
          (Int.ofNat (grid ⟨i, hi4⟩ ⟨j, hj⟩)) =
        embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i ++ [grid ⟨i, hi4⟩ ⟨j, hj⟩]) := by
    simp [embed, Array.push]
  simp only [ok_bind, hget, appendL_spec, hpush]
  have hidx : (toList4 (fun r => grid r ⟨j, hj⟩))[i]'(by rw [length_toList4]; exact hi4) =
      grid ⟨i, hi4⟩ ⟨j, hj⟩ := getElem_toList4 _ ⟨i, hi4⟩
  have hnext :
      (toList4 (fun r => grid r ⟨j, hj⟩)).take i ++ [grid ⟨i, hi4⟩ ⟨j, hj⟩] =
        (toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1) := by
    rw [← hidx]
    exact (take_succ_append (toList4 (fun r => grid r ⟨j, hj⟩)) i
      (by rw [length_toList4]; exact hi4)).symm
  rw [hnext]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem colRankStep_hit (xs : List Nat) (i : Nat) (hi : i ≤ 3) (hlen : xs.length = 4)
    (hsum : rankPref xs i ≤ 39) :
    colRankStep (embed xs) 3 (Int.ofNat i, Int.ofNat (rankPref xs i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, Int.ofNat (rankPref xs (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), Int.ofNat (rankPref xs (i + 1)))) := by
  unfold colRankStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hat := atL_embed xs i (by omega)
  rw [hat]
  simp only [ok_bind]
  have hcell : xs[i]'(by omega) = xs.getD i 0 := by simp [List.getD, show i < xs.length by omega]
  rw [show Int.ofNat (xs[i]'(by omega)) = Int.ofNat (xs.getD i 0) from by simp [hcell]]
  rw [rank_of_refines (xs.getD i 0)]
  simp only [ok_bind]
  have hadd := addI_ofNat (rankPref xs i) (rank (xs.getD i 0))
    (fits52 (by
      have hr : rank (xs.getD i 0) ≤ 13 := by
        simp [rank]
        omega
      omega))
  rw [hadd]
  simp only [ok_bind, rankPref]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem rotR_mod (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0) :
    rotR xs (k % xs.length) = rotR xs k := by
  simp [rotR, hne, Nat.mod_mod]

theorem applyCol_get (g : Grid Nat) (r : Fin 4) (c : Fin 13) :
    applyColRotates cardRank g r c =
      (rotR (toList4 (fun r' => g r' c)) (colRankSum cardRank g c))[r.val]'
        (by rw [length_rotR, length_toList4]; exact r.isLt) := by
  unfold applyColRotates colRotate ofList4
  rfl

theorem getElem_toList13_nat (f : Fin 13 → α) (i : Nat) (hi : i < 13) :
    (toList13 f)[i]'(by rw [length_toList13]; exact hi) = f ⟨i, hi⟩ := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | n + 13 => omega

theorem toList13_set {α : Type} (f : Fin 13 → α) (j : Nat) (_hj : j < 13) (v : α) :
    (toList13 f).set j v = toList13 (fun c => if c.val = j then v else f c) := by
  apply List.ext_getElem
  · simp [length_toList13, List.length_set]
  · intro i hi hi'
    have hi13 : i < 13 := by simpa [length_toList13] using hi
    have hL := getElem_toList13_nat f i hi13
    have hR := getElem_toList13_nat (fun c => if c.val = j then v else f c) i hi13
    rw [List.getElem_set]
    by_cases h : j = i
    · subst h
      simp only [↓reduceIte]
      have hfun : (fun c => if c.val = j then v else f c) ⟨j, hi13⟩ = v := by simp
      exact (hR.trans hfun).symm
    · simp only [h, ↓reduceIte]
      have hne : i ≠ j := fun h' => h h'.symm
      have hfun : (fun c => if c.val = j then v else f c) ⟨i, hi13⟩ = f ⟨i, hi13⟩ := by
        simp [hne]
      exact hL.trans (hfun.symm.trans hR.symm)

theorem embed_list_set (xs : List Nat) (k : Nat) (hk : k < xs.length) (v : Nat) :
    (embed xs).set ⟨k, by rw [size_embed]; exact hk⟩ (Int.ofNat v) = embed (xs.set k v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro i hi hi'
    rw [Array.getElem_set]
    by_cases h : k = i
    · simp [h, embed, get_embed, List.getElem_set]
    · simp [h, embed, get_embed, List.getElem_set]

theorem embedGrid_setCell (g : Grid Nat) (i j : Nat) (hi : i < 4) (hj : j < 13) (v : Nat) :
    ((embedGrid g).set ⟨i, by rw [embedGrid_size]; exact hi⟩
        ((embed (toList13 (g ⟨i, hi⟩))).set
          ⟨j, by rw [size_embed, length_toList13]; exact hj⟩ (Int.ofNat v))) =
      embedGrid (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) := by
  let idx : Fin (embedGrid g).size := ⟨i, by rw [embedGrid_size]; exact hi⟩
  apply Array.ext
  · simp [embedGrid, Array.size_set]
  · intro n hn hn'
    have hn4 : n < 4 := by simpa [embedGrid] using hn'
    rw [Array.getElem_set]
    by_cases heq : idx.val = n
    · rw [if_pos heq]
      have hin : (⟨i, hi⟩ : Fin 4) = ⟨n, hn4⟩ := by
        apply Fin.ext
        simpa [idx] using heq
      have hset := embed_list_set (toList13 (g ⟨i, hi⟩)) j
        (by rw [length_toList13]; exact hj) v
      rw [hset]
      have hget := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) ⟨n, hn4⟩
      rw [hget]
      apply congrArg embed
      rw [toList13_set (g ⟨i, hi⟩) j hj v]
      apply congrArg toList13
      funext c
      by_cases hc : c.val = j
      · have hc' : c = ⟨j, hj⟩ := Fin.ext hc
        simp [hin, hc, hc']
      · have hc' : ¬ (c = ⟨j, hj⟩) := by
          intro h
          exact hc (by simpa using congrArg Fin.val h)
        simp [hin, hc, hc']
    · simp only [heq, ↓reduceIte]
      have hget := embedGrid_get g ⟨n, hn4⟩
      have hget' := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) ⟨n, hn4⟩
      rw [hget, hget']
      have hr : (⟨n, hn4⟩ : Fin 4) ≠ ⟨i, hi⟩ := by
        intro h
        exact heq (by simpa [idx] using (Fin.ext_iff.mp h).symm)
      apply congrArg embed
      apply congrArg toList13
      funext c
      simp [hr]

theorem freshStep_hit (xs : List Nat) (s i : Nat) (hi : i ≤ 3) (hs : s < 4)
    (hlen : xs.length = 4) :
    freshStep (embed xs) (Int.ofNat s) 3
      (Int.ofNat i, embed ((rotR xs s).take i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed ((rotR xs s).take (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed ((rotR xs s).take (i + 1)))) := by
  have hi4 : i < 4 := by omega
  have hiL : i < xs.length := by rw [hlen]; exact hi4
  have hiR : i < (rotR xs s).length := by rw [length_rotR]; exact hiL
  unfold freshStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  rw [subI_bounded i s (by omega) (by omega)]
  simp only [ok_bind]
  rw [show (4 : Int) = Int.ofNat 4 from rfl]
  rw [modI_sub_small i s 4 hi4 hs (by decide)]
  simp only [ok_bind]
  have hixlt : (i + (4 - s)) % 4 < xs.length := by
    rw [hlen]
    exact Nat.mod_lt _ (by decide)
  have hat := atL_embed xs ((i + (4 - s)) % 4) hixlt
  rw [hat]
  simp only [ok_bind]
  have hcell :
      xs[(i + (4 - s)) % 4]'hixlt = (rotR xs s)[i]'hiR := by
    rw [getElem_rotR xs s i (by rw [hlen]; decide) hiL]
    have hidx :
        (i + (xs.length - s % xs.length)) % xs.length = (i + (4 - s)) % 4 := by
      rw [hlen, Nat.mod_eq_of_lt hs]
    simp [hidx]
  rw [hcell]
  have hpush :
      (embed ((rotR xs s).take i)).push (Int.ofNat ((rotR xs s)[i]'hiR)) =
        embed ((rotR xs s).take i ++ [(rotR xs s)[i]'hiR]) := by
    simp [embed, Array.push]
  simp only [appendL_spec, hpush]
  have hnext :
      (rotR xs s).take i ++ [(rotR xs s)[i]'hiR] = (rotR xs s).take (i + 1) :=
    (take_succ_append (rotR xs s) i hiR).symm
  rw [hnext]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem writeColStep_hit (g0 : Grid Nat) (j : Nat) (hj : j < 13) (i : Nat) (hi : i ≤ 3)
    (fresh : List Nat) (hf : fresh.length = 4)
    (hv : fresh[i]'(by rw [hf]; omega) = applyColRotates cardRank g0 ⟨i, by omega⟩ ⟨j, hj⟩) :
    writeColStep (embed fresh) (Int.ofNat j) 3
      (Int.ofNat i, embedGrid (colsWriting g0 j i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (colsWriting g0 j (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (colsWriting g0 j (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold writeColStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hatG := atL_ofNat (embedGrid (colsWriting g0 j i)) i (by rw [embedGrid_size]; exact hi4)
  have hrow := embedGrid_get (colsWriting g0 j i) ⟨i, hi4⟩
  have hatG' :
      (embedGrid (colsWriting g0 j i))[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 (colsWriting g0 j i ⟨i, hi4⟩)) := by simpa using hrow
  rw [hatG'] at hatG
  simp only [hatG, ok_bind]
  have hatF := atL_embed fresh i (by rw [hf]; exact hi4)
  rw [hatF]
  simp only [ok_bind, hv]
  have hputR := putL_ofNat (embed (toList13 (colsWriting g0 j i ⟨i, hi4⟩))) j
    (Int.ofNat (applyColRotates cardRank g0 ⟨i, hi4⟩ ⟨j, hj⟩))
    (by rw [size_embed, length_toList13]; exact hj)
  rw [hputR]
  simp only [ok_bind]
  have hputG := putL_ofNat (embedGrid (colsWriting g0 j i)) i
    ((embed (toList13 (colsWriting g0 j i ⟨i, hi4⟩))).set
      ⟨j, by rw [size_embed, length_toList13]; exact hj⟩
      (Int.ofNat (applyColRotates cardRank g0 ⟨i, hi4⟩ ⟨j, hj⟩)))
    (by rw [embedGrid_size]; exact hi4)
  rw [hputG]
  simp only [ok_bind]
  rw [embedGrid_setCell (colsWriting g0 j i) i j hi4 hj _]
  have hswap :
      (fun r c =>
        if r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ then applyColRotates cardRank g0 ⟨i, hi4⟩ ⟨j, hj⟩
        else colsWriting g0 j i r c) =
        (fun r c =>
          if r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ then applyColRotates cardRank g0 r c
          else colsWriting g0 j i r c) := by
    funext r c
    by_cases hrc : r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ <;> simp [hrc]
  rw [hswap, colsWriting_succ g0 j i hj hi4]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem write_loop (g0 : Grid Nat) (j : Nat) (hj : j < 13) (fresh : List Nat)
    (hf : fresh.length = 4)
    (hv : ∀ i : Nat, (hi : i < 4) →
      fresh[i]'(by rw [hf]; exact hi) = applyColRotates cardRank g0 ⟨i, hi⟩ ⟨j, hj⟩) :
    SudoRt.runLoopOn ((0 : Int), embedGrid (colsSummed g0 j)) fuel4
      (writeColStep (embed fresh) (Int.ofNat j) 3)
      (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
      (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)) =
      pure (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))) := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      writeColStep (embed fresh) (Int.ofNat j) 3
        (Int.ofNat i, embedGrid (colsWriting g0 j i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (colsWriting g0 j (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (colsWriting g0 j (i + 1)))) := by
    intro i _ hi
    have hi4 : i < 4 := by omega
    exact writeColStep_hit g0 j hj i hi fresh hf (by
      simpa [hf] using hv i hi4)
  have hrun := chain_loop
    (writeColStep (embed fresh) (Int.ofNat j) 3)
    (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
    (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r))
    (fun i => embedGrid (colsWriting g0 j i)) 0 3 (Nat.zero_le _) hstep
    (pure (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))))
    (by simp [colsWriting_four])
  have hcast :
      SudoRt.runLoopOn ((0 : Int), embedGrid (colsSummed g0 j)) fuel4
        (writeColStep (embed fresh) (Int.ofNat j) 3)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)) =
      SudoRt.runLoopOn (Int.ofNat 0, embedGrid (colsWriting g0 j 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (writeColStep (embed fresh) (Int.ofNat j) 3)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)) := by
    rw [fuel4_eq, colsWriting_zero]
    rfl
  simpa [Pure.pure, Except.pure] using hcast.trans hrun

theorem fresh_loop {β : Type} (xs : List Nat) (s : Nat) (hs : s < 4) (hlen : xs.length = 4)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embed (rotR xs s)) = goal) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
      (freshStep (embed xs) (Int.ofNat s) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      freshStep (embed xs) (Int.ofNat s) 3
        (Int.ofNat i, embed ((rotR xs s).take i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed ((rotR xs s).take (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed ((rotR xs s).take (i + 1)))) :=
    fun i _ hi => freshStep_hit xs s i hi hs hlen
  have ht : (rotR xs s).take 4 = rotR xs s := by
    simpa [length_rotR, hlen] using (List.take_length (rotR xs s))
  have hrun := chain_loop
    (freshStep (embed xs) (Int.ofNat s) 3) after onRet
    (fun i => embed ((rotR xs s).take i)) 0 3 (Nat.zero_le _) hstep goal
    (by simpa [ht] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
        (freshStep (embed xs) (Int.ofNat s) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((rotR xs s).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (freshStep (embed xs) (Int.ofNat s) 3) after onRet := by
    rw [fuel4_eq, List.take_zero, embed_nil]
    rfl
  exact hcast.trans hrun

theorem rank_loop {β : Type} (xs : List Nat) (hlen : xs.length = 4)
    (after : Int × Int → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, Int.ofNat (rankPref xs 4)) = goal) :
    SudoRt.runLoopOn ((0 : Int), (0 : Int)) fuel4
      (colRankStep (embed xs) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      colRankStep (embed xs) 3 (Int.ofNat i, Int.ofNat (rankPref xs i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, Int.ofNat (rankPref xs (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), Int.ofNat (rankPref xs (i + 1)))) :=
    fun i _ hi => colRankStep_hit xs i hi hlen (by
      have := rankPref_le xs i
      omega)
  have hrun := chain_loop
    (colRankStep (embed xs) 3) after onRet
    (fun i => Int.ofNat (rankPref xs i)) 0 3 (Nat.zero_le _) hstep goal hafter
  have h0 : rankPref xs 0 = 0 := rfl
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (0 : Int)) fuel4
        (colRankStep (embed xs) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, Int.ofNat (rankPref xs 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (colRankStep (embed xs) 3) after onRet := by
    rw [fuel4_eq, h0]
    rfl
  exact hcast.trans hrun

theorem collect_loop {β : Type} (grid : Grid Nat) (j : Nat) (hj : j < 13)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embed (toList4 (fun r => grid r ⟨j, hj⟩))) = goal) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
      (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      colCollectStep (embedGrid grid) (Int.ofNat j) 3
        (Int.ofNat i, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1)))) :=
    fun i _ hi => colCollectStep_hit grid j hj i hi
  have ht : (toList4 (fun r => grid r ⟨j, hj⟩)).take 4 =
      toList4 (fun r => grid r ⟨j, hj⟩) := by
    simpa [length_toList4] using
      (List.take_length (toList4 (fun r => grid r ⟨j, hj⟩)))
  have hrun := chain_loop
    (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet
    (fun i => embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) 0 3 (Nat.zero_le _) hstep
    goal (by simpa [ht] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
        (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet := by
    rw [fuel4_eq, List.take_zero, embed_nil]
    rfl
  exact hcast.trans hrun

/-- One column rotate, from a grid whose earlier columns are already rotated. -/
theorem sumColStep_hit (g0 : Grid Nat) (j : Nat) (hj : j ≤ 12) :
    sumColStep 12 (Int.ofNat j, embedGrid (colsSummed g0 j)) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, embedGrid (colsSummed g0 (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embedGrid (colsSummed g0 (j + 1)))) := by
  have hj13 : j < 13 := by omega
  let grid := colsSummed g0 j
  let xs := toList4 (fun r => g0 r ⟨j, hj13⟩)
  have hlen : xs.length = 4 := length_toList4 _
  have hxs : toList4 (fun r => grid r ⟨j, hj13⟩) = xs := by
    apply congrArg toList4
    funext r
    simp [grid, colsSummed, show ¬ j < j from Nat.lt_irrefl j]
  unfold sumColStep
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  have hwriteDone :
      ∀ (s : Nat) (hs : s < 4),
        s = rankPref xs 4 % 4 →
        (do
          let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
            (freshStep (embed xs) (Int.ofNat s) 3)
            (fun σ => do
              let fresh := σ.2
              let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid grid) fuel4
                (writeColStep fresh (Int.ofNat j) 3)
                (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
                (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
              pure _out)
            (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
          pure _out) =
        .ok (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))) := by
    intro s hs hsmod
    have hfresh : rotR xs s = rotR xs (colRankSum cardRank g0 ⟨j, hj13⟩) := by
      have hsum : rankPref xs 4 = colRankSum cardRank g0 ⟨j, hj13⟩ := by
        simpa [xs] using (colRank_pref g0 ⟨j, hj13⟩).symm
      have hmod : rankPref xs 4 % 4 = rankPref xs 4 % xs.length := by rw [hlen]
      rw [hsmod, ← hsum, hmod]
      exact rotR_mod xs (rankPref xs 4) (by rw [hlen]; decide)
    have hv : ∀ i : Nat, (hi : i < 4) →
        (rotR xs s)[i]'(by rw [length_rotR, hlen]; exact hi) =
          applyColRotates cardRank g0 ⟨i, hi⟩ ⟨j, hj13⟩ := by
      intro i hi
      simpa [xs, hfresh] using (applyCol_get g0 ⟨i, hi⟩ ⟨j, hj13⟩).symm
    have hwrite := write_loop g0 j hj13 (rotR xs s) (by rw [length_rotR, hlen]) hv
    have hfreshLoop := fresh_loop xs s hs hlen
      (fun σ => do
        let fresh := σ.2
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid grid) fuel4
          (writeColStep fresh (Int.ofNat j) 3)
          (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
          (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
        pure _out)
      (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r))
      (.ok (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))))
      (by
        dsimp only
        rw [except_bind_pure]
        exact hwrite)
    simpa [except_bind_pure] using hfreshLoop
  have hbody := collect_loop grid j hj13
    (fun σ => do
      let col := σ.2
      let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (0 : Int)) fuel4
        (colRankStep col 3)
        (fun σ => do
          let total := σ.2
          let s ← SudoRt.modI total (4 : Int)
          let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
            (freshStep col s 3)
            (fun σ => do
              let fresh := σ.2
              let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid grid) fuel4
                (writeColStep fresh (Int.ofNat j) 3)
                (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
                (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
              pure _out)
            (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
          pure _out)
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
      pure _out)
    (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r))
    (.ok (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))))
    (by
      dsimp only
      rw [hxs, except_bind_pure]
      exact rank_loop xs hlen
        (fun σ => do
          let total := σ.2
          let s ← SudoRt.modI total (4 : Int)
          let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
            (freshStep (embed xs) s 3)
            (fun σ => do
              let fresh := σ.2
              let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid grid) fuel4
                (writeColStep fresh (Int.ofNat j) 3)
                (fun σ => pure (SudoRt.Flow.cont (ρ := Array (Array Int)) σ.2))
                (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
              pure _out)
            (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)))
          pure _out)
        (fun r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r))
        (.ok (SudoRt.Flow.cont (embedGrid (colsSummed g0 (j + 1)))))
        (by
          dsimp only
          rw [show (4 : Int) = Int.ofNat 4 from rfl, modI_ofNat (rankPref xs 4) (by decide)]
          simp only [ok_bind]
          exact hwriteDone (rankPref xs 4 % 4) (Nat.mod_lt _ (by decide)) rfl))
  rw [hbody]
  simp only [except_bind_pure, ok_bind, Pure.pure, Except.pure]
  by_cases heq : j = 12
  · subst heq
    have hbeq : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hbeq]
  · have hbeq : ((Int.ofNat j) == (12 : Int)) = false := by
      cases hb : (Int.ofNat j) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    have hneI : (j : Int) ≠ (12 : Int) := by
      intro h
      exact heq (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h))
    simp [hbeq, hneI, ok_bind]
    rw [← ofNat_eq_natCast j]
    rw [addI_ofNat_one j (fits_succ_lt hj13 (by decide : 13 ≤ 52))]
    simp [ok_bind, heq]

theorem row_loop {β : Type} (g : Grid Nat)
    (after : Int × Array (Array Int) → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embedGrid (applyRowRotates cardRank g)) = goal) :
    SudoRt.runLoopOn ((0 : Int), embedGrid g) fuel4
      (sumRowStep 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      sumRowStep 3 (Int.ofNat i, embedGrid (rowsSummed g i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (rowsSummed g (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (rowsSummed g (i + 1)))) :=
    fun i _ hi => sumRowStep_hit g i hi
  have hrun := chain_loop (sumRowStep 3) after onRet
    (fun i => embedGrid (rowsSummed g i)) 0 3 (Nat.zero_le _) hstep goal
    (by simpa [rowsSummed_four] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), embedGrid g) fuel4 (sumRowStep 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embedGrid (rowsSummed g 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3)) (sumRowStep 3) after onRet := by
    rw [fuel4_eq, rowsSummed_base]
    rfl
  exact hcast.trans hrun

theorem col_loop {β : Type} (g0 : Grid Nat)
    (after : Int × Array (Array Int) → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 12, embedGrid (applyColRotates cardRank g0)) = goal) :
    SudoRt.runLoopOn ((0 : Int), embedGrid g0) fuel13
      (sumColStep 12) after onRet = goal := by
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      sumColStep 12 (Int.ofNat j, embedGrid (colsSummed g0 j)) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, embedGrid (colsSummed g0 (j + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embedGrid (colsSummed g0 (j + 1)))) :=
    fun j _ hj => sumColStep_hit g0 j hj
  have hrun := chain_loop (sumColStep 12) after onRet
    (fun j => embedGrid (colsSummed g0 j)) 0 12 (Nat.zero_le _) hstep goal
    (by simpa [colsSummed_all] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), embedGrid g0) fuel13 (sumColStep 12) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embedGrid (colsSummed g0 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12)) (sumColStep 12) after onRet := by
    rw [fuel13_eq, colsSummed_zero]
    rfl
  exact hcast.trans hrun

theorem sum_ranks_refines (g : Grid Nat) :
    Doubledeal.sum_ranks (embedGrid g) = .ok (embedGrid (sumRanks cardRank g)) := by
  rw [sum_ranks_as_loop]
  dsimp only
  rw [show (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) = fuel4 from rfl,
    except_bind_pure]
  exact row_loop g
    (fun σ => do
      let grid := σ.2
      let _fromV := (0 : Int)
      let _toV := (12 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) (_fromV, grid) fuel
        (sumColStep _toV)
        (fun σ => pure σ.2)
        (fun r => pure r))
      pure _out)
    (fun r => pure r)
    (.ok (embedGrid (sumRanks cardRank g)))
    (by
      dsimp only
      rw [show (if (0 : Int) > (12 : Int) then 1 else ((12 : Int) - 0).natAbs + 1) = fuel13 from rfl,
        except_bind_pure]
      exact col_loop (applyRowRotates cardRank g)
        (fun σ => pure σ.2)
        (fun r => pure r)
        (.ok (embedGrid (sumRanks cardRank g)))
        (by simp [sumRanks, Pure.pure, Except.pure]))

end DoubleDeal.Link2
