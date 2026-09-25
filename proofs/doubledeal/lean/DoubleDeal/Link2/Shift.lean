/-
  LINK 2. `shift_rows` refines algebraic `shiftRows` on a 4×13 grid.
-/
import Doubledeal
import DoubleDeal.Grid
import DoubleDeal.ShiftRows
import DoubleDeal.SumRanks
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck

namespace DoubleDeal.Link2

def embedGrid (g : Grid Nat) : Array (Array Int) :=
  #[embed (toList13 (g 0)), embed (toList13 (g 1)),
    embed (toList13 (g 2)), embed (toList13 (g 3))]

theorem embedGrid_size (g : Grid Nat) : (embedGrid g).size = 4 := by
  simp [embedGrid]

theorem embedGrid_get (g : Grid Nat) (r : Fin 4) :
    (embedGrid g)[r.val]'(by rw [embedGrid_size]; exact r.isLt) =
      embed (toList13 (g r)) := by
  revert r
  intro ⟨v, hv⟩
  match v with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => omega

/-- Rows `0 .. n-1` already shifted; the rest still original. -/
def rowsShifted (g : Grid Nat) (n : Nat) : Grid Nat :=
  fun r c => if r.val < n then shiftRows g r c else g r c

theorem rowsShifted_zero (g : Grid Nat) : rowsShifted g 0 = g := by
  funext r c
  simp [rowsShifted]

theorem rowsShifted_four (g : Grid Nat) : rowsShifted g 4 = shiftRows g := by
  funext r c
  have : r.val < 4 := r.isLt
  simp [rowsShifted, this]

theorem rowsShifted_succ (g : Grid Nat) (i : Nat) (hi : i < 4) :
    (fun r c => if r = ⟨i, hi⟩ then shiftRows g r c else rowsShifted g i r c) =
      rowsShifted g (i + 1) := by
  funext r c
  by_cases heq : r = ⟨i, hi⟩
  · cases heq
    simp [rowsShifted, hi]
  · have hne : r.val ≠ i := by
      intro hv
      exact heq (Fin.ext hv)
    simp only [rowsShifted, heq, ↓reduceIte]
    by_cases hlt : r.val < i
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have hge : i + 1 ≤ r.val := by omega
      simp [hlt, Nat.not_lt_of_ge hge]

def shiftRowsStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let i := σ.1
  let g := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, g))
    else
      match ← ((do
        let _ix181 := i
        let _t182 ← SudoRt.atL g i
        let _t183 ← Doubledeal.left_rotate _t182 i
        let _t184 ← SudoRt.putL g _ix181 _t183
        let g := _t184
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, _fs))
      | .cont _fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, _fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', _fs))

theorem shift_rows_as_loop (g : Array (Array Int)) :
    Doubledeal.shift_rows g =
      (do
        let _fromV := (0 : Int)
        let _toV := (3 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _init := (_fromV, g)
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) _init fuel
          (shiftRowsStep _toV)
          (fun σ =>
            let g := σ.2
            pure g)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.shift_rows
  rfl

theorem getElem_rotL {α : Type} (xs : List α) (k i : Nat)
    (hne : xs.length ≠ 0) (hi : i < xs.length) :
    (rotL xs k)[i]'(by rw [length_rotL]; exact hi) =
      xs[(i + k % xs.length) % xs.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero hne)) := by
  unfold rotL
  simp only [hne, ↓reduceIte]
  have hk'lt : k % xs.length < xs.length := Nat.mod_lt _ (Nat.pos_of_ne_zero hne)
  have hdrop : (xs.drop (k % xs.length)).length = xs.length - k % xs.length :=
    List.length_drop _ _
  by_cases hi' : i < xs.length - k % xs.length
  · have hidx : i < (xs.drop (k % xs.length)).length := by rw [hdrop]; exact hi'
    rw [List.getElem_append_left hidx, List.getElem_drop]
    have hsum : i + k % xs.length < xs.length := by omega
    simp [Nat.mod_eq_of_lt hsum, Nat.add_comm]
  · have hge : (xs.drop (k % xs.length)).length ≤ i := by rw [hdrop]; omega
    rw [List.getElem_append_right hge]
    simp only [hdrop]
    rw [List.getElem_take]
    have hmod : (i + k % xs.length) % xs.length = i - (xs.length - k % xs.length) := by
      have : i + k % xs.length = xs.length + (i - (xs.length - k % xs.length)) := by omega
      rw [this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    simp [hmod]

theorem toList13_shiftRow (g : Grid Nat) (r : Fin 4) :
    toList13 (shiftRows g r) = rotL (toList13 (g r)) r.val := by
  apply List.ext_getElem
  · simp [length_toList13, length_rotL]
  · intro i hi hi'
    have hi13 : i < 13 := by simpa [length_toList13] using hi
    have hr : r.val < 13 := by have := r.isLt; omega
    have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
    have hL : (toList13 (shiftRows g r))[i]'hi =
        shiftRows g r ⟨i, hi13⟩ :=
      getElem_toList13 (shiftRows g r) ⟨i, hi13⟩
    have hR : (rotL (toList13 (g r)) r.val)[i]'hi' =
        (toList13 (g r))[(i + r.val) % 13]'(Nat.mod_lt _ (by decide)) := by
      rw [getElem_rotL _ _ _ hne (by simpa [length_toList13] using hi13)]
      simp [length_toList13, Nat.mod_eq_of_lt hr]
    rw [hL, hR, shiftRows]
    exact (getElem_toList13 (g r) ⟨(i + r.val) % 13, Nat.mod_lt _ (by decide)⟩).symm

theorem embedGrid_setRow (g : Grid Nat) (i : Nat) (hi : i < 4) (row : List Nat)
    (hrow : row.length = 13) :
    (embedGrid g).set ⟨i, by rw [embedGrid_size]; exact hi⟩ (embed row) =
      embedGrid (fun r c => if r = ⟨i, hi⟩ then ofList13 row hrow c else g r c) := by
  let idx : Fin (embedGrid g).size := ⟨i, by rw [embedGrid_size]; exact hi⟩
  apply Array.ext
  · simp [embedGrid, Array.size_set]
  · intro j hj hj'
    have hj4 : j < 4 := by simpa [embedGrid] using hj'
    rw [Array.getElem_set]
    by_cases heq : idx.val = j
    · have hget := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ then ofList13 row hrow c else g r c) ⟨j, hj4⟩
      have hgetj :
          (embedGrid (fun r c => if r = ⟨i, hi⟩ then ofList13 row hrow c else g r c))[j]'hj' =
            embed (toList13 (fun c =>
              if (⟨j, hj4⟩ : Fin 4) = ⟨i, hi⟩ then ofList13 row hrow c else g ⟨j, hj4⟩ c)) := by
        simpa using hget
      simp only [heq, ↓reduceIte]
      rw [hgetj]
      simp [show i = j from by simpa [idx] using heq, toList13_ofList13]
    · simp only [heq, ↓reduceIte]
      have hget := embedGrid_get g ⟨j, hj4⟩
      have hget' := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ then ofList13 row hrow c else g r c) ⟨j, hj4⟩
      rw [hget, hget']
      have hr : (⟨j, hj4⟩ : Fin 4) ≠ ⟨i, hi⟩ := by
        intro h
        exact heq (by simpa [idx] using (Fin.ext_iff.mp h).symm)
      simp [hr]

theorem shiftRowsStep_hit (g : Grid Nat) (i : Nat) (hi : i ≤ 3) :
    shiftRowsStep (3 : Int) (Int.ofNat i, embedGrid (rowsShifted g i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (rowsShifted g (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (rowsShifted g (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold shiftRowsStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hrowL : (toList13 ((rowsShifted g i) ⟨i, hi4⟩)).length = 13 := length_toList13 _
  have hat := atL_ofNat (embedGrid (rowsShifted g i)) i
    (by rw [embedGrid_size]; exact hi4)
  have hcell := embedGrid_get (rowsShifted g i) ⟨i, hi4⟩
  have hcell' :
      (embedGrid (rowsShifted g i))[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 ((rowsShifted g i) ⟨i, hi4⟩)) := by
    simpa using hcell
  rw [hcell'] at hat
  -- reduce the monadic body, then the break/continue fork
  simp only [hat, ok_bind]
  rw [left_rotate_refines (toList13 ((rowsShifted g i) ⟨i, hi4⟩)) i
    (fits52 (by rw [length_toList13]; decide))]
  simp only [ok_bind]
  have hput := putL_ofNat (embedGrid (rowsShifted g i)) i
    (embed (rotL (toList13 ((rowsShifted g i) ⟨i, hi4⟩)) i))
    (by rw [embedGrid_size]; exact hi4)
  rw [hput]
  simp only [ok_bind]
  have hrot : rotL (toList13 ((rowsShifted g i) ⟨i, hi4⟩)) i =
      toList13 (shiftRows g ⟨i, hi4⟩) := by
    have hsame : rowsShifted g i ⟨i, hi4⟩ = g ⟨i, hi4⟩ := by
      funext c
      simp [rowsShifted, show ¬ i < i from Nat.lt_irrefl _]
    rw [hsame]
    exact (toList13_shiftRow g ⟨i, hi4⟩).symm
  rw [hrot]
  have hset := embedGrid_setRow (rowsShifted g i) i hi4
    (toList13 (shiftRows g ⟨i, hi4⟩)) (length_toList13 _)
  rw [hset]
  have hfun : (fun r c =>
      if r = ⟨i, hi4⟩ then ofList13 (toList13 (shiftRows g ⟨i, hi4⟩)) (length_toList13 _) c
      else rowsShifted g i r c) =
      rowsShifted g (i + 1) := by
    have hrow : ofList13 (toList13 (shiftRows g ⟨i, hi4⟩)) (length_toList13 _) =
        shiftRows g ⟨i, hi4⟩ := ofList13_toList13 _
    have hswap :
        (fun r c => if r = ⟨i, hi4⟩ then shiftRows g ⟨i, hi4⟩ c else rowsShifted g i r c) =
          (fun r c => if r = ⟨i, hi4⟩ then shiftRows g r c else rowsShifted g i r c) := by
      funext r c
      by_cases hr : r = ⟨i, hi4⟩ <;> simp [hr]
    rw [hrow, hswap]
    exact rowsShifted_succ g i hi4
  simp only [hfun]
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
        have heqI : Int.ofNat i = (3 : Int) := (beq_int_iff _ _).mp hb
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using heqI)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt hi4 (by decide : 4 ≤ 52))]
    simp [ok_bind, heq]

theorem shift_rows_loop (g : Grid Nat) :
    (do
      let _fromV := (0 : Int)
      let _toV := (3 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init := (_fromV, embedGrid g)
      let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) _init fuel
        (shiftRowsStep _toV)
        (fun σ =>
          let g := σ.2
          pure g)
        (fun r => pure r))
      pure _out) =
      .ok (embedGrid (shiftRows g)) := by
  have hfuel : (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 3) := by
    rw [fuelRange_le (Nat.zero_le 3)]
    decide
  dsimp only
  simp only [hfuel, except_bind_pure, rowsShifted_zero]
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      shiftRowsStep (3 : Int) (Int.ofNat i, embedGrid (rowsShifted g i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (rowsShifted g (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (rowsShifted g (i + 1)))) :=
    fun i _ hi => shiftRowsStep_hit g i hi
  have hrun := chain_loop (shiftRowsStep (3 : Int))
    (fun σ => let grid := σ.2; pure grid)
    (fun r => pure r)
    (fun i => embedGrid (rowsShifted g i)) 0 3 (Nat.zero_le _) hstep
    (pure (embedGrid (shiftRows g)))
    (by simp [rowsShifted_four])
  simpa [Pure.pure, Except.pure] using hrun

theorem shift_rows_refines (g : Grid Nat) :
    Doubledeal.shift_rows (embedGrid g) = .ok (embedGrid (shiftRows g)) := by
  rw [shift_rows_as_loop]
  exact shift_rows_loop g

end DoubleDeal.Link2
