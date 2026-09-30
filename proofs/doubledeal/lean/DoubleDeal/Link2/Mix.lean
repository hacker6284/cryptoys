/-
  LINK 2. `mix_columns` refines algebraic `mixColumns` on a length-52 packet
  whose card values fit in i64 (so `step_seat` cannot Trap).
-/
import Doubledeal
import DoubleDeal.Basic
import DoubleDeal.Concrete
import DoubleDeal.GridCycle
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Shift
import DoubleDeal.Link2.GridLay
import DoubleDeal.Link2.ScoopRm
import DoubleDeal.Link2.SumLink

namespace DoubleDeal.Link2

theorem step_seat_refines (card r c : Nat) (hr : r ≤ 3) (hc : c ≤ 12) (hb : CardBound card) :
    Doubledeal.step_seat (Int.ofNat card) (Int.ofNat r) (Int.ofNat c) =
      .ok (Int.ofNat ((r + suit card) % 4), Int.ofNat ((c + rank card) % 13)) := by
  unfold Doubledeal.step_seat
  rw [suit_of_refines, rank_of_refines]
  simp only [ok_bind]
  have hsuit : FitsLen (r + suit card) := by
    have hdiv : suit card ≤ card := Nat.div_le_self _ _
    have hbig : 4 ≤ i64MaxNat := by unfold i64MaxNat; decide
    unfold FitsLen CardBound at *
    omega
  rw [addI_ofNat r (suit card) hsuit]
  simp only [ok_bind]
  rw [show (4 : Int) = Int.ofNat 4 from rfl, modI_ofNat _ (by decide)]
  simp only [ok_bind]
  have hrnk : FitsLen (c + rank card) := by
    have : rank card ≤ 13 := by simp [rank]; omega
    have hbig : 25 ≤ i64MaxNat := by unfold i64MaxNat; decide
    unfold FitsLen
    omega
  rw [addI_ofNat c (rank card) hrnk]
  simp only [ok_bind]
  rw [show (13 : Int) = Int.ofNat 13 from rfl, modI_ofNat _ (by decide)]
  rfl

theorem gridStep_coords (card : Nat) (r : Fin 4) (c : Fin 13) :
    (gridStep card (r, c)).1.val = (r.val + suit card) % 4 ∧
    (gridStep card (r, c)).2.val = (c.val + rank card) % 13 := by
  simp [gridStep]

/-! ### `scan_row`: first free seat of one marker row, from column `start`

The emitted helper scans `col = (start + k) mod 13` for `k = 0 .. 12` and
keeps the first column whose mark is `0` (`found = -1` until then).
-/

/-- Loop body of the emitted `scan_row` (one offset `k`). -/
def scanBody (occ : Array (Array Int)) (row start k found : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Int) := do
  let s ← SudoRt.addI start k
  let col ← SudoRt.modI s (13 : Int)
  let hit ← (if decide (found < (0 : Int)) then (do
    let rowA ← SudoRt.atL occ row
    let cell ← SudoRt.atL rowA col
    pure (SudoRt.SEq.beq cell (0 : Int))) else pure false)
  if hit then
    pure (SudoRt.Flow.cont (ρ := Int) col)
  else
    pure (SudoRt.Flow.cont (ρ := Int) found)

def scanRowStep (occ : Array (Array Int)) (row start toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) Int) :=
  let k := σ.1
  let found := σ.2
  do
    if k > toV then
      pure (SudoRt.Flow.brk (ρ := Int) (k, found))
    else
      match ← scanBody occ row start k found with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int) (k, fs))
      | .cont fs =>
          if (k == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int) (k, fs))
          else do
            let k' ← SudoRt.addI k 1
            pure (SudoRt.Flow.cont (ρ := Int) (k', fs))

theorem scan_row_as_loop (occ : Array (Array Int)) (row start : Int) :
    Doubledeal.scan_row occ row start =
      (do
        let found ← SudoRt.negI (1 : Int)
        let _out ← (SudoRt.runLoopOn (ρ := Int) ((0 : Int), found) fuel13
          (scanRowStep occ row start 12)
          (fun σ => pure σ.2)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.scan_row
  rfl

def occMarks (occ : Occ) : Grid Nat :=
  fun r c => if occGet occ r c then 1 else 0

theorem scanRowN_succ (occ : Occ) (row : Fin 4) (start fuel k : Nat) :
    scanRowN occ row start (fuel + 1) k =
      if occGet occ row (rotCol start k) then scanRowN occ row start fuel (k + 1)
      else some (rotCol start k) := rfl

/-- `found` after offsets `0 .. n-1`. -/
def scanFoundR (occ : Occ) (row : Fin 4) (start : Nat) : Nat → Int
  | 0 => -1
  | n + 1 =>
    let prev := scanFoundR occ row start n
    if prev < 0 ∧ occGet occ row (rotCol start n) = false then
      Int.ofNat (rotCol start n).val
    else prev

/-- Sudo encoding of a scan result: the column, or `-1`. -/
def encCol : Option (Fin 13) → Int
  | some c => Int.ofNat c.val
  | none => -1

theorem scanBody_hit (occ : Occ) (row : Fin 4) (start : Nat) (hs : start < 13)
    (j : Nat) (hj : j ≤ 12) :
    scanBody (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) (Int.ofNat j)
      (scanFoundR occ row start j) =
      .ok (SudoRt.Flow.cont (scanFoundR occ row start (j + 1))) := by
  unfold scanBody
  rw [addI_ofNat start j (fits52 (by omega))]
  simp only [ok_bind]
  rw [show (13 : Int) = Int.ofNat 13 from rfl, modI_ofNat (start + j) (by decide)]
  simp only [ok_bind]
  have hm : (start + j) % 13 < 13 := Nat.mod_lt _ (by decide)
  by_cases hlt : scanFoundR occ row start j < 0
  · have hd : decide (scanFoundR occ row start j < 0) = true := decide_eq_true hlt
    have hat := atL_ofNat (embedGrid (occMarks occ)) row.val
      (by rw [embedGrid_size]; exact row.isLt)
    have hat' :
        (embedGrid (occMarks occ))[row.val]'(by rw [embedGrid_size]; exact row.isLt) =
          embed (toList13 (occMarks occ row)) := by simpa using embedGrid_get (occMarks occ) row
    rw [hat'] at hat
    have hatC := atL_embed (toList13 (occMarks occ row)) ((start + j) % 13)
      (by rw [length_toList13]; exact hm)
    have hget := getElem_toList13 (occMarks occ row) ⟨(start + j) % 13, hm⟩
    simp only [hd, ↓reduceIte, hat, ok_bind]
    rw [hatC]
    simp only [ok_bind, hget]
    cases hocc : occGet occ row (rotCol start j)
    · have hbit : occMarks occ row ⟨(start + j) % 13, hm⟩ = 0 := by
        simpa [occMarks, rotCol] using hocc
      have hnext : scanFoundR occ row start (j + 1) = Int.ofNat ((start + j) % 13) := by
        show (if scanFoundR occ row start j < 0 ∧ occGet occ row (rotCol start j) = false then
          Int.ofNat (rotCol start j).val else scanFoundR occ row start j) = _
        rw [if_pos ⟨hlt, hocc⟩]
        rfl
      rw [hbit, hnext]
      rfl
    · have hbit : occMarks occ row ⟨(start + j) % 13, hm⟩ = 1 := by
        simpa [occMarks, rotCol] using hocc
      have hnext : scanFoundR occ row start (j + 1) = scanFoundR occ row start j := by
        simp [scanFoundR, hocc]
      rw [hbit, hnext]
      rfl
  · have hd : decide (scanFoundR occ row start j < 0) = false := decide_eq_false hlt
    have hnext : scanFoundR occ row start (j + 1) = scanFoundR occ row start j := by
      simp [scanFoundR, hlt]
    simp [hd, hnext, Pure.pure, Except.pure]

theorem scanRowStep_hit (occ : Occ) (row : Fin 4) (start : Nat) (hs : start < 13)
    (j : Nat) (hj : j ≤ 12) :
    scanRowStep (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) 12
      (Int.ofNat j, scanFoundR occ row start j) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, scanFoundR occ row start (j + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), scanFoundR occ row start (j + 1))) := by
  have hj13 : j < 13 := by omega
  unfold scanRowStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  rw [scanBody_hit occ row start hs j hj]
  simp only [ok_bind]
  by_cases heq : j = 12
  · subst heq
    have hb : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hb, Pure.pure, Except.pure]
  · have hb : ((Int.ofNat j) == (12 : Int)) = false := by
      cases hbv : (Int.ofNat j) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
    simp only [hb, ↓reduceIte, Bool.false_eq_true]
    rw [addI_ofNat_one j (fits_succ_lt hj13 (by decide : 13 ≤ 52))]
    simp [ok_bind, heq, Pure.pure, Except.pure]

theorem scanFoundR_stable (occ : Occ) (row : Fin 4) (start n : Nat)
    (h : 0 ≤ scanFoundR occ row start n) :
    ∀ j, scanFoundR occ row start (n + j) = scanFoundR occ row start n
  | 0 => rfl
  | j + 1 => by
    have ih := scanFoundR_stable occ row start n h j
    rw [← Nat.add_assoc]
    simp only [scanFoundR, ih]
    have : ¬ scanFoundR occ row start n < 0 := by omega
    simp [this]

theorem scanFoundR_encode_from (occ : Occ) (row : Fin 4) (start : Nat) :
    ∀ m n, n + m = 13 → scanFoundR occ row start n = -1 →
      scanFoundR occ row start 13 = encCol (scanRowN occ row start m n)
  | 0, n, hnm, h => by
    have : n = 13 := by omega
    subst this
    simp [h, scanRowN, encCol]
  | m + 1, n, hnm, h => by
    rw [scanRowN_succ]
    cases hocc : occGet occ row (rotCol start n)
    · have hnext : scanFoundR occ row start (n + 1) = Int.ofNat (rotCol start n).val := by
        simp [scanFoundR, h, hocc]
      have hst := scanFoundR_stable occ row start (n + 1)
        (by rw [hnext]; exact Int.ofNat_nonneg _) m
      rw [show n + 1 + m = 13 by omega, hnext] at hst
      simp [hst, encCol]
    · have hnext : scanFoundR occ row start (n + 1) = -1 := by
        simp [scanFoundR, h, hocc]
      simpa using scanFoundR_encode_from occ row start m (n + 1) (by omega) hnext

theorem scanFoundR_encode (occ : Occ) (row : Fin 4) (start : Nat) :
    scanFoundR occ row start 13 = encCol (scanRow occ row start) :=
  scanFoundR_encode_from occ row start 13 0 rfl rfl

/-- Emitted `scan_row` = the model's rotated `scanRow`, encoded as a column or `-1`. -/
theorem scan_row_refines (occ : Occ) (row : Fin 4) (start : Nat) (hs : start < 13) :
    Doubledeal.scan_row (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) =
      .ok (encCol (scanRow occ row start)) := by
  rw [scan_row_as_loop, negI_one]
  simp only [ok_bind]
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      scanRowStep (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) 12
        (Int.ofNat j, scanFoundR occ row start j) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, scanFoundR occ row start (j + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), scanFoundR occ row start (j + 1))) :=
    fun j _ hj => scanRowStep_hit occ row start hs j hj
  have hrun := chain_loop
    (scanRowStep (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) 12)
    (fun σ => pure σ.2) (fun r => pure r)
    (fun j => scanFoundR occ row start j) 0 12 (Nat.zero_le _) hstep
    (.ok (encCol (scanRow occ row start)))
    (by simp [scanFoundR_encode, Pure.pure, Except.pure])
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (-1 : Int)) fuel13
        (scanRowStep (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) 12)
        (fun σ => pure σ.2) (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat 0, scanFoundR occ row start 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat 12))
        (scanRowStep (embedGrid (occMarks occ)) (Int.ofNat row.val) (Int.ofNat start) 12)
        (fun σ => pure σ.2) (fun r => pure r) := by
    rw [fuel13_eq, scanFoundR, show (0 : Int) = Int.ofNat 0 from rfl]
  rw [hcast, hrun, except_bind_pure]

/-! ### `overflow_seat`: rows `row, row+1, …` (mod 4), each scanned from `start` -/

/-- Loop body of the emitted `overflow_seat` (one attempt on `row`). -/
def overflowBody (occ : Array (Array Int)) (start row : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int (Int × Int)) := do
  let found ← Doubledeal.scan_row occ row start
  if decide (found ≥ (0 : Int)) then
    pure (SudoRt.Flow.ret (ρ := Int × Int) (row, found))
  else do
    let r1 ← SudoRt.addI row 1
    let r' ← SudoRt.modI r1 4
    pure (SudoRt.Flow.cont (ρ := Int × Int) r')

def overflowStep (occ : Array (Array Int)) (start toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Int × Int)) :=
  let attempt := σ.1
  let row := σ.2
  do
    if attempt > toV then
      pure (SudoRt.Flow.brk (ρ := Int × Int) (attempt, row))
    else
      match ← overflowBody occ start row with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int × Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int × Int) (attempt, fs))
      | .cont fs =>
          if (attempt == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int × Int) (attempt, fs))
          else do
            let attempt' ← SudoRt.addI attempt 1
            pure (SudoRt.Flow.cont (ρ := Int × Int) (attempt', fs))

/-- The emitted loop, up to the sudo line number of its unreachable
`assert false`. Stated with `∃ ln` (witness found by `rfl`) so sudo edits
that move the assert do not reach into Link 2. -/
theorem overflow_as_loop (occ : Array (Array Int)) (row start : Int) :
    ∃ ln : Nat, Doubledeal.overflow_seat occ row start =
      (do
        let _fromV := (0 : Int)
        let _toV := (3 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Int × Int) (_fromV, row) fuel
          (overflowStep occ start _toV)
          (fun _σ => do
            let _as ← SudoRt.sudoAssert false ln
            pure ((0 : Int), (0 : Int)))
          (fun r => pure r))
        pure _out) :=
  ⟨_, by unfold Doubledeal.overflow_seat; rfl⟩

theorem overflowBody_hit (occ : Occ) (t : Nat) (ht : t < 4) (start : Nat) (hs : start < 13) :
    overflowBody (embedGrid (occMarks occ)) (Int.ofNat start) (Int.ofNat t) =
      match scanRow occ ⟨t, ht⟩ start with
      | some c => .ok (SudoRt.Flow.ret (Int.ofNat t, Int.ofNat c.val))
      | none => .ok (SudoRt.Flow.cont (Int.ofNat ((t + 1) % 4))) := by
  unfold overflowBody
  have hscan := scan_row_refines occ ⟨t, ht⟩ start hs
  simp only at hscan
  rw [hscan]
  simp only [ok_bind]
  have hadd := addI_ofNat_one t (fits_succ_lt ht (by decide : 4 ≤ 52))
  rw [show (4 : Int) = Int.ofNat 4 from rfl]
  cases hscanR : scanRow occ ⟨t, ht⟩ start with
  | some c =>
    have hge : decide (Int.ofNat c.val ≥ (0 : Int)) = true := by
      simp [decide_eq_true_eq, Int.ofNat_nonneg]
    simp only [encCol, hge, ↓reduceIte]
    rfl
  | none =>
    have hge : decide ((-1 : Int) ≥ (0 : Int)) = false := by decide
    simp only [encCol, hge, ↓reduceIte, hadd, ok_bind, Bool.false_eq_true]
    rw [modI_ofNat (t + 1) (by decide)]
    rfl

theorem overflowStep_hit (occ : Occ) (start : Nat) (hs : start < 13)
    (attempt t : Nat) (ht : t < 4) (ha : attempt ≤ 3) :
    overflowStep (embedGrid (occMarks occ)) (Int.ofNat start) 3 (Int.ofNat attempt, Int.ofNat t) =
      match scanRow occ ⟨t, ht⟩ start with
      | some c =>
        .ok (SudoRt.Flow.ret (Int.ofNat t, Int.ofNat c.val))
      | none =>
        if attempt = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat attempt, Int.ofNat ((t + 1) % 4)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (attempt + 1), Int.ofNat ((t + 1) % 4))) := by
  unfold overflowStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat attempt > (3 : Int) from ofNat_not_gt ha)]
  rw [overflowBody_hit occ t ht start hs]
  cases hrow : scanRow occ ⟨t, ht⟩ start with
  | some c =>
    simp only [ok_bind, Pure.pure, Except.pure]
  | none =>
    simp only [ok_bind, Pure.pure, Except.pure]
    by_cases heq : attempt = 3
    · subst heq
      have hb : ((3 : Int) == (3 : Int)) = true := by decide
      simp [hb]
    · have hb : ((Int.ofNat attempt) == (3 : Int)) = false := by
        cases hbv : (Int.ofNat attempt) == (3 : Int) with
        | false => rfl
        | true =>
          exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
      simp only [hb, ↓reduceIte, Bool.false_eq_true]
      rw [addI_ofNat_one attempt (fits_succ_lt (by omega : attempt < 3) (by decide : 3 ≤ 52))]
      simp [ok_bind, heq]

theorem overflow_fuel_some (occ : Occ) (start : Nat) (hs : start < 13) (ln : Nat)
    (fuel t : Nat) (ht : t < 4) (hf : fuel ≤ 4)
    (r : Fin 4) (c : Fin 13)
    (h : overflowN occ start fuel t = some (r, c)) :
    SudoRt.runLoopOn (Int.ofNat (4 - fuel), Int.ofNat t) fuel
      (overflowStep (embedGrid (occMarks occ)) (Int.ofNat start) 3)
      (fun _ => do
        let _as ← SudoRt.sudoAssert false ln
        pure ((0 : Int), (0 : Int)))
      (fun x => pure x) =
      .ok (Int.ofNat r.val, Int.ofNat c.val) := by
  induction fuel generalizing t r c with
  | zero => simp [overflowN] at h
  | succ fuel ih =>
    have hstart : 4 - (fuel + 1) ≤ 3 := by omega
    have hstep := overflowStep_hit occ start hs (4 - (fuel + 1)) t ht hstart
    rw [runLoopOn_succ]
    rw [hstep]
    have htmod : t % 4 = t := Nat.mod_eq_of_lt ht
    simp only [overflowN, htmod] at h
    cases hscan : scanRow occ ⟨t, ht⟩ start with
    | some c0 =>
      simp only [hscan, h, Pure.pure, Except.pure] at h ⊢
      injection h with hpos
      cases hpos
      rfl
    | none =>
      simp only [hscan] at h
      have hne : 4 - (fuel + 1) ≠ 3 := by
        intro heq
        have : fuel = 0 := by omega
        subst this
        simp [overflowN] at h
      simp only [hne, ↓reduceIte, Pure.pure, Except.pure]
      have ht' : (t + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
      have hf' : fuel ≤ 4 := by omega
      have hfuelEq : 4 - fuel = (4 - (fuel + 1)) + 1 := by omega
      have hrec := ih ((t + 1) % 4) ht' hf' r c h
      simpa [hfuelEq] using hrec

theorem overflow_seat_refines (occ : Occ) (t : Nat) (ht : t < 4) (start : Nat) (hs : start < 13)
    (r : Fin 4) (c : Fin 13)
    (h : overflowSeat occ t start = some (r, c)) :
    Doubledeal.overflow_seat (embedGrid (occMarks occ)) (Int.ofNat t) (Int.ofNat start) =
      .ok (Int.ofNat r.val, Int.ofNat c.val) := by
  obtain ⟨ln, hloop⟩ := overflow_as_loop (embedGrid (occMarks occ)) (Int.ofNat t) (Int.ofNat start)
  rw [hloop]
  dsimp only
  have hfuel : (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) = 4 := by
    decide
  rw [hfuel, except_bind_pure]
  have hgo := overflow_fuel_some occ start hs ln 4 t ht (Nat.le_refl _) r c (by
    simpa [overflowSeat] using h)
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  exact hgo

def seatRow (g : NatGrid) (occ : Occ) (r : Fin 4) : List Int :=
  toList13 (fun c => if occGet occ r c then Int.ofNat (g r c) else -1)

def seatArr (g : NatGrid) (occ : Occ) : Array (Array Int) :=
  #[Array.mk (seatRow g occ 0), Array.mk (seatRow g occ 1),
    Array.mk (seatRow g occ 2), Array.mk (seatRow g occ 3)]

theorem toList13_const (v : Int) : toList13 (fun _ : Fin 13 => v) = List.replicate 13 v := by
  simp [toList13, List.replicate]

theorem map_toList13_ofNat (f : Fin 13 → Nat) :
    (toList13 f).map Int.ofNat = toList13 (fun c => Int.ofNat (f c)) := by
  simp [toList13]

theorem blank_seat (g : NatGrid) : blankRows 4 = seatArr g emptyOcc := by
  simp [blankRows, seatArr, seatRow, occGet_empty, repInt, toList13_const, List.replicate]

theorem seatArr_size (g : NatGrid) (occ : Occ) : (seatArr g occ).size = 4 := by
  simp [seatArr]

theorem seatArr_get (g : NatGrid) (occ : Occ) (r : Fin 4) :
    (seatArr g occ)[r.val]'(by rw [seatArr_size]; exact r.isLt) = Array.mk (seatRow g occ r) := by
  revert r
  intro ⟨v, hv⟩
  match v with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => omega

theorem seatArr_full (g : NatGrid) (occ : Occ) (h : ∀ r c, occGet occ r c = true) :
    seatArr g occ = embedGrid g := by
  apply Array.ext
  · simp [seatArr, embedGrid]
  · intro i hi hi'
    have hi4 : i < 4 := by simpa [seatArr] using hi
    rw [seatArr_get g occ ⟨i, hi4⟩, embedGrid_get g ⟨i, hi4⟩]
    simp [embed, seatRow, h, map_toList13_ofNat]

/-- One column of the occupancy bitmap: `0` if the seat is empty, else `1`. -/
def markColStep (grid : Array (Array Int)) (rr toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let cc := σ.1
  let marks := σ.2
  do
    if cc > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (cc, marks))
    else
      match ← ((do
        let row ← SudoRt.atL grid rr
        let cell ← SudoRt.atL row cc
        if decide (cell < (0 : Int)) then
          let _mb := SudoRt.appendL marks (0 : Int)
          let ⟨marks, _⟩ := _mb
          pure (SudoRt.Flow.cont (ρ := Array Int) marks)
        else
          let _mb := SudoRt.appendL marks (1 : Int)
          let ⟨marks, _⟩ := _mb
          pure (SudoRt.Flow.cont (ρ := Array Int) marks)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (cc, fs))
      | .cont fs =>
          if (cc == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (cc, fs))
          else do
            let cc' ← SudoRt.addI cc 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (cc', fs))

theorem seat_cell (g : NatGrid) (occ : Occ) (r : Fin 4) (j : Nat) (hj : j < 13) :
    (seatRow g occ r)[j]'(by unfold seatRow; rw [length_toList13]; exact hj) =
      if occGet occ r ⟨j, hj⟩ then Int.ofNat (g r ⟨j, hj⟩) else -1 := by
  unfold seatRow
  exact getElem_toList13_nat
    (fun c => if occGet occ r c then Int.ofNat (g r c) else -1) j hj

theorem mark_bit (occ : Occ) (r : Fin 4) (c : Fin 13) :
    (toList13 (occMarks occ r))[c.val]'(by rw [length_toList13]; exact c.isLt) =
      if occGet occ r c then 1 else 0 := by
  simpa [occMarks] using
    getElem_toList13_nat (fun c => if occGet occ r c then 1 else 0) c.val c.isLt

theorem markCol_hit (g : NatGrid) (occ : Occ) (r : Fin 4) (j : Nat) (hj : j ≤ 12) :
    markColStep (seatArr g occ) (Int.ofNat r.val) 12
      (Int.ofNat j, embed ((toList13 (occMarks occ r)).take j)) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, embed ((toList13 (occMarks occ r)).take (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed ((toList13 (occMarks occ r)).take (j + 1)))) := by
  have hj13 : j < 13 := by omega
  unfold markColStep
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  have hat := atL_ofNat (seatArr g occ) r.val (by rw [seatArr_size]; exact r.isLt)
  rw [seatArr_get g occ r] at hat
  simp only [hat, ok_bind]
  have hatC := atL_ofNat (Array.mk (seatRow g occ r)) j
    (by simpa [length_toList13] using hj13)
  rw [hatC]
  simp only [ok_bind]
  have hcell := seat_cell g occ r j hj13
  simp only [Array.getElem_mk, hcell]
  have hbit := mark_bit occ r ⟨j, hj13⟩
  have hnext (b : Nat) (hb : (toList13 (occMarks occ r))[j]'(by rw [length_toList13]; exact hj13) = b) :
      (toList13 (occMarks occ r)).take j ++ [b] =
        (toList13 (occMarks occ r)).take (j + 1) := by
    rw [← hb]
    exact (take_succ_append (toList13 (occMarks occ r)) j
      (by rw [length_toList13]; exact hj13)).symm
  by_cases hocc : occGet occ r ⟨j, hj13⟩ = true
  · simp only [hocc, ↓reduceIte]
    have hlt : decide (Int.ofNat (g r ⟨j, hj13⟩) < (0 : Int)) = false :=
      decide_eq_false (Int.not_lt.mpr (Int.ofNat_zero_le _))
    simp only [hlt, appendL_spec, ↓reduceIte]
    have hpush : (embed ((toList13 (occMarks occ r)).take j)).push (1 : Int) =
        embed ((toList13 (occMarks occ r)).take j ++ [1]) := by simp [embed, Array.push]
    simp only [hpush]
    have hone : (toList13 (occMarks occ r))[j]'(by rw [length_toList13]; exact hj13) = 1 := by
      simpa [hocc] using hbit
    rw [hnext 1 hone]
    by_cases heq : j = 12
    · subst heq
      simp only [ok_bind]
      have hb : ((12 : Int) == (12 : Int)) = true := by decide
      simp [hb, Pure.pure, Except.pure]
    · simp only [Pure.pure, Except.pure, ok_bind]
      have hb : ((Int.ofNat j) == (12 : Int)) = false := by
        cases hbv : (Int.ofNat j) == (12 : Int) with
        | false => rfl
        | true =>
          exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
      simp only [hb, ↓reduceIte]
      rw [addI_ofNat_one j (fits_succ_lt hj13 (by decide : 13 ≤ 52))]
      simp [ok_bind, heq]
  · have hempty : occGet occ r ⟨j, hj13⟩ = false := by
      simpa [Bool.not_eq_true] using hocc
    simp only [hempty, ↓reduceIte]
    have hlt : decide ((-1 : Int) < (0 : Int)) = true := by decide
    simp only [hlt, appendL_spec]
    have hpush : (embed ((toList13 (occMarks occ r)).take j)).push (0 : Int) =
        embed ((toList13 (occMarks occ r)).take j ++ [0]) := by simp [embed, Array.push]
    simp only [hpush]
    have hzero : (toList13 (occMarks occ r))[j]'(by rw [length_toList13]; exact hj13) = 0 := by
      simpa [hempty] using hbit
    rw [hnext 0 hzero]
    by_cases heq : j = 12
    · subst heq
      simp only [ok_bind]
      have hb : ((12 : Int) == (12 : Int)) = true := by decide
      simp [hb, Pure.pure, Except.pure]
    · simp only [Pure.pure, Except.pure, ok_bind]
      have hb : ((Int.ofNat j) == (12 : Int)) = false := by
        cases hbv : (Int.ofNat j) == (12 : Int) with
        | false => rfl
        | true =>
          exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
      simp only [hb, ↓reduceIte]
      rw [addI_ofNat_one j (fits_succ_lt hj13 (by decide : 13 ≤ 52))]
      simp [ok_bind, heq]

theorem mark_row_loop (g : NatGrid) (occ : Occ) (r : Fin 4) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel13
      (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
      (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
      (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) =
      pure (SudoRt.Flow.cont (embed (toList13 (occMarks occ r)))) := by
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      markColStep (seatArr g occ) (Int.ofNat r.val) 12
        (Int.ofNat j, embed ((toList13 (occMarks occ r)).take j)) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, embed ((toList13 (occMarks occ r)).take (j + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed ((toList13 (occMarks occ r)).take (j + 1)))) :=
    fun j _ hj => markCol_hit g occ r j hj
  have ht : (toList13 (occMarks occ r)).take 13 = toList13 (occMarks occ r) := by
    simpa [length_toList13] using List.take_length (toList13 (occMarks occ r))
  have hrun := chain_loop
    (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
    (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
    (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x))
    (fun j => embed ((toList13 (occMarks occ r)).take j)) 0 12 (Nat.zero_le _) hstep
    (pure (SudoRt.Flow.cont (embed (toList13 (occMarks occ r)))))
    (by simp [ht])
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel13
        (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
        (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((toList13 (occMarks occ r)).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12))
        (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
        (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) := by
    rw [fuel13_eq, List.take_zero, embed_nil, show (0 : Int) = Int.ofNat 0 from rfl]
  simpa [Pure.pure] using hcast.trans hrun

theorem seat_place (g : NatGrid) (occ : Occ) (r : Fin 4) (c : Fin 13) (card : Nat)
    (_hfree : occGet occ r c = false) (hsz : occ.size = 52) :
    (do
      let row ← SudoRt.atL (seatArr g occ) (Int.ofNat r.val)
      let row ← SudoRt.putL row (Int.ofNat c.val) (Int.ofNat card)
      SudoRt.putL (seatArr g occ) (Int.ofNat r.val) row) =
      .ok (seatArr (setGrid g (r, c) card) (setOcc occ (r, c))) := by
  have hat := atL_ofNat (seatArr g occ) r.val (by rw [seatArr_size]; exact r.isLt)
  rw [seatArr_get g occ r] at hat
  simp only [hat, ok_bind]
  have hrowSz : c.val < (Array.mk (seatRow g occ r)).size := by
    rw [Array.size_mk, seatRow, length_toList13]
    exact c.isLt
  have hputR := putL_ofNat (Array.mk (seatRow g occ r)) c.val (Int.ofNat card) hrowSz
  rw [hputR]
  simp only [ok_bind]
  have hputG := putL_ofNat (seatArr g occ) r.val
      ((Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card))
      (by rw [seatArr_size]; exact r.isLt)
  rw [hputG]
  apply congrArg Except.ok
  apply Array.ext
  · simp [seatArr, Array.size_set]
  · intro i hi hi'
    have hi4 : i < 4 := by simpa [seatArr] using hi
    by_cases heq : r.val = i
    · have hr : r = ⟨i, hi4⟩ := Fin.ext heq
      have hset : (Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card) =
          Array.mk ((seatRow g occ r).set c.val (Int.ofNat card)) := by
        apply Array.ext
        · simp [Array.size_mk, Array.size_set, List.length_set, seatRow, length_toList13]
        · intro k hk hk'
          simp [Array.getElem_set, Array.getElem_mk, List.getElem_set, Array.size_mk]
      rw [Array.getElem_set]
      simp only [heq, ↓reduceIte]
      rw [hset, seatArr_get (setGrid g (r, c) card) (setOcc occ (r, c)) ⟨i, hi4⟩, hr]
      apply congrArg Array.mk
      unfold seatRow
      rw [toList13_set _ c.val c.isLt]
      apply congrArg toList13
      funext c'
      have hget := occGet_setOcc occ (⟨i, hi4⟩, c) ⟨i, hi4⟩ c' hsz
      by_cases hc : c' = c
      · subst hc
        rw [hget]
        simp [setGrid]
      · rw [hget]
        have hne : c'.val ≠ c.val := fun h => hc (Fin.ext h)
        simp only [Prod.fst, Prod.snd]
        simp [hne, hc, setGrid]
    · have hrne : (⟨i, hi4⟩ : Fin 4) ≠ r := fun h => heq (congrArg Fin.val h).symm
      rw [Array.getElem_set, if_neg heq, seatArr_get g occ ⟨i, hi4⟩,
        seatArr_get (setGrid g (r, c) card) (setOcc occ (r, c)) ⟨i, hi4⟩]
      apply congrArg Array.mk
      unfold seatRow
      apply congrArg toList13
      funext c'
      have hget := occGet_setOcc occ (r, c) ⟨i, hi4⟩ c' hsz
      have hdec : decide ((⟨i, hi4⟩ : Fin 4) = r ∧ c' = c) = false := by
        simp [hrne]
      simp [setGrid, hget, hdec, hrne]

/-- One occupancy row: append the finished 0/1 marks onto `occ`. -/
def markRowStep (grid : Array (Array Int)) (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array Int)) :=
  let rr := σ.1
  let occ := σ.2
  do
    if rr > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (rr, occ))
    else
      match ← ((do
        let marks := (#[] : Array Int)
        let _fromV := (0 : Int)
        let _toV := (12 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array Int) (_fromV, marks) fuel
          (markColStep grid rr _toV)
          (fun σ =>
            let marks := σ.2
            do
              let _mb := SudoRt.appendL occ marks
              let ⟨occ, _⟩ := _mb
              pure (SudoRt.Flow.cont (ρ := Array Int) occ))
          (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)))
        pure _out
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (rr, fs))
      | .cont fs =>
          if (rr == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (rr, fs))
          else do
            let rr' ← SudoRt.addI rr 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (rr', fs))

/-- One placement of `mix_columns`. State is `(fr, fc, t, grid, prevCard)`
    (finger row/column, marker, table, last card). -/
def mixStep (d : Array Int) (toV : Int)
    (σ : Int × (Int × Int × Int × Array (Array Int) × Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Int × Int × Int × Array (Array Int) × Int)) (Array Int)) :=
  let i := σ.1
  let fr := σ.2.1
  let fc := σ.2.2.1
  let t := σ.2.2.2.1
  let grid := σ.2.2.2.2.1
  let prev_card := σ.2.2.2.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, (fr, fc, t, grid, prev_card)))
    else
      match ← ((do
        let card ← SudoRt.atL d i
        if decide (i > (0 : Int)) then
          do
            let stepped ← Doubledeal.step_seat prev_card fr fc
            let ⟨tr, tc⟩ := stepped
            let row0 ← SudoRt.atL grid tr
            let cell ← SudoRt.atL row0 tc
            if decide (cell < (0 : Int)) then
              do
                let row ← SudoRt.atL grid tr
                let row ← SudoRt.putL row tc card
                let grid ← SudoRt.putL grid tr row
                pure (SudoRt.Flow.cont (ρ := Array Int) (tr, tc, t, grid, card))
            else
              do
                let rowB ← SudoRt.atL grid tr
                let b ← SudoRt.atL rowB tc
                let occ := (#[] : Array (Array Int))
                let _fromV := (0 : Int)
                let _toV := (3 : Int)
                let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
                let _out ← (SudoRt.runLoopOn (ρ := Array Int) (_fromV, occ) fuel
                  (markRowStep grid _toV)
                  (fun σ =>
                    let occ := σ.2
                    do
                      let s ← Doubledeal.suit_of b
                      let a ← SudoRt.addI t s
                      let srow ← SudoRt.modI a (4 : Int)
                      let k ← Doubledeal.rank_of b
                      let a2 ← SudoRt.addI tc k
                      let scol ← SudoRt.modI a2 (13 : Int)
                      let seat ← Doubledeal.overflow_seat occ srow scol
                      let ⟨r, c⟩ := seat
                      let t1 ← SudoRt.addI t (1 : Int)
                      let t' ← SudoRt.modI t1 (4 : Int)
                      let f ← Doubledeal.step_seat b tr tc
                      let ⟨fr, fc⟩ := f
                      let row ← SudoRt.atL grid r
                      let row ← SudoRt.putL row c card
                      let grid ← SudoRt.putL grid r row
                      pure (SudoRt.Flow.cont (ρ := Array Int) (fr, fc, t', grid, card)))
                  (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)))
                pure _out
        else
          do
            let row ← SudoRt.atL grid (2 : Int)
            let row ← SudoRt.putL row (0 : Int) card
            let grid ← SudoRt.putL grid (2 : Int) row
            pure (SudoRt.Flow.cont (ρ := Array Int) (fr, fc, t, grid, card))
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

theorem chooseSeat!_init : chooseSeat! initWalk = (asStart, (0, asStart)) := by
  simp [chooseSeat!, chooseSeat?, initWalk]

theorem chooseSeat!_t_lt (st : WalkState) (ht : st.t < 4) (hct : occCount st.occ < 52) :
    (chooseSeat! st).2.1 < 4 := by
  cases hprev : st.prev with
  | none =>
    simp [chooseSeat!, chooseSeat?, hprev]
    exact ht
  | some pair =>
    by_cases hocc : occAt st.occ (gridStep pair.1 pair.2) = true
    · simp only [chooseSeat!, chooseSeat?, hprev, hocc, ↓reduceIte]
      obtain ⟨p, hs, _hf⟩ := blockedChoice_some st (gridStep pair.1 pair.2) hct
      simp only [hs]
      exact Nat.mod_lt _ (by decide)
    · have hf : occAt st.occ (gridStep pair.1 pair.2) = false := eq_false_of_ne_true hocc
      simp [chooseSeat!, chooseSeat?, hprev, hf]
      exact ht

theorem placeN_t_lt (hand : Fin 52 → Nat) : ∀ n, n ≤ 52 → (placeN hand n).2.t < 4
  | 0, _ => by simp [placeN, initWalk]
  | n + 1, hn => by
    have hlt : n < 52 := by omega
    have ht := placeN_t_lt hand n (Nat.le_of_lt hlt)
    have hct : occCount (placeN hand n).2.occ < 52 := by
      rw [placeN_count hand n (Nat.le_of_lt hlt)]; omega
    simp only [placeN, hlt, ↓reduceDIte, advance]
    exact chooseSeat!_t_lt (placeN hand n).2 ht hct

theorem placeN_step (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    (placeN hand (n + 1)).1 =
      setGrid (placeN hand n).1 (chooseSeat! (placeN hand n).2).1 (hand ⟨n, hn⟩) ∧
    (placeN hand (n + 1)).2 =
      advance (placeN hand n).2 (hand ⟨n, hn⟩)
        (chooseSeat! (placeN hand n).2).1 (chooseSeat! (placeN hand n).2).2 := by
  simp [placeN, hn, advance]

theorem placeN_prev_succ (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    (placeN hand (n + 1)).2.prev =
      some (hand ⟨n, hn⟩, (chooseSeat! (placeN hand n).2).2.2) := by
  simp [placeN_step hand n hn, advance]

/-- The walk state's `board` is the placed grid. -/
theorem placeN_board (hand : Fin 52 → Nat) : ∀ n, (placeN hand n).1 = (placeN hand n).2.board
  | 0 => rfl
  | n + 1 => by
    by_cases hn : n < 52
    · have hs := placeN_step hand n hn
      rw [hs.1, hs.2, placeN_board hand n]
      rfl
    · simp only [placeN, hn, ↓reduceDIte]
      exact placeN_board hand n

/-- Every cell of the placed grid is a hand card or the initial `0`. -/
theorem placeN_cardBound (hand : Fin 52 → Nat) (hcard : ∀ i, CardBound (hand i)) :
    ∀ n (r : Fin 4) (c : Fin 13), CardBound ((placeN hand n).1 r c)
  | 0, _, _ => cardBound_zero
  | n + 1, r, c => by
    by_cases hn : n < 52
    · rw [(placeN_step hand n hn).1]
      simp only [setGrid]
      split
      · exact hcard _
      · exact placeN_cardBound hand hcard n r c
    · simp only [placeN, hn, ↓reduceDIte]
      exact placeN_cardBound hand hcard n r c

theorem chooseSeat!_free_target (st : WalkState) (card : Nat) (f : Fin 4 × Fin 13)
    (hprev : st.prev = some (card, f))
    (hfree : occAt st.occ (gridStep card f) = false) :
    chooseSeat! st = (gridStep card f, (st.t, gridStep card f)) := by
  simp [chooseSeat!, chooseSeat?, hprev, hfree]

theorem chooseSeat!_blocked (st : WalkState) (card : Nat) (f p : Fin 4 × Fin 13)
    (hprev : st.prev = some (card, f))
    (hocc : occAt st.occ (gridStep card f) = true)
    (hov : overflowSeat st.occ
        ((st.t + suit (st.board (gridStep card f).1 (gridStep card f).2)) % 4)
        (((gridStep card f).2.val + rank (st.board (gridStep card f).1 (gridStep card f).2)) % 13)
        = some p) :
    chooseSeat! st = (p, ((st.t + 1) % 4,
      gridStep (st.board (gridStep card f).1 (gridStep card f).2) (gridStep card f))) := by
  simp [chooseSeat!, chooseSeat?, hprev, hocc, blockedChoice, hov]

theorem filter_length_eq_all {α : Type} (l : List α) (p : α → Bool)
    (h : (l.filter p).length = l.length) : ∀ x ∈ l, p x = true := by
  induction l with
  | nil =>
    intro x hx
    cases hx
  | cons x xs ih =>
    simp only [List.filter, List.length_cons] at h
    by_cases hp : p x = true
    · simp only [hp, ↓reduceIte, List.length_cons] at h
      have hxs : (xs.filter p).length = xs.length := by omega
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact ih hxs y hy
    · have hp' : p x = false := by
        cases hx : p x <;> simp_all
      simp only [hp', ↓reduceIte] at h
      have hle := List.length_filter_le p xs
      omega

theorem countCols_all (occ : Occ) (r : Fin 4) (h : countCols occ r = 13) :
    ∀ c, occGet occ r c = true := by
  have hlen : (fins13.filter (fun c => occGet occ r c)).length = fins13.length := by
    simpa [countCols, length_fins13] using h
  intro c
  exact filter_length_eq_all fins13 (fun c => occGet occ r c) hlen c (mem_fins13 c)

theorem occ_full_of_count (occ : Occ) (h : occCount occ = 52) :
    ∀ (r : Fin 4) (c : Fin 13), occGet occ r c = true := by
  have hsum :
      countCols occ 0 + (countCols occ 1 + (countCols occ 2 + countCols occ 3)) = 52 := by
    simpa [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero] using h
  have h0 := countCols_le occ 0
  have h1 := countCols_le occ 1
  have h2 := countCols_le occ 2
  have h3 := countCols_le occ 3
  have e0 : countCols occ 0 = 13 := by omega
  have e1 : countCols occ 1 = 13 := by omega
  have e2 : countCols occ 2 = 13 := by omega
  have e3 : countCols occ 3 = 13 := by omega
  intro r c
  match r with
  | ⟨0, _⟩ => exact countCols_all occ ⟨0, by decide⟩ e0 c
  | ⟨1, _⟩ => exact countCols_all occ ⟨1, by decide⟩ e1 c
  | ⟨2, _⟩ => exact countCols_all occ ⟨2, by decide⟩ e2 c
  | ⟨3, _⟩ => exact countCols_all occ ⟨3, by decide⟩ e3 c
  | ⟨n + 4, hn⟩ => omega

def rowMarks (occ : Occ) (r : Fin 4) : Array Int :=
  embed (toList13 (occMarks occ r))

def occSoFar (occ : Occ) : Nat → Array (Array Int)
  | 0 => #[]
  | 1 => #[rowMarks occ 0]
  | 2 => #[rowMarks occ 0, rowMarks occ 1]
  | 3 => #[rowMarks occ 0, rowMarks occ 1, rowMarks occ 2]
  | _ => #[rowMarks occ 0, rowMarks occ 1, rowMarks occ 2, rowMarks occ 3]

theorem occSoFar_succ (occ : Occ) (r : Nat) (hr : r < 4) :
    (occSoFar occ r).push (rowMarks occ ⟨r, hr⟩) = occSoFar occ (r + 1) := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr' with rfl | rfl | rfl | rfl
  · simp [occSoFar, Array.push]
  · simp [occSoFar, Array.push]
  · simp [occSoFar, Array.push]
  · simp [occSoFar, Array.push]

theorem occSoFar_grid (occ : Occ) : occSoFar occ 4 = embedGrid (occMarks occ) := by
  unfold occSoFar embedGrid rowMarks
  rfl

theorem mark_row_appended (g : NatGrid) (occ : Occ) (r : Fin 4) (base : Array (Array Int)) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel13
      (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
      (fun σ =>
        let marks := σ.2
        do
          let _mb := SudoRt.appendL base marks
          let ⟨occ, _⟩ := _mb
          pure (SudoRt.Flow.cont (ρ := Array Int) occ))
      (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) =
    .ok (SudoRt.Flow.cont (base.push (rowMarks occ r))) := by
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      markColStep (seatArr g occ) (Int.ofNat r.val) 12
        (Int.ofNat j, embed ((toList13 (occMarks occ r)).take j)) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, embed ((toList13 (occMarks occ r)).take (j + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed ((toList13 (occMarks occ r)).take (j + 1)))) :=
    fun j _ hj => markCol_hit g occ r j hj
  have ht : (toList13 (occMarks occ r)).take 13 = toList13 (occMarks occ r) := by
    simpa [length_toList13] using List.take_length (toList13 (occMarks occ r))
  have hafter :
      (fun σ : Int × Array Int =>
        let marks := σ.2
        (do
          let _mb := SudoRt.appendL base marks
          let ⟨occ, _⟩ := _mb
          pure (SudoRt.Flow.cont (ρ := Array Int) occ) :
          Except SudoRt.Trap (SudoRt.Flow (Array (Array Int)) (Array Int))))
        (Int.ofNat 12, embed ((toList13 (occMarks occ r)).take 13)) =
      .ok (SudoRt.Flow.cont (base.push (rowMarks occ r))) := by
    simp only [ht, appendL_spec, rowMarks]
    rfl
  have hrun := chain_loop
    (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
    (fun σ =>
      let marks := σ.2
      do
        let _mb := SudoRt.appendL base marks
        let ⟨occ, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array Int) occ))
    (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x))
    (fun j => embed ((toList13 (occMarks occ r)).take j)) 0 12 (Nat.zero_le _) hstep
    (.ok (SudoRt.Flow.cont (base.push (rowMarks occ r))))
    hafter
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel13
        (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
        (fun σ =>
          let marks := σ.2
          do
            let _mb := SudoRt.appendL base marks
            let ⟨occ, _⟩ := _mb
            pure (SudoRt.Flow.cont (ρ := Array Int) occ))
        (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((toList13 (occMarks occ r)).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12))
        (markColStep (seatArr g occ) (Int.ofNat r.val) 12)
        (fun σ =>
          let marks := σ.2
          do
            let _mb := SudoRt.appendL base marks
            let ⟨occ, _⟩ := _mb
            pure (SudoRt.Flow.cont (ρ := Array Int) occ))
        (fun x => pure (SudoRt.Flow.ret (ρ := Array Int) x)) := by
    rw [fuel13_eq, List.take_zero, embed_nil, show (0 : Int) = Int.ofNat 0 from rfl]
  exact hcast.trans hrun

theorem markRowStep_hit (g : NatGrid) (occ : Occ) (rr : Nat) (hr : rr ≤ 3) :
    markRowStep (seatArr g occ) 3 (Int.ofNat rr, occSoFar occ rr) =
      if rr = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat rr, occSoFar occ (rr + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (rr + 1), occSoFar occ (rr + 1))) := by
  have hr4 : rr < 4 := by omega
  unfold markRowStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat rr > (3 : Int) from ofNat_not_gt hr)]
  have hrow := mark_row_appended g occ ⟨rr, hr4⟩ (occSoFar occ rr)
  rw [show (if (0 : Int) > (12 : Int) then 1 else ((12 : Int) - 0).natAbs + 1) = fuel13 from rfl]
  rw [hrow, occSoFar_succ occ rr hr4]
  simp only [ok_bind, Pure.pure, Except.pure]
  by_cases heq : rr = 3
  · subst heq
    have hb : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hb]
  · have hb : ((Int.ofNat rr) == (3 : Int)) = false := by
      cases hbv : (Int.ofNat rr) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
    simp only [hb, ↓reduceIte]
    rw [addI_ofNat_one rr (fits_succ_lt (by omega : rr < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem occ_rows_loop {β : Type} (g : NatGrid) (occ : Occ)
    (after : Int × Array (Array Int) → Except SudoRt.Trap β)
    (onRet : Array Int → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embedGrid (occMarks occ)) = goal) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array (Array Int))) fuel4
      (markRowStep (seatArr g occ) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      markRowStep (seatArr g occ) 3 (Int.ofNat i, occSoFar occ i) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, occSoFar occ (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), occSoFar occ (i + 1))) :=
    fun i _ hi => markRowStep_hit g occ i hi
  have hrun := chain_loop (markRowStep (seatArr g occ) 3) after onRet
    (occSoFar occ) 0 3 (Nat.zero_le _) hstep goal (by simpa [occSoFar_grid] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array (Array Int))) fuel4
        (markRowStep (seatArr g occ) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, occSoFar occ 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (markRowStep (seatArr g occ) 3) after onRet := by
    rw [fuel4_eq, show (0 : Int) = Int.ofNat 0 from rfl]
    simp [occSoFar]
  exact hcast.trans hrun

/-- `(prevCard, finger row, finger column)`; the finger starts on AS = (2,0). -/
def mixPrev (st : WalkState) : Nat × Nat × Nat :=
  match st.prev with
  | none => (0, 2, 0)
  | some (card, f) => (card, f.1.val, f.2.val)

def mixPayload (hand : Fin 52 → Nat) (n : Nat) :
    Int × Int × Int × Array (Array Int) × Int :=
  let (g, st) := placeN hand n
  let p := mixPrev st
  (Int.ofNat p.2.1, Int.ofNat p.2.2, Int.ofNat st.t, seatArr g st.occ, Int.ofNat p.1)

theorem index_cont {σ : Type} (n : Nat) (hn : n ≤ 51) (st : σ) :
    (if ((Int.ofNat n) == (51 : Int)) = true then
        pure (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat n, st))
      else do
        let n' ← SudoRt.addI (Int.ofNat n) 1
        pure (SudoRt.Flow.cont (ρ := Array Int) (n', st))) =
    (if n = 51 then .ok (SudoRt.Flow.brk (Int.ofNat n, st))
    else .ok (SudoRt.Flow.cont (Int.ofNat (n + 1), st)) :
      Except SudoRt.Trap (SudoRt.Flow (Int × σ) (Array Int))) := by
  by_cases heq : n = 51
  · subst heq
    have hb : ((Int.ofNat 51) == (51 : Int)) = true := by decide
    simp [hb, Pure.pure, Except.pure]
  · have hb : ((Int.ofNat n) == (51 : Int)) = false := by
      cases hbv : (Int.ofNat n) == (51 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
    simp only [hb, ↓reduceIte, Pure.pure, Except.pure]
    rw [addI_ofNat_one n (fits_succ_lt (by omega : n < 51) (by decide : 51 ≤ 52))]
    simp [ok_bind, heq]

theorem mixPayload_at (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52)
    (pos : Fin 4 × Fin 13) (t' : Nat) (f : Fin 4 × Fin 13)
    (hseat : chooseSeat! (placeN hand n).2 = (pos, (t', f))) :
    mixPayload hand (n + 1) =
      (Int.ofNat f.1.val, Int.ofNat f.2.val, Int.ofNat t',
        seatArr (setGrid (placeN hand n).1 pos (hand ⟨n, hn⟩))
          (setOcc (placeN hand n).2.occ pos),
        Int.ofNat (hand ⟨n, hn⟩)) := by
  have hs := placeN_step hand n hn
  simp [mixPayload, hs.1, hs.2, hseat, advance, mixPrev]

theorem place_cont (g : NatGrid) (occ : Occ) (r : Fin 4) (c : Fin 13) (card : Nat)
    (fr fc t : Int)
    (hfree : occGet occ r c = false) (hsz : occ.size = 52) :
    (do
      let row ← SudoRt.atL (seatArr g occ) (Int.ofNat r.val)
      let row ← SudoRt.putL row (Int.ofNat c.val) (Int.ofNat card)
      let grid ← SudoRt.putL (seatArr g occ) (Int.ofNat r.val) row
      pure (SudoRt.Flow.cont (ρ := Array Int)
        (fr, fc, t, grid, Int.ofNat card))) =
    .ok (SudoRt.Flow.cont
      (fr, fc, t, seatArr (setGrid g (r, c) card) (setOcc occ (r, c)), Int.ofNat card)) := by
  have hpl := seat_place g occ r c card hfree hsz
  have hat := atL_ofNat (seatArr g occ) r.val (by rw [seatArr_size]; exact r.isLt)
  rw [seatArr_get g occ r] at hat
  have hrowSz : c.val < (Array.mk (seatRow g occ r)).size := by
    rw [Array.size_mk, seatRow, length_toList13]
    exact c.isLt
  have hputR := putL_ofNat (Array.mk (seatRow g occ r)) c.val (Int.ofNat card) hrowSz
  have hputG := putL_ofNat (seatArr g occ) r.val
      ((Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card))
      (by rw [seatArr_size]; exact r.isLt)
  simp only [hat, hputR, hputG, ok_bind, Pure.pure, Except.pure] at hpl ⊢
  injection hpl with harr
  rw [harr]

theorem seat_placed_array (g : NatGrid) (occ : Occ) (r : Fin 4) (c : Fin 13) (card : Nat)
    (hfree : occGet occ r c = false) (hsz : occ.size = 52)
    (hrowSz : c.val < (Array.mk (seatRow g occ r)).size) :
    (seatArr g occ).set ⟨r.val, by rw [seatArr_size]; exact r.isLt⟩
      ((Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card)) =
    seatArr (setGrid g (r, c) card) (setOcc occ (r, c)) := by
  have h := seat_place g occ r c card hfree hsz
  have hat := atL_ofNat (seatArr g occ) r.val (by rw [seatArr_size]; exact r.isLt)
  rw [seatArr_get g occ r] at hat
  have hputR := putL_ofNat (Array.mk (seatRow g occ r)) c.val (Int.ofNat card) hrowSz
  have hputG := putL_ofNat (seatArr g occ) r.val
      ((Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card))
      (by rw [seatArr_size]; exact r.isLt)
  simp only [hat, hputR, hputG, ok_bind] at h
  injection h with harr

/-- The blocked branch after the occupancy bitmap: blocker-directed scan,
    marker + 1, finger := target + step(blocker), then the write. -/
theorem blocked_after (g : NatGrid) (occ : Occ) (hsz : occ.size = 52)
    (t : Nat) (ht : t < 4) (target : Fin 4 × Fin 13) (B card : Nat) (hB : CardBound B)
    (p : Fin 4 × Fin 13) (hfree : occAt occ p = false)
    (hov : overflowSeat occ ((t + suit B) % 4) ((target.2.val + rank B) % 13) = some p) :
    (do
      let s ← Doubledeal.suit_of (Int.ofNat B)
      let a ← SudoRt.addI (Int.ofNat t) s
      let srow ← SudoRt.modI a (4 : Int)
      let k ← Doubledeal.rank_of (Int.ofNat B)
      let a2 ← SudoRt.addI (Int.ofNat target.2.val) k
      let scol ← SudoRt.modI a2 (13 : Int)
      let seat ← Doubledeal.overflow_seat (embedGrid (occMarks occ)) srow scol
      let t1 ← SudoRt.addI (Int.ofNat t) (1 : Int)
      let t' ← SudoRt.modI t1 (4 : Int)
      let f ← Doubledeal.step_seat (Int.ofNat B) (Int.ofNat target.1.val) (Int.ofNat target.2.val)
      let row ← SudoRt.atL (seatArr g occ) seat.1
      let row ← SudoRt.putL row seat.2 (Int.ofNat card)
      let grid ← SudoRt.putL (seatArr g occ) seat.1 row
      pure (SudoRt.Flow.cont (ρ := Array Int) (f.1, f.2, t', grid, Int.ofNat card))) =
    .ok (SudoRt.Flow.cont
      (Int.ofNat (gridStep B target).1.val, Int.ofNat (gridStep B target).2.val,
        Int.ofNat ((t + 1) % 4),
        seatArr (setGrid g p card) (setOcc occ p), Int.ofNat card)) := by
  have hbig : 30 ≤ i64MaxNat := by unfold i64MaxNat; decide
  have hsuit : FitsLen (t + suit B) := by
    have hdiv : suit B ≤ B := Nat.div_le_self _ _
    unfold FitsLen CardBound at *
    omega
  have hrk : FitsLen (target.2.val + rank B) := by
    have : rank B ≤ 13 := by simp [rank]; omega
    have := target.2.isLt
    unfold FitsLen
    omega
  have m4 : ∀ a : Nat, SudoRt.modI (Int.ofNat a) (4 : Int) = .ok (Int.ofNat (a % 4)) :=
    fun a => modI_ofNat a (by decide)
  have m13 : ∀ a : Nat, SudoRt.modI (Int.ofNat a) (13 : Int) = .ok (Int.ofNat (a % 13)) :=
    fun a => modI_ofNat a (by decide)
  have hov' := overflow_seat_refines occ ((t + suit B) % 4) (Nat.mod_lt _ (by decide))
    ((target.2.val + rank B) % 13) (Nat.mod_lt _ (by decide)) p.1 p.2 hov
  have hss := step_seat_refines B target.1.val target.2.val
    (by have := target.1.isLt; omega) (by have := target.2.isLt; omega) hB
  have hpl := place_cont g occ p.1 p.2 card
    (Int.ofNat ((target.1.val + suit B) % 4)) (Int.ofNat ((target.2.val + rank B) % 13))
    (Int.ofNat ((t + 1) % 4)) hfree hsz
  have hc : (gridStep B target).1.val = (target.1.val + suit B) % 4 ∧
      (gridStep B target).2.val = (target.2.val + rank B) % 13 := by
    simp [gridStep]
  simp only [suit_of_refines]; rw [ok_bind]
  simp only [addI_ofNat t (suit B) hsuit]; rw [ok_bind]
  simp only [m4]; rw [ok_bind]
  simp only [rank_of_refines]; rw [ok_bind]
  simp only [addI_ofNat _ _ hrk]; rw [ok_bind]
  simp only [m13]; rw [ok_bind]
  simp only [hov']; rw [ok_bind]
  simp only [addI_ofNat_one t (fits_succ_lt ht (by decide : 4 ≤ 52))]; rw [ok_bind]
  simp only [m4]; rw [ok_bind]
  simp only [hss]; rw [ok_bind]
  rw [hc.1, hc.2]
  exact hpl

set_option maxHeartbeats 1600000 in
theorem mixStep_hit (hand : Fin 52 → Nat) (hcard : ∀ i, CardBound (hand i))
    (n : Nat) (hn : n ≤ 51) :
    mixStep (embed (toDeck hand)) 51 (Int.ofNat n, mixPayload hand n) =
      if n = 51 then
        .ok (SudoRt.Flow.brk (Int.ofNat n, mixPayload hand (n + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (n + 1), mixPayload hand (n + 1))) := by
  have hlen : n < 52 := by omega
  unfold mixStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat n > (51 : Int) from ofNat_not_gt hn)]
  have hat := atL_embed (toDeck hand) n (by rw [length_toDeck]; exact hlen)
  rw [hat]
  simp only [toDeck, Array.getElem_toList, Array.getElem_ofFn, ok_bind]
  by_cases h0 : n = 0
  · subst h0
    have hgt : ¬ decide (Int.ofNat 0 > (0 : Int)) = true := by
      have hdec : decide (Int.ofNat 0 > (0 : Int)) = false := by decide
      simp [hdec]
    rw [if_neg hgt]
    have hgrid :
        (mixPayload hand 0).2.2.2.1 = seatArr (fun _ _ => (0 : Nat)) emptyOcc := by
      simp [mixPayload, placeN, initWalk]
    have hf0 : (mixPayload hand 0).1 = Int.ofNat 2 ∧ (mixPayload hand 0).2.1 = Int.ofNat 0 ∧
        (mixPayload hand 0).2.2.1 = Int.ofNat 0 := by
      simp [mixPayload, placeN, initWalk, mixPrev]
    simp only [hgrid, hf0.1, hf0.2.1, hf0.2.2]
    have hpl := place_cont (fun _ _ => (0 : Nat)) emptyOcc
      ⟨2, by decide⟩ ⟨0, by decide⟩ (hand ⟨0, by decide⟩) (Int.ofNat 2) (Int.ofNat 0)
      (Int.ofNat 0) (occGet_empty _ _) size_emptyOcc
    rw [show (2 : Int) = Int.ofNat 2 from rfl, show (0 : Int) = Int.ofNat 0 from rfl]
    rw [hpl]
    simp only [ok_bind]
    have hseat : chooseSeat! (placeN hand 0).2 = (asStart, (0, asStart)) := by
      simpa [placeN, initWalk] using chooseSeat!_init
    have hnext := mixPayload_at hand 0 (by decide) asStart 0 asStart hseat
    simp only [hnext, asStart]
    exact index_cont 0 (by decide) _
  · have ipos : 0 < n := by omega
    have hgt : decide (Int.ofNat n > (0 : Int)) = true :=
      decide_eq_true (by
        simpa [ofNat_eq_natCast] using (Int.ofNat_lt.mpr ipos))
    simp only [hgt, ↓reduceIte]
    have hprev : (placeN hand n).2.prev =
        some (hand ⟨n - 1, by omega⟩, (chooseSeat! (placeN hand (n - 1)).2).2.2) := by
      have h := placeN_prev_succ hand (n - 1) (by omega)
      simpa [show (n - 1) + 1 = n by omega] using h
    let card0 : Nat := hand ⟨n - 1, by omega⟩
    let pos : Fin 4 × Fin 13 := (chooseSeat! (placeN hand (n - 1)).2).2.2
    have hpay :
        mixPayload hand n =
          (Int.ofNat pos.1.val, Int.ofNat pos.2.val, Int.ofNat (placeN hand n).2.t,
            seatArr (placeN hand n).1 (placeN hand n).2.occ, Int.ofNat card0) := by
      simp [mixPayload, mixPrev, hprev, card0, pos]
    simp only [hpay]
    have hss := step_seat_refines card0 pos.1.val pos.2.val
      (by have := pos.1.isLt; omega) (by have := pos.2.isLt; omega) (hcard _)
    rw [hss]
    simp only [ok_bind]
    have hcoords := gridStep_coords card0 pos.1 pos.2
    rw [← hcoords.1, ← hcoords.2]
    let target : Fin 4 × Fin 13 := gridStep card0 (pos.1, pos.2)
    have hatG := atL_ofNat (seatArr (placeN hand n).1 (placeN hand n).2.occ) target.1.val
      (by rw [seatArr_size]; exact target.1.isLt)
    rw [seatArr_get (placeN hand n).1 (placeN hand n).2.occ target.1] at hatG
    simp only [hatG, ok_bind]
    have hrowSz : target.2.val <
        (Array.mk (seatRow (placeN hand n).1 (placeN hand n).2.occ target.1)).size := by
      rw [Array.size_mk, seatRow, length_toList13]
      exact target.2.isLt
    have hatC := atL_ofNat
      (Array.mk (seatRow (placeN hand n).1 (placeN hand n).2.occ target.1))
      target.2.val hrowSz
    rw [hatC]
    simp only [ok_bind, Array.getElem_mk,
      seat_cell (placeN hand n).1 (placeN hand n).2.occ target.1 target.2.val target.2.isLt]
    by_cases hfree : occGet (placeN hand n).2.occ target.1 target.2 = false
    · rw [hfree]
      rw [if_neg (show ¬ (false = true) from by decide)]
      rw [if_pos (by decide : decide ((-1 : Int) < (0 : Int)) = true)]
      have hputR := putL_ofNat
        (Array.mk (seatRow (placeN hand n).1 (placeN hand n).2.occ target.1))
        target.2.val (Int.ofNat (hand ⟨n, hlen⟩)) hrowSz
      have hputG := putL_ofNat (seatArr (placeN hand n).1 (placeN hand n).2.occ) target.1.val
        ((Array.mk (seatRow (placeN hand n).1 (placeN hand n).2.occ target.1)).set
          ⟨target.2.val, hrowSz⟩ (Int.ofNat (hand ⟨n, hlen⟩)))
        (by rw [seatArr_size]; exact target.1.isLt)
      have harr := seat_placed_array (placeN hand n).1 (placeN hand n).2.occ target.1 target.2
        (hand ⟨n, hlen⟩) hfree (placeN_occ_size hand n) hrowSz
      dsimp only [target] at hputR hputG harr
      rw [hputR]
      simp only [ok_bind]
      rw [hputG]
      simp only [ok_bind, harr, Pure.pure, Except.pure]
      have hch : chooseSeat! (placeN hand n).2 = (target, ((placeN hand n).2.t, target)) := by
        simpa [card0, pos, target] using
          chooseSeat!_free_target (placeN hand n).2 card0 pos hprev hfree
      have hnext := mixPayload_at hand n hlen target (placeN hand n).2.t target hch
      simp only [hnext]
      exact index_cont n hn _
    · have hocc : occGet (placeN hand n).2.occ target.1 target.2 = true := by
        simpa [Bool.not_eq_true] using hfree
      simp only [hocc, ↓reduceIte]
      have hlt : decide (Int.ofNat ((placeN hand n).1 target.1 target.2) < (0 : Int)) = false :=
        decide_eq_false (Int.not_lt.mpr (Int.ofNat_zero_le _))
      rw [hlt]
      rw [if_neg (show ¬ ((false : Bool) = true) from by decide)]
      have htlt := placeN_t_lt hand n (Nat.le_of_lt hlen)
      have hct : occCount (placeN hand n).2.occ < 52 := by
        rw [placeN_count hand n (Nat.le_of_lt hlen)]; omega
      let B : Nat := (placeN hand n).1 target.1 target.2
      have hB : CardBound B := placeN_cardBound hand hcard n target.1 target.2
      have hboard : (placeN hand n).2.board target.1 target.2 = B :=
        (congrFun (congrFun (placeN_board hand n) target.1) target.2).symm
      obtain ⟨p, hov, hfr⟩ := overflow_some_of_count_lt (placeN hand n).2.occ
        (((placeN hand n).2.t + suit B) % 4) ((target.2.val + rank B) % 13) hct
      rw [show (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) = fuel4 from rfl]
      rw [occ_rows_loop (placeN hand n).1 (placeN hand n).2.occ _ _ _ rfl]
      have hafter := blocked_after (placeN hand n).1 (placeN hand n).2.occ (placeN_occ_size hand n)
        (placeN hand n).2.t htlt target B (hand ⟨n, hlen⟩) hB p hfr hov
      erw [hafter]
      simp only [ok_bind, Pure.pure, Except.pure]
      have hch : chooseSeat! (placeN hand n).2 =
          (p, (((placeN hand n).2.t + 1) % 4, gridStep B target)) := by
        have hoccAt : occAt (placeN hand n).2.occ target = true := hocc
        have := chooseSeat!_blocked (placeN hand n).2 card0 pos p hprev hoccAt
          (by simpa [target, hboard] using hov)
        simpa [target, hboard] using this
      have hnext := mixPayload_at hand n hlen p _ _ hch
      simp only [hnext]
      exact index_cont n hn _

theorem mix_columns_as_loop (d : Array Int) :
    Doubledeal.mix_columns d =
      (do
        let grid ← Doubledeal.empty_rows
        let t := (0 : Int)
        let prev_card := (0 : Int)
        let fr := (2 : Int)
        let fc := (0 : Int)
        let _fromV := (0 : Int)
        let _toV := (51 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array Int)
          (_fromV, (fr, fc, t, grid, prev_card)) fuel
          (mixStep d _toV)
          (fun σ =>
            let grid := σ.2.2.2.2.1
            do
              let scooped ← Doubledeal.scoop_rm grid
              pure scooped)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.mix_columns
  rfl

set_option maxHeartbeats 800000 in
theorem mix_columns_refines (hand : Fin 52 → Nat) (hcard : ∀ i, CardBound (hand i)) :
    Doubledeal.mix_columns (embed (toDeck hand)) =
      .ok (embed (toDeck (mixColumns hand))) := by
  rw [mix_columns_as_loop, empty_rows_spec, ok_bind]
  have hinit :
      ((2 : Int), (0 : Int), (0 : Int), blankRows 4, (0 : Int)) = mixPayload hand 0 := by
    simp [mixPayload, placeN, initWalk, mixPrev]
    exact blank_seat (fun _ _ => (0 : Nat))
  have hfuel :
      (if (0 : Int) > (51 : Int) then 1 else ((51 : Int) - 0).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat 51) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  dsimp only
  rw [show ((0 : Int), (2 : Int), (0 : Int), (0 : Int), blankRows 4, (0 : Int)) =
      ((0 : Int), mixPayload hand 0) from by simpa using hinit]
  rw [hfuel, except_bind_pure]
  have hstep : ∀ i, 0 ≤ i → i ≤ 51 →
      mixStep (embed (toDeck hand)) 51 (Int.ofNat i, mixPayload hand i) =
        if i = 51 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, mixPayload hand (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), mixPayload hand (i + 1))) :=
    fun i _ hi => mixStep_hit hand hcard i hi
  have hrun := chain_loop (mixStep (embed (toDeck hand)) 51)
    (fun σ =>
      let grid := σ.2.2.2.2.1
      do
        let scooped ← Doubledeal.scoop_rm grid
        pure scooped)
    (fun r => pure r)
    (mixPayload hand) 0 51 (Nat.zero_le _) hstep
    (.ok (embed (toDeck (mixColumns hand)))) (by
      have hall := occ_full_of_count (placeN hand 52).2.occ (placeN_count hand 52 (Nat.le_refl _))
      have hseat := seatArr_full (placeN hand 52).1 (placeN hand 52).2.occ hall
      have hgrid : (mixPayload hand 52).2.2.2.1 = embedGrid (placeN hand 52).1 := by
        simp [mixPayload, hseat]
      dsimp only
      rw [hgrid, scoop_rm_refines, mixColumns, placedGrid, except_bind_pure])
  exact hrun

end DoubleDeal.Link2
