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

/-- Card values for which `r + suit` stays inside i64 when `r < 4`. -/
def CardBound (c : Nat) : Prop := c ≤ i64MaxNat - 4

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

/-- Generated occupancy-scan column step. `found = -1` until the first empty mark. -/
def scanColStep (occ : Array (Array Int)) (row toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Int × Int × Int)) :=
  let col := σ.1
  let found := σ.2
  do
    if col > toV then
      pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (col, found))
    else
      match ← ((do
        let hit ← (if decide (found < (0 : Int)) then (do
          let rowA ← SudoRt.atL occ row
          let cell ← SudoRt.atL rowA col
          pure (SudoRt.SEq.beq cell (0 : Int))) else pure false)
        if hit then
          pure (SudoRt.Flow.cont (ρ := Int × Int × Int) col)
        else
          pure (SudoRt.Flow.cont (ρ := Int × Int × Int) found)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Int × Int × Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int × Int × Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (col, fs))
      | .cont fs =>
          if (col == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (col, fs))
          else do
            let col' ← SudoRt.addI col 1
            pure (SudoRt.Flow.cont (ρ := Int × Int × Int) (col', fs))

def scanFound (empty : Nat → Bool) : Nat → Int
  | 0 => -1
  | n + 1 =>
    let prev := scanFound empty n
    if prev < 0 ∧ empty n then Int.ofNat n else prev

theorem scanFound_neg_or_lt (empty : Nat → Bool) : ∀ n, scanFound empty n < 0 ∨
    ∃ k, k < n ∧ scanFound empty n = Int.ofNat k
  | 0 => Or.inl (by simp [scanFound])
  | n + 1 => by
    simp only [scanFound]
    have ih := scanFound_neg_or_lt empty n
    by_cases h : scanFound empty n < 0 ∧ empty n
    · exact Or.inr ⟨n, Nat.lt_succ_self _, by simp [h]⟩
    · simpa [h] using
        ih.imp_right (fun ⟨k, hk, he⟩ => ⟨k, Nat.lt_succ_of_lt hk, he⟩)

def occMarks (occ : Occ) : Grid Nat :=
  fun r c => if occGet occ r c then 1 else 0

def rowEmpty (occ : Occ) (row : Fin 4) (i : Nat) : Bool :=
  if h : i < 13 then !occGet occ row ⟨i, h⟩ else false

theorem scanCol_hit (occ : Occ) (row : Fin 4) (j : Nat) (hj : j ≤ 12) :
    scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12
      (Int.ofNat j, scanFound (rowEmpty occ row) j) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, scanFound (rowEmpty occ row) (j + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), scanFound (rowEmpty occ row) (j + 1))) := by
  have hj13 : j < 13 := by omega
  unfold scanColStep
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  have hrow := embedGrid_get (occMarks occ) row
  have hat := atL_ofNat (embedGrid (occMarks occ)) row.val (by rw [embedGrid_size]; exact row.isLt)
  have hat' :
      (embedGrid (occMarks occ))[row.val]'(by rw [embedGrid_size]; exact row.isLt) =
        embed (toList13 (occMarks occ row)) := by simpa using hrow
  rw [hat'] at hat
  have hget := getElem_toList13 (occMarks occ row) ⟨j, hj13⟩
  have hatC := atL_embed (toList13 (occMarks occ row)) j (by rw [length_toList13]; exact hj13)
  by_cases hlt : scanFound (rowEmpty occ row) j < 0
  · have hd : decide (scanFound (rowEmpty occ row) j < 0) = true := decide_eq_true hlt
    simp only [hat, hd, ↓reduceIte, ok_bind]
    rw [hatC]
    simp only [ok_bind, hget]
    have hbit : occMarks occ row ⟨j, hj13⟩ = if rowEmpty occ row j then 0 else 1 := by
      cases hb : occGet occ row ⟨j, hj13⟩ <;> simp [occMarks, rowEmpty, hj13, hb]
    by_cases hempty : rowEmpty occ row j
    · have hbeq : SudoRt.SEq.beq (Int.ofNat (occMarks occ row ⟨j, hj13⟩)) (0 : Int) = true := by
        simp [hbit, hempty, SudoRt.SEq.beq, beq_int_iff]
      simp only [hbeq, ↓reduceIte]
      have hnext : scanFound (rowEmpty occ row) (j + 1) = Int.ofNat j := by
        simp [scanFound, hlt, hempty]
      simp only [hnext]
      -- break or continue
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
    · have hbeq : SudoRt.SEq.beq (Int.ofNat (occMarks occ row ⟨j, hj13⟩)) (0 : Int) = false := by
        simp [hbit, hempty, SudoRt.SEq.beq, beq_int_iff]
      simp only [hbeq, ↓reduceIte]
      have hnext : scanFound (rowEmpty occ row) (j + 1) = scanFound (rowEmpty occ row) j := by
        simp [scanFound, hlt, hempty]
      simp only [hnext]
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
  · have hd : decide (scanFound (rowEmpty occ row) j < 0) = false := decide_eq_false hlt
    simp only [hat, hd, ↓reduceIte, ok_bind]
    have hnext : scanFound (rowEmpty occ row) (j + 1) = scanFound (rowEmpty occ row) j := by
      simp [scanFound, hlt]
    simp only [hnext]
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

theorem scan_loop {β : Type} (occ : Occ) (row : Fin 4)
    (after : Int × Int → Except SudoRt.Trap β)
    (onRet : (Int × Int × Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 12, scanFound (rowEmpty occ row) 13) = goal) :
    SudoRt.runLoopOn ((0 : Int), (-1 : Int)) fuel13
      (scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12)
      after onRet = goal := by
  have hstep : ∀ j, 0 ≤ j → j ≤ 12 →
      scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12
        (Int.ofNat j, scanFound (rowEmpty occ row) j) =
        if j = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat j, scanFound (rowEmpty occ row) (j + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), scanFound (rowEmpty occ row) (j + 1))) :=
    fun j _ hj => scanCol_hit occ row j hj
  have hrun := chain_loop
    (scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12)
    after onRet (fun j => scanFound (rowEmpty occ row) j) 0 12 (Nat.zero_le _) hstep goal hafter
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (-1 : Int)) fuel13
        (scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, scanFound (rowEmpty occ row) 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat 12))
        (scanColStep (embedGrid (occMarks occ)) (Int.ofNat row.val) 12) after onRet := by
    rw [fuel13_eq, scanFound, show (0 : Int) = Int.ofNat 0 from rfl]
  exact hcast.trans hrun

/-- `scanFound n` is the first empty column below `n`, or `-1`. -/
theorem scanFound_spec (empty : Nat → Bool) :
    ∀ n, (∀ i, i < n → empty i = false) ∧ scanFound empty n = -1 ∨
      ∃ k, k < n ∧ empty k = true ∧ (∀ i, i < k → empty i = false) ∧
        scanFound empty n = Int.ofNat k
  | 0 => Or.inl ⟨fun i hi => by omega, by simp [scanFound]⟩
  | n + 1 => by
    have ih := scanFound_spec empty n
    simp only [scanFound]
    cases ih with
    | inl hfull =>
      by_cases hempty : empty n
      · refine Or.inr ⟨n, Nat.lt_succ_self _, hempty, hfull.1, ?_⟩
        simp [hfull.2, hempty]
      · refine Or.inl ⟨?_, by simp [hfull.2, hempty]⟩
        intro i hi
        by_cases hi' : i < n
        · exact hfull.1 i hi'
        · have : i = n := by omega
          simpa [this] using hempty
    | inr hsome =>
      obtain ⟨k, hk, hemp, hbefore, hkval⟩ := hsome
      refine Or.inr ⟨k, Nat.lt_succ_of_lt hk, hemp, hbefore, ?_⟩
      have hk0 : ¬ Int.ofNat k < (0 : Int) := Int.not_lt.mpr (Int.ofNat_zero_le _)
      rw [hkval]
      rw [if_neg (fun h : Int.ofNat k < 0 ∧ empty n = true => hk0 h.1)]

def occNat (occ : Occ) (row : Fin 4) (i : Nat) : Bool :=
  if h : i < 13 then occGet occ row ⟨i, h⟩ else true

theorem scanRowN_spec (occ : Occ) (row : Fin 4) :
    ∀ fuel col, col + fuel ≤ 13 →
      (∀ i, col ≤ i → i < col + fuel → occNat occ row i = true) ∧
        scanRowN occ row fuel col = none ∨
      ∃ c : Fin 13, col ≤ c.val ∧ c.val < col + fuel ∧ occGet occ row c = false ∧
        (∀ i, col ≤ i → i < c.val → occNat occ row i = true) ∧
        scanRowN occ row fuel col = some c
  | 0, col, _ => Or.inl ⟨fun i _ hi => by omega, by simp [scanRowN]⟩
  | fuel + 1, col, hsum => by
    have hclt : col < 13 := by omega
    simp only [scanRowN, hclt, ↓reduceDIte]
    by_cases hocc : occGet occ row ⟨col, hclt⟩
    · have ih := scanRowN_spec occ row fuel (col + 1) (by omega)
      simp only [hocc, ↓reduceIte]
      cases ih with
      | inl hfull =>
        refine Or.inl ⟨?_, hfull.2⟩
        intro i hi1 hi2
        by_cases heq : i = col
        · subst heq
          simp [occNat, hclt, hocc]
        · exact hfull.1 i (by omega) (by omega)
      | inr hsome =>
        obtain ⟨c, hc1, hc2, hemp, hbefore, hcval⟩ := hsome
        have hc2' : c.val < col + (fuel + 1) := by omega
        refine Or.inr ⟨c, by omega, hc2', hemp, ?_, hcval⟩
        intro i hi1 hi2
        by_cases heq : i = col
        · subst heq
          simp [occNat, hclt, hocc]
        · exact hbefore i (by omega) hi2
    · have hfalse : occGet occ row ⟨col, hclt⟩ = false := by
        simpa [Bool.not_eq_true] using hocc
      refine Or.inr ⟨⟨col, hclt⟩, Nat.le_refl _, ?_, hfalse,
        fun i _ hi2 => by
          have : (⟨col, hclt⟩ : Fin 13).val = col := rfl
          omega, ?_⟩
      · have : (⟨col, hclt⟩ : Fin 13).val = col := rfl
        omega
      · simp [hfalse]

theorem scanFound_encode (occ : Occ) (row : Fin 4) :
    scanFound (rowEmpty occ row) 13 =
      match scanRow occ row with
      | some c => Int.ofNat c.val
      | none => -1 := by
  have hf := scanFound_spec (rowEmpty occ row) 13
  have hs := scanRowN_spec occ row 13 0 (by decide)
  simp only [scanRow] at hs
  cases hf with
  | inl hfull =>
    cases hs with
    | inl hnone =>
      rw [scanRow, hfull.2, hnone.2]
    | inr hsome =>
      obtain ⟨c, hc1, hc2, hemp, _, _⟩ := hsome
      have hempty : rowEmpty occ row c.val = true := by simp [rowEmpty, c.isLt, hemp]
      exact absurd hempty (by simpa using hfull.1 c.val hc2)
  | inr hsome =>
    obtain ⟨k, hk, hemp, hbefore, hkval⟩ := hsome
    have hklt : k < 13 := hk
    cases hs with
    | inl hnone =>
      have hocc : occNat occ row k = true := hnone.1 k (by omega) (by omega)
      have hempty : rowEmpty occ row k = false := by
        simp [rowEmpty, occNat, hklt] at hocc ⊢
        simpa [Bool.not_eq_true] using hocc
      exact absurd hemp (by simpa using hempty)
    | inr hrow =>
      obtain ⟨c, hc1, hc2, hemp', hbefore', hcval⟩ := hrow
      have hempk : occGet occ row ⟨k, hklt⟩ = false := by
        simpa [rowEmpty, hklt] using hemp
      have hk' : k = c.val := by
        cases Nat.lt_trichotomy k c.val with
        | inl hlt =>
          have hnat : occNat occ row k = true := hbefore' k (Nat.zero_le _) hlt
          simp [occNat, hklt, hempk] at hnat
        | inr hrest =>
          cases hrest with
          | inl heq => exact heq
          | inr hgt =>
            have hem : rowEmpty occ row c.val = false := hbefore c.val hgt
            simp [rowEmpty, c.isLt, hemp'] at hem
      cases hk'
      rw [scanRow, hkval, hcval]

theorem attempt_refines (occ : Occ) (t : Nat) (ht : t < 4) :
    (do
      let row := Int.ofNat t
      let found ← SudoRt.negI (1 : Int)
      let fl ← (SudoRt.runLoopOn (ρ := Int × Int × Int) ((0 : Int), found) fuel13
        (scanColStep (embedGrid (occMarks occ)) row 12)
        (fun σ => do
          let found := σ.2
          if decide (found ≥ (0 : Int)) then
            let t1 ← SudoRt.addI row 1
            let t' ← SudoRt.modI t1 4
            pure (SudoRt.Flow.ret (ρ := Int × Int × Int) (row, found, t'))
          else
            let t1 ← SudoRt.addI row 1
            let t' ← SudoRt.modI t1 4
            pure (SudoRt.Flow.cont (ρ := Int × Int × Int) t'))
        (fun r => pure (SudoRt.Flow.ret (ρ := Int × Int × Int) r)))
      pure fl) =
      match scanRow occ ⟨t, ht⟩ with
      | some c => .ok (SudoRt.Flow.ret (Int.ofNat t, Int.ofNat c.val, Int.ofNat ((t + 1) % 4)))
      | none => .ok (SudoRt.Flow.cont (Int.ofNat ((t + 1) % 4))) := by
  rw [negI_one]
  simp only [ok_bind]
  have hfuel : fuel13 = fuelRange (Int.ofNat 0) (Int.ofNat 12) := fuel13_eq
  -- `scan_loop` starts at literal `-1`, which `negI` just produced.
  have hscan := scan_loop occ ⟨t, ht⟩
    (fun σ => do
      let found := σ.2
      if decide (found ≥ (0 : Int)) then
        let t1 ← SudoRt.addI (Int.ofNat t) 1
        let t' ← SudoRt.modI t1 4
        pure (SudoRt.Flow.ret (ρ := Int × Int × Int) (Int.ofNat t, found, t'))
      else
        let t1 ← SudoRt.addI (Int.ofNat t) 1
        let t' ← SudoRt.modI t1 4
        pure (SudoRt.Flow.cont (ρ := Int × Int × Int) t'))
    (fun r => pure (SudoRt.Flow.ret (ρ := Int × Int × Int) r))
    (match scanRow occ ⟨t, ht⟩ with
      | some c => .ok (SudoRt.Flow.ret (Int.ofNat t, Int.ofNat c.val, Int.ofNat ((t + 1) % 4)))
      | none => .ok (SudoRt.Flow.cont (Int.ofNat ((t + 1) % 4))))
    (by
      rw [scanFound_encode]
      have hadd := addI_ofNat_one t (fits_succ_lt ht (by decide : 4 ≤ 52))
      rw [show (4 : Int) = Int.ofNat 4 from rfl]
      cases hscanR : scanRow occ ⟨t, ht⟩ with
      | some c =>
        simp only [hscanR]
        have hge : decide (Int.ofNat c.val ≥ (0 : Int)) = true := by
          simp [decide_eq_true_eq, Int.ofNat_nonneg]
        simp only [hge, ↓reduceIte, hadd, ok_bind]
        rw [modI_ofNat (t + 1) (by decide)]
        rfl
      | none =>
        simp only [hscanR]
        have hge : decide ((-1 : Int) ≥ (0 : Int)) = false := by decide
        simp only [hge, ↓reduceIte, hadd, ok_bind]
        rw [modI_ofNat (t + 1) (by decide)]
        rfl)
  simpa [except_bind_pure, hfuel] using hscan

def overflowStep (occ : Array (Array Int)) (toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Int × Int × Int)) :=
  let attempt := σ.1
  let t := σ.2
  do
    if attempt > toV then
      pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (attempt, t))
    else
      match ← ((do
        let row := t
        let found ← SudoRt.negI (1 : Int)
        let fuel : Nat := if (0 : Int) > 12 then 1 else ((12 : Int) - 0).natAbs + 1
        let fl ← (SudoRt.runLoopOn (ρ := Int × Int × Int) ((0 : Int), found) fuel
          (scanColStep occ row 12)
          (fun σ => do
            let found := σ.2
            if decide (found ≥ (0 : Int)) then
              let t1 ← SudoRt.addI t 1
              let t' ← SudoRt.modI t1 4
              pure (SudoRt.Flow.ret (ρ := Int × Int × Int) (row, found, t'))
            else
              let t1 ← SudoRt.addI t 1
              let t' ← SudoRt.modI t1 4
              pure (SudoRt.Flow.cont (ρ := Int × Int × Int) t'))
          (fun r => pure (SudoRt.Flow.ret (ρ := Int × Int × Int) r)))
        pure fl
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Int × Int × Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int × Int × Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (attempt, fs))
      | .cont fs =>
          if (attempt == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int × Int × Int) (attempt, fs))
          else do
            let attempt' ← SudoRt.addI attempt 1
            pure (SudoRt.Flow.cont (ρ := Int × Int × Int) (attempt', fs))

theorem overflow_as_loop (occ : Array (Array Int)) (t : Int) :
    Doubledeal.overflow_seat occ t =
      (do
        let _fromV := (0 : Int)
        let _toV := (3 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Int × Int × Int) (_fromV, t) fuel
          (overflowStep occ _toV)
          (fun σ => do
            let _as ← SudoRt.sudoAssert false 143
            pure ((0 : Int), (0 : Int), (0 : Int)))
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.overflow_seat
  rfl

theorem overflowStep_hit (occ : Occ) (attempt t : Nat) (ht : t < 4) (ha : attempt ≤ 3) :
    overflowStep (embedGrid (occMarks occ)) 3 (Int.ofNat attempt, Int.ofNat t) =
      match scanRow occ ⟨t, ht⟩ with
      | some c =>
        .ok (SudoRt.Flow.ret (Int.ofNat t, Int.ofNat c.val, Int.ofNat ((t + 1) % 4)))
      | none =>
        if attempt = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat attempt, Int.ofNat ((t + 1) % 4)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (attempt + 1), Int.ofNat ((t + 1) % 4))) := by
  unfold overflowStep
  rw [if_neg (show ¬ Int.ofNat attempt > (3 : Int) from ofNat_not_gt ha)]
  have hatt := attempt_refines occ t ht
  rw [show (if (0 : Int) > 12 then 1 else ((12 : Int) - 0).natAbs + 1) = fuel13 from rfl]
  rw [hatt]
  simp only [ok_bind]
  cases hrow : scanRow occ ⟨t, ht⟩ with
  | some c =>
    simp only [hrow, ok_bind, Pure.pure, Except.pure]
  | none =>
    simp only [hrow, Pure.pure, Except.pure]
    by_cases heq : attempt = 3
    · subst heq
      have hb : ((3 : Int) == (3 : Int)) = true := by decide
      simp [hb]
    · have hb : ((Int.ofNat attempt) == (3 : Int)) = false := by
        cases hbv : (Int.ofNat attempt) == (3 : Int) with
        | false => rfl
        | true =>
          exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
      simp only [hb, ↓reduceIte]
      rw [addI_ofNat_one attempt (fits_succ_lt (by omega : attempt < 3) (by decide : 3 ≤ 52))]
      simp [ok_bind, heq]

theorem overflow_fuel_some (occ : Occ) (fuel t : Nat) (ht : t < 4) (hf : fuel ≤ 4)
    (r : Fin 4) (c : Fin 13) (t' : Nat)
    (h : overflowN occ fuel t = some ((r, c), t')) :
    SudoRt.runLoopOn (Int.ofNat (4 - fuel), Int.ofNat t) fuel
      (overflowStep (embedGrid (occMarks occ)) 3)
      (fun _ => do
        let _as ← SudoRt.sudoAssert false 143
        pure ((0 : Int), (0 : Int), (0 : Int)))
      (fun x => pure x) =
      .ok (Int.ofNat r.val, Int.ofNat c.val, Int.ofNat t') := by
  induction fuel generalizing t r c t' with
  | zero => simp [overflowN] at h
  | succ fuel ih =>
    have hstart : 4 - (fuel + 1) ≤ 3 := by omega
    have hstep := overflowStep_hit occ (4 - (fuel + 1)) t ht hstart
    rw [runLoopOn_succ]
    rw [hstep]
    have htmod : t % 4 = t := Nat.mod_eq_of_lt ht
    simp only [overflowN, htmod] at h
    cases hscan : scanRow occ ⟨t, ht⟩ with
    | some c0 =>
      simp only [hscan, h, Pure.pure, Except.pure] at h ⊢
      injection h with hpair
      injection hpair with hpos ht'
      cases hpos
      cases ht'
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
      have hrec := ih ((t + 1) % 4) ht' hf' r c t' h
      simpa [hfuelEq] using hrec

theorem overflow_seat_refines (occ : Occ) (t : Nat) (ht : t < 4)
    (r : Fin 4) (c : Fin 13) (t' : Nat)
    (h : overflowSeat occ t = some ((r, c), t')) :
    Doubledeal.overflow_seat (embedGrid (occMarks occ)) (Int.ofNat t) =
      .ok (Int.ofNat r.val, Int.ofNat c.val, Int.ofNat t') := by
  rw [overflow_as_loop]
  dsimp only
  have hfuel : (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) = 4 := by
    decide
  rw [hfuel, except_bind_pure]
  have hgo := overflow_fuel_some occ 4 t ht (Nat.le_refl _) r c t' (by
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

theorem overflowN_t_lt (occ : Occ) :
    ∀ fuel t r c t', overflowN occ fuel t = some ((r, c), t') → t' < 4
  | 0, t, r, c, t', h => by simp [overflowN] at h
  | fuel + 1, t, r, c, t', h => by
    simp only [overflowN] at h
    split at h
    · next hs =>
      cases h
      exact Nat.mod_lt _ (by decide)
    · next hn =>
      exact overflowN_t_lt occ fuel _ r c t' h

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

/-- One placement of `mix_columns`. State is `(t, grid, prevCard, prevR, prevC)`. -/
def mixStep (d : Array Int) (toV : Int)
    (σ : Int × (Int × Array (Array Int) × Int × Int × Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Int × Array (Array Int) × Int × Int × Int)) (Array Int)) :=
  let i := σ.1
  let t := σ.2.1
  let grid := σ.2.2.1
  let prev_card := σ.2.2.2.1
  let prev_r := σ.2.2.2.2.1
  let prev_c := σ.2.2.2.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, (t, grid, prev_card, prev_r, prev_c)))
    else
      match ← ((do
        let card ← SudoRt.atL d i
        if decide (i > (0 : Int)) then
          do
            let stepped ← Doubledeal.step_seat prev_card prev_r prev_c
            let ⟨tr, tc⟩ := stepped
            let row0 ← SudoRt.atL grid tr
            let cell ← SudoRt.atL row0 tc
            if decide (cell < (0 : Int)) then
              do
                let row ← SudoRt.atL grid tr
                let row ← SudoRt.putL row tc card
                let grid ← SudoRt.putL grid tr row
                pure (SudoRt.Flow.cont (ρ := Array Int) (t, grid, card, tr, tc))
            else
              do
                let occ := (#[] : Array (Array Int))
                let _fromV := (0 : Int)
                let _toV := (3 : Int)
                let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
                let _out ← (SudoRt.runLoopOn (ρ := Array Int) (_fromV, occ) fuel
                  (markRowStep grid _toV)
                  (fun σ =>
                    let occ := σ.2
                    do
                      let stepped ← Doubledeal.overflow_seat occ t
                      let ⟨r, c, t⟩ := stepped
                      let row ← SudoRt.atL grid r
                      let row ← SudoRt.putL row c card
                      let grid ← SudoRt.putL grid r row
                      pure (SudoRt.Flow.cont (ρ := Array Int) (t, grid, card, r, c)))
                  (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)))
                pure _out
        else
          do
            let row ← SudoRt.atL grid (2 : Int)
            let row ← SudoRt.putL row (0 : Int) card
            let grid ← SudoRt.putL grid (2 : Int) row
            pure (SudoRt.Flow.cont (ρ := Array Int) (t, grid, card, (2 : Int), (0 : Int)))
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

theorem chooseSeat!_init : chooseSeat! initWalk = (asStart, 0) := by
  simp [chooseSeat!, chooseSeat?, initWalk]

theorem chooseSeat!_t_lt (st : WalkState) (ht : st.t < 4) (hct : occCount st.occ < 52) :
    (chooseSeat! st).2 < 4 := by
  cases hprev : st.prev with
  | none =>
    simp [chooseSeat!, chooseSeat?, hprev]
    exact ht
  | some pair =>
    by_cases hocc : occAt st.occ (gridStep pair.1 pair.2) = true
    · simp only [chooseSeat!, chooseSeat?, hprev, hocc, ↓reduceIte]
      obtain ⟨p, t', hs, _hf⟩ := overflow_some_of_count_lt st.occ st.t hct
      simp only [hs]
      exact overflowN_t_lt st.occ 4 st.t p.1 p.2 t' (by simpa [overflowSeat] using hs)
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
      some (hand ⟨n, hn⟩, (chooseSeat! (placeN hand n).2).1) := by
  simp [placeN_step hand n hn, advance]

theorem chooseSeat!_free_target (st : WalkState) (card : Nat) (pos : Fin 4 × Fin 13)
    (hprev : st.prev = some (card, pos))
    (hfree : occAt st.occ (gridStep card pos) = false) :
    chooseSeat! st = (gridStep card pos, st.t) := by
  simp [chooseSeat!, chooseSeat?, hprev, hfree]

theorem chooseSeat!_overflow (st : WalkState) (card : Nat) (pos p : Fin 4 × Fin 13) (t' : Nat)
    (hprev : st.prev = some (card, pos))
    (hocc : occAt st.occ (gridStep card pos) = true)
    (hov : overflowSeat st.occ st.t = some (p, t')) :
    chooseSeat! st = (p, t') := by
  simp [chooseSeat!, chooseSeat?, hprev, hocc, hov]

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

def mixPrev (st : WalkState) : Nat × Nat × Nat :=
  match st.prev with
  | none => (0, 0, 0)
  | some (card, pos) => (card, pos.1.val, pos.2.val)

def mixPayload (hand : Fin 52 → Nat) (n : Nat) :
    Int × Array (Array Int) × Int × Int × Int :=
  let (g, st) := placeN hand n
  let p := mixPrev st
  (Int.ofNat st.t, seatArr g st.occ, Int.ofNat p.1, Int.ofNat p.2.1, Int.ofNat p.2.2)

theorem index_cont (n : Nat) (hn : n ≤ 51)
    (st : Int × Array (Array Int) × Int × Int × Int) :
    (if ((Int.ofNat n) == (51 : Int)) = true then
        pure (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat n, st))
      else do
        let n' ← SudoRt.addI (Int.ofNat n) 1
        pure (SudoRt.Flow.cont (ρ := Array Int) (n', st))) =
    if n = 51 then .ok (SudoRt.Flow.brk (Int.ofNat n, st))
    else .ok (SudoRt.Flow.cont (Int.ofNat (n + 1), st)) := by
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
    (pos : Fin 4 × Fin 13) (t' : Nat)
    (hseat : chooseSeat! (placeN hand n).2 = (pos, t')) :
    mixPayload hand (n + 1) =
      (Int.ofNat t',
        seatArr (setGrid (placeN hand n).1 pos (hand ⟨n, hn⟩))
          (setOcc (placeN hand n).2.occ pos),
        Int.ofNat (hand ⟨n, hn⟩), Int.ofNat pos.1.val, Int.ofNat pos.2.val) := by
  have hs := placeN_step hand n hn
  simp [mixPayload, hs.1, hs.2, hseat, advance, mixPrev]

theorem place_cont (g : NatGrid) (occ : Occ) (r : Fin 4) (c : Fin 13) (card t : Nat)
    (hfree : occGet occ r c = false) (hsz : occ.size = 52) :
    (do
      let row ← SudoRt.atL (seatArr g occ) (Int.ofNat r.val)
      let row ← SudoRt.putL row (Int.ofNat c.val) (Int.ofNat card)
      let grid ← SudoRt.putL (seatArr g occ) (Int.ofNat r.val) row
      pure (SudoRt.Flow.cont (ρ := Array Int)
        (Int.ofNat t, grid, Int.ofNat card, Int.ofNat r.val, Int.ofNat c.val))) =
    .ok (SudoRt.Flow.cont
      (Int.ofNat t, seatArr (setGrid g (r, c) card) (setOcc occ (r, c)),
        Int.ofNat card, Int.ofNat r.val, Int.ofNat c.val)) := by
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
  have h := place_cont g occ r c card 0 hfree hsz
  have hat := atL_ofNat (seatArr g occ) r.val (by rw [seatArr_size]; exact r.isLt)
  rw [seatArr_get g occ r] at hat
  have hputR := putL_ofNat (Array.mk (seatRow g occ r)) c.val (Int.ofNat card) hrowSz
  have hputG := putL_ofNat (seatArr g occ) r.val
      ((Array.mk (seatRow g occ r)).set ⟨c.val, hrowSz⟩ (Int.ofNat card))
      (by rw [seatArr_size]; exact r.isLt)
  simp only [hat, hputR, hputG, ok_bind, Pure.pure, Except.pure] at h
  injection h with hflow
  injection hflow with htup
  injection htup with _ hrest
  injection hrest with harr

set_option maxHeartbeats 800000 in
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
        (mixPayload hand 0).2.1 = seatArr (fun _ _ => (0 : Nat)) emptyOcc := by
      simp [mixPayload, placeN, initWalk]
    have ht0 : (mixPayload hand 0).1 = Int.ofNat 0 := by
      simp [mixPayload, placeN, initWalk]
    have hpc0 : (mixPayload hand 0).2.2 = (Int.ofNat 0, Int.ofNat 0, Int.ofNat 0) := by
      simp [mixPayload, placeN, initWalk, mixPrev]
    simp only [hgrid, ht0, hpc0]
    have hpl := place_cont (fun _ _ => (0 : Nat)) emptyOcc
      ⟨2, by decide⟩ ⟨0, by decide⟩ (hand ⟨0, by decide⟩) 0
      (occGet_empty _ _) size_emptyOcc
    rw [show (2 : Int) = Int.ofNat 2 from rfl, show (0 : Int) = Int.ofNat 0 from rfl]
    rw [hpl]
    simp only [ok_bind]
    have hseat : chooseSeat! (placeN hand 0).2 = (asStart, 0) := by
      simpa [placeN, initWalk] using chooseSeat!_init
    have hnext := mixPayload_at hand 0 (by decide) asStart 0 hseat
    simp only [hnext, asStart]
    exact index_cont 0 (by decide) _
  · have ipos : 0 < n := by omega
    have hgt : decide (Int.ofNat n > (0 : Int)) = true :=
      decide_eq_true (by
        simpa [ofNat_eq_natCast] using (Int.ofNat_lt.mpr ipos))
    simp only [hgt, ↓reduceIte]
    have hprev : (placeN hand n).2.prev =
        some (hand ⟨n - 1, by omega⟩, (chooseSeat! (placeN hand (n - 1)).2).1) := by
      have h := placeN_prev_succ hand (n - 1) (by omega)
      simpa [show (n - 1) + 1 = n by omega] using h
    let card0 : Nat := hand ⟨n - 1, by omega⟩
    let pos : Fin 4 × Fin 13 := (chooseSeat! (placeN hand (n - 1)).2).1
    have hpay :
        mixPayload hand n =
          (Int.ofNat (placeN hand n).2.t,
            seatArr (placeN hand n).1 (placeN hand n).2.occ,
            Int.ofNat card0, Int.ofNat pos.1.val, Int.ofNat pos.2.val) := by
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
      have hch : chooseSeat! (placeN hand n).2 = (target, (placeN hand n).2.t) := by
        simpa [card0, pos, target] using
          chooseSeat!_free_target (placeN hand n).2 card0 pos hprev hfree
      have hnext := mixPayload_at hand n hlen target (placeN hand n).2.t hch
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
      obtain ⟨p, t', hov, hfr⟩ := overflow_some_of_count_lt (placeN hand n).2.occ
        (placeN hand n).2.t hct
      have hloop : SudoRt.runLoopOn ((0 : Int), (#[] : Array (Array Int))) fuel4
          (markRowStep (seatArr (placeN hand n).1 (placeN hand n).2.occ) 3)
          (fun σ => do
            let stepped ← Doubledeal.overflow_seat σ.2 (Int.ofNat (placeN hand n).2.t)
            let row ← SudoRt.atL (seatArr (placeN hand n).1 (placeN hand n).2.occ) stepped.1
            let row ← SudoRt.putL row stepped.2.1 (Int.ofNat (hand ⟨n, hlen⟩))
            let grid ← SudoRt.putL (seatArr (placeN hand n).1 (placeN hand n).2.occ) stepped.1 row
            pure (SudoRt.Flow.cont (ρ := Array Int)
              (stepped.2.2, grid, Int.ofNat (hand ⟨n, hlen⟩), stepped.1, stepped.2.1)))
          (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)) =
          .ok (SudoRt.Flow.cont
            (Int.ofNat t',
              seatArr (setGrid (placeN hand n).1 p (hand ⟨n, hlen⟩))
                (setOcc (placeN hand n).2.occ p),
              Int.ofNat (hand ⟨n, hlen⟩), Int.ofNat p.1.val, Int.ofNat p.2.val)) := by
        refine occ_rows_loop (placeN hand n).1 (placeN hand n).2.occ _ _ _ ?_
        have hseat := overflow_seat_refines (placeN hand n).2.occ (placeN hand n).2.t htlt
          p.1 p.2 t' hov
        simp only [hseat, ok_bind]
        have hget : occGet (placeN hand n).2.occ p.1 p.2 = false := hfr
        have hpl := place_cont (placeN hand n).1 (placeN hand n).2.occ p.1 p.2
          (hand ⟨n, hlen⟩) t' hget (placeN_occ_size hand n)
        rw [hpl]
      rw [show (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) = fuel4 from rfl]
      rw [hloop]
      simp only [ok_bind, Pure.pure, Except.pure]
      have hch : chooseSeat! (placeN hand n).2 = (p, t') := by
        have hoccAt : occAt (placeN hand n).2.occ target = true := hocc
        simpa [card0, pos, target] using
          chooseSeat!_overflow (placeN hand n).2 card0 pos p t' hprev hoccAt hov
      have hnext := mixPayload_at hand n hlen p t' hch
      simp only [hnext]
      exact index_cont n hn _

theorem mix_columns_as_loop (d : Array Int) :
    Doubledeal.mix_columns d =
      (do
        let grid ← Doubledeal.empty_rows
        let t := (0 : Int)
        let prev_card := (0 : Int)
        let prev_r := (0 : Int)
        let prev_c := (0 : Int)
        let _fromV := (0 : Int)
        let _toV := (51 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array Int)
          (_fromV, (t, grid, prev_card, prev_r, prev_c)) fuel
          (mixStep d _toV)
          (fun σ =>
            let grid := σ.2.2.1
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
      ((0 : Int), blankRows 4, (0 : Int), (0 : Int), (0 : Int)) = mixPayload hand 0 := by
    simp [mixPayload, placeN, initWalk, mixPrev]
    exact blank_seat (fun _ _ => (0 : Nat))
  have hfuel :
      (if (0 : Int) > (51 : Int) then 1 else ((51 : Int) - 0).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat 51) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  dsimp only
  rw [show ((0 : Int), (0 : Int), blankRows 4, (0 : Int), (0 : Int), (0 : Int)) =
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
      let grid := σ.2.2.1
      do
        let scooped ← Doubledeal.scoop_rm grid
        pure scooped)
    (fun r => pure r)
    (mixPayload hand) 0 51 (Nat.zero_le _) hstep
    (.ok (embed (toDeck (mixColumns hand)))) (by
      have hall := occ_full_of_count (placeN hand 52).2.occ (placeN_count hand 52 (Nat.le_refl _))
      have hseat := seatArr_full (placeN hand 52).1 (placeN hand 52).2.occ hall
      have hgrid : (mixPayload hand 52).2.1 = embedGrid (placeN hand 52).1 := by
        simp [mixPayload, hseat]
      dsimp only
      rw [hgrid, scoop_rm_refines, mixColumns, placedGrid, except_bind_pure])
  exact hrun

end DoubleDeal.Link2
