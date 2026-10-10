/-
  `settle` slides a finished bench home: every hole from `n` up is empty, the prefix
  is written, moves and slides grow by twice the nonzero count, then `note_peak`.
  `value` of that home is the prefix. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem idx_goal {ρ β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i) =
        if i = toN then .ok (.brk (Int.ofNat i))
        else .ok (.cont (Int.ofNat (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hpost : after (Int.ofNat toN) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) (Nat.le_refl _), if_pos rfl]
    exact hpost
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    have hle' : fromN + 1 ≤ toN := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hle hne)
    rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, if_neg hne]
    dsimp
    exact ih (fromN + 1) hle'
      (fun i h1 h2 => hstep i (Nat.le_trans (Nat.le_succ fromN) h1) h2)
      (by omega)

/-- The tail check in `Ecbs.settle`: hole `i` of the bench is `0`. -/
def benchZeroStep (bench : Array Int) (toV : Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board) :=
  if i > toV then
    pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
  else do
    let lift ← (do
      let c ← SudoRt.atL bench i
      let _ ← SudoRt.sudoAssertEq c (0 : Int) 414
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ()))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
    | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
    | .cont _ =>
      if (i == toV) = true then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
      else do
        let i' ← SudoRt.addI i 1
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) i')

private theorem benchZero_at (xs : List Nat) (toN i : Nat)
    (hi : i < xs.length) (hz : xs[i] = 0) (hle : i ≤ toN) (hfit : FitsLen (i + 1)) :
    benchZeroStep (embed xs) (Int.ofNat toN) (Int.ofNat i) =
      if i = toN then .ok (.brk (Int.ofNat i))
      else .ok (.cont (Int.ofNat (i + 1))) := by
  unfold benchZeroStep
  dsimp only
  have hng : ¬ Int.ofNat i > Int.ofNat toN := by
    rw [GT.gt, ofNat_lt_iff]
    exact Nat.not_lt.mpr hle
  rw [if_neg hng, atL_embed xs i hi, ok_bind]
  rw [hz, show Int.ofNat 0 = (0 : Int) from rfl, sudoAssertEq_int rfl 414, ok_bind, pure_eq_ok]
  exact asc_tail_idx (ρ := Ecbs.Board) toN i hfit

private theorem benchZero_loop {β} (xs : List Nat) (n : Nat)
    (k : Except SudoRt.Trap β) (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : n < xs.length) (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hfit : FitsLen xs.length) :
    SudoRt.runLoopOn (Int.ofNat n)
      (fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)))
      (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
      (fun _ => k) onRet = k := by
  have hle : n ≤ xs.length - 1 := by omega
  refine idx_goal (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
    (fun _ => k) onRet n (xs.length - 1) hle ?_ k rfl
  intro i hlo hi
  have hix : i < xs.length := by omega
  exact benchZero_at xs (xs.length - 1) i hix (hzero i hlo hix) hi
    (FitsLen.of_le hfit (by omega))

private theorem benchZero_skip {β} (xs : List Nat) (n : Nat)
    (k : Except SudoRt.Trap β) (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : n = xs.length) (hpos : 0 < xs.length) :
    SudoRt.runLoopOn (Int.ofNat n)
      (fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)))
      (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
      (fun _ => k) onRet = k := by
  have hgt : Int.ofNat n > Int.ofNat (xs.length - 1) := by
    rw [hn]
    exact (ofNat_lt_iff (xs.length - 1) xs.length).mpr (Nat.sub_lt hpos (by decide))
  rw [fuelRange_gt hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  have hstep : benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)) (Int.ofNat n) =
      .ok (.brk (Int.ofNat n)) := by
    unfold benchZeroStep
    dsimp only
    rw [if_pos hgt, pure_eq_ok]
  rw [hstep]

private theorem atL_cast {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := by
  rw [← ofNat_eq_natCast i]
  exact atL_ofNat a i h

private theorem putL_cast {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (i : Int) v = .ok (a.set ⟨i, h⟩ v) := by
  rw [← ofNat_eq_natCast i]
  exact putL_ofNat a i v h

private theorem peg_embed (xs : List Nat) :
    nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  unfold pegCount
  rfl

private theorem decide_gt_ofNat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

private theorem addI_nat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a + b)) :=
  addI_ofNat a b h

/-- The board after a bench that is on, aimed at `home`, is slid home.
    `xs` is the bench. Holes `n ..` are empty, so the tail assert passes.
    Peak becomes the held-count of homes `0 .. 6` when that count is strictly larger. -/
def settleBoard (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) : Ecbs.Board :=
  let pegs := pegCount (xs.take n)
  if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 then
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
      sudo_5Board_8bench_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
        sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs)
        sudo_5Costs_4peak := Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } }
  else
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
      sudo_5Board_8bench_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
        sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs) } }

theorem settle_off (b : Ecbs.Board) (hoff : b.sudo_5Board_8bench_on = false) :
    Ecbs.settle b = .ok b := by
  unfold Ecbs.settle
  simp [hoff, Bool.not_false, pure_eq_ok]

theorem settle_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (n moves slides peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n))) :
    Ecbs.settle b = .ok (settleBoard b home hH hD xs n moves slides peak) := by
  unfold Ecbs.settle
  dsimp only
  simp only [hon, Bool.not_true, Bool.false_eq_true, if_false]
  rw [hbench, listLen_embed, subI_ofNat_one xs.length hpos hfitL, ok_bind, hn]
  rw [show (n : Int) = Int.ofNat n by rw [ofNat_eq_natCast]]
  by_cases hlt : n < xs.length
  · have hfuel :
        (if Int.ofNat n > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat n).natAbs + 1) =
        fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel]
    conv =>
      lhs
      arg 1
      arg 3
      change benchZeroStep (embed xs) (Int.ofNat (xs.length - 1))
    rw [benchZero_loop xs n _ (fun r => pure r) hlt hzero hfitL]
    rw [except_bind_pure]
    unfold Ecbs.need_empty
    rw [hto, atL_cast _ home hD, hempty]
    simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
    rw [prefix_refines xs n hnle hf, ok_bind]
    have hfs : FitsLen (embed (xs.take n)).size := by
      rw [size_embed, List.length_take, Nat.min_eq_left hnle]
      exact hf
    rw [npeg_refines (embed (xs.take n)) hfs, peg_embed, ok_bind]
    rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 _ hpeg, ok_bind]
    rw [hmoves, addI_nat moves _ hfitM, ok_bind, hslides, addI_nat slides _ hfitS, ok_bind]
    rw [putL_cast _ home _ hH, ok_bind, putL_cast _ home true hD, ok_bind]
    unfold Ecbs.note_peak settleBoard
    have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨home, hD⟩ true).size := by
      rw [Array.size_set]; exact h7
    have hocc := occupied_refines
      ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_8bench_to := (home : Int)
          sudo_5Board_5bench := embed xs
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } }) h7'
    rw [hocc, ok_bind, hpeak]
    simp only [GT.gt, ofNat_lt_iff]
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = true := by
        rw [decide_eq_true_eq]; exact hpk
      rw [hc, if_pos rfl, pure_eq_ok, ← hto, ← hbench]
      simp [hpk]
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = false := by
        rw [decide_eq_false_iff_not]; exact hpk
      rw [hc]
      simp only [Bool.false_eq_true, if_false]
      rw [pure_eq_ok, ← hto, ← hbench, ← hpeak]
      simp [hpk]
  · have heq : n = xs.length := Nat.le_antisymm hnle (Nat.le_of_not_lt hlt)
    have hfuel :
        (if Int.ofNat n > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat n).natAbs + 1) =
        fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel]
    conv =>
      lhs
      arg 1
      arg 3
      change benchZeroStep (embed xs) (Int.ofNat (xs.length - 1))
    rw [benchZero_skip xs n _ (fun r => pure r) heq hpos]
    rw [except_bind_pure]
    unfold Ecbs.need_empty
    rw [hto, atL_cast _ home hD, hempty]
    simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
    rw [prefix_refines xs n hnle hf, ok_bind]
    have hfs : FitsLen (embed (xs.take n)).size := by
      rw [size_embed, List.length_take, Nat.min_eq_left hnle]
      exact hf
    rw [npeg_refines (embed (xs.take n)) hfs, peg_embed, ok_bind]
    rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 _ hpeg, ok_bind]
    rw [hmoves, addI_nat moves _ hfitM, ok_bind, hslides, addI_nat slides _ hfitS, ok_bind]
    rw [putL_cast _ home _ hH, ok_bind, putL_cast _ home true hD, ok_bind]
    unfold Ecbs.note_peak settleBoard
    have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨home, hD⟩ true).size := by
      rw [Array.size_set]; exact h7
    have hocc := occupied_refines
      ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_8bench_to := (home : Int)
          sudo_5Board_5bench := embed xs
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } }) h7'
    rw [hocc, ok_bind, hpeak]
    simp only [GT.gt, ofNat_lt_iff]
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = true := by
        rw [decide_eq_true_eq]; exact hpk
      rw [hc, if_pos rfl, pure_eq_ok, ← hto, ← hbench]
      simp [hpk]
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = false := by
        rw [decide_eq_false_iff_not]; exact hpk
      rw [hc]
      simp only [Bool.false_eq_true, if_false]
      rw [pure_eq_ok, ← hto, ← hbench, ← hpeak]
      simp [hpk]

theorem cost_ext (a b : Ecbs.Costs)
    (hmoves : a.sudo_5Costs_5moves = b.sudo_5Costs_5moves)
    (hslides : a.sudo_5Costs_6slides = b.sudo_5Costs_6slides)
    (hctrl : a.sudo_5Costs_4ctrl = b.sudo_5Costs_4ctrl)
    (hcalls : a.sudo_5Costs_5calls = b.sudo_5Costs_5calls)
    (hstale : a.sudo_5Costs_13stale_cleared = b.sudo_5Costs_13stale_cleared)
    (hkey : a.sudo_5Costs_14key_grid_moves = b.sudo_5Costs_14key_grid_moves)
    (hlad : a.sudo_5Costs_12ladder_moves = b.sudo_5Costs_12ladder_moves)
    (hpeak : a.sudo_5Costs_4peak = b.sudo_5Costs_4peak)
    (hstrict : a.sudo_5Costs_11peak_strict = b.sudo_5Costs_11peak_strict)
    (hhole : a.sudo_5Costs_14max_bench_hole = b.sudo_5Costs_14max_bench_hole)
    (hhigh : a.sudo_5Costs_15control_highest = b.sudo_5Costs_15control_highest)
    (hmark : a.sudo_5Costs_17script_marker_max = b.sudo_5Costs_17script_marker_max)
    (htally : a.sudo_5Costs_9tally_max = b.sudo_5Costs_9tally_max)
    (hmbp : a.sudo_5Costs_14moves_by_phase = b.sudo_5Costs_14moves_by_phase)
    (hpbp : a.sudo_5Costs_13peak_by_phase = b.sudo_5Costs_13peak_by_phase)
    (hops : a.sudo_5Costs_3ops = b.sudo_5Costs_3ops) :
    a = b := by
  cases a
  cases b
  subst hmoves hslides hctrl hcalls hstale hkey hlad hpeak hstrict hhole hhigh hmark
    htally hmbp hpbp hops
  rfl

theorem board_ext (a b : Ecbs.Board)
    (ht : a.sudo_5Board_1t = b.sudo_5Board_1t)
    (hhome : a.sudo_5Board_4home = b.sudo_5Board_4home)
    (hheld : a.sudo_5Board_4held = b.sudo_5Board_4held)
    (hon : a.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on)
    (hto : a.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to)
    (hbench : a.sudo_5Board_5bench = b.sudo_5Board_5bench)
    (hcost : a.sudo_5Board_4cost = b.sudo_5Board_4cost)
    (hphase : a.sudo_5Board_5phase = b.sudo_5Board_5phase)
    (hm0 : a.sudo_5Board_8phase_m0 = b.sudo_5Board_8phase_m0)
    (hpk : a.sudo_5Board_8phase_pk = b.sudo_5Board_8phase_pk)
    (hrow : a.sudo_5Board_3row = b.sudo_5Board_3row)
    (hph : a.sudo_5Board_10phase_hole = b.sudo_5Board_10phase_hole)
    (hcall : a.sudo_5Board_12calling_hole = b.sudo_5Board_12calling_hole)
    (hl0 : a.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0)
    (hnr : a.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs)
    (hpark : a.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole)
    (ht0 : a.sudo_5Board_6tally0 = b.sudo_5Board_6tally0)
    (hmarker : a.sudo_5Board_6marker = b.sudo_5Board_6marker)
    (hfrom : a.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from)
    (hlen : a.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len)
    (hmon : a.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on)
    (hridx : a.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx)
    (hlad : a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (hlog : a.sudo_5Board_3log = b.sudo_5Board_3log) :
    a = b := by
  cases a
  cases b
  subst ht hhome hheld hon hto hbench hcost hphase hm0 hpk hrow hph hcall hl0 hnr hpark
    ht0 hmarker hfrom hlen hmon hridx hlad hlog
  rfl

private theorem set_fin {α : Type} (a : Array α) (i : Nat) (h₁ h₂ : i < a.size) (v : α) :
    a.set ⟨i, h₁⟩ v = a.set ⟨i, h₂⟩ v := by
  have hfin : (⟨i, h₁⟩ : Fin a.size) = ⟨i, h₂⟩ := Fin.ext rfl
  rw [hfin]

private theorem set_on_eq {α : Type} {a b : Array α} (hab : a = b) (i : Nat)
    (ha : i < a.size) (v : α) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, hab ▸ ha⟩ v := by
  subst hab
  rfl

/-- The operation-count bump writes one cell of the ops array and leaves every other field. -/
def bumpOp (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) : Ecbs.Board :=
  { b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_3ops :=
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨i, hops⟩ (Int.ofNat (cOps + 1)) } }

theorem bumpOp_ops (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨i, hops⟩ (Int.ofNat (cOps + 1)) := rfl

theorem bumpOp_moves (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

theorem bumpOp_peak (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

theorem bumpOp_held (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4held = b.sudo_5Board_4held := rfl

theorem bumpOp_home (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4home = b.sudo_5Board_4home := rfl

theorem bumpOp_bench (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      (bumpOp b i cOps hops).sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      (bumpOp b i cOps hops).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := by
  exact ⟨rfl, rfl, rfl⟩

/-- `settleBoard` when the held-count after the slide is strictly above the incoming peak.
    The new peak is that count. Ops are not written. -/
theorem settle_peak (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    settleBoard b home hH hD xs n moves slides peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
          sudo_5Costs_4peak :=
            Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } } := by
  unfold settleBoard
  rw [if_pos hpk]

/-- `settleBoard` when the incoming peak is already at least the held-count. Peak stays.
    Ops are not written. -/
theorem settle_keep (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (hnk : ¬ peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    settleBoard b home hH hD xs n moves slides peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } } := by
  unfold settleBoard
  rw [if_neg hnk]

theorem settle_ops (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem bump_home_lt (b : Ecbs.Board) (i cOps home : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hH : home < b.sudo_5Board_4home.size) :
    home < (bumpOp b i cOps hops).sudo_5Board_4home.size := by
  simpa [bumpOp] using hH

theorem bump_held_lt (b : Ecbs.Board) (i cOps home : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hD : home < b.sudo_5Board_4held.size) :
    home < (bumpOp b i cOps hops).sudo_5Board_4held.size := by
  simpa [bumpOp] using hD

theorem settle_ops_lt (b : Ecbs.Board) (i home : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    i < (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [settle_ops]; exact hops

/-- `settle` after an ops bump is the ops bump after `settle`. The peak test depends on
    the held array and the incoming peak, neither of which the bump writes. -/
theorem settle_bump_comm (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (home : Nat) (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard (bumpOp b i cOps hops) home
        (bump_home_lt b i cOps home hops hH) (bump_held_lt b i cOps home hops hD)
        xs n moves slides peak =
      bumpOp (settleBoard b home hH hD xs n moves slides peak) i cOps
        (settle_ops_lt b i home hops hH hD xs n moves slides peak) := by
  let bB := bumpOp b i cOps hops
  let hHB := bump_home_lt b i cOps home hops hH
  let hDB := bump_held_lt b i cOps home hops hD
  have hcount :
      countHeld (bB.sudo_5Board_4held.set ⟨home, hDB⟩ true) 7 =
        countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
    rfl
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkB : peak < countHeld (bB.sudo_5Board_4held.set ⟨home, hDB⟩ true) 7 := by
      rw [hcount]; exact hpk
    apply Eq.trans (settle_peak bB home hHB hDB xs n moves slides peak hpkB)
    apply board_ext
    case pos.hcost =>
      simp only [bumpOp, bB, settle_peak b home hH hD xs n moves slides peak hpk]
      apply cost_ext <;> first
        | rfl
        | exact congrArg Int.ofNat hcount
        | (let v := Int.ofNat (cOps + 1)
           let hs := settle_ops b home hH hD xs n moves slides peak
           let hlt := settle_ops_lt b i home hops hH hD xs n moves slides peak
           exact ((set_fin b.sudo_5Board_4cost.sudo_5Costs_3ops i hops (hs ▸ hlt) v).trans
             (set_on_eq hs i hlt v).symm).trans (set_fin _ i hlt _ v))
    all_goals simp only [bumpOp, bB, settle_peak b home hH hD xs n moves slides peak hpk]
  · have hnkB : ¬ peak < countHeld (bB.sudo_5Board_4held.set ⟨home, hDB⟩ true) 7 := by
      rw [hcount]; exact hpk
    apply Eq.trans (settle_keep bB home hHB hDB xs n moves slides peak hnkB)
    apply board_ext
    case neg.hcost =>
      simp only [bumpOp, bB, settle_keep b home hH hD xs n moves slides peak hpk]
      apply cost_ext <;> first
        | rfl
        | (let v := Int.ofNat (cOps + 1)
           let hs := settle_ops b home hH hD xs n moves slides peak
           let hlt := settle_ops_lt b i home hops hH hD xs n moves slides peak
           exact ((set_fin b.sudo_5Board_4cost.sudo_5Costs_3ops i hops (hs ▸ hlt) v).trans
             (set_on_eq hs i hlt v).symm).trans (set_fin _ i hlt _ v))
    all_goals simp only [bumpOp, bB, settle_keep b home hH hD xs n moves slides peak hpk]

/-- `settleBoard` turns the bench off. The ops array is not written. -/
theorem settle_bench_off (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8bench_on = false := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_held_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hD⟩ true := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_home_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n)) := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_tier_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_moves_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + 2 * pegCount (xs.take n)) := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_slides_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (xs.take n)) := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_tally_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_ctrl_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_high_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_marker_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_strict_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_hole_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

/-- The peak `settleBoard` leaves: the held-count after the slide, when that exceeds
    the incoming peak, and the incoming peak otherwise. -/
theorem settle_peak_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        then countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        else peak) := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk, if_pos hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk, hpeak, if_neg hpk]

theorem settle_held_lt (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    home < (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4held.size := by
  rw [settle_held_eq b home hH hD xs n moves slides peak, Array.size_set]
  exact hD

theorem settle_home_lt (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    home < (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4home.size := by
  rw [settle_home_eq b home hH hD xs n moves slides peak, Array.size_set]
  exact hH

/-- Replace the fields `tally_double` writes. A live `Ecbs.cube` and a live nocopy
    `Ecbs.mul` do not read them; they copy them onto the result. -/
def withTally (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) : Ecbs.Board :=
  { b with
    sudo_5Board_3row := row
    sudo_5Board_9tally_len := len
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := ctrl
      sudo_5Costs_15control_highest := high
      sudo_5Costs_9tally_max := tmax } }

theorem withTally_home (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4home = b.sudo_5Board_4home := rfl

theorem withTally_held (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4held = b.sudo_5Board_4held := rfl

theorem withTally_ops (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem withTally_marker (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := rfl

theorem withTally_on (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := rfl

theorem withTally_to (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := rfl

theorem withTally_bench (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_5bench = b.sudo_5Board_5bench := rfl

theorem withTally_tier (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_1t = b.sudo_5Board_1t := rfl

theorem withTally_moves (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

theorem withTally_slides (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := rfl

theorem withTally_peak (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

theorem withTally_hole (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl

theorem withTally_strict (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

theorem withTally_row (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_3row = row := rfl

theorem withTally_len (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_9tally_len = len := rfl

theorem withTally_ctrl (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_4ctrl = ctrl := rfl

theorem withTally_high (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_15control_highest = high := rfl

theorem withTally_max (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_9tally_max = tmax := rfl

/-- `settleBoard` does not read the tally fields, and it copies them onto the result. -/
theorem settleBoard_withTally (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int)
    (home : Nat) (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard (withTally b row len ctrl high tmax) home
        (withTally_home b row len ctrl high tmax ▸ hH)
        (withTally_held b row len ctrl high tmax ▸ hD) xs n moves slides peak =
      withTally (settleBoard b home hH hD xs n moves slides peak) row len ctrl high tmax := by
  let bT := withTally b row len ctrl high tmax
  let hHT : home < bT.sudo_5Board_4home.size := withTally_home b row len ctrl high tmax ▸ hH
  let hDT : home < bT.sudo_5Board_4held.size := withTally_held b row len ctrl high tmax ▸ hD
  have hcount :
      countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 =
        countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
    simp [bT, withTally]
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkT : peak < countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 := by
      simpa [hcount] using hpk
    rw [settle_peak bT home hHT hDT xs n moves slides peak hpkT,
      settle_peak b home hH hD xs n moves slides peak hpk]
    simp [bT, withTally]
  · have hpkT : ¬ peak < countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 := by
      simpa [hcount] using hpk
    rw [settle_keep bT home hHT hDT xs n moves slides peak hpkT,
      settle_keep b home hH hD xs n moves slides peak hpk]
    simp [bT, withTally]

/-- Replace the row, the control counter, the parked-from hole, and the rung index.
    `clear`, a live cube, and a live nocopy mul do not read them; they copy them. -/
def withPark (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) : Ecbs.Board :=
  { b with
    sudo_5Board_3row := row
    sudo_5Board_11parked_from := fromHole
    sudo_5Board_8rung_idx := ridx
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := ctrl } }

theorem withPark_home (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4home = b.sudo_5Board_4home := rfl

theorem withPark_held (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4held = b.sudo_5Board_4held := rfl

theorem withPark_ops (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem withPark_marker (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := rfl

theorem withPark_on (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := rfl

theorem withPark_to (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := rfl

theorem withPark_bench (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_5bench = b.sudo_5Board_5bench := rfl

theorem withPark_tier (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_1t = b.sudo_5Board_1t := rfl

theorem withPark_moves (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

theorem withPark_slides (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := rfl

theorem withPark_peak (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

theorem withPark_hole (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl

theorem withPark_strict (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

theorem withPark_tally0 (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := rfl

theorem withPark_len (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := rfl

theorem withPark_row (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_3row = row := rfl

theorem withPark_ctrl (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_4cost.sudo_5Costs_4ctrl = ctrl := rfl

theorem withPark_from (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_11parked_from = fromHole := rfl

theorem withPark_ridx (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int) :
    (withPark b row ctrl fromHole ridx).sudo_5Board_8rung_idx = ridx := rfl

theorem placeBoard_irrel (b : Ecbs.Board) (home : Nat)
    (hH hH' : home < b.sudo_5Board_4home.size) (hD hD' : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard b home hH hD xs moves peak = placeBoard b home hH' hD' xs moves peak := by
  unfold placeBoard
  have hFinH : (⟨home, hH⟩ : Fin _) = ⟨home, hH'⟩ := Fin.ext rfl
  have hFinD : (⟨home, hD⟩ : Fin _) = ⟨home, hD'⟩ := Fin.ext rfl
  simp [hFinH, hFinD]

theorem settleBoard_irrel (b : Ecbs.Board) (home : Nat)
    (hH hH' : home < b.sudo_5Board_4home.size) (hD hD' : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard b home hH hD xs n moves slides peak =
      settleBoard b home hH' hD' xs n moves slides peak := by
  unfold settleBoard
  have hFinH : (⟨home, hH⟩ : Fin _) = ⟨home, hH'⟩ := Fin.ext rfl
  have hFinD : (⟨home, hD⟩ : Fin _) = ⟨home, hD'⟩ := Fin.ext rfl
  simp [hFinH, hFinD]

/-- `place` does not read the park fields, and it copies them onto the result. -/
theorem placeBoard_withPark (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int)
    (home : Nat) (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard (withPark b row ctrl fromHole ridx) home
        (withPark_home b row ctrl fromHole ridx ▸ hH)
        (withPark_held b row ctrl fromHole ridx ▸ hD) xs moves peak =
      withPark (placeBoard b home hH hD xs moves peak) row ctrl fromHole ridx := by
  unfold placeBoard
  let bW := withPark b row ctrl fromHole ridx
  let hHW := withPark_home b row ctrl fromHole ridx ▸ hH
  let hDW := withPark_held b row ctrl fromHole ridx ▸ hD
  have hcount :
      countHeld (bW.sudo_5Board_4held.set ⟨home, hDW⟩ true) 7 =
        countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
    simp [bW, withPark]
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkW : peak < countHeld (bW.sudo_5Board_4held.set ⟨home, hDW⟩ true) 7 := by
      simpa [hcount] using hpk
    simp [hpk, hpkW, bW, withPark]
  · have hpkW : ¬ peak < countHeld (bW.sudo_5Board_4held.set ⟨home, hDW⟩ true) 7 := by
      simpa [hcount] using hpk
    simp [hpk, hpkW, bW, withPark]

/-- `settleBoard` does not read the park fields, and it copies them onto the result. -/
theorem settleBoard_withPark (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int)
    (home : Nat) (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard (withPark b row ctrl fromHole ridx) home
        (withPark_home b row ctrl fromHole ridx ▸ hH)
        (withPark_held b row ctrl fromHole ridx ▸ hD) xs n moves slides peak =
      withPark (settleBoard b home hH hD xs n moves slides peak) row ctrl fromHole ridx := by
  let bT := withPark b row ctrl fromHole ridx
  let hHT : home < bT.sudo_5Board_4home.size := withPark_home b row ctrl fromHole ridx ▸ hH
  let hDT : home < bT.sudo_5Board_4held.size := withPark_held b row ctrl fromHole ridx ▸ hD
  have hcount :
      countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 =
        countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
    simp [bT, withPark]
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkT : peak < countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 := by
      simpa [hcount] using hpk
    rw [settle_peak bT home hHT hDT xs n moves slides peak hpkT,
      settle_peak b home hH hD xs n moves slides peak hpk]
    simp [bT, withPark]
  · have hpkT : ¬ peak < countHeld (bT.sudo_5Board_4held.set ⟨home, hDT⟩ true) 7 := by
      simpa [hcount] using hpk
    rw [settle_keep bT home hHT hDT xs n moves slides peak hpkT,
      settle_keep b home hH hD xs n moves slides peak hpk]
    simp [bT, withPark]

end EcbsLink2.Link2
