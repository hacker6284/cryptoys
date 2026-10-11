/-
  One climb rung after the idle park: the emitted prefix, then the final white
  successor. Proof-only. Not a security claim. The park hole sits immediately
  after the climb holes (`ladder0 + nrungs`). `pegPack` is irreducible below
  `pegPack_fixed`: unfolding that recursion under the clear exceeds the
  heartbeat limit.
-/
import EcbsLink2.Link2.InvertDelta

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem arr_get {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  subst h
  rfl

theorem array_get_irrel {a : Array Int} {i : Nat} {h1 h2 : i < a.size} :
    a[i]'h1 = a[i]'h2 := by
  have : (⟨i, h1⟩ : Fin a.size) = ⟨i, h2⟩ := Fin.ext rfl
  simp [this]

theorem cell_eq_of {α : Type} {a b : Array α} (h : a = b) {i : Nat}
    {ha : i < a.size} {hb : i < b.size} {v : α}
    (hv : b[i]'hb = v) : a[i]'ha = v := by
  subst h
  have : (⟨i, ha⟩ : Fin a.size) = ⟨i, hb⟩ := Fin.ext rfl
  simpa [this] using hv

theorem idx_irrel {α : Type} {a : Array α} {i : Nat} {h1 h2 : i < a.size} :
    a[i]'h1 = a[i]'h2 := by
  have : (⟨i, h1⟩ : Fin a.size) = ⟨i, h2⟩ := Fin.ext rfl
  simp [this]

theorem arr_set_congr {a b : Array Int} (h : a = b) (i : Nat)
    (ha : i < a.size) (v : Int) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, h ▸ ha⟩ v := by
  subst h
  rfl

theorem array_set_idx {a : Array Int} {i : Nat} {h1 h2 : i < a.size} {v : Int} :
    a.set ⟨i, h1⟩ v = a.set ⟨i, h2⟩ v := by
  have : (⟨i, h1⟩ : Fin a.size) = ⟨i, h2⟩ := Fin.ext rfl
  rw [this]

/-- `clear` copies peak. The moves and slides copies live with the other deltas. -/
theorem clear_peak_copy (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

/-- Two peak raises against counts of at most seven stay under `max(pk0, 7)`. -/
theorem raised_twice_le (pk0 peak a b : Nat) (h : peak ≤ max pk0 7)
    (ha : a ≤ 7) (hb : b ≤ 7) :
    raisedPeak (raisedPeak peak a) b ≤ max pk0 7 :=
  peak_carry pk0 (raisedPeak peak a) _
    (peak_carry pk0 peak _ h (raisedPeak_carry peak a ha))
    (raisedPeak_carry _ b hb)

theorem not_rung_two (rung : Nat) (h : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

/-- The climb hole after one more rung, when the park is the cell past the ladder.
    It stays on the row, it is not the park, and it is not the hole just read. -/
theorem successor_hole (L R i park rowLen : Nat)
    (hL : 0 < L) (hi : i < R) (hp : park = L + R)
    (hold : climbAt L R i < rowLen) :
    climbAt L R (i + 1) < rowLen ∧
    climbAt L R (i + 1) ≠ park ∧
    climbAt L R i ≠ climbAt L R (i + 1) := by
  have hle : i + 1 ≤ R := Nat.succ_le_of_lt hi
  refine ⟨?_, climbAt_ne_sum L R (i + 1) park hL hle hp, ?_⟩
  · by_cases hlt : i + 1 < R
    · rw [climbAt_pred L R i hlt]
      have hpos : 0 < climbAt L R i := by
        have hge := climbAt_ge L R i hi
        omega
      omega
    · have heq : i + 1 = R := by omega
      rw [climbAt_end L R i hL heq]
      have holdEq : climbAt L R i = L := by
        unfold climbAt
        omega
      omega
  · by_cases hlt : i + 1 < R
    · rw [climbAt_pred L R i hlt]
      have hpos : 0 < climbAt L R i := by
        have hge := climbAt_ge L R i hi
        omega
      omega
    · have heq : i + 1 = R := by omega
      rw [climbAt_end L R i hL heq]
      have holdEq : climbAt L R i = L := by
        unfold climbAt
        omega
      omega

/-- A final rung's control fits the budget's counter room. The new counter is
    the park write plus one per tally peg; the peg-loop fit is that counter
    plus one more tally. -/
theorem final_white_ctrl_fit (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 1 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen ((ctrl + 2 + tally) + 2) ∧
    FitsLen (((ctrl + 2 + tally) + 2) + 2) ∧
    FitsLen ((ctrl + 2 + tally) + tally) := by
  have hx : 2 * (3 * mMax + 5) = 6 * mMax + 10 := by omega
  have hsplit : done * (3 * mMax + 5) + 2 * (3 * mMax + 5) =
      (done + 2) * (3 * mMax + 5) := (Nat.add_mul done 2 (3 * mMax + 5)).symm
  have hge : (done + 2) * (3 * mMax + 5) ≤ (R + 1) * (3 * mMax + 5) :=
    Nat.mul_le_mul_right _ (by omega : done + 2 ≤ R + 1)
  have hcap : ctrl + (6 * mMax + 10) ≤ ctrl0 + (R + 1) * (3 * mMax + 5) := by
    have h1 : ctrl + (6 * mMax + 10) ≤
        ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) := by omega
    have h2 : ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) =
        ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) := by
      rw [← hx]
      exact Nat.add_assoc _ _ _
    have h3 : ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) ≤
        ctrl0 + (R + 1) * (3 * mMax + 5) := by
      rw [hsplit]
      exact Nat.add_le_add_left hge _
    exact Nat.le_trans (Nat.le_trans h1 (Nat.le_of_eq h2)) h3
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega)⟩

/-- A non-final white double stays inside the counter budget. `done + 2 ≤ R`
    because this rung is not the last, so one more charge still fits. -/
theorem open_white_ctrl_fit (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 2 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 2 + 3 * tally) ∧
    FitsLen ((ctrl + 2 + 3 * tally) + 2) ∧
    FitsLen ((ctrl + 2 + 3 * tally) + 4) ∧
    FitsLen (ctrl + 2 + 3 * tally + 2 * tally) := by
  have hmul : (done + 2) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (6 * mMax + 10) := by
    rw [Nat.add_mul]
    omega
  have hbody : ctrl + 6 * mMax + 10 ≤ ctrl0 + (done + 2) * (3 * mMax + 5) := by
    omega
  have hcap : ctrl0 + (done + 2) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega)⟩

/-- A non-final red counter, the park fit, and the peg-loop fit. Two rungs
    remain, so two `3 · mMax + 5` steps cover `3 · tally + 5`. -/
theorem open_red_ctrl_fit (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 2 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen ((ctrl + 2 + 3 * tally + 1) + 2) ∧
    FitsLen (((ctrl + 2 + 3 * tally + 1) + 2) + 2) ∧
    FitsLen ((ctrl + 2 + 3 * tally + 1) + (2 * tally + 1)) := by
  have hmul : (done + 2) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (6 * mMax + 10) := by
    rw [Nat.add_mul]
    omega
  have hbody : ctrl + 6 * mMax + 10 ≤ ctrl0 + (done + 2) * (3 * mMax + 5) := by
    omega
  have hcap : ctrl + 6 * mMax + 10 ≤ ctrl0 + (R + 1) * (3 * mMax + 5) :=
    Nat.le_trans hbody
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : done + 2 ≤ R + 1)) _)
  have h3 : 3 * tally ≤ 3 * mMax := Nat.mul_le_mul_left 3 ht
  have h5 : 5 * tally ≤ 5 * mMax := Nat.mul_le_mul_left 5 ht
  have ha : (ctrl + 2 + 3 * tally + 1) + 2 ≤ ctrl + 6 * mMax + 10 := by
    omega
  have hb : ((ctrl + 2 + 3 * tally + 1) + 2) + 2 ≤ ctrl + 6 * mMax + 10 := by
    omega
  have hc : (ctrl + 2 + 3 * tally + 1) + (2 * tally + 1) ≤ ctrl + 6 * mMax + 10 := by
    omega
  exact ⟨FitsLen.of_le hf (Nat.le_trans ha hcap),
    FitsLen.of_le hf (Nat.le_trans hb hcap),
    FitsLen.of_le hf (Nat.le_trans hc hcap)⟩

theorem open_red_high (t0 tally : Nat) :
    t0 + (2 * tally + 1) - 1 ≤ t0 + 2 * tally := by
  rw [Nat.add_sub_assoc (Nat.le_add_left 1 (2 * tally)) t0, Nat.add_sub_cancel]
  exact Nat.le_refl _

theorem open_red_row_fit (t0 tally control : Nat)
    (h : t0 + 2 * tally ≤ control) (hc : FitsLen (control + 1)) :
    FitsLen (t0 + (2 * tally + 1)) :=
  FitsLen.of_le hc (by omega)

theorem open_red_tmax_lt (tally : Nat) :
    2 * tally + 1 < 2 * (2 * tally + 1) := by
  omega

/-- `tally_double` copies moves, slides, ops, and peak, so a rung delta survives it. -/
theorem rungDelta_cost {b b1 b2 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (h : RungDelta b b1 base m)
    (hmv : b2.sudo_5Board_4cost.sudo_5Costs_5moves =
      b1.sudo_5Board_4cost.sudo_5Costs_5moves)
    (hsl : b2.sudo_5Board_4cost.sudo_5Costs_6slides =
      b1.sudo_5Board_4cost.sudo_5Costs_6slides)
    (hops : b2.sudo_5Board_4cost.sudo_5Costs_3ops =
      b1.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hpk : b2.sudo_5Board_4cost.sudo_5Costs_4peak =
      b1.sudo_5Board_4cost.sudo_5Costs_4peak) :
    RungDelta b b2 base m := by
  obtain ⟨mv, mv', hb, hb', hle⟩ := h.moves
  obtain ⟨sl, sl', sb, sb', sle⟩ := h.slides
  obtain ⟨pk, pk', pb, pb', ple⟩ := h.peak
  refine
    { moves := ⟨mv, mv', hb, hmv.trans hb', hle⟩
      slides := ⟨sl, sl', sb, hsl.trans sb', sle⟩
      opsSize := by rw [hops, h.opsSize]
      ops := ?_
      peak := ⟨pk, pk', pb, hpk.trans pb', ple⟩ }
  intro i hi
  obtain ⟨c, c', hc, hc', hle⟩ := h.ops i hi
  refine ⟨c, c', hc, ?_, hle⟩
  simpa [hops] using hc'

/-- The row a final white rung leaves: the park write, then the tally painted red.
    The segment is the finished one. -/
theorem final_white_row_seg (s : ClimbModel) (x : List Nat) (r hole : Nat)
    (hseg : RowSeg s.row s.t0 s.tally false)
    (hF : s.fromHole < 0) (hwhite : r ≠ 2)
    (hp : s.parkAt < s.t0) (hh : hole < s.t0) :
    RowSeg (modelRung s x r hole true).row (modelRung s x r hole true).t0
      (modelRung s x r hole true).tally true := by
  let s' := modelRung s x r hole true
  have hMod := model_final_white s x r hole hwhite hF
  obtain ⟨_hgap, ht, _hon, _hwork, _hctrl, _hhigh, hrow, _hfrom, _hridx, ht0,
      _hpark, _hn, _hk, _hb⟩ := hMod
  have hsegR := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
    hseg hp hh (Or.inl hF)
  have hEq : s'.row =
      rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r true := by
    rw [hrow, rungRow, afterTally]
    simp
  simpa [hEq, ht0, ht, s'] using hsegR

/-- A non-final white rung doubles the red tally. The segment is white of length
    `2 · tally`, provided the row has room for that double. -/
theorem open_white_row_seg (s : ClimbModel) (x : List Nat) (r hole : Nat)
    (hseg : RowSeg s.row s.t0 s.tally false)
    (hF : s.fromHole < 0) (hwhite : r ≠ 2)
    (hp : s.parkAt < s.t0) (hh : hole < s.t0)
    (hroom : s.t0 + 2 * s.tally ≤ s.row.length) :
    let s' := modelRung s x r hole false
    RowSeg s'.row s'.t0 s'.tally false := by
  intro s'
  have hparked : decide (0 ≤ s.fromHole) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have hrow : s'.row =
      rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
    simp [s', modelRung, rungRow]
  have ht0 : s'.t0 = s.t0 := by simp [s', modelRung]
  have ht : s'.tally = 2 * s.tally := by
    simp [s', modelRung, invRung, hwhite, hparked]
  have hsegR := rungRow_open_white_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
    hseg hp hh (Or.inl hF) hroom hwhite
  rw [hrow, ht0, ht]
  exact hsegR

/-- Copy, the pegs, the gap mul, and `clear` stay inside one `rungCharge`. -/
theorem white_clear_move_piece (mv moves0 pegC m n bench pegG mvM : Nat)
    (hmov : moves0 ≤ mv + pegC + m * pegCharge n bench)
    (hmul : mvM ≤ moves0 + mulCharge n bench)
    (hc : pegC ≤ n) (hg : pegG ≤ n) :
    mvM + pegG ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n := by
  omega

theorem le_add_charge (mv n bench m a : Nat)
    (ha : a ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n) :
    a ≤ mv + rungCharge n bench m := by
  have h := charge_final_white n bench m
  omega

theorem white_clear_move_le (mv moves0 pegC m n bench pegG mvM : Nat)
    (hmov : moves0 ≤ mv + pegC + m * pegCharge n bench)
    (hmul : mvM ≤ moves0 + mulCharge n bench)
    (hc : pegC ≤ n) (hg : pegG ≤ n) :
    mvM + pegG ≤ mv + rungCharge n bench m :=
  le_add_charge mv n bench m _
    (white_clear_move_piece mv moves0 pegC m n bench pegG mvM hmov hmul hc hg)

theorem white_clear_slide_piece (sl slides m n peg : Nat)
    (hs : slides ≤ sl + m * (2 * n)) (hp : peg ≤ n) :
    slides + 2 * peg ≤ sl + m * (2 * n) + 2 * n := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  omega

theorem slide_piece_le_charge (n m : Nat) :
    m * (2 * n) + 2 * n ≤ rungSlideCharge n m := by
  have h := slide_open_red n m
  omega

theorem add_piece_le (sl a b charge : Nat) (h : a + b ≤ charge) :
    sl + a + b ≤ sl + charge := by
  omega

/-- The peg slides and the gap mul's slides stay inside one slide charge. -/
theorem white_clear_slide_le (sl slides m n peg : Nat)
    (hs : slides ≤ sl + m * (2 * n)) (hp : peg ≤ n) :
    slides + 2 * peg ≤ sl + rungSlideCharge n m := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have hsum : slides + 2 * peg ≤ sl + m * (2 * n) + 2 * n := Nat.add_le_add hs h2
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by rw [Nat.add_mul]
  have h3 : 2 * n ≤ 3 * (2 * n) := by
    calc
      2 * n = 1 * (2 * n) := (Nat.one_mul _).symm
      _ ≤ 3 * (2 * n) := Nat.mul_le_mul_right _ (by decide : (1 : Nat) ≤ 3)
  have hpiece : m * (2 * n) + 2 * n ≤ (m + 3) * (2 * n) := by
    rw [hsplit]
    exact Nat.add_le_add_left h3 _
  have hre : sl + m * (2 * n) + 2 * n ≤ sl + (m + 3) * (2 * n) := by
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left hpiece sl
  exact Nat.le_trans hsum (by
    unfold rungSlideCharge
    exact hre)

theorem parkKeep_fixed (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hP : park < b.sudo_5Board_3row.size) (hH : hole < b.sudo_5Board_3row.size) :
    let bP := parkKeepBoard b hole park rung i ctrl hP hH
    bP.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    bP.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    bP.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    bP.sudo_5Board_1t = b.sudo_5Board_1t ∧
    bP.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
    bP.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
    bP.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    bP.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold parkKeepBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem place_fixed (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    let b1 := placeBoard b home hH hD xs moves peak
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem settle_fixed (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    let b1 := settleBoard b home hH hD xs n moves slides peak
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem cubeOff_fixed (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size) (hHome : src < b.sudo_5Board_4home.size) :
    let b1 := cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold cubeOffBoard
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem cubeLive_fixed (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let b1 := cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold cubeLiveBoard
  have hS := settle_fixed b src hH hD xs n moves slides peak
  have hC := cubeOff_fixed (settleBoard b src hH hD xs n moves slides peak) dst src (xs.take n)
    n k (moves + 2 * pegCount (xs.take n)) hole bench
    (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)) peakS cOps
    (settle_ops_lt b 1 src hops hH hD xs n moves slides peak)
    (settle_held_lt b src hH hD xs n moves slides peak)
    (settle_home_lt b src hH hD xs n moves slides peak)
  exact ⟨hC.1.trans hS.1, hC.2.1.trans hS.2.1, hC.2.2.1.trans hS.2.2.1,
    hC.2.2.2.trans hS.2.2.2⟩

theorem pegStep_fixed (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    let b1 := pegStep bC t0 j hrow ctrl
    b1.sudo_5Board_7ladder0 = bC.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = bC.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      bC.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = bC.sudo_5Board_1t := by
  unfold pegStep
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pegPack_fixed (c : PegCtx) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m) :
    let b1 := (pegPack c i h0 hle).b
    b1.sudo_5Board_7ladder0 = c.b0.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = c.b0.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      c.b0.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = c.b0.sudo_5Board_1t := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    simp only [pegPack, pegFromOff, hle, dite_true]
    unfold offPeg
    have hs := pegStep_fixed
      (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
      c.t0 0 (offRowPr c) c.ctrl0
    have hc := cubeOff_fixed c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
      c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome
    exact ⟨hs.1.trans hc.1, hs.2.1.trans hc.2.1, hs.2.2.1.trans hc.2.2.1,
      hs.2.2.2.trans hc.2.2.2⟩
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have ih := pegPack_fixed c (n + 1) (Nat.succ_pos n) hle1
    simp only [pegPack, pegNext, hle, dite_true]
    unfold livePegBoard
    have hs := pegStep_fixed
      (cubeLiveBoard (pegPack c (n + 1) (Nat.succ_pos n) hle1).b c.src c.src
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).xs c.n c.k
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).moves
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).slides
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).hole c.bench
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).peak
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).peakS
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).cOps
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).hH
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).hD
        (pegPack c (n + 1) (Nat.succ_pos n) hle1).hops)
      c.t0 (n + 1) (liveRowPr c (pegPack c (n + 1) (Nat.succ_pos n) hle1)
        (Nat.lt_of_succ_le hle))
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).ctrl
    have hc := cubeLive_fixed (pegPack c (n + 1) (Nat.succ_pos n) hle1).b c.src c.src
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).xs c.n c.k
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).moves
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).slides
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).hole c.bench
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).peak
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).peakS
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).cOps
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).hH
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).hD
      (pegPack c (n + 1) (Nat.succ_pos n) hle1).hops
    exact ⟨hs.1.trans (hc.1.trans ih.1), hs.2.1.trans (hc.2.1.trans ih.2.1),
      hs.2.2.1.trans (hc.2.2.1.trans ih.2.2.1),
      hs.2.2.2.trans (hc.2.2.2.trans ih.2.2.2)⟩

/- `pegPack` is the cube-peg recursion. Unfolding that body under the clear
   reduced it inside `whnf` and blew the heartbeat limit, so from here on it
   stays folded. `pegPack_fixed` above is the last lemma that opens it.
   Later facts read the board through `pegPack_board` and the ops lemmas,
   after the board has been abstracted to a variable. -/
attribute [local irreducible] pegPack

theorem mul_fixed (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let b1 := mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps
      hH hD hops
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold mulNoLiveBoard mulNoOffBoard
  have hS := settle_fixed b second hH hD ys n moves slides peak
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩

theorem clear_fixed (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    let b1 := clearHeldBoard b home xs moves hH hD
    b1.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b1.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    b1.sudo_5Board_1t = b.sudo_5Board_1t ∧
    b1.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
    b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold clearHeldBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mulLive_hole (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx
        (school n xs (ys.take n) (List.replicate bench 0) false))) := by
  unfold mulNoLiveBoard mulNoOffBoard
  rfl

/-- The product list is trits when the zero strip is, which it is. -/
theorem fieldMul_trits (n k bench : Nat) (g ys : List Nat)
    (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench g (ys.take n)) := by
  have hrep : allTritList (List.replicate bench 0) := by
    intro x hx
    simp [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    decide
  have hwide : ∀ i, i < n → i + (n - 1) < (List.replicate bench 0).length := by
    intro i hi
    rw [List.length_replicate]
    have h2 : 2 * (n - 1) < bench :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)) hspan
    omega
  have hsch := school_trits g (ys.take n) (List.replicate bench 0) false n hrep hwide
  have hfold := laneFold_trits n (n - k)
    (school n g (ys.take n) (List.replicate bench 0) false) hsch (Nat.sub_le _ _)
    (by
      rw [show (school n g (ys.take n) (List.replicate bench 0) false).length = bench by
        simpa [List.length_replicate] using
          school_length g (ys.take n) (List.replicate bench 0) false n]
      exact hn)
  simpa [fieldMul, laneFold] using allTritList_take hfold n

/-- The peg-loop ops array, with the `pegPack` board abstracted before the
    equality is read. The conclusion is about `pegBoard`, which does not
    reduce to the recursion. -/
theorem pegBoard_ops_eq (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m) :
    (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
        (Int.ofNat (c.cOps0 + k)) := by
  have hB := (pegPack_board c k h0 hle).1
  generalize hb : (pegPack c k h0 hle).b = bPeg at hB
  have hEq := pegPack_ops_eq c k h0 hle
  have hMove : bPeg.sudo_5Board_4cost.sudo_5Costs_3ops =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
        (Int.ofNat (c.cOps0 + k)) :=
    (congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hb).symm.trans hEq
  exact (congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hB).symm.trans hMove

/-- A slot other than 1, after the peg board has been turned into a variable.
    `pegPack_ops_ne` is applied to that variable's equation, not under a clear. -/
theorem pegBoard_ops_ne (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m)
    (j : Nat) (hne : j ≠ 1)
    (hj : j < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hj' : j < (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj' =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have hB := (pegPack_board c k h0 hle).1
  generalize hb : (pegPack c k h0 hle).b = bPeg at hB
  have hneP := pegPack_ops_ne c k h0 hle j hne hj
  have hArr : bPeg.sudo_5Board_4cost.sudo_5Costs_3ops =
      (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops :=
    (congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hb).symm
  have hszP : j < (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [pegPack_ops_eq c k h0 hle, Array.size_set]
    exact hj
  have hszB : j < bPeg.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hArr]
    exact hszP
  have hFrom : bPeg.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hszB =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[j] :=
    (arr_get hArr j hszB).trans hneP
  have hArrB : (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops =
      bPeg.sudo_5Board_4cost.sudo_5Costs_3ops :=
    (congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hB).symm
  exact (arr_get hArrB j hj').trans hFrom

/-- Ops slot 1 of the peg-loop board is the entry cube count plus the peg count. -/
theorem pegBoard_ops_one (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m)
    (h1 : 1 < (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (pegBoard c k).sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 =
      ((c.cOps0 + k : Nat) : Int) := by
  have hEq := pegBoard_ops_eq c k h0 hle
  have hget := arr_get hEq 1 h1
  rw [hget, Array.getElem_set, if_pos rfl, ofNat_eq_natCast]

/-- Slot 0 of a one-slot bump, then a copy, is the entry value plus one.
    Slot 1 is the peg-loop value. Every other slot is the entry value.
    `entry`, `peg`, `mul`, and `clr` are arrays: this proof never unfolds a board. -/
theorem bumped_clear_ops (entry peg mul clr : Array Int) (tally c0 c1 : Nat)
    (h0p : 0 < peg.size) (h1p : 1 < peg.size)
    (hp1 : peg[1]'h1p = ((c1 + tally : Nat) : Int))
    (hpNe : ∀ j, j ≠ 1 → ∀ (he : j < entry.size) (hp : j < peg.size),
      peg[j]'hp = entry[j]'he)
    (hsz : peg.size = entry.size)
    (hmul : mul = peg.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int))
    (hclr : clr = mul) :
    (∀ (hc : 0 < clr.size), clr[0]'hc = ((c0 + 1 : Nat) : Int)) ∧
    (∀ (hc : 1 < clr.size), clr[1]'hc = ((c1 + tally : Nat) : Int)) ∧
    (∀ j, j ≠ 0 → j ≠ 1 → ∀ (he : j < entry.size) (hc : j < clr.size),
      clr[j]'hc = entry[j]'he) ∧
    clr.size = entry.size := by
  have hszM : mul.size = peg.size := by rw [hmul, Array.size_set]
  have hszC : clr.size = entry.size := by rw [hclr, hszM, hsz]
  refine ⟨?_, ?_, ?_, hszC⟩
  · intro hc
    have hM : 0 < mul.size := hclr ▸ hc
    rw [arr_get hclr 0 hc, arr_get hmul 0 hM]
    exact Array.getElem_set_eq peg ⟨0, h0p⟩ _ rfl _
  · intro hc
    have hM : 1 < mul.size := hclr ▸ hc
    rw [arr_get hclr 1 hc, arr_get hmul 1 hM]
    have hne0 : (0 : Nat) ≠ 1 := by decide
    rw [Array.getElem_set_ne peg ⟨0, h0p⟩ _ _ hne0]
    exact hp1
  · intro j hz ho he hc
    have hM : j < mul.size := hclr ▸ hc
    have hp : j < peg.size := hszM ▸ hM
    rw [arr_get hclr j hc, arr_get hmul j hM]
    have hne0 : (⟨0, h0p⟩ : Fin peg.size).1 ≠ j := Ne.symm hz
    rw [Array.getElem_set_ne peg ⟨0, h0p⟩ _ _ hne0]
    exact hpNe j ho he hp

/-- Exact ops of an idle clear: slot 0 grew by one, slot 1 by the tally, and
    every other slot is the rung entry. Arrays only. -/
structure ClearSlots (entry clr : Array Int) (tally : Nat) : Prop where
  size : clr.size = entry.size
  slots : ∀ i (hi : i < entry.size),
    ∃ cE cC : Nat,
      entry[i]'hi = (cE : Int) ∧
      clr[i]'(size ▸ hi) = (cC : Int) ∧
      (i = 0 → cC = cE + 1) ∧
      (i = 1 → cC = cE + tally) ∧
      (i ≠ 0 → i ≠ 1 → cC = cE)

/-- The peg-loop bump, the gap mul's slot-0 write, and `clear` (which copies ops)
    are one `ClearSlots`. -/
theorem clearSlots_of_bump (entry peg mul clr : Array Int) (tally c0 c1 : Nat)
    (h0e : 0 < entry.size) (h1e : 1 < entry.size)
    (he0 : entry[0]'h0e = (c0 : Int))
    (he1 : entry[1]'h1e = (c1 : Int))
    (hNat : ∀ i (hi : i < entry.size), ∃ c : Nat, entry[i]'hi = (c : Int))
    (h0p : 0 < peg.size) (h1p : 1 < peg.size)
    (hp1 : peg[1]'h1p = ((c1 + tally : Nat) : Int))
    (hpNe : ∀ j, j ≠ 1 → ∀ (he : j < entry.size) (hp : j < peg.size),
      peg[j]'hp = entry[j]'he)
    (hsz : peg.size = entry.size)
    (hmul : mul = peg.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int))
    (hclr : clr = mul) :
    ClearSlots entry clr tally := by
  obtain ⟨hz, ho, hr, hsize⟩ := bumped_clear_ops entry peg mul clr tally c0 c1
    h0p h1p hp1 hpNe hsz hmul hclr
  refine ⟨hsize, ?_⟩
  intro i hi
  obtain ⟨c, hc⟩ := hNat i hi
  have hiC : i < clr.size := hsize ▸ hi
  by_cases hzero : i = 0
  · subst hzero
    have hc0 : c = c0 := natCast_inj (hc.symm.trans he0)
    refine ⟨c, c0 + 1, hc, ?_, ?_, ?_, ?_⟩
    · rw [hz hiC]
    · intro _; rw [hc0]
    · intro h; exact absurd h (by decide)
    · intro h _; exact absurd h (by decide)
  · by_cases hone : i = 1
    · subst hone
      have hc1 : c = c1 := natCast_inj (hc.symm.trans he1)
      refine ⟨c, c1 + tally, hc, ?_, ?_, ?_, ?_⟩
      · rw [ho hiC]
      · intro h; exact absurd h (by decide)
      · intro _; rw [hc1]
      · intro _ h; exact absurd h (by decide)
    · refine ⟨c, c, hc, ?_, ?_, ?_, ?_⟩
      · rw [hr i hzero hone hi hiC, hc]
      · intro h; exact absurd h hzero
      · intro h; exact absurd h hone
      · intro _ _; rfl

/-- A cube writes slot 1 and a mul writes slot 0. On top of a clear whose slot 0
    grew by one and whose slot 1 grew by the tally, the red cube and the red mul
    leave every slot inside `mMax + 3` of the rung entry. -/
theorem red_ops_on_clear (entry clr cube red : Array Int) (tally mMax v1 v0 : Nat)
    (ht : tally ≤ mMax)
    (hs : ClearSlots entry clr tally)
    (hszU : cube.size = clr.size) (hszR : red.size = cube.size)
    (h1 : 1 < clr.size) (h0 : 0 < cube.size)
    (hv1 : clr[1]'h1 = (v1 : Int))
    (hcube : cube = clr.set ⟨1, h1⟩ (Int.ofNat (v1 + 1)))
    (hv0 : cube[0]'h0 = (v0 : Int))
    (hmul : red = cube.set ⟨0, h0⟩ (Int.ofNat (v0 + 1))) :
    red.size = entry.size ∧
    ∀ i (hi : i < entry.size),
      ∃ c c' : Nat,
        entry[i]'hi = (c : Int) ∧
        red[i]'(by rw [hszR, hszU, hs.size]; exact hi) = (c' : Int) ∧
        c' ≤ c + (mMax + 3) := by
  refine ⟨by rw [hszR, hszU, hs.size], ?_⟩
  intro i hi
  obtain ⟨cE, cC, hcE, hcC, h0s, h1s, hrest⟩ := hs.slots i hi
  have hiC : i < clr.size := hs.size ▸ hi
  have hiU : i < cube.size := hszU ▸ hiC
  have hiR : i < red.size := by rw [hszR, hszU, hs.size]; exact hi
  by_cases hz : i = 0
  · subst hz
    have hc0 : cC = cE + 1 := h0s rfl
    have hred : red[0]'hiR = Int.ofNat (v0 + 1) := by
      rw [arr_get hmul 0 hiR]
      exact Array.getElem_set_eq cube ⟨0, h0⟩ _ rfl _
    have hcU : cube[0]'h0 = clr[0]'hiC := by
      rw [arr_get hcube 0 h0]
      rw [Array.getElem_set_ne clr ⟨1, h1⟩ _ _ (by decide : (1 : Nat) ≠ 0)]
    have hv : v0 = cC := by
      apply ofNat_inj_nat
      exact hv0.symm.trans (hcU.trans hcC)
    refine ⟨cE, cE + 2, hcE, ?_, ?_⟩
    · have hnum : v0 + 1 = cE + 2 := by rw [hv, hc0]
      rw [hred, hnum, ofNat_eq_natCast]
    · omega
  · by_cases ho : i = 1
    · subst ho
      have hc1 : cC = cE + tally := h1s rfl
      have hred1 : red[1]'hiR = cube[1]'hiU := by
        rw [arr_get hmul 1 hiR]
        rw [Array.getElem_set_ne cube ⟨0, h0⟩ _ _ (by decide : (0 : Nat) ≠ 1)]
      have hcu1 : cube[1]'hiU = Int.ofNat (v1 + 1) := by
        rw [arr_get hcube 1 hiU]
        exact Array.getElem_set_eq clr ⟨1, h1⟩ _ rfl _
      have hv : v1 = cC := by
        apply ofNat_inj_nat
        exact hv1.symm.trans hcC
      refine ⟨cE, cE + tally + 1, hcE, ?_, ?_⟩
      · have hnum : v1 + 1 = cE + tally + 1 := by rw [hv, hc1]
        rw [hred1, hcu1, hnum, ofNat_eq_natCast]
      · have hle : tally + 1 ≤ mMax + 3 := Nat.succ_le_succ (Nat.le_trans ht (Nat.le_add_right _ 2))
        omega
    · have hcEq : cC = cE := hrest hz ho
      have hredN : red[i]'hiR = cube[i]'hiU := by
        rw [arr_get hmul i hiR]
        rw [Array.getElem_set_ne cube ⟨0, h0⟩ _ _ (Ne.symm hz)]
      have hcuN : cube[i]'hiU = clr[i]'hiC := by
        rw [arr_get hcube i hiU]
        rw [Array.getElem_set_ne clr ⟨1, h1⟩ _ _ (Ne.symm ho)]
      refine ⟨cE, cE, hcE, ?_, Nat.le_add_right _ _⟩
      rw [hredN, hcuN, hcC, hcEq]

/-- The three slot facts are one rung's ops bound: slot 0 grows by one, slot 1
    by the tally, and every other slot stays. Each of those is at most `mMax + 3`. -/
theorem rung_ops_of_bump (entry peg mul clr : Array Int) (tally mMax c0 c1 : Nat)
    (ht : tally ≤ mMax)
    (h0e : 0 < entry.size) (h1e : 1 < entry.size)
    (he0 : entry[0]'h0e = (c0 : Int))
    (he1 : entry[1]'h1e = (c1 : Int))
    (hNat : ∀ i (hi : i < entry.size), ∃ c : Nat, entry[i]'hi = (c : Int))
    (h0p : 0 < peg.size) (h1p : 1 < peg.size)
    (hp1 : peg[1]'h1p = ((c1 + tally : Nat) : Int))
    (hpNe : ∀ j, j ≠ 1 → ∀ (he : j < entry.size) (hp : j < peg.size),
      peg[j]'hp = entry[j]'he)
    (hsz : peg.size = entry.size)
    (hmul : mul = peg.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int))
    (hclr : clr = mul) :
    clr.size = entry.size ∧
    ∀ i (hi : i < entry.size) (hc : i < clr.size),
      ∃ c c' : Nat,
        entry[i]'hi = (c : Int) ∧
        clr[i]'hc = (c' : Int) ∧
        c' ≤ c + (mMax + 3) := by
  obtain ⟨hz, ho, hr, hsize⟩ := bumped_clear_ops entry peg mul clr tally c0 c1
    h0p h1p hp1 hpNe hsz hmul hclr
  refine ⟨hsize, ?_⟩
  intro i hi hiC
  obtain ⟨c, hc⟩ := hNat i hi
  by_cases hzero : i = 0
  · subst hzero
    have hc0 : c = c0 := natCast_inj (hc.symm.trans he0)
    refine ⟨c, c0 + 1, hc, hz hiC, ?_⟩
    rw [hc0]
    omega
  · by_cases hone : i = 1
    · subst hone
      have hc1 : c = c1 := natCast_inj (hc.symm.trans he1)
      refine ⟨c, c1 + tally, hc, ho hiC, ?_⟩
      rw [hc1]
      have ht3 : tally ≤ mMax + 3 := Nat.le_trans ht (Nat.le_add_right mMax 3)
      omega
    · exact ⟨c, c, hc, (hr i hzero hone hi hiC).trans hc, Nat.le_add_right _ _⟩

/-- Park, copy, the white scan, the cube-peg loop, the gap mul, and `clear`.
    The result is that clear. Its row, counter, parked-from hole, rung index,
    and tally length are the final white model once the rung is not red; the
    fields below do not depend on that. The rung delta is the three ops slots
    of that clear: slot 0 grows by one, slot 1 by the tally, and the rest stay. -/
theorem gap_clear_emit
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hp : s.parkAt < s.t0)
    (hh : climbAt base.ladder0 base.R s.ridx < s.t0) :
    ∃ bClear : Ecbs.Board,
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) = .ok bClear ∧
      bClear.sudo_5Board_3row =
        embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + 2 + s.tally : Nat) : Int) ∧
      bClear.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bClear.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bClear.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bClear.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClear.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bClear.sudo_5Board_9marker_on = false ∧
      bClear.sudo_5Board_8bench_on = true ∧
      bClear.sudo_5Board_8bench_to = (5 : Int) ∧
      bClear.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      bClear.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bClear.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bClear.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      5 < bClear.sudo_5Board_4home.size ∧
      5 < bClear.sudo_5Board_4held.size ∧
      6 < bClear.sudo_5Board_4home.size ∧
      6 < bClear.sudo_5Board_4held.size ∧
      7 ≤ bClear.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bClear.sudo_5Board_4held.size, bClear.sudo_5Board_4held[5] = false) ∧
      (∀ h6 : 6 < bClear.sudo_5Board_4held.size, bClear.sudo_5Board_4held[6] = false) ∧
      CellKeep bClear base.xHome base.x ∧
      allTritList (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally)) ∧
      (1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size) ∧
      (∃ c1 : Nat, ∀ (h1 : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int)) ∧
      (∃ p : Nat, bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)) ∧
      (∃ holeN : Nat, bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int)) ∧
      (RungDelta b bClear base s.tally ∧
        ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
          bClear.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
        (∃ mv mvC : Nat,
          b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
          bClear.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
          mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
            mulCharge base.n base.bench + base.n) ∧
        (∃ sl slC : Nat,
          b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
          bClear.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
          slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n)) ∧
      ∃ (c : PegCtx) (bMul : Ecbs.Board),
        Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
        Ecbs.mul (pegBoard c c.m) ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
            false false false = .ok bMul ∧
        c.row0 = afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r ∧
        c.ctrl0 = s.ctrl + 2 ∧
        c.m = s.tally ∧
        c.t0 = s.t0 ∧
        c.g = s.gap ∧ c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧ c.src = 6 ∧
        ∃ bPark, Ecbs.park_rung b (r : Int) = .ok bPark ∧
          Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨c, bMul, hmul, hrow, hctrl, hfromB, hridxB, hlenB, hrow0, hctrl0, hmT, ht0c,
      hfrom, hridx, hlen0, hlive⟩ := parked_gap_mul h hF hm hT hhome
  obtain ⟨ys, moves, slides, holeM, peak, peakS, cOps, hH, hD, hops, hnamed, hys,
      hmov, hslP, hho, hpkP, hps, hop0, hsrc, hg, hn, hk, hbch, hparkE, h5⟩ := hlive
  obtain ⟨bPark, hpark, hcopy⟩ := hparkE
  obtain ⟨h5D, h5H, h5held, h5arr⟩ := h5
  obtain ⟨bPark0, c0, hpark0, hcopy0, _, _, _, _, _, _, _, _, _, _, _, _, hpack⟩ :=
    parked_peg_ctx h hF hm hT hhome
  obtain ⟨mv, pk, sl, h6H, h6D, hmv, hpk, hsl, hmov0, hsl0, hb0place⟩ := hpack
  have hBP : bPark = bPark0 := by injection hpark.symm.trans hpark0
  have hb0eq : c.b0 = c0.b0 := by
    injection (hBP ▸ hcopy).symm.trans hcopy0
  obtain ⟨bP, hparkP, _, _, hkeep⟩ := park_of_shape h
  obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
  have hPK : bPark0 = parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH := by
    have hb : bPark0 = bP := by injection hpark0.symm.trans hparkP
    exact hb.trans hEq
  have hplace : c.b0 = placeBoard bPark0 6 h6H h6D s.gap mv pk := hb0eq.trans hb0place
  have hFixP := parkKeep_fixed b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hmvPark : bPark0.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [hPK]; exact hFixP.2.2.2.2.1.trans hmv
  have hpkPark : bPark0.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hPK]; exact hFixP.2.2.2.2.2.1.trans hpk
  have hslPark : bPark0.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := by
    rw [hPK]; exact hFixP.2.2.2.2.2.2.1.trans hsl
  have h5Hp : 5 < bPark0.sudo_5Board_4home.size := by
    rw [hPK]; simpa [parkKeepBoard, Array.size_set] using h.inv.hG
  have h5Dp : 5 < bPark0.sudo_5Board_4held.size := by
    rw [hPK]; simpa [parkKeepBoard, Array.size_set] using h.inv.hGs
  have h7p : 7 ≤ bPark0.sudo_5Board_4held.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.shape.h7
  have hheldEq : bPark0.sudo_5Board_4held = b.sudo_5Board_4held := by
    rw [hPK]; unfold parkKeepBoard; rfl
  have hhomeEq : bPark0.sudo_5Board_4home = b.sudo_5Board_4home := by
    rw [hPK]; unfold parkKeepBoard; rfl
  have hheld5 : bPark0.sudo_5Board_4held[5]'(h5Dp) = true :=
    (arr_get hheldEq 5 h5Dp).trans (h.inv.gapHome hhome).1
  have harr5 : bPark0.sudo_5Board_4home[5]'(h5Hp) = embed s.gap :=
    (arr_get hhomeEq 5 h5Hp).trans (h.inv.gapHome hhome).2
  have h6Dp : 6 < bPark0.sudo_5Board_4held.size :=
    Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 7) h7p
  have hempty6 : bPark0.sudo_5Board_4held[6]'h6Dp = false :=
    (arr_get hheldEq 6 h6Dp).trans h.shape.spareE
  have hnP : bPark0.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) := by
    rw [hPK]
    simpa [parkKeepBoard] using (by rw [h.shape.gapLen]; exact h.shape.tierN)
  obtain ⟨mvE, hmvE, hmvLe⟩ := h.moves
  obtain ⟨slE, hslE, hslLe⟩ := h.slides
  have hmvSame : mv = mvE := natCast_inj (hmv.symm.trans hmvE)
  have hslSame : sl = slE := natCast_inj (hsl.symm.trans hslE)
  have hR1 : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    omega
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hcopyLe : pegCount s.gap + s.tally * pegCharge base.n base.bench ≤
      rungCharge base.n base.bench base.mMax :=
    gap_copy_le_rung base.n base.bench base.mMax s.tally (pegCount s.gap) hpegN hT
  have hfitBig := copy_then_pegs_fit base.moves0 mv done.length base.R
    (rungCharge base.n base.bench base.mMax) (pegCount s.gap)
    (s.tally * pegCharge base.n base.bench) hR1 (by rw [hmvSame]; exact hmvLe)
    hcopyLe base.fitM
  have hfitCopy : FitsLen (mv + pegCount s.gap) :=
    FitsLen.of_le hfitBig (Nat.le_add_right _ _)
  have hmov0c : c.moves0 = mv + pegCount s.gap := by
    have hcast : (c.moves0 : Int) = ((mv + pegCount s.gap : Nat) : Int) := by
      rw [← c.hmoves0, hb0eq, c0.hmoves0, hmov0]
    exact natCast_inj hcast
  have hsl0c : c.slides0 = sl := by
    apply natCast_inj
    have hd := c.hslides0
    rw [hb0eq] at hd
    have h := hd.symm.trans c0.hslides0
    rw [hsl0] at h
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpk0 : c.peak0 ≤ max pk 7 := by
    have hdelta := place_peak_delta bPark0 6 h6H h6D s.gap mv pk hpkPark
    have hcast : (c.peak0 : Int) =
        Int.ofNat (raisedPeak pk (countHeld (bPark0.sudo_5Board_4held.set ⟨6, h6D⟩ true) 7)) := by
      rw [← c.hpeak0, hplace, hdelta]
    have hnum := natCast_inj (hcast.trans (ofNat_eq_natCast _))
    rw [hnum]
    exact raisedPeak_carry pk _ (countHeld_seven _)
  have hmovB : moves ≤ c.moves0 + c.m * pegCharge c.n c.bench := by
    rw [hmov]
    exact (pegPack c c.m c.hm (Nat.le_refl _)).hmovB
  have hsldB : slides ≤ c.slides0 + c.m * (2 * c.n) := by
    rw [hslP]
    exact (pegPack c c.m c.hm (Nat.le_refl _)).hsldB
  have hpeakB : peak ≤ max c.peak0 7 := by
    rw [hpkP]
    exact (pegPack c c.m c.hm (Nat.le_refl _)).hpeakB
  have hmulLe : mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
      c.n c.k c.bench ≤ moves + mulCharge c.n c.bench := by
    simpa [mulStepMoves] using mul_moves_delta moves c.n c.k c.bench c.g ys c.n_le
  let mvM := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvM : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = (mvM : Int) := by
    rw [hnamed]
    simpa [mvM, ofNat_eq_natCast] using
      mul_live_moves (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
        peak peakS cOps hH hD hops
  have h1mv : moves ≤ mv + pegCount s.gap + s.tally * pegCharge c.n c.bench := by
    rw [hmT, hmov0c] at hmovB
    simpa [Nat.add_assoc] using hmovB
  have hcP : pegCount s.gap ≤ c.n := by
    rw [hn, h.hn]; exact hpegN
  have hgP : pegCount c.g ≤ c.n := by
    rw [hg]; exact hcP
  have hpieceM : mvM + pegCount c.g ≤
      mv + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n := by
    have hraw := white_clear_move_piece mv moves (pegCount s.gap) s.tally c.n c.bench
      (pegCount c.g) mvM h1mv hmulLe hcP hgP
    rw [hn, hbch, h.hn, h.hbench] at hraw
    exact hraw
  have hmoveLe : mvM + pegCount c.g ≤ mv + rungCharge base.n base.bench s.tally :=
    le_add_charge mv base.n base.bench s.tally _ hpieceM
  have hfitClear : FitsLen (mvM + pegCount c.g) := by
    have hle := lift_to_budget base.moves0 base.R done.length base.n base.bench s.tally
      base.mMax mv (mvM + pegCount c.g) hT hR1 (by rw [hmvSame]; exact hmvLe) hmoveLe
    exact FitsLen.of_le base.fitM hle
  have hClear := clear_held_refines bMul 5 c.g mvM h5H h5D h5held h5arr hmvM
    (by rw [c.hlenx]; exact c.hf) hfitClear
  have hseg := afterPark_seg s.row (-1) s.parkAt hole r s.t0 s.tally h.shape.seg hp hh
    (Or.inl (by decide : (-1 : Int) < 0))
  have hWhite : ∀ j (hj : j < c.m),
      c.row0[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) c.hRoom) = 1 := by
    intro j hj
    have hc := hseg.colour j (by rwa [← hmT])
    simpa [hrow0, ht0c] using hc
  let bLoop := mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
    c.bench peak peakS cOps hH hD hops
  have hH5 : 5 < bLoop.sudo_5Board_4home.size := by
    rw [show bLoop = bMul from hnamed.symm]
    exact h5H
  have hD5 : 5 < bLoop.sudo_5Board_4held.size := by
    rw [show bLoop = bMul from hnamed.symm]
    exact h5D
  have hClearL := clear_held_refines bLoop 5 c.g mvM hH5 hD5
    (by simpa [hnamed] using h5held) (by simpa [hnamed] using h5arr)
    (by simpa [hnamed] using hmvM) (by rw [c.hlenx]; exact c.hf) hfitClear
  have hrun0 := rung_prefix_refines b bPark0 r hpark0 s.gap mv pk h6H h6D h5Hp h5Dp h7p
    hheld5 harr5 hempty6 hnP (by rw [h.shape.gapLen]; exact h.shape.peg.fitN)
    hmvPark hpkPark hfitCopy c hplace c.row0 c.hT0 c.hRow c.hRoom hWhite c.hfitRow
    c.g ys c.n c.k moves slides holeM c.bench peak peakS cOps hH hD hops
    (hnamed ▸ hmul) hH5 hD5 mvM hClearL
  let bClear := clearHeldBoard bMul 5 c.g mvM h5H h5D
  have hsame : clearHeldBoard bLoop 5 c.g mvM hH5 hD5 = bClear := by
    have hfun := congrArg (fun bd => Ecbs.clear bd (5 : Int)) hnamed.symm
    injection hClearL.symm.trans (hfun.trans hClear)
  have hrun0b := hrun0
  rw [hsame] at hrun0b
  have hrun : (do
      let b ← Ecbs.park_rung b (r : Int)
      let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
      let _ ← SudoRt.runLoopOn (Int.ofNat 0)
          (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
          (whiteStep b (Int.ofNat (s.tally - 1)))
          (fun j => .ok (b, j))
          (fun _ => .ok (b, (0 : Int)))
      let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
          (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
          (cubePegStep 6 (Int.ofNat (s.tally - 1)))
          (fun σ => .ok σ)
          (fun r => .ok ((0 : Int), r))
      let b := out.2
      let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
      Ecbs.clear b (5 : Int)) = .ok bClear := by
    simp only [hmT, hsrc] at hrun0b
    exact hrun0b
  have hC := clearHeld_book bMul 5 c.g mvM h5H h5D
  have hMulB := mulLive_book (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
    peak peakS cOps hH hD hops
  have hPack := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hPl := place_book bPark0 6 h6H h6D s.gap mv pk
  have hPf := place_fixed bPark0 6 h6H h6D s.gap mv pk
  have hMf := mul_fixed (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
    peak peakS cOps hH hD hops
  have hCf := clear_fixed bMul 5 c.g mvM h5H h5D
  have hPegF := pegPack_fixed c c.m c.hm (Nat.le_refl _)
  have hhighM : bMul.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_15control_highest := by
    rw [hnamed]
    exact hMulB.2.2.2.2.2.1
  have ht0M : bMul.sudo_5Board_6tally0 = (pegBoard c c.m).sudo_5Board_6tally0 := by
    rw [hnamed]
    exact hMulB.2.2.2.1
  have hparkM : bMul.sudo_5Board_9park_hole = (pegBoard c c.m).sudo_5Board_9park_hole := by
    rw [hnamed]
    exact hMulB.2.2.2.2.1
  have hmarkM : bMul.sudo_5Board_9marker_on = false := by
    rw [hnamed]
    exact mul_live_marker (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
      peak peakS cOps hH hD hops
  have haim := mul_live_aimed (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
    peak peakS cOps hH hD hops
  have hbenchM := mul_live_bench_gap (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
    c.bench peak peakS cOps hH hD hops c.hn0 c.gap_pos c.n_le
  have hpre : ys.take c.n = cubeTimes c.n c.k c.bench c.g c.m := by
    rw [hys]
    exact cubeBenchIter_prefix c.n c.k c.bench c.g c.hlenx c.m
  refine ⟨bClear, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC.1, hrow, hrow0, ht0c, hmT]
  · rw [hC.2.2.2.2.2.2.2.1, hctrl, hctrl0, hmT]
  · rw [hC.2.1, hfromB, hfrom]
  · rw [hC.2.2.1, hridxB, hridx]
  · rw [hC.2.2.2.1, hlenB, hlen0]
  · rw [hC.2.2.2.2.1, ht0M, ← hPack.1, hPack.2.2.2.2.1, hplace, hPl.2.2.2.2.1, hPK]
    simpa [parkKeepBoard] using h.inv.t0
  · rw [hC.2.2.2.2.2.1, hparkM, ← hPack.1, hPack.2.2.2.2.2.1, hplace, hPl.2.2.2.2.2.1, hPK]
    simpa [parkKeepBoard] using h.inv.park
  · rw [hC.2.2.2.2.2.2.1, hhighM, ← hPack.1, hPack.2.2.2.2.2.2.1, hplace,
      hPl.2.2.2.2.2.2.1, hPK]
    simpa [parkKeepBoard] using h.inv.high
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.1, hmarkM]
  · rw [hC.2.2.2.2.2.2.2.2.1, hnamed]
    exact haim.1
  · rw [hC.2.2.2.2.2.2.2.2.2.1, hnamed]
    exact haim.2
  · rw [hC.2.2.2.2.2.2.2.2.2.2.1, hnamed, hbenchM, hpre, hmT, hg, hn, hk, hbch]
  · rw [hCf.2.2.2.1, hnamed, hMf.2.2.2, ← hPack.1, hPegF.2.2.2, hplace, hPf.2.2.2, hPK]
    simpa [parkKeepBoard] using rfl
  · rw [hCf.1, hnamed, hMf.1, ← hPack.1, hPegF.1, hplace, hPf.1, hPK]
    simpa [parkKeepBoard] using rfl
  · rw [hCf.2.1, hnamed, hMf.2.1, ← hPack.1, hPegF.2.1, hplace, hPf.2.1, hPK]
    simpa [parkKeepBoard] using rfl
  · rw [hCf.2.2.1, hnamed, hMf.2.2.1, ← hPack.1, hPegF.2.2.1, hplace, hPf.2.2.1, hPK]
    simpa [parkKeepBoard] using rfl
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1, hnamed, mul_live_home, Array.size_set, ← hPack.1,
      hPack.2.2.2.2.2.2.2.1, hplace, hPl.2.2.2.2.2.2.2.2.1, hPK]
    simpa [parkKeepBoard, Array.size_set] using h.inv.hG
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, hnamed, mul_live_held, Array.size_set,
      settle_held_eq, Array.size_set, ← hPack.1, hPack.2.2.2.2.2.2.2.2, hplace,
      hPl.2.2.2.2.2.2.2.2.2, hPK]
    simpa [parkKeepBoard, Array.size_set] using h.inv.hGs
  · have h6 : 6 < bClear.sudo_5Board_4home.size := by
      rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1, hnamed, mul_live_home, Array.size_set]
      exact hH
    exact h6
  · have h6 : 6 < bClear.sudo_5Board_4held.size := by
      rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, hnamed, mul_live_held, Array.size_set,
        settle_held_eq, Array.size_set]
      exact hD
    exact h6
  · have hsz : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size :=
      hC.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hszM : bMul.sudo_5Board_4held.size = (pegBoard c c.m).sudo_5Board_4held.size := by
      rw [hnamed, mul_live_held, Array.size_set, settle_held_eq, Array.size_set]
    rw [hsz, hszM, ← hPack.1, hPack.2.2.2.2.2.2.2.2, hplace, hPl.2.2.2.2.2.2.2.2.2, hPK]
    simpa [parkKeepBoard] using h.shape.h7
  · intro h5
    have hEq : bClear.sudo_5Board_4held = bMul.sudo_5Board_4held.set ⟨5, h5D⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [arr_get hEq 5 h5, Array.getElem_set]
    simp
  · intro h6
    have hEq : bClear.sudo_5Board_4held = bMul.sudo_5Board_4held.set ⟨5, h5D⟩ false := by
      simp [bClear, clearHeldBoard]
    have h6M : 6 < bMul.sudo_5Board_4held.size := by
      have hsz := hC.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact hsz ▸ h6
    rw [arr_get hEq 6 h6, Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    have hHeld := mul_live_held (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
      peak peakS cOps hH hD hops
    have hHeldB : bMul.sudo_5Board_4held = (mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k
        moves slides holeM c.bench peak peakS cOps hH hD hops).sudo_5Board_4held := by
      rw [hnamed]
    have hget := arr_get (hHeldB.trans hHeld) 6 h6M
    rw [hget, Array.getElem_set]
    simp
  · have hopsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      have hopsPlace := place_ops_delta bPark0 6 h6H h6D s.gap mv pk
      rw [← hplace] at hopsPlace
      have hparkOps : bPark0.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [hPK]; exact hFixP.2.2.2.2.2.2.2
      exact hopsPlace.trans hparkOps
    have hsz0 : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsEq]
      exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
    obtain ⟨cMul, hcMul, _⟩ := h.ops 0 (by rw [← hopsEq]; exact hsz0)
    have hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) :=
      (arr_get hopsEq 0 hsz0).trans hcMul
    have hXD : base.xHome < c.b0.sudo_5Board_4held.size := by
      rw [hplace, hPl.2.2.2.2.2.2.2.2.2, hPK]
      simpa [parkKeepBoard] using h.shape.xD
    have hXH : base.xHome < c.b0.sudo_5Board_4home.size := by
      rw [hplace, hPl.2.2.2.2.2.2.2.2.1, hPK]
      simpa [parkKeepBoard] using h.shape.xH
    have hParkD : base.xHome < bPark0.sudo_5Board_4held.size := by
      rw [hPK]; simpa [parkKeepBoard] using h.shape.xD
    have hParkH : base.xHome < bPark0.sudo_5Board_4home.size := by
      rw [hPK]; simpa [parkKeepBoard] using h.shape.xH
    have hPlaceD : base.xHome <
        (placeBoard bPark0 6 h6H h6D s.gap mv pk).sudo_5Board_4held.size :=
      hplace.symm ▸ hXD
    have hPlaceH : base.xHome <
        (placeBoard bPark0 6 h6H h6D s.gap mv pk).sudo_5Board_4home.size :=
      hplace.symm ▸ hXH
    have hHeldEqP : c.b0.sudo_5Board_4held =
        (placeBoard bPark0 6 h6H h6D s.gap mv pk).sudo_5Board_4held := by rw [hplace]
    have hHomeEqP : c.b0.sudo_5Board_4home =
        (placeBoard bPark0 6 h6H h6D s.gap mv pk).sudo_5Board_4home := by rw [hplace]
    have hParkHeld : bPark0.sudo_5Board_4held = b.sudo_5Board_4held := by
      rw [hPK]; unfold parkKeepBoard; rfl
    have hParkHome : bPark0.sudo_5Board_4home = b.sudo_5Board_4home := by
      rw [hPK]; unfold parkKeepBoard; rfl
    have hXheld : c.b0.sudo_5Board_4held[base.xHome]'(hXD) = true :=
      (arr_get hHeldEqP base.xHome hXD).trans
        ((place_held_other bPark0 6 base.xHome h6H h6D s.gap mv pk (Ne.symm h.shape.xNe6) hParkD hPlaceD).trans
          ((arr_get hParkHeld base.xHome hParkD).trans h.shape.xHeld))
    have hXarr : c.b0.sudo_5Board_4home[base.xHome]'(hXH) = embed base.x :=
      (arr_get hHomeEqP base.xHome hXH).trans
        ((place_home_other bPark0 6 base.xHome h6H h6D s.gap mv pk (Ne.symm h.shape.xNe6) hParkH hPlaceH).trans
          ((arr_get hParkHome base.xHome hParkH).trans h.shape.xArr))
    have hKeep := pegPack_keep c base.xHome base.x cMul c.m c.hm (Nat.le_refl _)
      hXD hXH (by rw [hsrc]; exact h.shape.xNe6) hXheld hXarr hsz0 hopZ
    have hKeepB : CellKeep (pegBoard c c.m) base.xHome base.x := by
      rw [← hPack.1]
      exact { heldLt := hKeep.heldLt, held := hKeep.held, homeLt := hKeep.homeLt, arr := hKeep.arr }
    have hMulK := mulLive_keep (pegBoard c c.m) 5 6 base.xHome c.g ys c.n c.k moves slides
      holeM c.bench peak peakS cOps base.x hH hD hops h.shape.xNe6
      hKeepB.heldLt hKeepB.homeLt hKeepB.held hKeepB.arr
    have hMulK' : CellKeep bMul base.xHome base.x := by
      rw [hnamed]
      exact hMulK
    exact clearCell_keep bMul 5 base.xHome c.g mvM base.x h5H h5D (Ne.symm h.shape.xNe5) hMulK'
  · have hspan : 3 * (s.n - 1) < s.benchlen := by
      rw [← hn, ← hbch]
      exact c.span3
    have hnle : s.n ≤ s.benchlen := by rw [← hn, ← hbch]; exact c.n_le
    have htri := fieldMul_trits c.n c.k c.bench c.g ys c.span3 c.n_le
    rw [hpre, hmT, hg, hn, hk, hbch] at htri
    exact htri
  · have hsz : bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [clear_ops_delta, hnamed, mul_live_ops, Array.size_set, settle_ops, ← hPack.1,
        pegPack_ops_eq c c.m c.hm (Nat.le_refl _), Array.size_set]
      have hopsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by
        have hopsPlace := place_ops_delta bPark0 6 h6H h6D s.gap mv pk
        rw [← hplace] at hopsPlace
        exact hopsPlace.trans (by rw [hPK]; exact hFixP.2.2.2.2.2.2.2)
      rw [hopsEq]
    exact hsz ▸ h.shape.peg.opsGt
  · have hops1 : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hsz : bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [clear_ops_delta, hnamed, mul_live_ops, Array.size_set, settle_ops, ← hPack.1,
          pegPack_ops_eq c c.m c.hm (Nat.le_refl _), Array.size_set]
        have hopsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
            b.sudo_5Board_4cost.sudo_5Costs_3ops := by
          have hopsPlace := place_ops_delta bPark0 6 h6H h6D s.gap mv pk
          rw [← hplace] at hopsPlace
          exact hopsPlace.trans (by rw [hPK]; exact hFixP.2.2.2.2.2.2.2)
        rw [hopsEq]
      exact hsz ▸ h.shape.peg.opsGt
    have hOps := pegPack_ops_one c c.m c.hm (Nat.le_refl _)
    have hHere : ∀ (h1 : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = ((c.cOps0 + c.m : Nat) : Int) := by
      intro h1
      have hclr := clear_ops_delta bMul 5 c.g mvM h5H h5D
      have h1b : 1 < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
        (congrArg Array.size hclr) ▸ h1
      rw [arr_get hclr 1 h1]
      have hop := pegPack_ops_one c c.m c.hm (Nat.le_refl _)
      have hOpsB : bMul.sudo_5Board_4cost.sudo_5Costs_3ops =
          (mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
            peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [hnamed]
      have h1m : 1 < (mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
          c.bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
        (congrArg Array.size hOpsB).symm ▸ h1b
      have hmulOps := mul_live_ops (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
        c.bench peak peakS cOps hH hD hops
      have hset := settle_ops (pegBoard c c.m) 6 hH hD ys c.n moves slides peak
      rw [arr_get hOpsB 1 h1b]
      have hslot : (mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
          c.bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1m =
          (settleBoard (pegBoard c c.m) 6 hH hD ys c.n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by
            rw [← Array.size_set, ← hmulOps]; exact h1m) := by
        rw [arr_get hmulOps 1 h1m, Array.getElem_set, if_neg (by decide : (0 : Nat) ≠ 1)]
      rw [hslot]
      have h1s : 1 < (settleBoard (pegBoard c c.m) 6 hH hD ys c.n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hset, ← hPack.1]
        exact (pegPack c c.m c.hm (Nat.le_refl _)).hops
      rw [arr_get hset 1 h1s]
      have hBoard : (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops =
          (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_3ops :=
        congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hPack.1.symm
      have h1p : 1 < (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
        (congrArg Array.size hBoard).symm ▸ (by
          rw [hset] at h1s
          exact h1s)
      exact (arr_get hBoard 1 (by rw [hset] at h1s; exact h1s)).trans hop
    exact ⟨c.cOps0 + c.m, hHere⟩
  · have hS := mul_live_strict (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
      peak peakS cOps hH hD hops
    have hCeq := (clear_fixed bMul 5 c.g mvM h5H h5D).2.2.2.2.2.1
    refine ⟨raisedPeak peakS (countHeld (settleBoard (pegBoard c c.m) 6 hH hD ys c.n moves slides
      peak).sudo_5Board_4held 7), ?_⟩
    rw [hCeq, hnamed, hS, ofNat_eq_natCast]
  · have hS := mulLive_hole (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM c.bench
      peak peakS cOps hH hD hops
    have hCeq := (clear_fixed bMul 5 c.g mvM h5H h5D).2.2.2.2.2.2
    refine ⟨raisedHole holeM (topIdx (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)), ?_⟩
    rw [hCeq, hnamed, hS, ofNat_eq_natCast]
  · obtain ⟨mvE, hmvE, _⟩ := h.moves
    obtain ⟨slE, hslE, _⟩ := h.slides
    obtain ⟨pkE, hpkE, _⟩ := h.peak
    have hparkMv : bPark0.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves := by
      rw [hPK]; exact hFixP.2.2.2.2.1
    have hmvId : mv = mvE := natCast_inj ((hmvPark.symm.trans hparkMv).trans hmvE)
    have hparkSl : bPark0.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides := by
      rw [hPK]; exact hFixP.2.2.2.2.2.2.1
    have hslId : sl = slE := natCast_inj ((hslPark.symm.trans hparkSl).trans hslE)
    have hparkPk : bPark0.sudo_5Board_4cost.sudo_5Costs_4peak =
        b.sudo_5Board_4cost.sudo_5Costs_4peak := by
      rw [hPK]; exact hFixP.2.2.2.2.2.1
    have hpkId : pk = pkE := natCast_inj ((hpkPark.symm.trans hparkPk).trans hpkE)
    have hmvC : bClear.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((mvM + pegCount c.g : Nat) : Int) := by
      have hraw := clear_moves_delta bMul 5 c.g mvM h5H h5D
      simp only [bClear] at hraw
      rwa [ofNat_eq_natCast] at hraw
    have hslM : bMul.sudo_5Board_4cost.sudo_5Costs_6slides =
        ((slides + 2 * pegCount (ys.take c.n) : Nat) : Int) := by
      have hraw := mul_live_slides (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
        c.bench peak peakS cOps hH hD hops
      rw [← hnamed] at hraw
      simpa [ofNat_eq_natCast] using hraw
    have hslC : bClear.sudo_5Board_4cost.sudo_5Costs_6slides =
        ((slides + 2 * pegCount (ys.take c.n) : Nat) : Int) := by
      have hraw := clear_slides_delta bMul 5 c.g mvM h5H h5D
      simp only [bClear] at hraw
      exact hraw.trans hslM
    have hpegTake : pegCount (ys.take c.n) ≤ base.n := by
      have hpeg : pegCount (ys.take c.n) ≤ c.n := by
        have hlen : (ys.take c.n).length ≤ c.n := by
          rw [List.length_take]
          exact Nat.min_le_left _ _
        exact Nat.le_trans (pegCount_le _) hlen
      exact Nat.le_trans hpeg (Nat.le_of_eq (hn.trans h.hn))
    have hsSlides : slides ≤ sl + s.tally * (2 * base.n) := by
      have h1 := hsldB
      rw [hsl0c, hmT, hn, h.hn] at h1
      exact h1
    have hpieceS : slides + 2 * pegCount (ys.take c.n) ≤
        sl + s.tally * (2 * base.n) + 2 * base.n :=
      white_clear_slide_piece sl slides s.tally base.n
        (pegCount (ys.take c.n)) hsSlides hpegTake
    have hslideLe : slides + 2 * pegCount (ys.take c.n) ≤
        sl + rungSlideCharge base.n s.tally :=
      Nat.le_trans hpieceS (add_piece_le sl (s.tally * (2 * base.n)) (2 * base.n)
        (rungSlideCharge base.n s.tally) (slide_piece_le_charge base.n s.tally))
    have hpeakPeg : peak ≤ max pk 7 := peak_carry pk c.peak0 peak hpk0 hpeakB
    let bS := settleBoard (pegBoard c c.m) 6 hH hD ys c.n moves slides peak
    let pk1 := raisedPeak peak
      (countHeld ((pegBoard c c.m).sudo_5Board_4held.set ⟨6, hD⟩ true) 7)
    let hFs := settle_held_lt (pegBoard c c.m) 6 hH hD ys c.n moves slides peak
    let pkN := raisedPeak pk1 (countHeld (bS.sudo_5Board_4held.set ⟨6, hFs⟩ false) 7)
    have hpkM : bMul.sudo_5Board_4cost.sudo_5Costs_4peak = (pkN : Int) := by
      have hlive := mul_live_peak (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
        c.bench peak peakS cOps hH hD hops
      rw [← hnamed] at hlive
      simpa [pkN, pk1, bS, hFs, ofNat_eq_natCast] using hlive
    have hpkLe : pkN ≤ max pk 7 :=
      raised_twice_le pk peak
        (countHeld ((pegBoard c c.m).sudo_5Board_4held.set ⟨6, hD⟩ true) 7)
        (countHeld (bS.sudo_5Board_4held.set ⟨6, hFs⟩ false) 7)
        hpeakPeg (countHeld_seven _) (countHeld_seven _)
    have hpkC : bClear.sudo_5Board_4cost.sudo_5Costs_4peak = (pkN : Int) := by
      have hraw := clear_peak_copy bMul 5 c.g mvM h5H h5D
      simp only [bClear] at hraw
      exact hraw.trans hpkM
    have hopsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      have hopsPlace := place_ops_delta bPark0 6 h6H h6D s.gap mv pk
      rw [← hplace] at hopsPlace
      exact hopsPlace.trans (by rw [hPK]; exact hFixP.2.2.2.2.2.2.2)
    have hszPeg : (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [pegBoard_ops_eq c c.m c.hm (Nat.le_refl _), Array.size_set]
    have h0e : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
    have h1e : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
    obtain ⟨c0, hc0, _⟩ := h.ops 0 h0e
    obtain ⟨c1, hc1, _⟩ := h.ops 1 h1e
    have h0b0 : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsEq]; exact h0e
    have h1b0 : 1 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsEq]; exact h1e
    have h0peg : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hszPeg]; exact h0b0
    have h1peg : 1 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hszPeg]; exact h1b0
    have hc1eq : c.cOps0 = c1 :=
      natCast_inj (c.hop10.symm.trans ((arr_get hopsEq 1 h1b0).trans hc1))
    have hpeg1 : (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1peg =
        ((c1 + s.tally : Nat) : Int) := by
      have h := pegBoard_ops_one c c.m c.hm (Nat.le_refl _) h1peg
      have hsum : c.cOps0 + c.m = c1 + s.tally := by rw [hc1eq, hmT]
      exact h.trans (congrArg (fun n : Nat => (n : Int)) hsum)
    have hpNe : ∀ j (hne : j ≠ 1)
        (he : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hp : j < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size),
        (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hp =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'he := by
      intro j hne he hp
      have he0 : j < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hopsEq]; exact he
      exact (pegBoard_ops_ne c c.m c.hm (Nat.le_refl _) j hne he0 hp).trans
        (arr_get hopsEq j he0)
    have hcOps : cOps = c0 :=
      natCast_inj (hop0.symm.trans
        (((pegBoard_ops_ne c c.m c.hm (Nat.le_refl _) 0 (by decide) h0b0 h0peg).trans
          (arr_get hopsEq 0 h0b0)).trans hc0))
    have hmulArr : bMul.sudo_5Board_4cost.sudo_5Costs_3ops =
        (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0peg⟩
          ((c0 + 1 : Nat) : Int) := by
      have hlive := mul_live_ops (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
        c.bench peak peakS cOps hH hD hops
      have hsettle := settle_ops (pegBoard c c.m) 6 hH hD ys c.n moves slides peak
      have hidx := settle_ops_lt (pegBoard c c.m) 0 6 hops hH hD ys c.n moves slides peak
      have hstep := ops_set_transport hsettle 0 hidx h0peg
        (Int.ofNat (cOps + 1)) (Int.ofNat (cOps + 1)) rfl
      have hval := ops_set_transport rfl 0 h0peg h0peg
        (Int.ofNat (cOps + 1)) ((c0 + 1 : Nat) : Int)
        (by rw [hcOps, ofNat_eq_natCast])
      have hB : bMul.sudo_5Board_4cost.sudo_5Costs_3ops =
          (mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys c.n c.k moves slides holeM
            c.bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [hnamed]
      exact hB.trans (hlive.trans (hstep.trans hval))
    have hclrArr : bClear.sudo_5Board_4cost.sudo_5Costs_3ops =
        bMul.sudo_5Board_4cost.sudo_5Costs_3ops := by
      have hraw := clear_ops_delta bMul 5 c.g mvM h5H h5D
      simp only [bClear] at hraw
      exact hraw
    have hNat : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        ∃ cN : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = (cN : Int) := by
      intro i hi
      obtain ⟨cN, hcN, _⟩ := h.ops i hi
      exact ⟨cN, hcN⟩
    have hszArr : (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hszPeg, hopsEq]
    have hbump := rung_ops_of_bump
      b.sudo_5Board_4cost.sudo_5Costs_3ops
      (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops
      s.tally base.mMax c0 c1 hT h0e h1e hc0 hc1 hNat h0peg h1peg hpeg1 hpNe hszArr
      hmulArr hclrArr
    have hslots := clearSlots_of_bump
      b.sudo_5Board_4cost.sudo_5Costs_3ops
      (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops
      s.tally c0 c1 h0e h1e hc0 hc1 hNat h0peg h1peg hpeg1 hpNe hszArr
      hmulArr hclrArr
    refine ⟨?_, hslots, ?_, ?_⟩
    · refine
        { moves := ⟨mv, mvM + pegCount c.g, ?_, hmvC, hmoveLe⟩
          slides := ⟨sl, slides + 2 * pegCount (ys.take c.n), ?_, hslC, hslideLe⟩
          opsSize := hbump.1
          ops := ?_
          peak := ⟨pk, pkN, ?_, hpkC, hpkLe⟩ }
      · rw [hmvId]; exact hmvE
      · rw [hslId]; exact hslE
      · intro i hi
        exact hbump.2 i hi (hbump.1 ▸ hi)
      · rw [hpkId]; exact hpkE
    · exact ⟨mv, mvM + pegCount c.g, by rw [hmvId]; exact hmvE, hmvC, hpieceM⟩
    · exact ⟨sl, slides + 2 * pegCount (ys.take c.n), by rw [hslId]; exact hslE,
        hslC, hpieceS⟩
  · exact ⟨c, bMul, hClear, hmul, hrow0, hctrl0, hmT, ht0c, hg, hn, hk, hbch, hsrc,
      ⟨bPark, hpark, hcopy⟩⟩

/-- Idle final white rung. The park hole is the cell after the ladder
    (`ladder0 + R`). The emitted park-through-clear is the `ClimbInvK`
    successor: the row segment is the finished tally, and `ParkRead` is the
    climb hole just parked, with nothing left on the ladder. -/
theorem white_final_k
    {done : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [r] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hp : s.parkAt < s.t0)
    (hh : climbAt base.ladder0 base.R s.ridx < s.t0)
    (hwhite : r ≠ 2)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done [r] ≤ base.mMax) :
    ∃ b',
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) = .ok b' ∧
      ClimbInvK (done ++ [r]) [] b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) true) base ∧
      RungDelta b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole true
  obtain ⟨b', hAll⟩ := gap_clear_emit h hF hm hT hhome hp hh
  rcases hAll with ⟨hrun, hrowE, hctrlE, hfromE, hridxE, hlenE, ht0E, hparkE,
      hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδs, _hctx⟩
  obtain ⟨hδ, _⟩ := hδs
  have hFrom : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hMod := model_final_white s base.x r hole hwhite hF
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := hMod
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hinv : ClimbInv b' s' := by
    refine
      { hG := h5H
        hGs := h5D
        marker := hmarkE
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · rw [hlenE, htall]
    · rw [hctrlE, hctrlM]
    · rw [hhighE, hhighM]
    · rw [ht0E, ht0M]
    · rw [hrowE, hrowM, hFrom]
    · rw [hparkE, hparkM]
    · rw [hfromE, hfromM]
    · rw [hridxE, hridxM]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨hbonE, htoE, ?_, ?_⟩
      · rw [hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork, hgap]
  have hseg : RowSeg s'.row s'.t0 s'.tally true :=
    final_white_row_seg s base.x r hole h.shape.seg hF hwhite hp hh
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone base.fitCtrl
  have hpark' : ParkRead b' s' [] base := by
    refine
      { ladder0B := ?_
        nrungsB := ?_
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · rw [hladE, h.shape.park.ladder0B]
    · rw [hnrE, h.shape.park.nrungsB]
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      exact h.shape.park.parkLe
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _hnn
      rw [hfromM]
      rfl
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hle : hole ≤ s.high := by
          have hhi : hole < s.t0 := hh
          have htop : s.high = s.t0 + s.tally - 1 := h.highTop hm
          omega
        rw [hhighM]
        simpa [Int.toNat_ofNat] using hle
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rs hrs
      cases hrs
    · intro k hk _hlt
      simp at hk
    · rw [hctrlM]
      exact hfits.1
    · rw [hctrlM]
      exact hfits.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  obtain ⟨c1, hc1⟩ := hc1E
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := hopsE
        cOps := ⟨c1, hc1 hopsE⟩
        peakS := hpkSE
        holeM := hholeE
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · rw [hgap]; exact htrits
    · intro hpos
      rw [ht0M, htall, hhighM]
      have htop : s.high = s.t0 + s.tally - 1 := h.highTop (by
        rw [htall] at hpos
        exact hpos)
      omega
    · rw [ht0M, htall]; exact h.shape.peg.fitRow
    · rw [htall]; exact h.shape.peg.fitTall
    · rw [hctrlM, htall]; exact hfits.2.2
    · rw [hnM]; exact h.shape.peg.n_pos
    · rw [hnM, hbM]; exact h.shape.peg.span
    · rw [hbM]; exact h.shape.peg.small
    · rw [hnM]; exact h.shape.peg.n_small
    · rw [hnM]; exact h.shape.peg.fitN
    · rw [hbM]; exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] hnM hkM hbM hgapLen
      hseg h6D h6H (h6f (Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 7) h7E)) h7E
      (by intro _; exact h5f (Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h7E))
      (by intro hOff; rw [hon] at hOff; cases hOff)
      hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr
      (by rw [htierE, hnM]; exact h.shape.tierN)
      (by rw [htierE, hkM]; exact h.shape.tierK)
      (by rw [htierE, hbM]; exact h.shape.tierB)
      (by rw [htierE]; exact h.shape.tierW)
      (by rw [htierE]; exact h.shape.tierH)
      (by rw [htierE]; exact h.shape.tierR)
      (by rw [htierE]; exact h.shape.tierCg)
      (by rw [htierE]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, by rw [htmaxE, htm], ?_⟩
    intro hpos
    have hlt := hnote (by rw [← htall]; exact hpos)
    rw [htall]
    exact hlt
  have hK := climbInvK_succ h hinv hδ hCap hshape hh htmax rfl
  exact ⟨b', hrun, hK, hδ⟩

private theorem cons_tail (r : Nat) (rest : List Nat) (k : Nat) (hk : k < rest.length) :
    (r :: rest)[1 + k]'(by simp; omega) = rest[k] := by
  have hcomm : 1 + k = k + 1 := Nat.add_comm 1 k
  have hk1 : k + 1 < (r :: rest).length := by
    simpa [hcomm] using (by simp; omega : 1 + k < (r :: rest).length)
  exact (getElem_congr (c := r :: rest) (i := 1 + k) (j := k + 1)
    (h := by simp; omega) hcomm).trans (List.getElem_cons_succ r rest k hk1)

/-- Idle non-final white rung. Park through clear, then `tally_double`.
    The empty tail supplies the second white half. Later ladder holes sit
    below the tally, so the double does not rewrite them. -/
theorem white_open_k
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2) (hrest : rest ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          Ecbs.tally_double b) = .ok b' ∧
      ClimbInvK (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base ∧
      RungDelta b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  obtain ⟨bClear, hAll⟩ := gap_clear_emit h hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, hrowE, hctrlE, hfromE, hridxE, hlenE, ht0E, hparkE,
      hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδs, _hctx⟩
  obtain ⟨hδ, _⟩ := hδs
  have hFrom : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hMod := model_open_white s base.x r hole hwhite hF
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := hMod
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hge
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax0, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax0 < 2 * s.tally := hNote0 hm
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hfitC : FitsLen (s.ctrl + 2 + s.tally + 2 * s.tally) := by
    rw [show s.ctrl + 2 + s.tally + 2 * s.tally = s.ctrl + 2 + 3 * s.tally by omega]
    exact hfits.1
  let parked := afterPark s.row (-1) s.parkAt hole r
  let xs := paintRed parked s.t0 s.tally
  have hRow : bClear.sudo_5Board_3row = embed xs := by
    simpa [xs, parked] using hrowE
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, parked, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo parked s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, parked, paintRed_length, afterPark_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [h.shape.rowLen]
      omega
    have hsrc := h.openZero hge k hk (by simpa [Nat.add_assoc] using hix)
    have hpj : s.parkAt < s.t0 + s.tally + k :=
      Nat.lt_of_lt_of_le h.parkBelow
        (Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k))
    have hhj : hole < s.t0 + s.tally + k :=
      Nat.lt_of_lt_of_le h.holeBelow
        (Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k))
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      rw [h.shape.rowLen]
      exact Nat.lt_of_lt_of_le hlt hRoom
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      hpj hhj (Or.inl (by decide)) hjLen
    have hget := paintRed_get_hi parked s.t0 s.tally (s.t0 + s.tally + k)
      (Nat.le_add_right _ _) (by rw [afterPark_length]; exact hjLen)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    simpa [xs, parked] using hget.trans (hAp.trans hsrc')
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    rw [htierE]
    exact h.shape.tierC
  have hhighC : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((s.t0 + s.tally - 1 : Nat) : Int) := by
    rw [hhighE, hHighEq]
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax0 : Int) :=
    htmaxE.trans hMax
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + 2 + s.tally)
    (s.t0 + s.tally - 1) base.control tmax0 hm hlenE ht0E hRow
    (by
      simp [xs, parked, paintRed_length, afterPark_length, h.shape.rowLen]
      exact hRoom)
    hRed hZero hctrlN hhighC rfl hctrlE hRoom hFitI hfitC hFitM hmaxC hNote
  let wide := paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
  let b' :=
    { bClear with
      sudo_5Board_3row := embed wide
      sudo_5Board_9tally_len := Int.ofNat (2 * s.tally)
      sudo_5Board_4cost := { bClear.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + 2 + s.tally + 2 * s.tally)
        sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
        sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally) } }
  have htallyW : Ecbs.tally_double bClear = .ok b' := by
    simpa [b', wide, xs] using htally
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          Ecbs.tally_double b) = .ok b' := by
    rw [hrun, ok_bind]
    exact htallyW
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hctrlNat : s.ctrl + 2 + s.tally + 2 * s.tally = s'.ctrl := by
    rw [hctrlM]
    omega
  have hhighNat : s.t0 + 2 * s.tally - 1 = s'.high := by
    rw [hhighM]
  have hinv : ClimbInv b' s' := by
    refine
      { hG := by simpa [b'] using h5H
        hGs := by simpa [b'] using h5D
        marker := by simpa [b'] using hmarkE
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · rw [show b'.sudo_5Board_9tally_len = Int.ofNat (2 * s.tally) by simp [b'], htall]
      rfl
    · rw [show b'.sudo_5Board_4cost.sudo_5Costs_4ctrl =
          Int.ofNat (s.ctrl + 2 + s.tally + 2 * s.tally) by simp [b'], hctrlNat]
      rfl
    · rw [show b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
          ((s.t0 + 2 * s.tally - 1 : Nat) : Int) by simp [b'], hhighNat]
    · rw [show b'.sudo_5Board_6tally0 = bClear.sudo_5Board_6tally0 by simp [b'], ht0E, ht0M]
    · have hwide : wide =
          paintOnes (paintOnes (paintRed (afterPark s.row s.fromHole s.parkAt hole r)
            s.t0 s.tally) s.t0 s.tally) (s.t0 + s.tally) s.tally := by
        simp [wide, xs, parked, hFrom]
      rw [show b'.sudo_5Board_3row = embed wide by simp [b'], hwide, hrowM]
    · rw [show b'.sudo_5Board_9park_hole = bClear.sudo_5Board_9park_hole by simp [b'],
        hparkE, hparkM]
    · rw [show b'.sudo_5Board_11parked_from = bClear.sudo_5Board_11parked_from by simp [b'],
        hfromE, hfromM]
    · rw [show b'.sudo_5Board_8rung_idx = bClear.sudo_5Board_8rung_idx by simp [b'],
        hridxE, hridxM]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨by simpa [b'] using hbonE, by simpa [b'] using htoE, ?_, ?_⟩
      · rw [show b'.sudo_5Board_5bench = bClear.sudo_5Board_5bench by simp [b'],
          hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork, hgap]
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty := by
    rw [hempty]
    exact open_white_row_seg s base.x r hole h.shape.seg hF hwhite h.parkBelow h.holeBelow
      (by rw [h.shape.rowLen]; exact hRoom)
  have hpark' : ParkRead b' s' rest base := by
    refine
      { ladder0B := by rw [show b'.sudo_5Board_7ladder0 = bClear.sudo_5Board_7ladder0 by simp [b'],
          hladE, h.shape.park.ladder0B]
        nrungsB := by rw [show b'.sudo_5Board_6nrungs = bClear.sudo_5Board_6nrungs by simp [b'],
          hnrE, h.shape.park.nrungsB]
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [show b'.sudo_5Board_7ladder0 = bClear.sudo_5Board_7ladder0 by simp [b'],
          hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [show b'.sudo_5Board_6nrungs = bClear.sudo_5Board_6nrungs by simp [b'],
          hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      have hhi : s.parkAt < s.t0 := h.parkBelow
      omega
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _
      rw [hfromM]
      rfl
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · rw [hhighM]
        have hhi : hole < s.t0 := h.holeBelow
        simpa [Int.toNat_ofNat] using (by omega : hole ≤ s.t0 + 2 * s.tally - 1)
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rs hrs
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail 1
        (by simp [hrs]) hlt0
      have hj : climbAt base.ladder0 base.R (s.ridx + 1) < s'.row.length := by
        rw [hlenRow]; exact hlt0
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1) < s.t0 :=
        climb_below base.ladder0 base.R s.ridx 1 s.t0 h.shape.park.l0pos
          (by omega) h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1) := by
        exact (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
      have hget := rungRow_white_below s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1)) hF hwhite hneP hneH hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      have hhead : (r :: rest)[1]'(by simp [hrs]) = r2 := by simp [hrs]
      refine ⟨?_, ?_⟩
      · simpa [hrowR, hridxM, hhead] using hget.trans hcol
      · simpa [hhead] using hnz
    · intro k hk hlt
      have hoff : s.ridx + (1 + k) ≤ base.R := by
        rw [h.idx]
        have hlen := h.kLe
        simp [List.length_append, List.length_cons] at hlen
        omega
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.row.length := by
        rw [← hlenRow, ← hridxM]
        exact hlt
      have hltTail : climbAt base.ladder0 base.R (s.ridx + (1 + k)) < s.row.length := by
        simpa [Nat.add_assoc] using hlt0
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail (1 + k)
        (by simp; omega) hltTail
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.t0 := by
        simpa [Nat.add_assoc] using
          (climb_below base.ladder0 base.R s.ridx (1 + k) s.t0 h.shape.park.l0pos hoff
            h.holeBelow)
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1 + k) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        intro heq
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        simp [hole, climbAt] at heq
        omega
      have hget := rungRow_white_below s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hF hwhite hneP hneH hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      refine ⟨?_, ?_⟩
      · have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
            climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
          rw [hridxM]
        have hmove := getElem_congr (c := s'.row)
          (i := climbAt base.ladder0 base.R (s'.ridx + k))
          (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := hlt) hixEq
        have hcoll := getElem_congr_coll (c := s'.row)
          (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := by rw [← hixEq]; exact hlt) hrowR
        have hlist := cons_tail r rest k hk
        exact hmove.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((cons_tail r rest k hk).trans hz)
    · rw [hctrlM]
      exact hfits.2.1
    · rw [hctrlM]
      exact hfits.2.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  obtain ⟨c1, hc1⟩ := hc1E
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := by simpa [b'] using hopsE
        cOps := ⟨c1, by
          have h1 : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            simpa [b'] using hopsE
          simpa [b'] using hc1 h1⟩
        peakS := by
          obtain ⟨p, hp⟩ := hpkSE
          exact ⟨p, by simpa [b'] using hp⟩
        holeM := by
          obtain ⟨hn, hh⟩ := hholeE
          exact ⟨hn, by simpa [b'] using hh⟩
        trits := by rw [hgap]; exact htrits
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · intro hpos
      rw [ht0M, htall, hhighM]
      omega
    · rw [ht0M, htall]
      exact hFitI
    · rw [htall]
      exact hFitM
    · rw [hctrlM, htall]
      exact hfits.2.2.2
    · rw [hnM]
      exact h.shape.peg.n_pos
    · rw [hnM, hbM]
      exact h.shape.peg.span
    · rw [hbM]
      exact h.shape.peg.small
    · rw [hnM]
      exact h.shape.peg.n_small
    · rw [hnM]
      exact h.shape.peg.fitN
    · rw [hbM]
      exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' rest base :=
    shape_refresh h.shape b' s' rest hnM hkM hbM hgapLen hseg
      (by simpa [b'] using h6D) (by simpa [b'] using h6H)
      (by simpa [b'] using h6f (Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 7) h7E))
      (by simpa [b'] using h7E)
      (by intro _; simpa [b'] using h5f (Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h7E))
      (by intro hOff; rw [hon] at hOff; cases hOff)
      (by simpa [b'] using hkeep.heldLt) (by simpa [b'] using hkeep.homeLt)
      (by simpa [b'] using hkeep.held) (by simpa [b'] using hkeep.arr)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE, hnM]
        exact h.shape.tierN)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE, hkM]
        exact h.shape.tierK)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE, hbM]
        exact h.shape.tierB)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE]
        exact h.shape.tierW)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE]
        exact h.shape.tierH)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE]
        exact h.shape.tierR)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE]
        exact h.shape.tierCg)
      (by
        rw [show b'.sudo_5Board_1t = bClear.sudo_5Board_1t by simp [b'], htierE]
        exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have hδ' : RungDelta b b' base s.tally :=
    rungDelta_cost hδ (by simp [b']) (by simp [b']) (by simp [b']) (by simp [b'])
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally, by simp [b'], ?_⟩
    intro hpos
    rw [htall]
    omega
  have hK := climbInvK_succ h (by simpa [hempty] using hinv) hδ' hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax) rfl
  exact ⟨b', hprog, by simpa [hempty] using hK, hδ'⟩

/-- The parked clear, the unparked red cube and mul, and the cost projections.
    `red_cube_mul` is obtained once here. The row proof and the successor read
    this bundle, so they do not elaborate that theorem again. -/
theorem red_open_view
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bClearP bClearU bCube bRed : Ecbs.Board),
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) = .ok bClearP ∧
      bClearP = withPark bClearU
        (embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (((s.ctrl + 2 + s.tally : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      bClearU.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bClearU.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClearU.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) ∧
      bClearU.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      bRed.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bRed.sudo_5Board_1t = bClearU.sudo_5Board_1t ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.cube (withPark (withTally bClearU rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.mul (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withPark (withTally bRed rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∃ (mvE mvR slE slR : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
        mvR ≤ mvE + rungCharge base.n base.bench s.tally ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
        slR ≤ slE + rungSlideCharge base.n s.tally) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      RungDelta b bClearP base s.tally ∧
      ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
        bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
      bClearP.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bClearP.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bClearP.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
      bClearP.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClearP.sudo_5Board_9marker_on = false ∧
      bClearP.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      bClearP.sudo_5Board_8bench_on = true ∧
      bClearP.sudo_5Board_8bench_to = (5 : Int) ∧
      bClearP.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      5 < bClearP.sudo_5Board_4home.size ∧
      5 < bClearP.sudo_5Board_4held.size ∧
      6 < bClearP.sudo_5Board_4home.size ∧
      6 < bClearP.sudo_5Board_4held.size ∧
      7 ≤ bClearP.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
        bClearP.sudo_5Board_4held[5]'h5 = false) ∧
      (∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
        bClearP.sudo_5Board_4held[6]'h6 = false) ∧
      CellKeep bClearP base.xHome base.x ∧
      1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∃ c1 : Nat, ∀ (h1 : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int)) ∧
      (∃ p : Nat, bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)) ∧
      (∃ holeN : Nat,
        bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int)) ∧
      allTritList (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally)) ∧
      (∃ mv mvC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        bClearP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
        mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n) ∧
      (∃ sl slC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        bClearP.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
        slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n) := by

  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bClearP, hAll⟩ := gap_clear_emit h hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, _hrowE, _hctrlE, _hfromE, _hridxE, _hlenE, ht0E, hparkE,
      _hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδs, hctx⟩
  obtain ⟨hδ, hslots, hpieceM, hpieceS⟩ := hδs
  obtain ⟨cG, bMulG, hclearG, hmulG, hrowG, hctrlG, hmG, ht0G, hgG, hnG, hkG, hbG, hsrcG,
      ⟨bParkG, hparkG, hcopyG⟩⟩ := hctx
  obtain ⟨bLoopU, bMulU0, bClearU, bCube0, bRed0, hmulU, _hclearU, hcubeU, hredU,
      _hbounds, hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
      _ht0Cube, ht0Red, _htierCube, htierRed, _hcubeF, _hmulF,
      honR, htoR, hlenR, hbenchR, hclearP, _hcubeP, _hmulP,
      hcubeBoth, hmulBoth, hpack, hrel, _hhighR, _htmaxR⟩ := red_cube_mul h hm hT hhome hxLen hxT
  obtain ⟨cU, _ysU, _mvU, _slU, _hoU, _pkU, _psU, _cOpsU, _hHU, _hDU, _hopsU,
      hloopU, hrowU, hctrlU, hgU, hmU, hnU, hkU, hbU, hsrcU, ht0U, _hnamed,
      _hys, _hmv, _hsl, _hho, _hpk, _hps, hcopyU⟩ := hpack
  obtain ⟨bMulU, bMulD, ⟨cP, bLoopP, hmulP, hloopP, hcopyP, hrowP, hctrlP, hgP,
      hmP, hnP, hkP, hbP, hsrcP, ht0P⟩, ⟨cD, hmulD, hrowD, hctrlD, hmD, ht0D, hgD,
      hnD, hkD, hbD, hsrcD, ⟨bParkD, hparkD, hcopyD⟩⟩, hrelP⟩ :=
    parked_gap_is_withPark h hF hm hT hhome
  have hb0U : cP.b0 = cU.b0 := by injection hcopyP.symm.trans hcopyU
  have hboardsU := pegBoard_same_copy cP cU hb0U
    (hsrcU.trans hsrcP.symm) (hgU.trans hgP.symm) (hnU.trans hnP.symm)
    (hkU.trans hkP.symm) (hbU.trans hbP.symm) (hrowU.trans hrowP.symm)
    (ht0U.trans ht0P.symm) (hctrlU.trans hctrlP.symm) (hmU.trans hmP.symm)
  have hloopsU : bLoopU = bLoopP := by
    rw [hloopU, hloopP, hboardsU]
  have hmulSame : bMulU0 = bMulU := by
    rw [hloopsU] at hmulU
    injection hmulU.symm.trans hmulP
  have hparkMul : bMulD = withPark bMulU0
      (embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    simpa [hmulSame, hole] using hrelP
  have hbPark : bParkG = bParkD := by injection hparkG.symm.trans hparkD
  have hb0D : cG.b0 = cD.b0 := by
    have hcg := hcopyG
    rw [hbPark] at hcg
    injection hcg.symm.trans hcopyD
  have hboardsD := pegBoard_same_copy cG cD hb0D
    (hsrcD.trans hsrcG.symm) (hgD.trans hgG.symm) (hnD.trans hnG.symm)
    (hkD.trans hkG.symm) (hbD.trans hbG.symm) (hrowD.trans hrowG.symm)
    (ht0D.trans ht0G.symm) (hctrlD.trans hctrlG.symm) (hmD.trans hmG.symm)
  have hmulGD : bMulG = bMulD := by
    rw [← hboardsD] at hmulG
    injection hmulG.symm.trans hmulD
  let rowRed := embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally)
  let ctrlRed := ((s.ctrl + 2 + s.tally : Nat) : Int)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hclearW := hclearP rowRed ctrlRed fromH ridxH
  rw [← hparkMul, ← hmulGD] at hclearW
  have hClearEq : bClearP = withPark bClearU rowRed ctrlRed fromH ridxH := by
    injection hclearG.symm.trans hclearW
  exact ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, hlenC, ht0C, hrowC, hctrlN,
    hhighC, hctrlC, hmaxC, ht0Red, htierRed, hcubeBoth, hmulBoth, hrel, honR, htoR,
    hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE, ht0E, hmarkE, htierE, htmaxE,
    hcubeU, hredU, hbonE, htoE, hbenchE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
    hopsE, hc1E, hpkSE, hholeE, htrits, hpieceM, hpieceS⟩

theorem settle_park (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cube_live_park (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9marker_on =
      false := by
  unfold cubeLiveBoard cubeOffBoard
  have hs := settle_park b src hH hD xs n moves slides peak
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, rfl⟩

theorem mul_live_park (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9marker_on =
      false ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold mulNoLiveBoard mulNoOffBoard
  have hs := settle_park b second hH hD ys n moves slides peak
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, rfl, hs.2.2.2.2⟩

theorem clearSlots_cast {entry a b : Array Int} {tally : Nat}
    (hs : ClearSlots entry a tally) (h : a = b) : ClearSlots entry b tally := by
  cases h
  exact hs

/-- The tail of a bench padded with zeros is zero. -/
theorem pad_zero (xs : List Nat) (k i : Nat)
    (hn : xs.length ≤ i) (hi : i < (xs ++ List.replicate k 0).length) :
    (xs ++ List.replicate k 0)[i]'hi = 0 := by
  rw [List.getElem_append_right hn]
  simp [List.getElem_replicate]

/-- What the unparked spare cube and the mul by the input leave, read off the
    named live boards. Ops and peak are the `RungDelta`. Park, ladder, marker,
    tier, the spare, and the input cell are field projections. -/
structure RedCarry (b bRed bClear : Ecbs.Board) (base : ClimbBudget) (tally xHome : Nat)
    (x : List Nat) : Prop where
  delta : RungDelta b bRed base tally
  park : bRed.sudo_5Board_9park_hole = bClear.sudo_5Board_9park_hole
  ladder : bRed.sudo_5Board_7ladder0 = bClear.sudo_5Board_7ladder0
  nrungs : bRed.sudo_5Board_6nrungs = bClear.sudo_5Board_6nrungs
  tally0 : bRed.sudo_5Board_6tally0 = bClear.sudo_5Board_6tally0
  marker : bRed.sudo_5Board_9marker_on = false
  tier : bRed.sudo_5Board_1t = bClear.sudo_5Board_1t
  home6 : 6 < bRed.sudo_5Board_4home.size
  held6 : 6 < bRed.sudo_5Board_4held.size
  held7 : 7 ≤ bRed.sudo_5Board_4held.size
  empty5 : bRed.sudo_5Board_4held[5]'(Nat.lt_trans (by decide : (5 : Nat) < 6) held6) = false
  empty6 : bRed.sudo_5Board_4held[6]'held6 = false
  keep : CellKeep bRed xHome x
  strict : ∃ p : Nat, bRed.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  hole : ∃ h : Nat, bRed.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (h : Int)

/-- Spare cube, then the mul by the input, on the unparked clear. The cube writes
    ops slot 1 only. The mul writes ops slot 0 only. Each peak stays at most
    `max(entry, 7)`. Live boards are named only for those projections. -/
theorem red_unparked_delta
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x)
    (bClearP bClearU bCube0 bRed0 : Ecbs.Board)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (hClearEq : bClearP = withPark bClearU row ctrl fromHole ridx)
    (hδ : RungDelta b bClearP base s.tally)
    (hslots : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally)
    (hmarkE : bClearP.sudo_5Board_9marker_on = false)
    (htierE : bClearP.sudo_5Board_1t = b.sudo_5Board_1t)
    (hcubeU : Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube0)
    (hredU : Ecbs.mul bCube0 ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
      false false false = .ok bRed0)
    (hrel : ∃ mvE mvR slE slR : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
      bRed0.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
      mvR ≤ mvE + rungCharge base.n base.bench s.tally ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
      bRed0.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
      slR ≤ slE + rungSlideCharge base.n s.tally)
    (hbonE : bClearP.sudo_5Board_8bench_on = true)
    (htoE : bClearP.sudo_5Board_8bench_to = (5 : Int))
    (hbenchE : bClearP.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0))
    (h5H : 5 < bClearP.sudo_5Board_4home.size)
    (h5D : 5 < bClearP.sudo_5Board_4held.size)
    (h6H : 6 < bClearP.sudo_5Board_4home.size)
    (h6D : 6 < bClearP.sudo_5Board_4held.size)
    (h7E : 7 ≤ bClearP.sudo_5Board_4held.size)
    (h5f : ∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[5]'h5 = false)
    (h6f : ∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[6]'h6 = false)
    (hkeep : CellKeep bClearP base.xHome base.x)
    (hopsE : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hc1E : ∃ c1 : Nat, ∀ h1 : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int))
    (hpkSE : ∃ p : Nat, bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int))
    (hholeE : ∃ holeN : Nat,
      bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int))
    (htrits : allTritList (fieldMul s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally)))
    (hpieceM : ∃ mv mvC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
      mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n)
    (_hpieceS : ∃ sl slC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
      slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n) :
    RedCarry b bRed0 bClearP base s.tally base.xHome base.x := by
  have hmarkU : bClearU.sudo_5Board_9marker_on = false := by
    have hback : bClearU.sudo_5Board_9marker_on = bClearP.sudo_5Board_9marker_on := by
      rw [hClearEq]; rfl
    exact hback.trans hmarkE
  have honU : bClearU.sudo_5Board_8bench_on = true := by
    have hback : bClearU.sudo_5Board_8bench_on = bClearP.sudo_5Board_8bench_on := by
      rw [hClearEq]; rfl
    exact hback.trans hbonE
  have htoU : bClearU.sudo_5Board_8bench_to = (5 : Int) := by
    have hback : bClearU.sudo_5Board_8bench_to = bClearP.sudo_5Board_8bench_to := by
      rw [hClearEq]; rfl
    exact hback.trans htoE
  let gap := fieldMul s.n s.k s.benchlen s.gap
    (cubeTimes s.n s.k s.benchlen s.gap s.tally)
  let xs := gap ++ List.replicate (s.benchlen - s.n) 0
  have hbenchU : bClearU.sudo_5Board_5bench = embed xs := by
    have hback : bClearU.sudo_5Board_5bench = bClearP.sudo_5Board_5bench := by
      rw [hClearEq]; rfl
    simpa [xs, gap] using hback.trans hbenchE
  have hhomeU : bClearU.sudo_5Board_4home = bClearP.sudo_5Board_4home := by
    rw [hClearEq]; rfl
  have hheldU : bClearU.sudo_5Board_4held = bClearP.sudo_5Board_4held := by
    rw [hClearEq]; rfl
  have h5HU : 5 < bClearU.sudo_5Board_4home.size := by rw [hhomeU]; exact h5H
  have h5DU : 5 < bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h5D
  have h7U : 7 ≤ bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h7E
  have hemptyU : bClearU.sudo_5Board_4held[5]'h5DU = false := by
    have hget := arr_get hheldU 5 h5DU
    exact hget.trans (h5f (hheldU ▸ h5DU))
  have htierU : bClearU.sudo_5Board_1t = b.sudo_5Board_1t := by
    have hback : bClearU.sudo_5Board_1t = bClearP.sudo_5Board_1t := by
      rw [hClearEq]; rfl
    exact hback.trans htierE
  have hnU : bClearU.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [htierU]; exact h.shape.tierN
  have hkU : bClearU.sudo_5Board_1t.sudo_4Tier_1k = (s.k : Int) := by
    rw [htierU]; exact h.shape.tierK
  have hblU : bClearU.sudo_5Board_1t.sudo_4Tier_8benchlen = (s.benchlen : Int) := by
    rw [htierU]; exact h.shape.tierB
  have hcgU : bClearU.sudo_5Board_1t.sudo_4Tier_7combgap = (base.cg : Int) := by
    rw [htierU]; exact h.shape.tierCg
  have hwU : bClearU.sudo_5Board_1t.sudo_4Tier_1w = (base.w : Int) := by
    rw [htierU]; exact h.shape.tierW
  have hhU : bClearU.sudo_5Board_1t.sudo_4Tier_1h = (base.h : Int) := by
    rw [htierU]; exact h.shape.tierH
  have hrU : bClearU.sudo_5Board_1t.sudo_4Tier_1r = (base.r : Int) := by
    rw [htierU]; exact h.shape.tierR
  have hopsU : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops =
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hClearEq]; rfl
  have hops1U : 1 < bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact hopsE
  obtain ⟨c1, hc1⟩ := hc1E
  have hop1U : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops1U = (c1 : Int) := by
    exact (arr_get hopsU 1 hops1U).trans (hc1 (hopsU ▸ hops1U))
  obtain ⟨pkS, hpkS⟩ := hpkSE
  have hstrictU : bClearU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (pkS : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      rw [hClearEq]; rfl
    exact hback.trans hpkS
  obtain ⟨holeN, hholeN⟩ := hholeE
  have hholeU : bClearU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      rw [hClearEq]; rfl
    exact hback.trans hholeN
  obtain ⟨mv, mvC, hmv, hmvC, hpiece⟩ := hpieceM
  have hmovesU : bClearU.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_5moves =
        bClearP.sudo_5Board_4cost.sudo_5Costs_5moves := by
      rw [hClearEq]; rfl
    exact hback.trans hmvC
  obtain ⟨sl, slC, hsl, hslC, hpieceS⟩ := _hpieceS
  have hslidesU : bClearU.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_6slides =
        bClearP.sudo_5Board_4cost.sudo_5Costs_6slides := by
      rw [hClearEq]; rfl
    exact hback.trans hslC
  obtain ⟨pk, pkC, hpk, hpkC, hpkLe⟩ := hδ.peak
  have hpeakU : bClearU.sudo_5Board_4cost.sudo_5Costs_4peak = (pkC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_4peak =
        bClearP.sudo_5Board_4cost.sudo_5Costs_4peak := by
      rw [hClearEq]; rfl
    exact hback.trans hpkC
  have hnleB : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hlenG : gap.length = s.n :=
    fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnleB
  have hlenX : xs.length = s.benchlen := by
    simp [xs, hlenG, List.length_replicate, Nat.add_sub_of_le hnleB]
  have hposX : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hnleX : s.n ≤ xs.length := by rw [hlenX]; exact hnleB
  have hzeroX : ∀ i, s.n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 := by
    intro i hi hix
    have hlenI : gap.length ≤ i := by rw [hlenG]; exact hi
    simpa [xs] using pad_zero gap (s.benchlen - s.n) i hlenI hix
  have htake : xs.take s.n = gap := by
    have hle : s.n ≤ gap.length := Nat.le_of_eq hlenG.symm
    rw [show xs = gap ++ List.replicate (s.benchlen - s.n) 0 from rfl,
      List.take_append_of_le_length hle]
    exact List.take_of_length_le (Nat.le_of_eq hlenG)
  have htriX : allTritList (xs.take s.n) := by rw [htake]; exact htrits
  have hpegX : pegCount (xs.take s.n) ≤ s.n := by
    rw [htake]
    exact Nat.le_trans (pegCount_le gap) (Nat.le_of_eq hlenG)
  have hstepR : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  obtain ⟨mv0, hmv0, hmvBound⟩ := h.moves
  have hmvEq : mv = mv0 := ofNat_inj_nat (hmv.symm.trans hmv0)
  have hmvLe : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    rw [hmvEq]; exact hmvBound
  have hpieceN : mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
      mulCharge base.n base.bench + base.n := hpiece
  have hpegN : pegCount (xs.take base.n) ≤ base.n := by
    rw [← h.hn]
    exact hpegX
  have hfitM4 := clear_move_fit base.moves0 base.R done.length base.n base.bench s.tally
    base.mMax mv mvC (pegCount (xs.take base.n)) hT hstepR hmvLe hpieceN hpegN
  obtain ⟨sl0, hsl0, hslBound⟩ := h.slides
  have hslEq : sl = sl0 := ofNat_inj_nat (hsl.symm.trans hsl0)
  have hslLe : sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    rw [hslEq]; exact hslBound
  have hfitS := clear_slide_fit base.slides0 base.R done.length base.n s.tally base.mMax
    sl slC (pegCount (xs.take base.n)) hT hstepR hslLe hpieceS hpegN
  have h1e : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ.opsSize ▸ hopsE
  obtain ⟨cE, cC, hcE, hcC, _h0s, h1s, _hrest⟩ := hslots.slots 1 h1e
  have hplus : cC = cE + s.tally := h1s rfl
  have hc1eq : c1 = cC := by
    apply ofNat_inj_nat
    have hget := arr_get hopsU 1 hops1U
    have hcP : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsU ▸ hops1U) = (cC : Int) :=
      (array_get_irrel (h1 := hopsU ▸ hops1U) (h2 := hslots.size ▸ h1e)).trans hcC
    exact hop1U.symm.trans (hget.trans hcP)
  obtain ⟨cSlot, hcSlot, hcLe⟩ := h.ops 1 h1e
  have hcEeq : cE = cSlot := ofNat_inj_nat (hcE.symm.trans hcSlot)
  have hent : cE ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [hcEeq]; exact hcLe
  have hfitO := clear_ops_fit base.ops0 base.R done.length base.mMax cE s.tally c1
    hT hstepR hent (by rw [hc1eq, hplus])
  have hlive := cube_eq_live bClearU 6 5 xs base.w base.h base.r s.n s.k mvC slC holeN
    s.benchlen pkC pkS c1 base.cg
    hmarkU honU htoU h5HU h5DU h7U hemptyU hbenchU
    hnU h.shape.peg.n_pos hposX hnleX hzeroX
    h.shape.peg.fitN (by rw [hlenX]; exact h.shape.peg.fitBn)
    hmovesU hslidesU hpeakU
    (FitsLen.of_le base.fitM (by
      have h2 := hfitM4.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    (FitsLen.of_le base.fitM (by
      have h2 := hfitM4.2.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    (FitsLen.of_le base.fitS (by
      have h2 := hfitS
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    hops1U hop1U (FitsLen.of_le base.fitO hfitO)
    hblU hcgU h.shape.peg.span
    htriX h.shape.peg.fit3
    (FitsLen.of_le base.fitM (by
      have h2 := hfitM4.2.2.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      have htwo : 2 * base.n = 2 * s.n := by rw [h.hn]
      rw [hidx, htwo] at h2
      exact h2))
    h.shape.w0 h.shape.h0 h.shape.rlt h.shape.r0
    h.shape.n_eq h.shape.k_le h.shape.gap_eq
    hwU hhU hrU hkU
    hholeU hstrictU h.shape.peg.small h.shape.peg.n_small
    h.shape.peg.fitBn
    (FitsLen.of_le base.fitM (by
      have h2 := hfitM4.2.2.2
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      have htwo : 2 * base.n = 2 * s.n := by rw [h.hn]
      have hsub : base.bench - base.n = s.benchlen - s.n := by rw [h.hn, h.hbench]
      rw [hidx, htwo, hsub] at h2
      exact h2))
  have hEq : bCube0 = cubeLiveBoard bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U := by
    injection hcubeU.symm.trans hlive
  have hOps := cube_live_ops bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
    pkC pkS c1 h5HU h5DU hops1U
  have hOpsB : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops =
      (cubeLiveBoard bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen pkC pkS c1
        h5HU h5DU hops1U).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hEq
  let occ1 := countHeld (bClearU.sudo_5Board_4held.set ⟨5, h5DU⟩ true) 7
  let bS := settleBoard bClearU 5 h5HU h5DU xs s.n mvC slC pkC
  let hFs := settle_held_lt bClearU 5 h5HU h5DU xs s.n mvC slC pkC
  let occ2 := countHeld (bS.sudo_5Board_4held.set ⟨5, hFs⟩ false) 7
  let pkU := raisedPeak (raisedPeak pkC occ1) occ2
  have hpkLive := cube_live_peak bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
    pkC pkS c1 h5HU h5DU hops1U
  have hpkB : bCube0.sudo_5Board_4cost.sudo_5Costs_4peak =
      (cubeLiveBoard bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen pkC pkS c1
        h5HU h5DU hops1U).sudo_5Board_4cost.sudo_5Costs_4peak :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_4peak) hEq
  have hpkU : bCube0.sudo_5Board_4cost.sudo_5Costs_4peak = (pkU : Int) := by
    have hraw := hpkB.trans hpkLive
    simpa [pkU, occ1, occ2, bS, hFs, ofNat_eq_natCast] using hraw
  have hpkUle : pkU ≤ max pk 7 :=
    raised_twice_le pk pkC occ1 occ2 hpkLe (countHeld_seven _) (countHeld_seven _)
  have h0e : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) h1e
  obtain ⟨cE0, cC0, hcE0, hcC0, h0s, _h1s0, _hrest0⟩ := hslots.slots 0 h0e
  have h0plus : cC0 = cE0 + 1 := h0s rfl
  have h0u : 0 < bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact Nat.lt_trans (by decide : (0 : Nat) < 1) hopsE
  have hc0U : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0u = (cC0 : Int) := by
    have hget := arr_get hopsU 0 h0u
    have hcP : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hopsU ▸ h0u) = (cC0 : Int) :=
      (array_get_irrel (h1 := hopsU ▸ h0u) (h2 := hslots.size ▸ h0e)).trans hcC0
    exact hget.trans hcP
  have h0cubeSz : 0 < bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hsz : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hEq]
      exact cube_live_ops_size bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
        pkC pkS c1 h5HU h5DU hops1U
    exact hsz.symm ▸ h0u
  have hop0C : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0cubeSz =
      bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[0] :=
    cube_live_op0 bClearU bCube0 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U hEq h0cubeSz
  have hv0 : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0cubeSz = (cC0 : Int) :=
    hop0C.trans hc0U
  let pegX := pegCount (xs.take s.n)
  let mvCube := cubeMoves (mvC + 2 * pegX) (xs.take s.n) s.n s.k s.benchlen
  let slCube := slC + 2 * pegX
  have hCubeLe : mvCube ≤ mvC + pegCharge base.n base.bench := by
    have hraw := cube_moves_delta mvC xs s.n s.k s.benchlen
    have hle : mvCube ≤ mvC + pegCharge s.n s.benchlen := by
      simpa [mvCube, pegX] using hraw
    rw [h.hn, h.hbench] at hle
    exact hle
  let ys := laneFold s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
  have hlenY : ys.length = s.benchlen := by
    have hcomb : (combStrip s.n s.benchlen (xs.take s.n)).length = s.benchlen :=
      combStrip_length s.n s.benchlen (xs.take s.n)
    simpa [ys, hcomb] using
      laneFold_length s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
        (by rw [hcomb]; exact hnleB)
  have hgapPos : 0 < s.n - s.k := by
    rw [h.shape.gap_eq]
    exact Nat.mul_pos h.shape.w0 h.shape.r0
  have hzeroY : ∀ i, s.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0 := by
    intro i hi hix
    have hixB : i < s.benchlen := by rw [← hlenY]; exact hix
    have hcoeff := cube_live_high xs s.n s.k s.benchlen h.shape.peg.n_pos hgapPos i hi hixB
    exact (coeff_eq_get ys i hix).symm.trans hcoeff
  have hposY : 0 < ys.length := by
    rw [hlenY]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hnleY : s.n ≤ ys.length := by rw [hlenY]; exact hnleB
  have htriStrip : allTritList (combStrip s.n s.benchlen (xs.take s.n)) :=
    combStrip_trits (xs.take s.n) s.n s.benchlen htriX (by
      have hsp := h.shape.peg.span
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) hsp)
  have htriY : allTritList (ys.take s.n) := by
    have hfold := laneFold_trits s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
      htriStrip (Nat.sub_le _ _) (by
        rw [combStrip_length]; exact hnleB)
    simpa [ys] using allTritList_take hfold s.n
  have hpegY : pegCount (ys.take s.n) ≤ s.n := by
    exact Nat.le_trans (pegCount_le (ys.take s.n)) (by
      rw [List.length_take]
      exact Nat.min_le_left _ _)
  have hmvCubeB : bCube0.sudo_5Board_4cost.sudo_5Costs_5moves = (mvCube : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_5moves) hEq
    have hlive := cube_live_moves bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [mvCube, pegX, ofNat_eq_natCast] using hB.trans hlive
  have hslCubeB : bCube0.sudo_5Board_4cost.sudo_5Costs_6slides = (slCube : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_6slides) hEq
    have hlive := cube_live_slides bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [slCube, pegX, ofNat_eq_natCast] using hB.trans hlive
  have hbenchC : bCube0.sudo_5Board_5bench = embed ys := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_5bench) hEq
    have hlive := cube_live_bench bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [ys] using hB.trans hlive
  have hmkC : bCube0.sudo_5Board_9marker_on = false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9marker_on) hEq
    exact hB.trans (cube_live_marker bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U)
  have honC : bCube0.sudo_5Board_8bench_on = true := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_8bench_on) hEq
    exact hB.trans (cube_live_on bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U)
  have htoC : bCube0.sudo_5Board_8bench_to = (6 : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_8bench_to) hEq
    exact hB.trans (cube_live_to bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U)
  have hheldSz : bCube0.sudo_5Board_4held.size = bClearU.sudo_5Board_4held.size := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held.size) hEq
    exact hB.trans (cube_live_held_size bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U)
  have h6DU : 6 < bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h6D
  have h6fU : bClearU.sudo_5Board_4held[6]'h6DU = false :=
    (arr_get hheldU 6 h6DU).trans (h6f (hheldU ▸ h6DU))
  have h6DC : 6 < bCube0.sudo_5Board_4held.size := by rw [hheldSz]; exact h6DU
  have hempty6 : bCube0.sudo_5Board_4held[6]'h6DC = false :=
    (cube_live_held_other bClearU bCube0 6 5 6 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U hEq (by decide : (5 : Nat) ≠ 6) h6DU h6DC).trans h6fU
  have hhomeSz : bCube0.sudo_5Board_4home.size = bClearU.sudo_5Board_4home.size := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq).trans
      (cube_live_home bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
        pkC pkS c1 h5HU h5DU hops1U)
    have hs := congrArg Array.size hL
    rw [Array.size_set] at hs
    exact hs
  have h6HC : 6 < bCube0.sudo_5Board_4home.size := by
    rw [hhomeSz, hhomeU]; exact h6H
  let holeC := raisedHole holeN (topIdx (combStrip s.n s.benchlen (xs.take s.n)))
  have hholeC : bCube0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeC : Int) := by
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hEq
    have hlive := cube_live_hole bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [holeC, ofNat_eq_natCast] using hB.trans hlive
  let peakSC := raisedPeak pkS (countHeld bS.sudo_5Board_4held 7)
  have hstrictC : bCube0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSC : Int) := by
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hEq
    have hlive := cube_live_strict bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [peakSC, bS, ofNat_eq_natCast] using hB.trans hlive
  have htierC : bCube0.sudo_5Board_1t = bClearU.sudo_5Board_1t := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hEq
    exact hB.trans (cubeLive_fixed bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U).2.2.2
  have hxDU : base.xHome < bClearU.sudo_5Board_4held.size := by
    rw [hheldU]; exact hkeep.heldLt
  have hxHU : base.xHome < bClearU.sudo_5Board_4home.size := by
    rw [hhomeU]; exact hkeep.homeLt
  have hxHeldU : bClearU.sudo_5Board_4held[base.xHome]'hxDU = true :=
    (arr_get hheldU base.xHome hxDU).trans (by
      simpa using hkeep.held)
  have hxArrU : bClearU.sudo_5Board_4home[base.xHome]'hxHU = embed base.x :=
    (arr_get hhomeU base.xHome hxHU).trans (by
      simpa using hkeep.arr)
  have hxDC : base.xHome < bCube0.sudo_5Board_4held.size := by rw [hheldSz]; exact hxDU
  have hxHC : base.xHome < bCube0.sudo_5Board_4home.size := by rw [hhomeSz]; exact hxHU
  have hxHeldC : bCube0.sudo_5Board_4held[base.xHome]'hxDC = true :=
    (cube_live_held_other bClearU bCube0 6 5 base.xHome xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U hEq (Ne.symm h.shape.xNe5) hxDU hxDC).trans hxHeldU
  have hxArrC : bCube0.sudo_5Board_4home[base.xHome]'hxHC = embed base.x := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq).trans
      (cube_live_home bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
        pkC pkS c1 h5HU h5DU hops1U)
    have hget := arr_get hL base.xHome hxHC
    rw [hget, Array.getElem_set_ne _ ⟨5, h5HU⟩ _ _ (Ne.symm h.shape.xNe5)]
    exact hxArrU
  have hspan2 : 2 * (s.n - 1) < s.benchlen := by
    have hsp := h.shape.peg.span
    have h2 : 2 * (s.n - 1) ≤ 3 * (s.n - 1) :=
      Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)
    exact Nat.lt_of_le_of_lt h2 (Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) hsp)
  have hfitMul := red_mul_move_fit base.moves0 base.R done.length base.n base.bench s.tally
    base.mMax mv mvC mvCube (pegCount (ys.take base.n)) hT hstepR hmvLe hpieceN hCubeLe
    (by
      have hp := hpegY
      rw [h.hn] at hp
      exact hp)
  have hfitSl := red_slide_fit base.slides0 base.R done.length base.n s.tally base.mMax
    sl slC pegX (pegCount (ys.take base.n)) hT hstepR hslLe hpieceS
    (by
      have hp : pegX ≤ s.n := hpegX
      rw [h.hn] at hp
      exact hp)
    (by rw [h.hn] at hpegY; exact hpegY)
  obtain ⟨cSlot0, hcSlot0, hcLe0⟩ := h.ops 0 h0e
  have hcE0eq : cE0 = cSlot0 := ofNat_inj_nat (hcE0.symm.trans hcSlot0)
  have hent0 : cE0 ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [hcE0eq]; exact hcLe0
  have hfitOp0 := mul_ops_fit base.ops0 base.R done.length base.mMax cE0 cC0
    hstepR hent0 h0plus
  have hmulLive := mul_eq_live bCube0 5 base.xHome 6 base.x ys
    base.w base.h base.r s.n s.k mvCube slCube holeC s.benchlen pkU peakSC cC0
    hmkC honC htoC h6HC h6DC (by
      rw [hheldSz]
      exact h7U)
    hempty6 hbenchC
    (by rw [htierC]; exact hnU) h.shape.peg.n_pos hposY hnleY hzeroY
    h.shape.peg.fitN (by rw [hlenY]; exact h.shape.peg.fitBn)
    hmvCubeB hslCubeB hpkU
    (FitsLen.of_le base.fitM (by
      have h2 := hfitMul.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    (FitsLen.of_le base.fitM (by
      have h2 := hfitMul.2.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    (FitsLen.of_le base.fitS (by
      have h2 := hfitSl
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2))
    h0cubeSz hv0 (FitsLen.of_le base.fitO hfitOp0)
    (by rw [htierC]; exact hblU)
    hxDC hxHC hxHeldC hxArrC h.shape.xNe6
    (by rw [h.hn]; exact hxLen) hspan2 hxT
    (FitsLen.of_le h.shape.peg.fit3
      (Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)))
    (FitsLen.of_le base.fitM (by
      have h2 := hfitMul.2.2.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      have hnn : base.n * (base.n + 1) = s.n * (s.n + 1) := by rw [h.hn]
      rw [hidx, hnn] at h2
      exact h2))
    h.shape.w0 h.shape.h0 h.shape.rlt h.shape.r0
    h.shape.n_eq h.shape.k_le h.shape.gap_eq
    (by rw [htierC]; exact hwU) (by rw [htierC]; exact hhU)
    (by rw [htierC]; exact hrU) (by rw [htierC]; exact hkU)
    hholeC hstrictC h.shape.peg.small h.shape.peg.n_small
    h.shape.peg.fitBn
    (FitsLen.of_le base.fitM (by
      have h2 := hfitMul.2.2.2
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      have hnn : base.n * (base.n + 1) = s.n * (s.n + 1) := by rw [h.hn]
      have hsub : base.bench - base.n = s.benchlen - s.n := by rw [h.hn, h.hbench]
      rw [hidx, hnn, hsub] at h2
      exact h2))
  have hRedEq : bRed0 = mulNoLiveBoard bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
      s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz := by
    injection hredU.symm.trans hmulLive
  have hmulOps := mul_live_ops bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
    s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
  have hsettleOps := settle_ops bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
  have hidx0 := settle_ops_lt bCube0 0 6 h0cubeSz h6HC h6DC ys s.n mvCube slCube pkU
  have hstep := ops_set_transport hsettleOps 0 hidx0 h0cubeSz
    (Int.ofNat (cC0 + 1)) (Int.ofNat (cC0 + 1)) rfl
  have hRedOpsB : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops =
      (mulNoLiveBoard bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC s.benchlen
        pkU peakSC cC0 h6HC h6DC h0cubeSz).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hRedEq
  have hRedSet : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops =
      bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0cubeSz⟩ (Int.ofNat (cC0 + 1)) :=
    hRedOpsB.trans (hmulOps.trans hstep)
  let occM1 := countHeld (bCube0.sudo_5Board_4held.set ⟨6, h6DC⟩ true) 7
  let bSM := settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
  let hFsM := settle_held_lt bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
  let occM2 := countHeld (bSM.sudo_5Board_4held.set ⟨6, hFsM⟩ false) 7
  let pkR := raisedPeak (raisedPeak pkU occM1) occM2
  have hpkMul := mul_live_peak bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
    s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
  have hpkRB : bRed0.sudo_5Board_4cost.sudo_5Costs_4peak =
      (mulNoLiveBoard bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC s.benchlen
        pkU peakSC cC0 h6HC h6DC h0cubeSz).sudo_5Board_4cost.sudo_5Costs_4peak :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_4peak) hRedEq
  have hpkR : bRed0.sudo_5Board_4cost.sudo_5Costs_4peak = (pkR : Int) := by
    have hraw := hpkRB.trans hpkMul
    simpa [pkR, occM1, occM2, bSM, hFsM, ofNat_eq_natCast] using hraw
  have hpkRle : pkR ≤ max pk 7 :=
    raised_twice_le pk pkU occM1 occM2 hpkUle (countHeld_seven _) (countHeld_seven _)
  obtain ⟨mvE, mvR, slE, slR, hmvE, hmvR, hmovR, hslE, hslR, hsldR⟩ := hrel
  have hszR : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hRedSet, Array.size_set, hOpsB.trans hOps, Array.size_set, hopsU]
    exact hδ.opsSize
  have hslotsR : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed0.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hszR ▸ hi) = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3) := by
    intro i hi
    have hraw := red_ops_on_clear b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearU.sudo_5Board_4cost.sudo_5Costs_3ops
      bCube0.sudo_5Board_4cost.sudo_5Costs_3ops
      bRed0.sudo_5Board_4cost.sudo_5Costs_3ops
      s.tally base.mMax c1 cC0 hT
      (clearSlots_cast hslots (by
        have hback : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops =
            bClearU.sudo_5Board_4cost.sudo_5Costs_3ops := hopsU.symm
        exact hback))
      (by rw [hOpsB.trans hOps, Array.size_set])
      (by rw [hRedSet, Array.size_set])
      hops1U h0cubeSz hop1U (hOpsB.trans hOps) hv0 hRedSet
    obtain ⟨c, c', hc, hc', hle⟩ := hraw.2 i hi
    refine ⟨c, c', hc, ?_, hle⟩
    exact (array_get_irrel (h1 := hszR ▸ hi)
      (h2 := by rw [hraw.1]; exact hi)).trans hc'
  have hδRed : RungDelta b bRed0 base s.tally :=
    rungDelta_cube_mul hmvE hmvR hmovR hslE hslR hsldR hpk hpkR hpkRle hszR hslotsR
  have hfixC := cube_live_park bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
    pkC pkS c1 h5HU h5DU hops1U
  have hfixM := mul_live_park bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
    s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
  have hparkC : bCube0.sudo_5Board_9park_hole = bClearU.sudo_5Board_9park_hole :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9park_hole) hEq).trans hfixC.1
  have hparkR : bRed0.sudo_5Board_9park_hole = bCube0.sudo_5Board_9park_hole :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9park_hole) hRedEq).trans hfixM.1
  have hparkU : bClearU.sudo_5Board_9park_hole = bClearP.sudo_5Board_9park_hole := by
    rw [hClearEq]; rfl
  have hladC : bCube0.sudo_5Board_7ladder0 = bClearU.sudo_5Board_7ladder0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_7ladder0) hEq).trans hfixC.2.1
  have hladR : bRed0.sudo_5Board_7ladder0 = bCube0.sudo_5Board_7ladder0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_7ladder0) hRedEq).trans hfixM.2.1
  have hladU : bClearU.sudo_5Board_7ladder0 = bClearP.sudo_5Board_7ladder0 := by
    rw [hClearEq]; rfl
  have hnrC : bCube0.sudo_5Board_6nrungs = bClearU.sudo_5Board_6nrungs :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6nrungs) hEq).trans hfixC.2.2.1
  have hnrR : bRed0.sudo_5Board_6nrungs = bCube0.sudo_5Board_6nrungs :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6nrungs) hRedEq).trans hfixM.2.2.1
  have hnrU : bClearU.sudo_5Board_6nrungs = bClearP.sudo_5Board_6nrungs := by
    rw [hClearEq]; rfl
  have ht0C : bCube0.sudo_5Board_6tally0 = bClearU.sudo_5Board_6tally0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6tally0) hEq).trans hfixC.2.2.2.1
  have ht0R : bRed0.sudo_5Board_6tally0 = bCube0.sudo_5Board_6tally0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6tally0) hRedEq).trans hfixM.2.2.2.1
  have ht0U : bClearU.sudo_5Board_6tally0 = bClearP.sudo_5Board_6tally0 := by
    rw [hClearEq]; rfl
  have hmarkR : bRed0.sudo_5Board_9marker_on = false :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9marker_on) hRedEq).trans hfixM.2.2.2.2.1
  have htierR : bRed0.sudo_5Board_1t = bClearU.sudo_5Board_1t := by
    have hM := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hRedEq).trans hfixM.2.2.2.2.2
    exact hM.trans htierC
  have htierP : bClearU.sudo_5Board_1t = bClearP.sudo_5Board_1t := by
    rw [hClearEq]; rfl
  let hFs5 := settle_held_lt bClearU 5 h5HU h5DU xs s.n mvC slC pkC
  have h5set : bCube0.sudo_5Board_4held =
      (settleBoard bClearU 5 h5HU h5DU xs s.n mvC slC pkC).sudo_5Board_4held.set
        ⟨5, hFs5⟩ false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hEq
    have hlive := cube_live_held bClearU 6 5 xs s.n s.k mvC slC holeN s.benchlen
      pkC pkS c1 h5HU h5DU hops1U
    simpa [hFs5] using hB.trans hlive
  have h5DC : 5 < bCube0.sudo_5Board_4held.size := by
    rw [h5set, Array.size_set, settle_held_eq, Array.size_set, hheldU]
    exact h5D
  have h5fC : bCube0.sudo_5Board_4held[5]'h5DC = false := by
    have hget := arr_get h5set 5 h5DC
    rw [hget]
    exact Array.getElem_set_eq _ ⟨5, hFs5⟩ false rfl _
  have hhomeRsz : bRed0.sudo_5Board_4home.size = bCube0.sudo_5Board_4home.size := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq).trans
      (mul_live_home bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
        s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz)
    have hs := congrArg Array.size hL
    rw [Array.size_set] at hs
    exact hs
  have h6HR : 6 < bRed0.sudo_5Board_4home.size := by rw [hhomeRsz]; exact h6HC
  let hFsR := settle_held_lt bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
  have hheldSet : bRed0.sudo_5Board_4held =
      (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.set
        ⟨6, hFsR⟩ false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hRedEq
    have hlive := mul_live_held bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
      s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
    simpa [hFsR] using hB.trans hlive
  have hheldRsz : bRed0.sudo_5Board_4held.size = bCube0.sudo_5Board_4held.size := by
    rw [hheldSet, Array.size_set, settle_held_eq, Array.size_set]
  have h6DR : 6 < bRed0.sudo_5Board_4held.size := by rw [hheldRsz]; exact h6DC
  have h7R : 7 ≤ bRed0.sudo_5Board_4held.size := by
    rw [hheldRsz, hheldSz, hheldU]
    exact h7E
  have h6fR : bRed0.sudo_5Board_4held[6]'h6DR = false := by
    have hget := arr_get hheldSet 6 h6DR
    rw [hget]
    exact Array.getElem_set_eq _ ⟨6, hFsR⟩ false rfl _
  have h5DR : 5 < bRed0.sudo_5Board_4held.size :=
    Nat.lt_trans (by decide : (5 : Nat) < 6) h6DR
  have h5fR : bRed0.sudo_5Board_4held[5]'h5DR = false := by
    have hget := arr_get hheldSet 5 h5DR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, hFsR⟩ _ _ (by decide : (6 : Nat) ≠ 5)]
    have hS := settle_held_eq bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
    have hszS : 5 <
        (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]
      exact h5DC
    have hgetS := arr_get hS 5 hszS
    rw [hgetS]
    rw [Array.getElem_set_ne _ ⟨6, h6DC⟩ _ _ (by decide : (6 : Nat) ≠ 5)]
    exact (idx_irrel (h2 := h5DC)).trans h5fC
  have hxDR : base.xHome < bRed0.sudo_5Board_4held.size := by rw [hheldRsz]; exact hxDC
  have hxHR : base.xHome < bRed0.sudo_5Board_4home.size := by rw [hhomeRsz]; exact hxHC
  have hxHeldR : bRed0.sudo_5Board_4held[base.xHome]'hxDR = true := by
    have hget := arr_get hheldSet base.xHome hxDR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, hFsR⟩ _ _ (Ne.symm h.shape.xNe6)]
    have hS := settle_held_eq bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
    have hszS : base.xHome <
        (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]
      exact hxDC
    have hgetS := arr_get hS base.xHome hszS
    rw [hgetS]
    rw [Array.getElem_set_ne _ ⟨6, h6DC⟩ _ _ (Ne.symm h.shape.xNe6)]
    exact (idx_irrel (h2 := hxDC)).trans hxHeldC
  have hxArrR : bRed0.sudo_5Board_4home[base.xHome]'hxHR = embed base.x := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq).trans
      (mul_live_home bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
        s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz)
    have hget := arr_get hL base.xHome hxHR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, h6HC⟩ _ _ (Ne.symm h.shape.xNe6)]
    exact (idx_irrel (h2 := hxHC)).trans hxArrC
  have hkeepR : CellKeep bRed0 base.xHome base.x :=
    { heldLt := hxDR, held := hxHeldR, homeLt := hxHR, arr := hxArrR }
  have hstrictR : ∃ p : Nat,
      bRed0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int) := by
    let occ := countHeld
      (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held 7
    refine ⟨raisedPeak peakSC occ, ?_⟩
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hRedEq
    have hlive := mul_live_strict bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
      s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
    simpa [occ, ofNat_eq_natCast] using hB.trans hlive
  have hholeR : ∃ holeR : Nat,
      bRed0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeR : Int) := by
    let holeR := raisedHole holeC (topIdx
      (school s.n base.x (ys.take s.n) (List.replicate s.benchlen 0) false))
    refine ⟨holeR, ?_⟩
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hRedEq
    have hlive := mulLive_hole bCube0 5 6 base.x ys s.n s.k mvCube slCube holeC
      s.benchlen pkU peakSC cC0 h6HC h6DC h0cubeSz
    simpa [holeR, ofNat_eq_natCast] using hB.trans hlive
  exact {
    delta := hδRed
    park := hparkR.trans (hparkC.trans hparkU)
    ladder := hladR.trans (hladC.trans hladU)
    nrungs := hnrR.trans (hnrC.trans hnrU)
    tally0 := ht0R.trans (ht0C.trans ht0U)
    marker := hmarkR
    tier := htierR.trans htierP
    home6 := h6HR
    held6 := h6DR
    held7 := h7R
    empty5 := (idx_irrel (h2 := h5DR)).trans h5fR
    empty6 := h6fR
    keep := hkeepR
    strict := hstrictR
    hole := hholeR }
/-- Idle non-final red rung. The parked clear is the unparked clear with the
    park row and a counter `2` higher. `tally_double` and `tally_add_one` keep
    that offset. The spare cube and the mul by the input are `withPark` of the
    unparked results, on the doubled park row. -/
theorem red_open_emit
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rest ≠ [])
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ bAdd,
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok bAdd ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + 2 + 3 * s.tally + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_9tally_len = ((2 * s.tally + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((s.t0 + 2 * s.tally : Nat) : Int) ∧
      bAdd.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bAdd.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_3row =
        embed (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false).row ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        ((2 * s.tally + 1 : Nat) : Int) ∧
      RungDelta b bAdd base s.tally ∧
      ∃ (bClearP bClearU bCube bR : Ecbs.Board),
        bAdd.sudo_5Board_4cost.sudo_5Costs_5moves =
          bR.sudo_5Board_4cost.sudo_5Costs_5moves ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_6slides =
          bR.sudo_5Board_4cost.sudo_5Costs_6slides ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_3ops =
          bR.sudo_5Board_4cost.sudo_5Costs_3ops ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_4peak =
          bR.sudo_5Board_4cost.sudo_5Costs_4peak ∧
        bAdd.sudo_5Board_4held = bR.sudo_5Board_4held ∧
        bAdd.sudo_5Board_4home = bR.sudo_5Board_4home ∧
        bAdd.sudo_5Board_5bench = bR.sudo_5Board_5bench ∧
        bAdd.sudo_5Board_8bench_on = bR.sudo_5Board_8bench_on ∧
        bAdd.sudo_5Board_8bench_to = bR.sudo_5Board_8bench_to ∧
        bAdd.sudo_5Board_9marker_on = bR.sudo_5Board_9marker_on ∧
        bAdd.sudo_5Board_1t = bR.sudo_5Board_1t ∧
        bAdd.sudo_5Board_7ladder0 = bR.sudo_5Board_7ladder0 ∧
        bAdd.sudo_5Board_6nrungs = bR.sudo_5Board_6nrungs ∧
        bAdd.sudo_5Board_9park_hole = bR.sudo_5Board_9park_hole ∧
        bAdd.sudo_5Board_6tally0 = bR.sudo_5Board_6tally0 ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
          bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
          bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
        bClearP = withPark bClearU
          (embed (paintRed (afterPark s.row (-1) s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (((s.ctrl + 2 + s.tally : Nat) : Int))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)) ∧
        RungDelta b bClearP base s.tally ∧
        ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
          bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
        (∃ (mvE mvR slE slR : Nat),
          b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
          bR.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
          mvR ≤ mvE + rungCharge base.n base.bench s.tally ∧
          b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
          bR.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
          slR ≤ slE + rungSlideCharge base.n s.tally) ∧
        bClearP.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
        bClearP.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
        bClearP.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
        bClearP.sudo_5Board_6tally0 = (s.t0 : Int) ∧
        bClearP.sudo_5Board_9marker_on = false ∧
        bClearP.sudo_5Board_1t = b.sudo_5Board_1t ∧
        bR.sudo_5Board_8bench_on = true ∧
        bR.sudo_5Board_8bench_to = (5 : Int) ∧
        bR.sudo_5Board_9tally_len = (s.tally : Int) ∧
        bR.sudo_5Board_6tally0 = (s.t0 : Int) ∧
        bR.sudo_5Board_5bench =
          embed (fieldMul s.n s.k s.benchlen base.x
            (fieldCube s.n s.k s.benchlen
              (fieldMul s.n s.k s.benchlen s.gap
                (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
            List.replicate (s.benchlen - s.n) 0) ∧
        RedCarry b bR bClearP base s.tally base.xHome base.x := by

  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, _hlenC, _ht0C, _hrowC,
      _hctrlN, _hhighC, _hctrlC, _hmaxC, ht0Red, _htierRed, hcubeBoth, hmulBoth,
      hrel, honR, htoR, hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE,
      ht0E, hmarkE, htierE, _htmaxE, hcubeU, hredU, hbonE, htoE, hbenchE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, hopsE, hc1E, hpkSE, hholeE,
      htrits, hpieceM, hpieceS⟩ :=
    red_open_view h hF hm hT hhome hxLen hxT
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hge
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax0, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax0 < 2 * s.tally := hNote0 hm
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) := double_len_fit hn0 hRpos hT base.fitM
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hCtrlU := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hfitCU : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hCtrlU.1 (by omega)
  have hfitCP : FitsLen (s.ctrl + s.tally + 2 + 2 * s.tally) := by
    rw [show s.ctrl + s.tally + 2 + 2 * s.tally = s.ctrl + 2 + 3 * s.tally by omega]
    exact hfits.1
  let xs := paintRed s.row s.t0 s.tally
  let xsP := paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
  have htwo : 2 * s.tally = s.tally + s.tally := Nat.two_mul s.tally
  have hle2 : s.t0 + s.tally ≤ s.t0 + 2 * s.tally := by
    rw [htwo]
    exact Nat.add_le_add_left (Nat.le_add_left s.tally s.tally) s.t0
  have hsumEq : (s.t0 + s.tally) + s.tally = s.t0 + 2 * s.tally := by
    rw [Nat.add_assoc, ← htwo]
  have hixHalf (k : Nat) (hk : k < s.tally) : s.t0 + s.tally + k < s.row.length := by
    rw [h.shape.rowLen]
    have hassoc : s.t0 + s.tally + k = s.t0 + (s.tally + k) := Nat.add_assoc _ _ _
    have hlt : s.t0 + (s.tally + k) < s.t0 + (s.tally + s.tally) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left hk s.tally) s.t0
    have h2 : s.t0 + (s.tally + s.tally) = s.t0 + 2 * s.tally := by rw [← htwo]
    have hlt' : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by
      rw [hassoc, ← h2]
      exact hlt
    exact Nat.lt_of_lt_of_le hlt' hRoom
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        dsimp only [xs]
        rw [paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    exact paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hRedP : ∀ j (hj : j < s.tally),
      xsP[s.t0 + j]'(by
        dsimp only [xsP]
        rw [paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    exact paintRed_get_lo (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        dsimp only [xs]
        rw [paintRed_length]
        exact hixHalf k hk) = 0 := by
    intro k hk
    have hsrc := h.openZero hge k hk (hixHalf k hk)
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (Nat.le_add_right _ k) (hixHalf k hk)
    dsimp only [xs]
    exact hget.trans hsrc
  have hZeroP : ∀ k (hk : k < s.tally),
      xsP[s.t0 + s.tally + k]'(by
        dsimp only [xsP]
        rw [paintRed_length, afterPark_length]
        exact hixHalf k hk) = 0 := by
    intro k hk
    have hleJ : s.t0 ≤ s.t0 + s.tally + k :=
      Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow hleJ)
      (Nat.lt_of_lt_of_le h.holeBelow hleJ)
      (Or.inl (by decide)) (hixHalf k hk)
    have hget := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (Nat.le_add_right _ k)
      (by rw [afterPark_length]; exact hixHalf k hk)
    have hsrc := h.openZero hge k hk (hixHalf k hk)
    dsimp only [xsP]
    exact hget.trans (hAp.trans hsrc)
  have hctrlPark :
      (((s.ctrl + 2 + s.tally : Nat) : Int)) = ((s.ctrl + s.tally + 2 : Nat) : Int) := by
    apply congrArg Int.ofNat
    omega
  have hdouble := tally_double_withPark bClearU xs xsP s.t0 s.tally (s.ctrl + s.tally)
    (s.t0 + s.tally - 1) base.control tmax0 fromH ridxH
    hm _hlenC _ht0C _hrowC
    (by dsimp only [xs]; rw [paintRed_length, h.shape.rowLen]; exact hRoom)
    (by dsimp only [xsP]; rw [paintRed_length, afterPark_length, h.shape.rowLen]; exact hRoom)
    hRed hRedP hZero hZeroP _hctrlN (by rw [_hhighC, hHighEq]) rfl
    _hctrlC hRoom hFitI hfitCU hfitCP hFitM (by rw [_hmaxC]; exact hMax) hNote
  have hClear0 := hClearEq
  rw [hctrlPark] at hClearEq
  rw [← hClearEq] at hdouble
  let rowD := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let rowP := embed (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let lenD := Int.ofNat (2 * s.tally)
  let ctrlD := Int.ofNat (s.ctrl + s.tally + 2 * s.tally)
  let highD := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
  let maxD := Int.ofNat (2 * s.tally)
  let ctrlP := Int.ofNat (s.ctrl + s.tally + 2 + 2 * s.tally)
  have hcube := hcubeBoth rowD rowP lenD highD maxD ctrlD ctrlP fromH ridxH
  have hmul := hmulBoth rowD rowP lenD highD maxD ctrlD ctrlP fromH ridxH
  -- The double result is the withPark form hcube reads.
  have hDoubleForm :
      Ecbs.tally_double bClearP =
        .ok (withPark (withTally bClearU rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) := by
    dsimp only [rowD, rowP, lenD, ctrlD, highD, maxD, ctrlP, xs, xsP, withTally, hole]
    exact hdouble
  have hcubeRun :
      Ecbs.cube (withPark (withTally bClearU rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark (withTally bCube0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) :=
    hcube
  have hmulRun :
      Ecbs.mul (withPark (withTally bCube0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int) false false false =
        .ok (withPark (withTally bRed0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) :=
    hmul
  let bRedP := withPark (withTally bRed0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH
  have hPast : s.t0 + 2 * s.tally < base.control := by
    have hfit := h.tailFit
    have hgrow := red_final_gt s.tally r rest hr hrest
    have hwhole : climbTally s.tally (r :: rest) =
        climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [h.htally0]
      exact climbTally_prefix_rest base.tally0 done (r :: rest)
    rw [h.shape.rowLen] at hfit
    have hlt : 2 * s.tally < climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [← hwhole]; exact hgrow
    omega
  have hixP : s.t0 + 2 * s.tally < rowP.size := by
    dsimp only [rowP]
    rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length,
      h.shape.rowLen]
    exact hPast
  have hzeroCell : rowP[s.t0 + 2 * s.tally]'hixP = 0 := by
    have hwide := paintOnes_get_hi (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally
      (s.t0 + 2 * s.tally) (Nat.le_of_eq hsumEq)
      (by dsimp only [xsP]; rw [paintOnes_length, paintRed_length, afterPark_length, h.shape.rowLen]; exact hPast)
    have hmid := paintOnes_get_hi xsP s.t0 s.tally (s.t0 + 2 * s.tally) hle2
      (by dsimp only [xsP]; rw [paintRed_length, afterPark_length, h.shape.rowLen]; exact hPast)
    have hred := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + 2 * s.tally) hle2
      (by rw [afterPark_length, h.shape.rowLen]; exact hPast)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + 2 * s.tally)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inl (by decide)) (by rw [h.shape.rowLen]; exact hPast)
    have htail := h.tailZero (2 * s.tally) (by omega)
      (by
        have hgrow := red_final_gt s.tally r rest hr hrest
        have hwhole : climbTally s.tally (r :: rest) =
            climbTally base.tally0 (done ++ (r :: rest)) := by
          rw [h.htally0]
          exact climbTally_prefix_rest base.tally0 done (r :: rest)
        rw [← hwhole]; exact hgrow)
      (by rw [h.shape.rowLen]; exact hPast)
    have hrowIx : s.t0 + 2 * s.tally < s.row.length := by
      rw [h.shape.rowLen]; exact hPast
    have hlist0 :
        (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally)[s.t0 + 2 * s.tally]'(by
          rw [paintOnes_length, paintOnes_length]
          dsimp only [xsP]
          rw [paintRed_length, afterPark_length]
          exact hrowIx) = 0 :=
      hwide.trans (hmid.trans (hred.trans (hAp.trans htail)))
    dsimp only [rowP, embed]
    rw [Array.getElem_mk, List.getElem_map, hlist0]
    rfl
  have hAdd := tally_add_one_withPark
      (withTally bRed0 rowD lenD ctrlD highD maxD) s.t0 (2 * s.tally)
      (s.t0 + 2 * s.tally - 1) base.control (s.ctrl + s.tally + 2 * s.tally) (2 * s.tally)
      rowP fromH ridxH
      (by simp [withTally, lenD]) (by simp [withTally, ht0Red])
      (by
        rw [withTally_row]
        dsimp only [rowD]
        rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, h.shape.rowLen]
        exact hPast)
      hixP
      (by
        have hwide := paintOnes_get_hi (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
          (s.t0 + 2 * s.tally) (Nat.le_of_eq hsumEq)
          (by dsimp only [xs]; rw [paintOnes_length, paintRed_length, h.shape.rowLen]; exact hPast)
        have hmid := paintOnes_get_hi xs s.t0 s.tally (s.t0 + 2 * s.tally) hle2
          (by dsimp only [xs]; rw [paintRed_length, h.shape.rowLen]; exact hPast)
        have hred := paintRed_get_hi s.row s.t0 s.tally (s.t0 + 2 * s.tally) hle2
          (by rw [h.shape.rowLen]; exact hPast)
        have htail := h.tailZero (2 * s.tally) (by omega)
          (by
            have hgrow := red_final_gt s.tally r rest hr hrest
            have hwhole : climbTally s.tally (r :: rest) =
                climbTally base.tally0 (done ++ (r :: rest)) := by
              rw [h.htally0]
              exact climbTally_prefix_rest base.tally0 done (r :: rest)
            rw [← hwhole]; exact hgrow)
          (by rw [h.shape.rowLen]; exact hPast)
        have hlist0 :
            (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)[s.t0 + 2 * s.tally]'(by
              rw [paintOnes_length, paintOnes_length]
              dsimp only [xs]
              rw [paintRed_length, h.shape.rowLen]
              exact hPast) = 0 :=
          hwide.trans (hmid.trans (hred.trans htail))
        have hixT : s.t0 + 2 * s.tally <
            (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_3row.size := by
          rw [withTally_row]
          dsimp only [rowD]
          rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, h.shape.rowLen]
          exact hPast
        have harr : rowD[s.t0 + 2 * s.tally]'(by
            dsimp only [rowD]
            rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, h.shape.rowLen]
            exact hPast) = 0 := by
          dsimp only [rowD, embed]
          rw [Array.getElem_mk, List.getElem_map, hlist0]
          rfl
        exact (getElem_congr_coll
          (c := (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_3row)
          (d := rowD) (i := s.t0 + 2 * s.tally) (h := hixT)
          (withTally_row _ _ _ _ _ _)).trans harr)
      hzeroCell
      (by simp [withTally, _htierRed, _hctrlN]) hPast
      (by simp [withTally, highD]) (by omega) hFitI
      (by simp [withTally, ctrlD]) (FitsLen.of_le hCtrlU.2 (by omega))
      (by
        have h1 : FitsLen (s.ctrl + 2 + 3 * s.tally + 1) := by
          have hpos : 1 ≤ 2 * s.tally :=
            Nat.le_trans hm (by rw [Nat.two_mul]; exact Nat.le_add_left s.tally s.tally)
          exact FitsLen.of_le hfits.2.2.2
            (Nat.add_le_add_left hpos (s.ctrl + 2 + 3 * s.tally))
        have hsame : s.ctrl + s.tally + 2 * s.tally + 2 + 1 =
            s.ctrl + 2 + 3 * s.tally + 1 := by omega
        exact hsame.symm ▸ h1)
      hFitL1 (by simp [withTally, maxD]) (by omega)
  have hctrlOut : ((s.ctrl + s.tally + 2 * s.tally + 2 : Nat) : Int) = ctrlP := by
    apply congrArg (fun n : Nat => (n : Int))
    omega
  rw [hctrlOut] at hAdd
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok
        (withPark
          { withTally bRed0 rowD lenD ctrlD highD maxD with
              sudo_5Board_3row :=
                (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_3row.set
                  ⟨s.t0 + 2 * s.tally, by
                    rw [withTally_row]
                    dsimp only [rowD]
                    rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length,
                      h.shape.rowLen]
                    exact hPast⟩ (1 : Int)
              sudo_5Board_9tally_len := Int.ofNat (2 * s.tally + 1)
              sudo_5Board_4cost :=
                { (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_4cost with
                    sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally : Nat) : Int)
                    sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 1)
                    sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally + 1) } }
          (rowP.set ⟨s.t0 + 2 * s.tally, hixP⟩ (1 : Int))
          (Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 2 + 1))
          fromH ridxH) := by
    rw [hrun, ok_bind, hDoubleForm, ok_bind, hcubeRun, ok_bind, hmulRun, ok_bind]
    simpa [bRedP] using hAdd
  have hpack :=
    red_unparked_delta h hm hT hhome hxLen hxT
      bClearP bClearU bCube0 bRed0
      (embed (paintRed (afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
      (Int.ofNat (s.ridx + 1))
      hClear0 hδ hslots hmarkE htierE hcubeU hredU hrel
      hbonE htoE hbenchE h5H h5D h6H h6D h7E h5f h6f hkeep hopsE hc1E hpkSE hholeE
      htrits hpieceM hpieceS
  have hδRed : RungDelta b bRed0 base s.tally := hpack.delta
  refine ⟨_, hprog, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [withPark, withTally, ctrlD]
    omega
  · simp [withPark, withTally, lenD]
  · simp [withPark, withTally]
  · simp [withPark, fromH]
  · simp [withPark, ridxH]
  · rw [withPark_row]
    have hFrom : s.fromHole = -1 := h.shape.park.fromIdle hF
    obtain ⟨_, _, _, _, _, _, hrowM, _, _, _, _, _, _, _⟩ :=
      model_open_red s base.x r hole hr hF
    let xsL := paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally
    have hlist : xsL.set (s.t0 + 2 * s.tally) 1 =
        (modelRung s base.x r hole false).row := by
      simpa [xsL, xsP, hFrom, hole] using hrowM.symm
    have hlenL : s.t0 + 2 * s.tally < xsL.length := by
      dsimp only [xsL]
      rw [paintOnes_length, paintOnes_length]
      dsimp only [xsP]
      rw [paintRed_length, afterPark_length, h.shape.rowLen]
      exact hPast
    have hrowP : rowP = embed xsL := by simp [rowP, xsL]
    have hixL : s.t0 + 2 * s.tally < (embed xsL).size := by
      rw [size_embed]; exact hlenL
    rw [show (1 : Int) = Int.ofNat 1 from rfl]
    rw [arr_set_congr hrowP (s.t0 + 2 * s.tally) hixP (Int.ofNat 1)]
    rw [array_set_idx (h1 := hrowP ▸ hixP) (h2 := hixL)]
    rw [embed_set xsL (s.t0 + 2 * s.tally) 1 hlenL, hlist]
  · rw [withPark_tmax]
    rfl
  · exact rungDelta_cost hδRed
      (by rw [withPark_moves, withTally_moves])
      (by rw [withPark_slides, withTally_slides])
      (by rw [withPark_ops, withTally_ops])
      (by rw [withPark_peak, withTally_peak])
  · refine ⟨bClearP, bClearU, bCube0, bRed0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hClear0, hδ, hslots, hrel, hladE, hnrE, hparkE, ht0E, hmarkE, htierE,
      honR, htoR, hlenR, ht0Red, hbenchR, hpack⟩
    · rw [withPark_moves]; rfl
    · rw [withPark_slides]; rfl
    · rw [withPark_ops]; rfl
    · rw [withPark_peak]; rfl
    · rw [withPark_held]; rfl
    · rw [withPark_home]; rfl
    · rw [withPark_bench]; rfl
    · rw [withPark_on]; rfl
    · rw [withPark_to]; rfl
    · rw [withPark_marker]; rfl
    · rw [withPark_tier]; rfl
    · rw [withPark_ladder]; rfl
    · rw [withPark_nrungs]; rfl
    · rw [withPark_park]; rfl
    · rw [withPark_tally0]; rfl
    · rw [withPark_strict]; rfl
    · rw [withPark_hole]; rfl

/-- Idle non-final red rung. Park through the clear, the double, the spare cube,
    the mul by the input, and the extra peg. The cost is the unparked
    `RungDelta`: park, the double, and the peg do not add moves, slides, or
    ops, and they do not change peak. -/
theorem red_open_k
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rest ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok b' ∧
      ClimbInvK (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base ∧
      RungDelta b b' base s.tally := by
  obtain ⟨bAdd, hprog, hctrlA, hlenA, hhighA, hfromA, hridxA, hrowA, htmaxA, hδA,
      _bCP, _bCU, _bC, _bR,
      _hmvA, _hslA, _hopsA, _hpkA,
      hheldA, hhomeA, hbenchA, honA, htoA, hmarkA, htierA,
      hladA, hnrA, hparkA, ht0A, hstrictA, hholeA,
      _hClear, _hδC, _hslots, _hrel,
      hladE, hnrE, hparkE, _ht0E, _hmarkE, htierE,
      honR, htoR, _hlenR, ht0R, hbenchR, hcarry⟩ :=
    red_open_emit h hF hm hT hhome hr hrest hxLen hxT
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_open_red s base.x r hole hr hF
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_red_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, List.length_set, paintOnes_length, paintOnes_length, paintRed_length,
      afterPark_length]
  have htierB : bAdd.sudo_5Board_1t = b.sudo_5Board_1t :=
    (htierA.trans hcarry.tier).trans htierE
  have hinv : ClimbInv bAdd s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := hmarkA.trans hcarry.marker
        len := hlenA.trans (congrArg (fun n : Nat => (n : Int)) htall.symm)
        ctrl := hctrlA.trans (congrArg (fun n : Nat => (n : Int)) hctrlM.symm)
        high := hhighA.trans (congrArg (fun n : Nat => (n : Int)) hhighM.symm)
        t0 := (ht0A.trans ht0R).trans (congrArg (fun n : Nat => (n : Int)) ht0M.symm)
        row := hrowA
        park := (hparkA.trans (hcarry.park.trans hparkE)).trans
          (congrArg (fun n : Nat => (n : Int)) hparkM.symm)
        fromP := hfromA.trans hfromM.symm
        ridx := hridxA.trans (congrArg (fun n : Nat => (n : Int)) hridxM.symm)
        gapHome := ?_
        gapBench := ?_ }
    · rw [hhomeA]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.home6
    · rw [hheldA]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.held6
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      refine ⟨honA.trans honR, htoA.trans htoR, ?_, hwork.trans hgap.symm⟩
      have hnle := span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
      have hlenG := fieldMul_len s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
      rw [hbenchA, hbenchR, hgap, hnM, hbM,
        List.take_of_length_le (Nat.le_of_eq hlenG)]
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hPast : s.t0 + 2 * s.tally < s.row.length := by
    have hgrow := red_final_gt s.tally r rest hr hrest
    have hwhole : climbTally s.tally (r :: rest) =
        climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [h.htally0]
      exact climbTally_prefix_rest base.tally0 done (r :: rest)
    have hlt : 2 * s.tally < climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [← hwhole]
      exact hgrow
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt s.t0) h.tailFit
  have hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty := by
    rw [hempty]
    have hrowS : s'.row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
      simp [s', modelRung, hr]
    have hseg0 : RowSeg s.row s.t0 s.tally false := by
      simpa using h.shape.seg
    rw [hrowS, ht0M, htall]
    exact rungRow_open_red_seg s.row s.fromHole s.parkAt hole s.t0 s.tally
      hseg0 h.parkBelow h.holeBelow (Or.inl hF) hPast
  have hpark' : ParkRead bAdd s' rest base := by
    refine
      { ladder0B := by rw [hladA, hcarry.ladder, hladE]; exact h.shape.park.ladder0B
        nrungsB := by rw [hnrA, hcarry.nrungs, hnrE]; exact h.shape.park.nrungsB
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · have hL : bAdd.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [hladA, hcarry.ladder, hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : bAdd.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrA, hcarry.nrungs, hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines bAdd base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      exact Nat.le_trans (Nat.le_of_lt h.parkBelow) (Nat.le_add_right s.t0 (2 * s.tally))
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _
      rw [hfromM]
      rfl
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · rw [hhighM]
        simpa [Int.toNat_ofNat] using
          Nat.le_trans (Nat.le_of_lt h.holeBelow) (Nat.le_add_right s.t0 (2 * s.tally))
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rs hrs
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail 1 (by simp [hrs]) hlt0
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1) < s.t0 :=
        climb_below base.ladder0 base.R s.ridx 1 s.t0 h.shape.park.l0pos
          (by omega) h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
      have hget := rungRow_red_below s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1)) hF hneP hneH hbelow hlt0
      have hrowR : s'.row =
          rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
        simp [s', modelRung, hr]
      have hhead : (r :: rest)[1]'(by simp [hrs]) = r2 := by simp [hrs]
      refine ⟨?_, ?_⟩
      · simpa [hrowR, hridxM, hhead] using hget.trans hcol
      · simpa [hhead] using hnz
    · intro k hk hlt
      have hoff : s.ridx + (1 + k) ≤ base.R := by
        rw [h.idx]
        have hlen := h.kLe
        simp [List.length_append, List.length_cons] at hlen
        omega
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.row.length := by
        rw [← hlenRow, ← hridxM]
        exact hlt
      have hltTail : climbAt base.ladder0 base.R (s.ridx + (1 + k)) < s.row.length := by
        simpa [Nat.add_assoc] using hlt0
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail (1 + k) (by simp; omega) hltTail
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.t0 := by
        simpa [Nat.add_assoc] using
          (climb_below base.ladder0 base.R s.ridx (1 + k) s.t0 h.shape.park.l0pos hoff
            h.holeBelow)
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1 + k) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        intro heq
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        simp [hole, climbAt] at heq
        omega
      have hget := rungRow_red_below s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hF hneP hneH hbelow hlt0
      have hrowR : s'.row =
          rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
        simp [s', modelRung, hr]
      refine ⟨?_, ?_⟩
      · have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
            climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
          rw [hridxM]
        have hmove := getElem_congr (c := s'.row)
          (i := climbAt base.ladder0 base.R (s'.ridx + k))
          (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := hlt) hixEq
        have hcoll := getElem_congr_coll (c := s'.row)
          (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := by rw [← hixEq]; exact hlt) hrowR
        have hlist := cons_tail r rest k hk
        exact hmove.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((cons_tail r rest k hk).trans hz)
    · rw [hctrlM]
      exact hfits.1
    · rw [hctrlM]
      exact hfits.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  have hnleG := span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen base.x
      (fieldCube s.n s.k s.benchlen
        (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnleG
  have hpeg : PegRead bAdd s' base := by
    refine
      { opsGt := ?_
        cOps := ?_
        peakS := ?_
        holeM := ?_
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · rw [hδA.opsSize]
      exact h.shape.peg.opsGt
    · have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
      obtain ⟨_, c', _, hc', _⟩ := hδA.ops 1 h1
      refine ⟨c', ?_⟩
      exact (array_get_irrel (h2 := hδA.opsSize ▸ h1)).trans hc'
    · obtain ⟨p, hp⟩ := hcarry.strict
      exact ⟨p, hstrictA.trans hp⟩
    · obtain ⟨hn, hh⟩ := hcarry.hole
      exact ⟨hn, hholeA.trans hh⟩
    · rw [hgap]
      have h3 : 3 * (s.n - 1) < s.benchlen :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) h.shape.peg.span
      have hlenC : (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))).length ≤ s.n := by
        rw [fieldCube, List.length_take]
        exact Nat.min_le_left _ _
      rw [← List.take_of_length_le hlenC]
      exact fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) h3 hnleG
    · intro _
      rw [ht0M, htall, hhighM]
      exact open_red_high s.t0 s.tally
    · rw [ht0M, htall]
      exact open_red_row_fit s.t0 s.tally base.control (h.openRoom hge) base.fitControl
    · rw [htall]
      exact (double_index_fit_le (h.openRoom hge) base.fitControl).2.2
    · rw [hctrlM, htall]
      exact hfits.2.2
    · rw [hnM]
      exact h.shape.peg.n_pos
    · rw [hnM, hbM]
      exact h.shape.peg.span
    · rw [hbM]
      exact h.shape.peg.small
    · rw [hnM]
      exact h.shape.peg.n_small
    · rw [hnM]
      exact h.shape.peg.fitN
    · rw [hbM]
      exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hshape : ClimbShape bAdd s' rest base :=
    shape_refresh h.shape bAdd s' rest hnM hkM hbM hgapLen hseg
      (by rw [hheldA]; exact hcarry.held6)
      (by rw [hhomeA]; exact hcarry.home6)
      (by exact cell_eq_of hheldA hcarry.empty6)
      (by rw [hheldA]; exact hcarry.held7)
      (by intro _; exact cell_eq_of hheldA hcarry.empty5)
      (by intro hOff; rw [hon] at hOff; cases hOff)
      (by rw [hheldA]; exact hcarry.keep.heldLt)
      (by rw [hhomeA]; exact hcarry.keep.homeLt)
      (by exact cell_eq_of hheldA hcarry.keep.held)
      (by exact cell_eq_of hhomeA hcarry.keep.arr)
      (by rw [htierB, hnM]; exact h.shape.tierN)
      (by rw [htierB, hkM]; exact h.shape.tierK)
      (by rw [htierB, hbM]; exact h.shape.tierB)
      (by rw [htierB]; exact h.shape.tierW)
      (by rw [htierB]; exact h.shape.tierH)
      (by rw [htierB]; exact h.shape.tierR)
      (by rw [htierB]; exact h.shape.tierCg)
      (by rw [htierB]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg
  have htmax : ∃ tmax : Nat,
      bAdd.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally + 1, htmaxA, ?_⟩
    intro _
    rw [htall]
    exact open_red_tmax_lt s.tally
  have hK := climbInvK_succ h (by simpa [hempty] using hinv) hδA hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax) rfl
  exact ⟨bAdd, hprog, by simpa [hempty] using hK, hδA⟩

/-- Ops after the red cube and the red mul, read off the idle clear. The cube
    writes slot 1 and the mul writes slot 0. -/
theorem red_rung_ops {b bClear bCube bRed : Ecbs.Board} {base : ClimbBudget} {tally : Nat}
    (ht : tally ≤ base.mMax)
    (hs : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops tally)
    (hcost : ∃ (v1 v0 : Nat)
        (h1 : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (h0 : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (v1 : Int) ∧
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops =
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, h1⟩ (Int.ofNat (v1 + 1)) ∧
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0 = (v0 : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_3ops =
        bCube.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0⟩ (Int.ofNat (v0 + 1))) :
    bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
    ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hi' : i < bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi' = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3) := by
  obtain ⟨v1, v0, h1, h0, hv1, hcube, hv0, hmul⟩ := hcost
  have hszU : bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hcube, Array.size_set]
  have hszR : bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hmul, Array.size_set]
  have hraw := red_ops_on_clear b.sudo_5Board_4cost.sudo_5Costs_3ops
    bClear.sudo_5Board_4cost.sudo_5Costs_3ops
    bCube.sudo_5Board_4cost.sudo_5Costs_3ops
    bRed.sudo_5Board_4cost.sudo_5Costs_3ops
    tally base.mMax v1 v0 ht hs hszU hszR h1 h0 hv1 hcube hv0 hmul
  refine ⟨hraw.1, ?_⟩
  intro i hi hi'
  obtain ⟨c, c', hc, hc', hle⟩ := hraw.2 i hi
  refine ⟨c, c', hc, ?_, hle⟩
  exact (array_get_irrel (h1 := hi') (h2 := by rw [hszR, hszU, hs.size]; exact hi)).trans hc'

/-- Idle non-final red rung is a `ClimbInvK` successor. Costs are the unparked
    red board's costs: park, the double, and the extra peg do not add moves,
    slides, or ops, and they do not change peak. -/
theorem rungDelta_withPark {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m) (row : Array Int) (ctrl fromHole ridx : Int) :
    RungDelta b (withPark b1 row ctrl fromHole ridx) base m := by
  obtain ⟨hmv, hsl, hops, hpk⟩ := withPark_counters b1 row ctrl fromHole ridx
  exact rungDelta_cost hδ hmv hsl hops hpk

/-- Unpark then park, as a list. The restored colour is the one that was sitting
    in the parking hole. -/
theorem afterPark_resume (row : List Nat) (src park hole colour prev : Nat)
    (hsrc : src < row.length) (hpark : park < row.length) (hprev : row[park]'hpark = prev) :
    afterPark row (src : Int) park hole colour =
      (((row.set src prev).set park 0).set park colour).set hole 0 := by
  have hnn : ¬ ((src : Int) < 0) := fun hlt => by
    have : (0 : Int) ≤ (src : Int) := Int.ofNat_nonneg src
    omega
  unfold afterPark
  simp only [hnn, Int.toNat_ofNat, if_false]
  have hopt : (row[park]?).getD 0 = prev := by
    rw [List.getElem?_eq_getElem hpark]
    simp [hprev]
  simp [hopt]

/-- A rung that is already parked unparks, then parks. The row is `afterPark`
    and the counter grows by 4. Later copy and cube steps are still the idle
    ones on this board; this is only the park those steps start from. -/
theorem resume_park_row
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) :
    ∃ bPark,
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bPark.sudo_5Board_3row =
        embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 4 : Nat) : Int) ∧
      bPark.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bPark.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bPark.sudo_5Board_4home = b.sudo_5Board_4home ∧
      bPark.sudo_5Board_4held = b.sudo_5Board_4held ∧
      bPark.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_4peak =
        b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      ∃ (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
        bPark = withPark
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          (embed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r))
          (((s.ctrl + 4 : Nat) : Int))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let holes := downFrom (base.ladder0 + base.R - 1) base.R
  have hidxN : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hAt : s.ridx < holes.length := by
    simpa [holes, downFromLen] using hidxN
  have hHole : holes[s.ridx] = hole := by
    simpa [holes, hole, climbAt] using
      downFromAt (base.ladder0 + base.R - 1) base.R s.ridx hidxN
  have hrung := h.shape.park.nextRung r rest rfl
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hColour : b.sudo_5Board_3row[hole] = (r : Int) := by
    have harr := arr_get h.inv.row hole hRowH
    have hemb := embed_nat s.row hole h.shape.park.holeLt
    exact harr.trans ((idx_irrel
      (h2 := by rw [size_embed]; exact h.shape.park.holeLt)).trans
      (hemb.trans (congrArg (fun n : Nat => (n : Int)) hrung.1)))
  have hpos : r ≠ 0 := hrung.2
  obtain ⟨prev, hprev⟩ := h.shape.park.parkHeld hge
  have hsrc := h.shape.park.srcOk hge
  have hFrom : b.sudo_5Board_11parked_from = (s.fromHole.toNat : Int) := by
    rw [h.inv.fromP]
    exact h.shape.park.fromNat hge
  have hPrevB : b.sudo_5Board_3row[s.parkAt] = (prev : Int) := by
    have harr := arr_get h.inv.row s.parkAt hRowP
    have hemb := embed_nat s.row s.parkAt h.shape.park.parkLt
    exact harr.trans ((idx_irrel
      (h2 := by rw [size_embed]; exact h.shape.park.parkLt)).trans
      (hemb.trans (congrArg (fun n : Nat => (n : Int)) hprev)))
  have hRowS : s.fromHole.toNat < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact hsrc.1
  have hNat : s.fromHole = (s.fromHole.toNat : Int) := h.shape.park.fromNat hge
  let src := s.fromHole.toNat
  let bU := unparkedBoard b src s.parkAt prev s.ctrl hRowS hRowP
  let bPark :=
    { bU with
      sudo_5Board_3row :=
        ((bU.sudo_5Board_3row.set
            ⟨s.parkAt, by simp [bU, unparkedBoard, Array.size_set]; exact hRowP⟩ (r : Int)).set
          ⟨hole, by simp [bU, unparkedBoard, Array.size_set]; exact hRowH⟩ (0 : Int))
      sudo_5Board_4cost :=
        { bU.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat ((s.ctrl + 2) + 2) }
      sudo_5Board_11parked_from := (hole : Int)
      sudo_5Board_8rung_idx := Int.ofNat (s.ridx + 1) }
  have hres := park_rung_resume b holes s.ridx src hole s.parkAt prev r
    s.high base.control s.ctrl h.shape.park.climbH h.inv.ridx hAt hHole hFrom h.inv.park
    hRowS hRowH hRowP hPrevB hColour hpos h.shape.tierC hsrc.2.1 h.shape.park.parkIn
    h.inv.high hsrc.2.2.1 h.shape.park.parkLe h.inv.ctrl h.shape.park.fit2 h.shape.park.fit4
    h.shape.park.parkNe (Ne.symm hsrc.2.2.2) h.shape.park.fitI
  have hrun : Ecbs.park_rung b (r : Int) = .ok bPark := by
    simpa [bPark, bU, src] using hres
  let bKeep := parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hrowEq : bPark.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt hole r) := by
    have hlist := afterPark_resume s.row src s.parkAt hole r prev
      hsrc.1 h.shape.park.parkLt hprev
    have hfromRow : afterPark s.row s.fromHole s.parkAt hole r =
        afterPark s.row (src : Int) s.parkAt hole r := by
      rw [← hNat]
    rw [hfromRow, hlist]
    apply Array.ext
    · simp [bPark, bU, unparkedBoard, Array.size_set, h.inv.row, size_embed,
        List.length_set]
    · intro j hj1 hj2
      simp [bPark, bU, unparkedBoard, h.inv.row, embed, Array.getElem_set,
        Array.getElem_mk, List.getElem_set, ofNat_eq_natCast, hsrc.1,
        h.shape.park.parkLt, h.shape.park.holeLt]
      by_cases hhj : hole = j
      · simp [hhj]
      · by_cases hpj : s.parkAt = j
        · simp [hhj, hpj]
        · by_cases hsj : src = j
          · simp [hhj, hpj, hsj]
          · simp [hhj, hpj, hsj]
  have hframe : bPark = withPark bKeep
      (embed (afterPark s.row s.fromHole s.parkAt hole r))
      (Int.ofNat ((s.ctrl + 2) + 2))
      (((hole : Nat) : Int))
      (Int.ofNat (s.ridx + 1)) := by
    apply board_ext
    case hrow =>
      rw [hrowEq, withPark_row]
    case hcost =>
      apply cost_ext
      case hctrl =>
        simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
      all_goals
        simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
    all_goals
      simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
  refine ⟨bPark, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrowEq
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark]
  · dsimp [bPark]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · refine ⟨hRowP, hRowH, ?_⟩
    have h4 : Int.ofNat ((s.ctrl + 2) + 2) = ((s.ctrl + 4 : Nat) : Int) := by
      apply congrArg Int.ofNat
      omega
    rw [← h4]
    exact hframe

/-- Unpark-then-park is keep-park of the same board, with the restored row and a
    counter two higher. Later `place`, `settle`, `cube`, `mul`, `tally_double`,
    and `tally_add_one` already commute with `withPark`, so a parked rung is that
    transport of the idle rung. -/
theorem resume_park_withPark
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) :
    ∃ (bPark bKeep : Ecbs.Board)
      (hRowP : s.parkAt < b.sudo_5Board_3row.size)
      (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bKeep = parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
        s.ridx s.ctrl hRowP hRowH ∧
      bPark = withPark bKeep
        (embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r))
        (((s.ctrl + 4 : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) := by
  obtain ⟨bPark, hpark, _hrow, _hctrl, _hfrom, _hridx, _hhome, _hheld, _htier, _hmv, _hpk,
      hRowP, hRowH, hframe⟩ := resume_park_row h hge
  exact ⟨bPark, _, hRowP, hRowH, hpark, rfl, hframe⟩

/-- Park does not write home or held. The spare stays empty and the gap stays
    held at home 5, so the copy is `place` of the gap, as on an idle rung. -/
theorem resume_copy
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (_hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark bCopy : Ecbs.Board) (moves peak : Nat)
      (h6H : 6 < bPark.sudo_5Board_4home.size)
      (h6D : 6 < bPark.sudo_5Board_4held.size),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy ∧
      bCopy = placeBoard bPark 6 h6H h6D s.gap moves peak ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
  obtain ⟨bPark, hpark, _hrow, _hctrl, _hfrom, _hridx, hhomeEq, hheldEq, htierEq, hmvEq, hpkEq,
      _hRowP, _hRowH, _hframe⟩ :=
    resume_park_row h hge
  obtain ⟨mv, hmv, hmvLe⟩ := h.moves
  obtain ⟨pk, hpk, _hpkLe⟩ := h.peak
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    rw [hhomeEq]; exact h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.shape.spareD
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    rw [hhomeEq]; exact h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.inv.hGs
  have h7 : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.shape.h7
  have hheld5 : bPark.sudo_5Board_4held[5]'h5D = true :=
    cell_eq_of hheldEq (h.inv.gapHome hhome).1
  have harr5 : bPark.sudo_5Board_4home[5]'h5H = embed s.gap :=
    cell_eq_of hhomeEq (h.inv.gapHome hhome).2
  have hempty : bPark.sudo_5Board_4held[6]'h6D = false :=
    cell_eq_of hheldEq h.shape.spareE
  have hn : bPark.sudo_5Board_1t.sudo_4Tier_1n = ((s.gap.length : Nat) : Int) := by
    rw [htierEq, h.shape.gapLen]
    exact h.shape.tierN
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := hmvEq.trans hmv
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := hpkEq.trans hpk
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hcopyLe := gap_copy_le_rung base.n base.bench base.mMax s.tally
    (pegCount s.gap) hpegN hT
  have hR1 : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    omega
  have hpegsLe : pegCount s.gap + 0 ≤ rungCharge base.n base.bench base.mMax := by
    simpa using Nat.le_trans (Nat.le_add_right (pegCount s.gap) _) hcopyLe
  have hfitBig := copy_then_pegs_fit base.moves0 mv done.length base.R
    (rungCharge base.n base.bench base.mMax) (pegCount s.gap) 0 hR1 hmvLe
    hpegsLe base.fitM
  have hfit : FitsLen (mv + pegCount s.gap) := by
    simpa using hfitBig
  have hlenFit : FitsLen s.gap.length := by
    rw [h.shape.gapLen]; exact h.shape.peg.fitN
  have hcopy := copy_band_refines bPark 6 5 s.gap mv pk h6H h6D h5H h5D h7
    hheld5 harr5 hempty hn hlenFit hmvP hpkP hfit
  exact ⟨bPark, _, mv, pk, h6H, h6D, hpark, hcopy, rfl, hmv, hpk⟩

/-- `place` writes one home. Marker, bench flag, tier, strict peak, and the
    recorded bench hole stay. -/
theorem place_side (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem place_held_src (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held[home] = true := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hD⟩ true := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

theorem place_home_src (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home[home] = embed xs := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs) := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

/-- The white scan reads the tally segment and returns the board it was given.
    Park writes sit before that segment, so the scan on `withPark` is the idle
    scan with the parked row and counter put back: both sides are the parked
    board, unchanged. -/
theorem list_idx_irrel {α : Type} {xs : List α} {i : Nat} {h1 h2 : i < xs.length} :
    xs[i]'h1 = xs[i]'h2 := by
  have : (⟨i, h1⟩ : Fin xs.length) = ⟨i, h2⟩ := Fin.ext rfl
  simp [this]

theorem get_add_eq {xs : List Nat} {a b j : Nat} (hab : a = b)
    (ha : a + j < xs.length) :
    xs[a + j]'ha = xs[b + j]'(hab ▸ ha) := by
  cases hab
  rfl

theorem list_eq_get {xs ys : List Nat} (h : xs = ys) {i : Nat} (hi : i < xs.length) :
    xs[i]'hi = ys[i]'(h ▸ hi) := by
  cases h
  rfl

theorem board_home_cell {b b' : Ecbs.Board} (h : b = b') (i : Nat)
    (hi : i < b.sudo_5Board_4home.size) :
    b.sudo_5Board_4home[i] = b'.sudo_5Board_4home[i]'(h ▸ hi) := by
  cases h
  rfl

theorem board_held_cell {b b' : Ecbs.Board} (h : b = b') (i : Nat)
    (hi : i < b.sudo_5Board_4held.size) :
    b.sudo_5Board_4held[i] = b'.sudo_5Board_4held[i]'(h ▸ hi) := by
  cases h
  rfl

theorem white_scan_withPark
    (b : Ecbs.Board) (xs xsP : List Nat) (t0 m : Nat)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRowP : row = embed xsP)
    (hRoom : t0 + m ≤ xs.length) (hRoomP : t0 + m ≤ xsP.length)
    (hAgree : ∀ j (hj : j < m),
      xsP[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoomP) =
        xs[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoom))
    (hWhite : ∀ j (hj : j < m),
      xs[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoom) = 1)
    (hfit : FitsLen (t0 + m)) (hfitM : FitsLen m) :
    SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep (withPark b row ctrl fromHole ridx) (Int.ofNat (m - 1)))
        (fun j => .ok (withPark b row ctrl fromHole ridx, j))
        (fun _ => .ok (withPark b row ctrl fromHole ridx, (0 : Int))) =
      .ok (withPark b row ctrl fromHole ridx, Int.ofNat (m - 1)) := by
  have hWhiteP : ∀ j (hj : j < m), xsP[t0 + j]'(by omega) = 1 := by
    intro j hj
    have hA := hAgree j hj
    have hW := hWhite j hj
    have hAp : xsP[t0 + j]'(by omega) =
        xsP[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoomP) :=
      list_idx_irrel
    exact hAp.trans (hA.trans hW)
  exact white_scan_loop_refines (withPark b row ctrl fromHole ridx) xsP t0 m hm
    (by rw [withPark_tally0]; exact hT0)
    (by rw [withPark_row]; exact hRowP)
    hRoomP hWhiteP hfit hfitM

/-- `pegPack_twin` read at the last index: the parked peg board is the idle peg
    board with the painted park row, the parked counter, and the park hole. -/
theorem pegBoard_park (c d : PegCtx) (t : PegTwin c d) :
    pegBoard d c.m =
      withPark (pegBoard c c.m)
        (embed (paintRed d.row0 d.t0 c.m))
        (Int.ofNat (d.ctrl0 + c.m)) t.fromHole t.ridx := by
  have hloop := pegPack_twin c d t c.m c.hm (Nat.le_refl _)
  have hPc := (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  have hD := packEqBoard d c.m c.hm _ hloop
  rw [hPc] at hD
  exact hD

/-- The cube-peg loop on the parked start is the idle loop with that park frame.
    `pegPack_twin` is the step; this only rewrites the loop equality. -/
theorem cube_peg_loop_withPark (c d : PegCtx) (t : PegTwin c d) :
    SudoRt.runLoopOn (Int.ofNat 0, d.b0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (d.m - 1)))
        (cubePegStep d.src (Int.ofNat (d.m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      .ok (Int.ofNat (c.m - 1),
        withPark (pegBoard c c.m)
          (embed (paintRed d.row0 d.t0 c.m))
          (Int.ofNat (d.ctrl0 + c.m)) t.fromHole t.ridx) := by
  rw [cube_peg_loop_refines d]
  have hsub : d.m - 1 = c.m - 1 := by rw [t.m]
  have hboard : pegBoard d d.m = pegBoard d c.m := by rw [t.m]
  rw [hsub, hboard, pegBoard_park c d t]

/-- `clear` of a held home copies the park frame. The cleared board is `withPark`
    of the idle clear. -/
theorem clear_withPark
    (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int)
    (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hf : FitsLen xs.length)
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.clear (withPark b row ctrl fromHole ridx) (home : Int) =
      .ok (withPark (clearHeldBoard b home xs moves hH hD) row ctrl fromHole ridx) := by
  let bW := withPark b row ctrl fromHole ridx
  have hHW : home < bW.sudo_5Board_4home.size :=
    withPark_home b row ctrl fromHole ridx ▸ hH
  have hDW : home < bW.sudo_5Board_4held.size :=
    withPark_held b row ctrl fromHole ridx ▸ hD
  have hheldW : bW.sudo_5Board_4held[home] = true := by
    simpa [bW, withPark] using hheld
  have harrW : bW.sudo_5Board_4home[home] = embed xs := by
    simpa [bW, withPark] using harr
  have hmvW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [bW, withPark] using hmoves
  rw [clear_held_refines bW home xs moves hHW hDW hheldW harrW hmvW hf hfit]
  rw [← clearHeld_withPark b row ctrl fromHole ridx home xs moves hH hD]
  rfl

/-- Same cube-peg context, with a replacement row, counter, parked-from hole,
    and rung index. Every field the cube reads is the original one. -/
def pegCtxPark (c : PegCtx) (row0 : List Nat) (ctrl0 : Nat)
    (fromHole ridx : Int)
    (hRoom : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m)) : PegCtx where
  b0 := withPark c.b0 (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx
  src := c.src
  g := c.g
  row0 := row0
  w := c.w
  h := c.h
  r := c.r
  n := c.n
  k := c.k
  bench := c.bench
  cg := c.cg
  moves0 := c.moves0
  slides0 := c.slides0
  hole0 := c.hole0
  peak0 := c.peak0
  peakS0 := c.peakS0
  cOps0 := c.cOps0
  t0 := c.t0
  high := c.high
  control := c.control
  ctrl0 := ctrl0
  m := c.m
  hm := c.hm
  hmk := c.hmk
  hoff := c.hoff
  hops0 := c.hops0
  hop10 := c.hop10
  hbl := c.hbl
  hcg := c.hcg
  hspan := c.hspan
  hF := c.hF
  hHome := c.hHome
  hHF := c.hHF
  hArr := c.hArr
  h7 := c.h7
  hn0 := c.hn0
  hn := c.hn
  hlenx := c.hlenx
  hf := c.hf
  hmoves0 := c.hmoves0
  hpeak0 := c.hpeak0
  hpeakS0 := c.hpeakS0
  hxsT := c.hxsT
  h3 := c.h3
  hw0 := c.hw0
  hh0 := c.hh0
  hrR := c.hrR
  hrP := c.hrP
  hnE := c.hnE
  hkLe := c.hkLe
  hgap := c.hgap
  hwF := c.hwF
  hhF := c.hhF
  hrF := c.hrF
  hkF := c.hkF
  hHole0 := c.hHole0
  hsm := c.hsm
  hnsm := c.hnsm
  hfitB := c.hfitB
  hT0 := c.hT0
  hRow := by rw [withPark_row]
  hRoom := hRoom
  hCtrlN := c.hCtrlN
  hHigh := c.hHigh
  hTop := c.hTop
  hIn := c.hIn
  hCtrl0 := by rw [withPark_ctrl]
  hslides0 := c.hslides0
  hfitRow := c.hfitRow
  hfitM := c.hfitM
  hBudget := c.hBudget
  hSlide := c.hSlide
  hOpsB := c.hOpsB
  hCtrlB := hCtrlB

/-- The parked context is a `PegTwin` of the idle one. -/
def pegTwinPark (c : PegCtx) (row0 : List Nat) (ctrl0 : Nat)
    (fromHole ridx : Int)
    (hRoom : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m)) :
    PegTwin c (pegCtxPark c row0 ctrl0 fromHole ridx hRoom hCtrlB) where
  src := rfl
  g := rfl
  n := rfl
  k := rfl
  bench := rfl
  moves0 := rfl
  slides0 := rfl
  hole0 := rfl
  peak0 := rfl
  peakS0 := rfl
  cOps0 := rfl
  t0 := rfl
  m := rfl
  fromHole := fromHole
  ridx := ridx
  b0 := rfl

/-- Park, copy, the white scan, the cube-peg loop, `mul`, and `clear`, rewritten
    from the six equations. Nothing in the block is unfolded. -/
theorem parked_prefix_rw
    (b bPark bCopy bPeg bMul bClear : Ecbs.Board) (rung m : Nat)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (hCopy : Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy)
    (hScan : SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep bCopy (Int.ofNat (m - 1)))
        (fun j => .ok (bCopy, j))
        (fun _ => .ok (bCopy, (0 : Int))) = .ok (bCopy, Int.ofNat (m - 1)))
    (hPeg : SudoRt.runLoopOn (Int.ofNat 0, bCopy)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep 6 (Int.ofNat (m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) = .ok (Int.ofNat (m - 1), bPeg))
    (hMul : Ecbs.mul bPeg (5 : Int) (5 : Int) (6 : Int) false false false = .ok bMul)
    (hClear : Ecbs.clear bMul (5 : Int) = .ok bClear) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (whiteStep b (Int.ofNat (m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) = .ok bClear := by
  rw [hPark, ok_bind, hCopy, ok_bind, hScan, ok_bind, hPeg, ok_bind]
  dsimp only
  rw [hMul, ok_bind, hClear]

/-- Park, copy, white scan, and the cube-peg loop, then `mul` and `clear`.
    The scan and the loop are the idle ones under `withPark`. `mul` and `clear`
    are the existing park transports, passed in as the two equations they
    return. The block is only `rw`. -/
theorem parked_clear_transport
    (b bPark bCopy : Ecbs.Board) (rung : Nat)
    (c : PegCtx) (xs row0 : List Nat) (ctrl0 : Nat) (fromHole ridx : Int)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (hCopy : Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy)
    (hFrame : bCopy =
      withPark c.b0 (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx)
    (hRoom0 : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m))
    (hsrc : c.src = 6)
    (hT0 : c.b0.sudo_5Board_6tally0 = (c.t0 : Int))
    (hRowIdle : c.b0.sudo_5Board_3row = embed xs)
    (hRoom : c.t0 + c.m ≤ xs.length)
    (hAgree : ∀ j (hj : j < c.m),
      row0[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom0) =
        xs[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom))
    (hWhite : ∀ j (hj : j < c.m),
      xs[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom) = 1)
    (bMul bClear : Ecbs.Board)
    (hMul : Ecbs.mul
        (withPark (pegBoard c c.m)
          (embed (paintRed row0 c.t0 c.m))
          (Int.ofNat (ctrl0 + c.m)) fromHole ridx)
        (5 : Int) (5 : Int) (6 : Int) false false false = .ok bMul)
    (hClear : Ecbs.clear bMul (5 : Int) = .ok bClear) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (whiteStep b (Int.ofNat (c.m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (cubePegStep 6 (Int.ofNat (c.m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) = .ok bClear := by
  let d := pegCtxPark c row0 ctrl0 fromHole ridx hRoom0 hCtrlB
  let t := pegTwinPark c row0 ctrl0 fromHole ridx hRoom0 hCtrlB
  have hScan0 := white_scan_withPark c.b0 xs row0 c.t0 c.m
    (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx
    c.hm hT0 rfl hRoom hRoom0 hAgree hWhite c.hfitRow c.hfitM
  have hScan : SudoRt.runLoopOn (Int.ofNat 0)
      (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
      (whiteStep bCopy (Int.ofNat (c.m - 1)))
      (fun j => .ok (bCopy, j))
      (fun _ => .ok (bCopy, (0 : Int))) =
      .ok (bCopy, Int.ofNat (c.m - 1)) := by
    simpa [hFrame] using hScan0
  have hPeg0 := cube_peg_loop_withPark c d t
  have hd0 : d.b0 = bCopy := by
    unfold d pegCtxPark
    exact hFrame.symm
  have hsrcD : d.src = 6 := by
    unfold d pegCtxPark
    exact hsrc
  have hmD : d.m = c.m := by
    unfold d pegCtxPark
    rfl
  have hrowD : d.row0 = row0 := by
    unfold d pegCtxPark
    rfl
  have ht0D : d.t0 = c.t0 := by
    unfold d pegCtxPark
    rfl
  have hctrlD : d.ctrl0 = ctrl0 := by
    unfold d pegCtxPark
    rfl
  have hfromT : t.fromHole = fromHole := by
    unfold t pegTwinPark
    rfl
  have hridxT : t.ridx = ridx := by
    unfold t pegTwinPark
    rfl
  rw [hd0, hsrcD, hmD, hrowD, ht0D, hctrlD, hfromT, hridxT] at hPeg0
  exact parked_prefix_rw b bPark bCopy
    (withPark (pegBoard c c.m)
      (embed (paintRed row0 c.t0 c.m))
      (Int.ofNat (ctrl0 + c.m)) fromHole ridx)
    bMul bClear rung c.m hPark hCopy hScan hPeg0 hMul hClear

theorem withTally_id (b : Ecbs.Board) :
    withTally b b.sudo_5Board_3row b.sudo_5Board_9tally_len
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max = b := by
  apply board_ext
  case hcost =>
    apply cost_ext
    all_goals rfl
  all_goals rfl

/-- Idle final red rung: the clear, then one spare cube onto the gap and the mul
    by the input. No tally double and no extra peg. The rung delta is the clear's
    delta plus that cube (ops slot 1) and that mul (ops slot 0). -/
theorem red_final_k
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done [2] ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b ((2 : Nat) : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false) = .ok b' ∧
      ClimbInvK (done ++ [2]) [] b'
        (modelRung s base.x 2 (climbAt base.ladder0 base.R s.ridx) true) base ∧
      RungDelta b b' base s.tally := by
  obtain ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, hlenC, _ht0C, _hrowC,
      _hctrlN, hhighC, _hctrlC, hmaxC, ht0Red, _htierRed, hcubeBoth, hmulBoth,
      hrel, honR, htoR, _hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE,
      _ht0E, _hmarkE, htierE, _htmaxE, hcubeU, hredU, hbonE, htoE, hbenchE,
      _h5H, _h5D, _h6H, _h6D, _h7E, _h5f, _h6f, _hkeep, hopsE, _hc1E, _hpkSE, _hholeE,
      _htrits, hpieceM, hpieceS⟩ :=
    red_open_view h hF hm hT hhome hxLen hxT
  have hpack :=
    red_unparked_delta h hm hT hhome hxLen hxT
      bClearP bClearU bCube0 bRed0
      (embed (paintRed (afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) 2) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
      (Int.ofNat (s.ridx + 1))
      hClearEq hδ hslots _hmarkE htierE hcubeU hredU hrel
      hbonE htoE hbenchE _h5H _h5D _h6H _h6D _h7E _h5f _h6f _hkeep hopsE _hc1E
      _hpkSE _hholeE _htrits hpieceM hpieceS
  let hole := climbAt base.ladder0 base.R s.ridx
  let rowU := bClearU.sudo_5Board_3row
  let lenU := bClearU.sudo_5Board_9tally_len
  let ctrlU := bClearU.sudo_5Board_4cost.sudo_5Costs_4ctrl
  let highU := bClearU.sudo_5Board_4cost.sudo_5Costs_15control_highest
  let maxU := bClearU.sudo_5Board_4cost.sudo_5Costs_9tally_max
  let rowRed := embed (paintRed (afterPark s.row (-1) s.parkAt hole 2) s.t0 s.tally)
  let ctrlRed := ((s.ctrl + 2 + s.tally : Nat) : Int)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hcube0 := hcubeBoth rowU rowRed lenU highU maxU ctrlU ctrlRed fromH ridxH
  have hid : withTally bClearU rowU lenU ctrlU highU maxU = bClearU := withTally_id bClearU
  rw [hid] at hcube0
  have hClearEq' : bClearP = withPark bClearU rowRed ctrlRed fromH ridxH := by
    simpa [rowRed, ctrlRed, fromH, ridxH, hole] using hClearEq
  rw [← hClearEq'] at hcube0
  have hmul0 := hmulBoth rowU rowRed lenU highU maxU ctrlU ctrlRed fromH ridxH
  let b' := withPark (withTally bRed0 rowU lenU ctrlU highU maxU) rowRed ctrlRed fromH ridxH
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b ((2 : Nat) : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false) = .ok b' := by
    rw [hrun, ok_bind, hcube0, ok_bind]
    exact hmul0
  have hδR : RungDelta b b' base s.tally :=
    rungDelta_cost hpack.delta
      (by rw [withPark_moves, withTally_moves])
      (by rw [withPark_slides, withTally_slides])
      (by rw [withPark_ops, withTally_ops])
      (by rw [withPark_peak, withTally_peak])
  let s' := modelRung s base.x 2 hole true
  have hM := model_final_red s base.x hole hF
  obtain ⟨hgap, htall, _hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, _ht0M,
      _hparkM⟩ := hM
  have hIdle : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hhomeB : b'.sudo_5Board_4home = bRed0.sudo_5Board_4home := by
    rw [withPark_home, withTally_home]
  have hheldB : b'.sudo_5Board_4held = bRed0.sudo_5Board_4held := by
    rw [withPark_held, withTally_held]
  have hinv : ClimbInv b' s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := ?_
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · rw [hhomeB]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.home6
    · rw [hheldB]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.held6
    · rw [withPark_marker]
      simpa [withTally] using hpack.marker
    · rw [withPark_len, withTally_len]
      unfold lenU
      rw [hlenC, htall]
    · rw [withPark_ctrl]
      unfold ctrlRed
      rw [hctrlM]
    · rw [withPark_high, withTally_high]
      unfold highU
      rw [hhighC, hhighM]
    · rw [withPark_tally0]
      simp only [withTally]
      rw [ht0Red, _ht0M]
    · rw [withPark_row, hrowM, hIdle]
    · have hpB : b'.sudo_5Board_9park_hole = bRed0.sudo_5Board_9park_hole := by
        rw [withPark_park]
        rfl
      rw [hpB, hpack.park, hparkE, _hparkM]
    · rw [withPark_from]
      unfold fromH
      rw [hfromM]
    · rw [withPark_ridx]
      unfold ridxH
      rw [hridxM]
      exact (ofNat_eq_natCast _).symm
    · intro hOff
      simp [s', modelRung] at hOff
    · intro _
      refine ⟨?_, ?_, ?_, rfl⟩
      · rw [withPark_on]
        simpa [withTally] using honR
      · rw [withPark_to]
        simpa [withTally] using htoR
      · rw [withPark_bench, withTally_bench, hbenchR, hgap]
        have hnle : s.n ≤ s.benchlen :=
          span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
        have hlenG : s'.gap.length = s.n := by
          rw [hgap]
          exact fieldMul_len s.n s.k s.benchlen base.x
            (fieldCube s.n s.k s.benchlen
              (fieldMul s.n s.k s.benchlen s.gap
                (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
        have hn' : s'.n = s.n := rfl
        have hb' : s'.benchlen = s.benchlen := rfl
        have htake :
            (fieldMul s.n s.k s.benchlen base.x
              (fieldCube s.n s.k s.benchlen
                (fieldMul s.n s.k s.benchlen s.gap
                  (cubeTimes s.n s.k s.benchlen s.gap s.tally)))).take s.n =
              fieldMul s.n s.k s.benchlen base.x
                (fieldCube s.n s.k s.benchlen
                  (fieldMul s.n s.k s.benchlen s.gap
                    (cubeTimes s.n s.k s.benchlen s.gap s.tally))) := by
          apply List.take_of_length_le
          have hlen := hlenG
          rw [hgap] at hlen
          exact Nat.le_of_eq hlen
        rw [hn', hb', htake]
  have hseg : RowSeg s'.row s'.t0 s'.tally true := by
    have hred := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally 2
      h.shape.seg h.parkBelow h.holeBelow (Or.inl hF)
    have hEq : s'.row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 true := by
      rw [hrowM, rungRow, afterTally]
      simp
    simpa [hEq, s'] using hred
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone base.fitCtrl
  have hpark' : ParkRead b' s' [] base := by
    refine
      { ladder0B := ?_
        nrungsB := ?_
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · rw [withPark_ladder]
      simp only [withTally]
      rw [hpack.ladder, hladE]
      exact h.shape.park.ladder0B
    · rw [withPark_nrungs]
      simp only [withTally]
      rw [hpack.nrungs, hnrE]
      exact h.shape.park.nrungsB
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [withPark_ladder]
        simp only [withTally]
        rw [hpack.ladder, hladE, h.shape.park.ladder0B]
        exact (ofNat_eq_natCast _).symm
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [withPark_nrungs]
        simp only [withTally]
        rw [hpack.nrungs, hnrE, h.shape.park.nrungsB]
        exact (ofNat_eq_natCast _).symm
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM] at hne
      exact hne
    · rw [hhighM]
      exact h.shape.park.parkLe
    · exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _hnn
      rw [hfromM]
      rfl
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hle : hole ≤ s.high := by
          have hhi : hole < s.t0 := h.holeBelow
          have htop : s.high = s.t0 + s.tally - 1 := h.highTop hm
          omega
        rw [hhighM]
        simpa [Int.toNat_ofNat] using hle
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro _ _ hrs
      cases hrs
    · intro _ hk _hlt
      simp at hk
    · rw [hctrlM]
      exact hfits.1
    · rw [hctrlM]
      exact hfits.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  have hopsB : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [withPark_ops, withTally_ops, hpack.delta.opsSize, ← hδ.opsSize]
    exact hopsE
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := hopsB
        cOps := ?_
        peakS := ?_
        holeM := ?_
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · have hi : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hδ.opsSize]
        exact hopsE
      obtain ⟨_, c', _, hc', _⟩ := hpack.delta.ops 1 hi
      refine ⟨c', ?_⟩
      have hOpsEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
          bRed0.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [withPark_ops, withTally_ops]
      exact (arr_get hOpsEq 1 hopsB).trans hc'
    · obtain ⟨p, hp⟩ := hpack.strict
      refine ⟨p, ?_⟩
      rw [withPark_strict]
      simpa [withTally] using hp
    · obtain ⟨hn0, hh⟩ := hpack.hole
      refine ⟨hn0, ?_⟩
      rw [withPark_hole]
      simpa [withTally] using hh
    · have hspan3 : 3 * (s.n - 1) < s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have hnle : s.n ≤ s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have htri := fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hspan3 hnle
      simpa [hgap, fieldCube, List.take_take] using htri
    · intro hpos
      rw [_ht0M, htall, hhighM]
      exact Nat.le_of_eq (h.highTop (htall.symm ▸ hpos)).symm
    · rw [htall]
      exact h.shape.peg.fitRow
    · rw [htall]
      exact h.shape.peg.fitTall
    · rw [hctrlM, htall]
      exact hfits.2.2
    · exact h.shape.peg.n_pos
    · exact h.shape.peg.span
    · exact h.shape.peg.small
    · exact h.shape.peg.n_small
    · exact h.shape.peg.fitN
    · exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have h7' : 7 ≤ b'.sudo_5Board_4held.size := by
    rw [hheldB]
    exact hpack.held7
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] rfl rfl rfl
      (by
        rw [hgap]
        have hnle : s.n ≤ s.benchlen := by
          have hs := h.shape.peg.span
          omega
        exact fieldMul_len s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle)
      hseg
      (by rw [hheldB]; exact hpack.held6)
      (by rw [hhomeB]; exact hpack.home6)
      (by
        have h6 : 6 < b'.sudo_5Board_4held.size := by
          rw [hheldB]; exact hpack.held6
        exact cell_eq_of hheldB hpack.empty6)
      h7'
      (by
        intro _
        exact cell_eq_of hheldB hpack.empty5)
      (by
        intro hOff
        simp [s', modelRung] at hOff)
      (by rw [hheldB]; exact hpack.keep.heldLt)
      (by rw [hhomeB]; exact hpack.keep.homeLt)
      (by exact cell_eq_of hheldB hpack.keep.held)
      (by exact cell_eq_of hhomeB hpack.keep.arr)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierN)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierK)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierB)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierW)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierH)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierR)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierCg)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, ?_, ?_⟩
    · rw [withPark_tmax, withTally_max]
      unfold maxU
      rw [hmaxC, htm]
    · intro hpos
      have hlt := hnote (by rw [← htall]; exact hpos)
      rw [htall]
      exact hlt
  have hK := climbInvK_succ h hinv hδR hCap hshape h.holeBelow htmax rfl
  exact ⟨b', hprog, hK, hδR⟩

/-- A parked resume spends two more control steps than an idle park. The peg
    loop still fits the same counter budget: `4 + tally ≤ 3 · mMax + 5`. -/
theorem ctrl_resume_peg_fit {ctrl tally ctrl0 done R mMax : Nat}
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (_hm : 0 < tally) (hd : done ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 4 + tally) := by
  apply FitsLen.of_le hf
  have hmul : (done + 1) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (3 * mMax + 5) := by rw [Nat.succ_mul]
  have hstep : ctrl + 4 + tally ≤ ctrl0 + (done + 1) * (3 * mMax + 5) := by
    have hpiece : 4 + tally ≤ 3 * mMax + 5 := by omega
    omega
  have hR : ctrl0 + (done + 1) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : done + 1 ≤ R + 1)) _
  omega

theorem parkKeep_irrel (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP hRowP' : park < b.sudo_5Board_3row.size)
    (hRowH hRowH' : hole < b.sudo_5Board_3row.size) :
    parkKeepBoard b hole park rung i ctrl hRowP hRowH =
      parkKeepBoard b hole park rung i ctrl hRowP' hRowH' := by
  have hp : hRowP = hRowP' := Subsingleton.elim _ _
  have hh : hRowH = hRowH' := Subsingleton.elim _ _
  subst hp
  subst hh
  rfl

theorem place_of_eq {b b' : Ecbs.Board} (hbb : b = b') (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard b home hH hD xs moves peak =
      placeBoard b' home (hbb ▸ hH) (hbb ▸ hD) xs moves peak := by
  cases hbb
  rfl

/-- The idle park-and-copy peg context, for any rung whose gap is in home 5.
    `peg_of_shape` is the copy of the entry. Keep-park is `withPark` of that
    entry, so the peg context after the idle park is the same context with the
    park row and a counter two higher. `fromHole` is not read. -/
theorem idle_park_peg
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (c : PegCtx),
      c.row0 = afterPark s.row (-1) s.parkAt (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 2 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.src = 6 ∧
      c.g = s.gap ∧
      c.n = s.n ∧
      c.k = s.k ∧
      c.bench = s.benchlen ∧
      ∃ (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size)
        (mv pk sl : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        c.moves0 = mv + pegCount s.gap ∧
        c.slides0 = sl ∧
        c.b0 = placeBoard
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨mv, pk, sl, cE, hmv, hpk, hsl, _hmvLe, _hslLe, hb0, _hcopy, hsrc, hg, hmT,
      _hrow0, hn, hkN, hbch, hmv0, hsl0, ht0, _hctrl0, _hhigh, _hcontrol, _hlen, _hmax⟩ :=
    peg_of_shape h hm hT hhome
  let rowI := afterPark s.row (-1) s.parkAt hole r
  have hRoom : cE.t0 + cE.m ≤ rowI.length := by
    have hlenA : rowI.length = s.row.length :=
      afterPark_length s.row (-1) s.parkAt hole r
    rw [ht0, hmT, hlenA]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R := by
    have hlenK := h.kLe
    simp [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.le_add_right done.length _) hlenK
  have hCtrl : FitsLen ((s.ctrl + 2) + s.tally) :=
    ctrl_park_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  let c := pegCtxPark cE rowI (s.ctrl + 2) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hRoom (by rw [hmT]; exact hCtrl)
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  have hPW := parkKeep_withPark b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH
    h.inv.row h.shape.park.parkLt h.shape.park.holeLt
  have hpl := placeBoard_withPark b (embed rowI) (Int.ofNat (s.ctrl + 2))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hb0p : placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk = cE.b0 := hb0.symm
  have hplace : placeBoard
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk = c.b0 := by
    have h1 := place_of_eq hPW 6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hir := placeBoard_irrel
      (withPark b (embed rowI) (Int.ofNat (s.ctrl + 2)) ((hole : Nat) : Int)
        (Int.ofNat (s.ridx + 1)))
      6 (hPW ▸ h.shape.spareH) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hPW ▸ h.shape.spareD) (withPark_held _ _ _ _ _ ▸ h.shape.spareD)
      s.gap mv pk
    rw [h1, hir, hpl, hb0p]
    unfold c pegCtxPark
    rfl
  refine ⟨c, rfl, rfl, ?_, ?_, hsrc, hg, hn, hkN, hbch, hRowP, hRowH, mv, pk, sl,
      hmv, hpk, hsl, ?_, ?_, hplace.symm⟩
  · dsimp [c, pegCtxPark]; exact hmT
  · dsimp [c, pegCtxPark]; exact ht0
  · dsimp [c, pegCtxPark]; exact hmv0
  · dsimp [c, pegCtxPark]; exact hsl0

/-- A parked rung's copy is the idle park-and-copy peg context with the restored
    row and a counter two higher. `parked_peg_ctx` is that idle context; this is
    the same context after `withPark`. -/
theorem parked_peg_ctx_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark bCopy : Ecbs.Board) (cIdle c : PegCtx),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy ∧
      bCopy = withPark cIdle.b0
        (embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r))
        (((s.ctrl + 4 : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      c.b0 = bCopy ∧
      c.row0 = afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 4 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.src = 6 ∧
      c.g = s.gap ∧
      cIdle.row0 = afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r ∧
      cIdle.ctrl0 = s.ctrl + 2 ∧
      cIdle.m = s.tally ∧
      cIdle.t0 = s.t0 ∧
      cIdle.src = 6 ∧
      cIdle.g = s.gap ∧
      cIdle.n = s.n ∧
      cIdle.k = s.k ∧
      cIdle.bench = s.benchlen ∧
      ∃ (mv pk sl : Nat)
        (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        cIdle.moves0 = mv + pegCount s.gap ∧
        cIdle.slides0 = sl ∧
        cIdle.b0 = placeBoard
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨cIdle, hrowI, hctrlI, hmI, htI, hsrcI, hgI, hnI, hkI, hbI,
      hRowP, hRowH, mv, pk, sl, hmv, hpk, hsl, hmv0, hsl0, hplace⟩ :=
    idle_park_peg h hm hT hhome
  obtain ⟨bPark, bKeep, hRowP', hRowH', hpark, hkeep, hframe⟩ :=
    resume_park_withPark h hge
  have hKeepEq : bKeep =
      parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH := by
    rw [hkeep]
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    rw [hframe, withPark_home, hKeepEq]
    exact h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.shape.spareD
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    rw [hframe, withPark_home, hKeepEq]
    exact h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.inv.hGs
  have h7 : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.shape.h7
  have hheld5 : bPark.sudo_5Board_4held[5] = true := by
    have hEq : bPark.sudo_5Board_4held = b.sudo_5Board_4held := by
      rw [hframe, withPark_held, hKeepEq]
      rfl
    exact cell_eq_of hEq (h.inv.gapHome hhome).1
  have harr5 : bPark.sudo_5Board_4home[5] = embed s.gap := by
    have hEq : bPark.sudo_5Board_4home = b.sudo_5Board_4home := by
      rw [hframe, withPark_home, hKeepEq]
      rfl
    exact cell_eq_of hEq (h.inv.gapHome hhome).2
  have hempty : bPark.sudo_5Board_4held[6] = false := by
    have hEq : bPark.sudo_5Board_4held = b.sudo_5Board_4held := by
      rw [hframe, withPark_held, hKeepEq]
      rfl
    exact cell_eq_of hEq h.shape.spareE
  have hnP : bPark.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) := by
    have hEq : bPark.sudo_5Board_1t = b.sudo_5Board_1t := by
      rw [hframe, withPark_tier, hKeepEq]
      rfl
    rw [hEq, h.shape.gapLen]
    exact h.shape.tierN
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [hframe, withPark_moves, hKeepEq]
    exact hmv
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hframe, withPark_peak, hKeepEq]
    exact hpk
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hcopyLe := gap_copy_le_rung base.n base.bench base.mMax s.tally
    (pegCount s.gap) hpegN hT
  have hR1 : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) hlenK
  obtain ⟨mvE, hmvE, hmvLe⟩ := h.moves
  have hmvSame : mv = mvE := ofNat_inj_nat (hmv.symm.trans hmvE)
  have hpegsLe : pegCount s.gap + 0 ≤ rungCharge base.n base.bench base.mMax := by
    exact Nat.le_trans (Nat.le_add_right (pegCount s.gap) _) hcopyLe
  have hfitBig := copy_then_pegs_fit base.moves0 mvE done.length base.R
    (rungCharge base.n base.bench base.mMax) (pegCount s.gap) 0 hR1 hmvLe
    hpegsLe base.fitM
  have hfit : FitsLen (mv + pegCount s.gap) := by
    rw [hmvSame]
    simpa using hfitBig
  have hlenFit : FitsLen s.gap.length := by
    rw [h.shape.gapLen]; exact h.shape.peg.fitN
  have hcopy := copy_band_refines bPark 6 5 s.gap mv pk h6H h6D h5H h5D h7
    hheld5 harr5 hempty hnP hlenFit hmvP hpkP hfit
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  have hRoomP : cIdle.t0 + cIdle.m ≤ rowP.length := by
    rw [htI, hmI, afterPark_length]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R :=
    Nat.le_trans (Nat.le_succ done.length) hR1
  have hCtrl4 : FitsLen ((s.ctrl + 4) + s.tally) :=
    ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hCtrlP : FitsLen (cIdle.ctrl0 + cIdle.m) := by
    rw [hctrlI, hmI]
    have hsum : s.ctrl + 2 + s.tally ≤ s.ctrl + 4 + s.tally := by omega
    exact FitsLen.of_le hCtrl4 hsum
  let c := pegCtxPark cIdle rowP (s.ctrl + 4) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hRoomP (by rw [hmI]; exact hCtrl4)
  have hpl := placeBoard_withPark
    (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
    (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hframe' : bPark = withPark
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    rw [hframe, hKeepEq]
  have hbc : placeBoard bPark 6 h6H h6D s.gap mv pk =
      withPark cIdle.b0 (embed rowP) (((s.ctrl + 4 : Nat) : Int))
        ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    have h1 := place_of_eq hframe' 6 h6H h6D s.gap mv pk
    have hir := placeBoard_irrel
      (withPark (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)))
      6 (hframe' ▸ h6H) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hframe' ▸ h6D) (withPark_held _ _ _ _ _ ▸ h.shape.spareD) s.gap mv pk
    rw [h1, hir, hpl, ← hplace]
  refine ⟨bPark, _, cIdle, c, hpark, hcopy, hbc, ?_, rfl, rfl, ?_, ?_, ?_, ?_,
      hrowI, hctrlI, hmI, htI, hsrcI, hgI, hnI, hkI, hbI,
      mv, pk, sl, hRowP, hRowH, hmv, hpk, hsl, hmv0, hsl0, hplace⟩
  · dsimp [c, pegCtxPark]
    exact hbc.symm
  · dsimp [c, pegCtxPark]; exact hmI
  · dsimp [c, pegCtxPark]; exact htI
  · dsimp [c, pegCtxPark]; exact hsrcI
  · dsimp [c, pegCtxPark]; exact hgI

/-- Park, copy, the white scan, the cube-peg loop, `mul`, and `clear` on a rung
    that is already parked. The peg context is the idle one transported across
    the resume frame, and the block is `parked_clear_transport`. -/
theorem parked_clear_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ bClear bIdle,
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) = .ok bClear ∧
      bClear = withPark bIdle
        (embed (paintRed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (((s.ctrl + 4 + s.tally : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      bIdle.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      bIdle.sudo_5Board_8bench_on = true ∧
      bIdle.sudo_5Board_8bench_to = (5 : Int) ∧
      bIdle.sudo_5Board_9marker_on = false ∧
      bIdle.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bIdle.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bIdle.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bIdle.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bIdle.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bIdle.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      5 < bIdle.sudo_5Board_4home.size ∧
      5 < bIdle.sudo_5Board_4held.size ∧
      6 < bIdle.sudo_5Board_4home.size ∧
      6 < bIdle.sudo_5Board_4held.size ∧
      7 ≤ bIdle.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[5] = false) ∧
      (∀ h6 : 6 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[6] = false) ∧
      CellKeep bIdle base.xHome base.x ∧
      (∃ ps : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int)) ∧
      (∃ hn : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hn : Int)) ∧
      bIdle.sudo_5Board_3row =
        embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally) ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 + s.tally : Nat) : Int) ∧
      RungDelta b bClear base s.tally ∧
      ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
      (∃ mv mvC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        bClear.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
        mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n) ∧
      (∃ sl slC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        bClear.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
        slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bPark, bCopy, cIdle, _cP, hpark, hcopy, hFrame, _hc0, _hrowP, _hctrlP,
      _hmP, _htP, _hsrcP, _hgP, hrowI, hctrlI, hmI, htI, hsrcI, hgI,
      hnI, hkI, hbI, mv, pk, sl, hRowP, hRowH, hmv, hpk, hsl, hmv0, hsl0, hplace⟩ :=
    parked_peg_ctx_ge h hge hm hT hhome
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  let rowI := afterPark s.row (-1) s.parkAt hole r
  have hRoom : cIdle.t0 + cIdle.m ≤ cIdle.row0.length := by
    rw [htI, hmI, hrowI, afterPark_length]
    exact h.shape.seg.room
  have hRoom0 : cIdle.t0 + cIdle.m ≤ rowP.length := by
    rw [htI, hmI, afterPark_length]
    exact h.shape.seg.room
  have hseg0 := h.shape.seg
  have hAgree : ∀ j (hj : j < cIdle.m),
      rowP[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom0) =
        cIdle.row0[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom) := by
    intro j hj
    have hjM : j < s.tally := by
      have h := hj
      rw [hmI] at h
      exact h
    have hix : s.t0 + j < s.row.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) hseg0.room
    have hgetP := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (Nat.le_add_right s.t0 j)))
      hix
    have hgetI := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inl (by decide : (-1 : Int) < 0))
      hix
    have hgoal := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom0
    have hLP := get_add_eq htI hgoal
    have hixP : s.t0 + j < rowP.length := by
      unfold rowP
      rw [afterPark_length]
      exact hix
    have hmid : rowP[s.t0 + j]'(htI ▸ hgoal) = rowP[s.t0 + j]'hixP := list_idx_irrel
    have hgoalI := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom
    have hrow := list_eq_get hrowI hgoalI
    have hixI : s.t0 + j < rowI.length := by
      unfold rowI
      rw [afterPark_length]
      exact hix
    have hback := get_add_eq htI.symm hixI
    exact hLP.trans (hmid.trans (hgetP.trans (hgetI.symm.trans
      ((list_idx_irrel).trans (hback.trans hrow.symm)))))
  have hWhite : ∀ j (hj : j < cIdle.m),
      cIdle.row0[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom) = 1 := by
    intro j hj
    have hjM : j < s.tally := by
      have h := hj
      rw [hmI] at h
      exact h
    have hsegI := afterPark_seg s.row (-1) s.parkAt hole r s.t0 s.tally hseg0
      h.parkBelow h.holeBelow (Or.inl (by decide : (-1 : Int) < 0))
    have hcol := hsegI.colour j hjM
    have hixI : s.t0 + j < rowI.length := by
      unfold rowI
      rw [afterPark_length]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) hseg0.room
    have h1 : rowI[s.t0 + j]'hixI = 1 := by
      unfold rowI at hixI ⊢
      exact list_idx_irrel.trans (by simpa using hcol)
    have hgoalI := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom
    have hrow := list_eq_get hrowI hgoalI
    have hback := get_add_eq htI.symm hixI
    exact hrow.trans (hback.symm.trans h1)
  -- Home 5 survives the idle copy. The peg loop keeps it.
  have h5D : 5 < cIdle.b0.sudo_5Board_4held.size := by
    rw [hplace]
    have hsz := (place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk).2.2.2.2.2.2.2.2.2
    rw [hsz]
    simp [parkKeepBoard]
    exact h.inv.hGs
  have h5H : 5 < cIdle.b0.sudo_5Board_4home.size := by
    rw [hplace]
    have hsz := (place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk).2.2.2.2.2.2.2.2.1
    rw [hsz]
    simp [parkKeepBoard]
    exact h.inv.hG
  have hHeld5 : cIdle.b0.sudo_5Board_4held[5] = true := by
    have hF : 5 < (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held.size := by
      rw [← hplace]; exact h5D
    have h5K : 5 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.size := by
      simp [parkKeepBoard]
      exact h.inv.hGs
    have hcell := place_held_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 5 h.shape.spareH h.shape.spareD s.gap mv pk (by decide) h5K hF
    have hpk : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held[5] = true := by
      simp [parkKeepBoard]
      exact (h.inv.gapHome hhome).1
    have hgot := hcell.trans hpk
    have hgot' := board_held_cell hplace.symm 5 hF
    exact hgot'.symm.trans hgot
  have hArr5 : cIdle.b0.sudo_5Board_4home[5] = embed cIdle.g := by
    have hF : 5 < (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home.size := by
      rw [← hplace]; exact h5H
    have h5K : 5 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home.size := by
      simp [parkKeepBoard]
      exact h.inv.hG
    have hcell := place_home_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 5 h.shape.spareH h.shape.spareD s.gap mv pk (by decide) h5K hF
    have hpk : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home[5] =
        embed s.gap := by
      simp [parkKeepBoard]
      exact (h.inv.gapHome hhome).2
    have hgot := hcell.trans hpk
    have hgot' := board_home_cell hplace.symm 5 hF
    have hfin : cIdle.b0.sudo_5Board_4home[5] = embed s.gap := hgot'.symm.trans hgot
    exact hfin.trans (congrArg embed hgI.symm)
  have hopsEq : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hplace, place_ops_delta]
    simp [parkKeepBoard]
  have hopsZ : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
  obtain ⟨cMul, hcMul, hcLe⟩ := h.ops 0 (by rw [← hopsEq]; exact hopsZ)
  have hopZ : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) :=
    (arr_get hopsEq 0 hopsZ).trans hcMul
  have hne5 : (5 : Nat) ≠ cIdle.src := by rw [hsrcI]; decide
  have hkeep := pegPack_keep cIdle 5 cIdle.g cMul cIdle.m cIdle.hm (Nat.le_refl _)
    h5D h5H hne5 hHeld5 hArr5 hopsZ hopZ
  let d := pegPack cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hPack := pegPack_board cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hpTake : pegCount (d.xs.take cIdle.n) ≤ cIdle.n := pegCount_take_le d.xs cIdle.n
  have hlenY : d.xs.length = cIdle.bench := by
    rw [d.hxs, cubeBenchIter_length cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.n_le cIdle.m cIdle.hm]
  have hfitL : FitsLen d.xs.length := by rw [hlenY]; exact cIdle.hfitB
  have hspan2 : 2 * (cIdle.n - 1) < cIdle.bench := by
    have hs := cIdle.hspan
    omega
  have hfi : FitsLen (2 * (cIdle.n - 1)) := FitsLen.of_le cIdle.h3 (by omega)
  have hsum : d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1) +
      3 * (cIdle.bench - cIdle.n) ≤
      cIdle.moves0 + cIdle.m * pegCharge cIdle.n cIdle.bench + mulCharge cIdle.n cIdle.bench := by
    have hgeM := mulCharge_ge cIdle.n cIdle.bench d.moves d.xs d.xs cIdle.k cIdle.n_le hpTake
    exact Nat.le_trans hgeM (Nat.add_le_add_right d.hmovB _)
  obtain ⟨mvE, hmvE, hmvLe⟩ := h.moves
  obtain ⟨slE, hslE, hslLe⟩ := h.slides
  have hmvSame : mv = mvE := ofNat_inj_nat (hmv.symm.trans hmvE)
  have hslSame : sl = slE := ofNat_inj_nat (hsl.symm.trans hslE)
  have hk : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    simp [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right done.length _)) hlenK
  have hcap : cIdle.moves0 + cIdle.m * pegCharge cIdle.n cIdle.bench +
      mulCharge cIdle.n cIdle.bench ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    rw [hmv0, hmI, hnI, hbI]
    have hpegN : pegCount s.gap ≤ base.n := by
      have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
      rw [h.shape.gapLen, h.hn] at h1
      exact h1
    have hpiece : pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
        mulCharge s.n s.benchlen ≤ rungCharge base.n base.bench base.mMax := by
      rw [h.hn, h.hbench]
      exact gap_mul_le_rung base.n base.bench base.mMax s.tally (pegCount s.gap) hpegN hT
    have hleft : mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
        mulCharge s.n s.benchlen ≤ mv + rungCharge base.n base.bench base.mMax := by
      have hassoc : mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
          mulCharge s.n s.benchlen =
          mv + (pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
            mulCharge s.n s.benchlen) := by
        rw [← Nat.add_assoc, ← Nat.add_assoc]
      rw [hassoc]
      exact Nat.add_le_add_left hpiece mv
    have hmvR : mv + rungCharge base.n base.bench base.mMax ≤
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      have h1 : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
        rw [hmvSame]; exact hmvLe
      have hsplit : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax =
          base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
        rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add_right h1 _) (Nat.le_of_eq hsplit)
    have hR : base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans hleft (Nat.le_trans hmvR hR)
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1) +
      3 * (cIdle.bench - cIdle.n)) :=
    FitsLen.of_le base.fitM (Nat.le_trans hsum hcap)
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpegF : FitsLen (2 * pegCount (d.xs.take cIdle.n)) := FitsLen.of_le hfitM (by omega)
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take cIdle.n)) := by
    apply FitsLen.of_le base.fitS
    have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * cIdle.n :=
      Nat.mul_le_mul_left 2 hpTake
    have hprev : d.slides ≤ sl + s.tally * (2 * s.n) := by
      have hEq : cIdle.slides0 + cIdle.m * (2 * cIdle.n) = sl + s.tally * (2 * s.n) := by
        rw [hsl0, hmI, hnI]
      exact Nat.le_trans d.hsldB (Nat.le_of_eq hEq)
    have hloc : d.slides + 2 * pegCount (d.xs.take cIdle.n) ≤
        sl + s.tally * (2 * s.n) + 2 * s.n := by
      have h2s : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * s.n := by rw [← hnI]; exact h2
      exact Nat.add_le_add hprev h2s
    have hpiece : sl + s.tally * (2 * s.n) + 2 * s.n ≤
        base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
      have hstep : (s.tally + 1) * (2 * s.n) ≤ rungSlideCharge base.n base.mMax := by
        unfold rungSlideCharge
        rw [h.hn]
        exact Nat.mul_le_mul_right _ (Nat.le_trans (Nat.succ_le_succ hT)
          (Nat.le_add_right (base.mMax + 1) 2))
      have hmulS : s.tally * (2 * s.n) + 2 * s.n = (s.tally + 1) * (2 * s.n) :=
        (Nat.succ_mul s.tally (2 * s.n)).symm
      have hslB : sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
        rw [hslSame]; exact hslLe
      have hsumS : sl + s.tally * (2 * s.n) + 2 * s.n = sl + (s.tally + 1) * (2 * s.n) :=
        (Nat.add_assoc sl (s.tally * (2 * s.n)) (2 * s.n)).trans
          (congrArg (fun z => sl + z) hmulS)
      have hle1 : sl + (s.tally + 1) * (2 * s.n) ≤
          sl + rungSlideCharge base.n base.mMax := Nat.add_le_add_left hstep _
      have hsplit : base.slides0 + done.length * rungSlideCharge base.n base.mMax +
          rungSlideCharge base.n base.mMax =
          base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
        rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.le_trans (Nat.le_of_eq hsumS)
        (Nat.le_trans hle1 (Nat.le_trans (Nat.add_le_add_right hslB _) (Nat.le_of_eq hsplit)))
    have hR : base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax ≤
        base.slides0 + base.R * rungSlideCharge base.n base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans hloc (Nat.le_trans hpiece hR)
  have hfops : FitsLen (cMul + 1) := by
    apply FitsLen.of_le base.fitO
    have h1 : cMul + 1 ≤ base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      have hone : (1 : Nat) ≤ base.mMax + 3 := Nat.le_add_left 1 (base.mMax + 2)
      have hsumC : cMul + 1 ≤
          base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) :=
        Nat.add_le_add hcLe hone
      have hsplit : base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) =
          base.ops0 + (done.length + 1) * (base.mMax + 3) := by
        rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.le_trans hsumC (Nat.le_of_eq hsplit)
    have hR : base.ops0 + (done.length + 1) * (base.mMax + 3) ≤
        base.ops0 + base.R * (base.mMax + 3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 hR
  have hH6 : 6 < d.b.sudo_5Board_4home.size := by rw [← hsrcI]; exact d.hH
  have hD6 : 6 < d.b.sudo_5Board_4held.size := by rw [← hsrcI]; exact d.hD
  have hempty : d.b.sudo_5Board_4held[6] = false := by simpa [hsrcI] using d.hempty
  have hto : d.b.sudo_5Board_8bench_to = ((6 : Nat) : Int) := by rw [d.toB, hsrcI]
  have hnB : d.b.sudo_5Board_1t.sudo_4Tier_1n = (cIdle.n : Int) := by rw [d.tier]; exact cIdle.hn
  have hbl : d.b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat cIdle.bench := by
    rw [d.tier]; exact cIdle.hbl
  have hwF : d.b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat cIdle.w := by rw [d.tier]; exact cIdle.hwF
  have hhF : d.b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat cIdle.h := by rw [d.tier]; exact cIdle.hhF
  have hrF : d.b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat cIdle.r := by rw [d.tier]; exact cIdle.hrF
  have hkF : d.b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat cIdle.k := by rw [d.tier]; exact cIdle.hkF
  let paint := embed (paintRed rowP cIdle.t0 cIdle.m)
  let ctrlM := Int.ofNat ((s.ctrl + 4) + s.tally)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hmulW := mul_eq_live_withPark d.b 5 5 6 cIdle.g d.xs cIdle.w cIdle.h cIdle.r cIdle.n cIdle.k
    d.moves d.slides d.hole cIdle.bench d.peak d.peakS cMul
    d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench
    hnB cIdle.hn0 d.hpos d.hnle d.hzero cIdle.hf hfitL
    d.hmoves d.hslides d.hpeak hpegF hfitM hfitS
    hkeep.opsLt hkeep.op0 hfops hbl
    hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) cIdle.hlenx
    hspan2 cIdle.hxsT hfi hfm
    cIdle.hw0 cIdle.hh0 cIdle.hrR cIdle.hrP cIdle.hnE cIdle.hkLe cIdle.hgap hwF hhF hrF hkF
    d.hHole d.hpeakS cIdle.hsm cIdle.hnsm cIdle.hfitB hfold
    paint ctrlM fromH ridxH
  have hmulP : Ecbs.mul
      (withPark (pegBoard cIdle cIdle.m) paint ctrlM fromH ridxH)
      (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (withPark
        (mulNoLiveBoard d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole cIdle.bench
          d.peak d.peakS cMul hH6 hD6 hkeep.opsLt)
        paint ctrlM fromH ridxH) := by
    have hcong := congrArg
      (fun bd => Ecbs.mul (withPark bd paint ctrlM fromH ridxH)
        (5 : Int) (5 : Int) (6 : Int) false false false) hPack.1
    exact hcong.symm.trans hmulW
  let bU := mulNoLiveBoard d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hmvU : bU.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mulMovesNo (d.moves + 2 * pegCount (d.xs.take cIdle.n)) cIdle.g
        (d.xs.take cIdle.n) cIdle.n cIdle.k cIdle.bench) :=
    mul_live_moves d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole cIdle.bench
      d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  let mvM := mulMovesNo (d.moves + 2 * pegCount (d.xs.take cIdle.n)) cIdle.g
    (d.xs.take cIdle.n) cIdle.n cIdle.k cIdle.bench
  have h5DU : 5 < bU.sudo_5Board_4held.size := by
    have hHeld := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have hsz : bU.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak, Array.size_set]
    rw [hsz]
    exact hkeep.heldLt
  have hheldU : bU.sudo_5Board_4held[5] = true := by
    have hHeld := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h1 := arr_get hHeld 5 h5DU
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    have hszS : 5 <
        (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).sudo_5Board_4held.size := by
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak, Array.size_set]
      exact hkeep.heldLt
    have h2 := arr_get (settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak) 5 hszS
    rw [h2, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.held
  have h5HU : 5 < bU.sudo_5Board_4home.size := by
    have hHome := mul_live_home d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    rw [hHome, Array.size_set]
    exact hkeep.homeLt
  have harrU : bU.sudo_5Board_4home[5] = embed cIdle.g := by
    have hHome := mul_live_home d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h1 := arr_get hHome 5 h5HU
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.arr
  have hmovD : d.moves ≤ mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
    rw [← hmv0, ← hmI, ← h.hn, ← hnI, ← h.hbench, ← hbI]
    simpa [Nat.add_assoc] using d.hmovB
  have hmulLe : mvM ≤ d.moves + mulCharge base.n base.bench := by
    rw [← h.hn, ← hnI, ← h.hbench, ← hbI]
    simpa [mvM, mulStepMoves] using
      mul_moves_delta d.moves cIdle.n cIdle.k cIdle.bench cIdle.g d.xs cIdle.n_le
  have hpegC : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hpegG : pegCount cIdle.g ≤ base.n := by
    rw [hgI]; exact hpegC
  have hpiece := white_clear_move_le mv d.moves (pegCount s.gap) s.tally base.n base.bench
    (pegCount cIdle.g) mvM hmovD hmulLe hpegC hpegG
  have hfitC : FitsLen (mvM + pegCount cIdle.g) := by
    apply FitsLen.of_le base.fitM
    have hmvB : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
      rw [hmvSame]; exact hmvLe
    exact lift_to_budget base.moves0 base.R done.length base.n base.bench s.tally base.mMax
      mv (mvM + pegCount cIdle.g) hT hk hmvB hpiece
  have hclearW := clear_withPark bU paint ctrlM fromH ridxH 5 cIdle.g mvM h5HU h5DU
    hheldU harrU (by simpa [mvM] using hmvU) (by rw [cIdle.hlenx]; exact cIdle.hf) hfitC
  have hdoneLe : done.length ≤ base.R := Nat.le_trans (Nat.le_succ done.length) hk
  have hCtrlB : FitsLen ((s.ctrl + 4) + cIdle.m) := by
    rw [hmI]
    exact ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hrun := parked_clear_transport b bPark bCopy r cIdle cIdle.row0 rowP (s.ctrl + 4)
    fromH ridxH hpark hcopy hFrame hRoom0 hCtrlB hsrcI cIdle.hT0 cIdle.hRow hRoom hAgree hWhite
    (withPark bU paint ctrlM fromH ridxH)
    (withPark (clearHeldBoard bU 5 cIdle.g mvM h5HU h5DU) paint ctrlM fromH ridxH)
    (by
      have hrowC : paint = embed (paintRed rowP cIdle.t0 cIdle.m) := rfl
      simpa [hmI, htI, hrowC] using hmulP)
    hclearW
  let bIdle0 := clearHeldBoard bU 5 cIdle.g mvM h5HU h5DU
  have hC := clearHeld_book bU 5 cIdle.g mvM h5HU h5DU
  have hMulB := mulLive_book d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hPackB := pegPack_board cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hPl := place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hPegF := pegPack_fixed cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hpre : d.xs.take cIdle.n = cubeTimes cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.m := by
    rw [d.hxs]
    exact cubeBenchIter_prefix cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.hlenx cIdle.m
  have hbenchM := mul_live_bench_gap d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides
    d.hole cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    cIdle.hn0 cIdle.gap_pos cIdle.n_le
  have haim := mul_live_aimed d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hmarkM := mul_live_marker d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hbenchI : bIdle0.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0) := by
    rw [hC.2.2.2.2.2.2.2.2.2.2.1, hbenchM, hpre, hmI, hgI, hnI, hkI, hbI, h.hn, h.hbench]
  have hlenI : bIdle0.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hC.2.2.2.1, hMulB.2.2.1, hPackB.2.2.2.1, hplace, hPl.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.len
  have ht0I : bIdle0.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hC.2.2.2.2.1, hMulB.2.2.2.1, hPackB.2.2.2.2.1, hplace, hPl.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.t0
  have hparkI : bIdle0.sudo_5Board_9park_hole = (s.parkAt : Int) := by
    rw [hC.2.2.2.2.2.1, hMulB.2.2.2.2.1, hPackB.2.2.2.2.2.1, hplace, hPl.2.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.park
  have hhighI : bIdle0.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hC.2.2.2.2.2.2.1, hMulB.2.2.2.2.2.1, hPackB.2.2.2.2.2.2.1, hplace,
      hPl.2.2.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.high
  have htierI : bIdle0.sudo_5Board_1t = b.sudo_5Board_1t := by
    have h1 : bIdle0.sudo_5Board_1t = bU.sudo_5Board_1t := by
      simp [bIdle0, clearHeldBoard]
    have h2 : bU.sudo_5Board_1t = d.b.sudo_5Board_1t := by
      simp [bU, mulNoLiveBoard, mulNoOffBoard, settleBoard]
      split <;> rfl
    rw [h1, h2, hPegF.2.2.2, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  obtain ⟨c0, hc0, _⟩ := h.ops 0 (by
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt)
  obtain ⟨c1, hc1, _⟩ := h.ops 1 h.shape.peg.opsGt
  have hszP : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
      place_ops_delta]
    simp [parkKeepBoard]
  have h1p : 1 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszP]; exact h.shape.peg.opsGt
  have h0p : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) h1p
  have hp1 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((c1 + s.tally : Nat) : Int) := by
    have hArr := pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _)
    have hget := arr_get hArr 1 h1p
    rw [hget, Array.getElem_set, if_pos rfl, hmI]
    have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hplace, place_ops_delta]
      simp [parkKeepBoard]
    have h1b : 1 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsz]; exact h.shape.peg.opsGt
    have hplaceOps := place_ops_delta
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hgetB := arr_get (hplace ▸ hplaceOps) 1 h1b
    have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
    have h1k : 1 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hpkOps]; exact h.shape.peg.opsGt
    have hgetK := arr_get hpkOps 1 h1k
    have hcell := hgetB.trans (hgetK.trans hc1)
    have hcOps : cIdle.cOps0 = c1 := by
      apply ofNat_inj_nat
      exact cIdle.hop10.symm.trans hcell
    rw [hcOps, ofNat_eq_natCast]
  have hpNe : ∀ j, j ≠ 1 → ∀ (he : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hp : j < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
    intro j hne he hp
    have hsz0 : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hplace, place_ops_delta]
      simp [parkKeepBoard]
    have hj0 : j < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsz0]; exact he
    have hpB : j < (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      hPackB.1.symm ▸ hp
    have hneB := pegBoard_ops_ne cIdle cIdle.m cIdle.hm (Nat.le_refl _) j hne hj0 hpB
    have hplaceOps := place_ops_delta
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
    have hjk : j < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hpkOps]; exact he
    have hcellB := (arr_get (hplace ▸ hplaceOps) j hj0).trans (arr_get hpkOps j hjk)
    have hBB : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
        (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops :=
      congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hPackB.1
    exact (arr_get hBB j hp).trans (hneB.trans hcellB)
  have hmulArr : bU.sudo_5Board_4cost.sudo_5Costs_3ops =
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int) := by
    have hlive := mul_live_ops d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have hset := settle_ops d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
    have hcMul0 : cMul = c0 := by
      apply ofNat_inj_nat
      have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hplace, place_ops_delta]
        simp [parkKeepBoard]
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
      have hplaceOps := place_ops_delta
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk
      have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
      have h0k : 0 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hpkOps]
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
      have hcell0 := (arr_get (hplace ▸ hplaceOps) 0 h0b).trans
        ((arr_get hpkOps 0 h0k).trans hc0)
      exact hopZ.symm.trans hcell0
    rw [hlive]
    have hidx := settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
    exact ops_set_transport hset 0 hidx h0p (Int.ofNat (cMul + 1)) ((c0 + 1 : Nat) : Int)
      (by rw [hcMul0, ofNat_eq_natCast])
  have hclrArr : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops =
      bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp only [bIdle0, clearHeldBoard]
  have hNat : ∀ j (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ cN : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = (cN : Int) := by
    intro j hj
    obtain ⟨cN, hcN, _⟩ := h.ops j hj
    exact ⟨cN, hcN⟩
  have hslotsIdle := clearSlots_of_bump
    b.sudo_5Board_4cost.sudo_5Costs_3ops
    d.b.sudo_5Board_4cost.sudo_5Costs_3ops
    bU.sudo_5Board_4cost.sudo_5Costs_3ops
    bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops
    s.tally c0 c1
    (Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt) h.shape.peg.opsGt
    hc0 hc1 hNat h0p h1p hp1 hpNe hszP hmulArr hclrArr
  refine ⟨withPark bIdle0 paint ctrlM fromH ridxH, bIdle0, ?_, ?_, hbenchI, ?_, ?_, ?_,
      hlenI, ht0I, hparkI, hhighI, htierI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hmI] using hrun
  · unfold paint ctrlM rowP
    rw [htI, hmI]
    rfl
  · rw [hC.2.2.2.2.2.2.2.2.1]
    exact haim.1
  · rw [hC.2.2.2.2.2.2.2.2.2.1]
    exact haim.2
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hmarkM
  · have h1 : bIdle0.sudo_5Board_7ladder0 = d.b.sudo_5Board_7ladder0 := by
      simp [bIdle0, clearHeldBoard, bU, mulNoLiveBoard, mulNoOffBoard, settleBoard]
      split <;> rfl
    rw [h1, hPegF.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · have h1 : bIdle0.sudo_5Board_6nrungs = d.b.sudo_5Board_6nrungs := by
      simp [bIdle0, clearHeldBoard, bU, mulNoLiveBoard, mulNoOffBoard, settleBoard]
      split <;> rfl
    rw [h1, hPegF.2.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · have h1 : bIdle0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        d.b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
      simp [bIdle0, clearHeldBoard, bU, mulNoLiveBoard, mulNoOffBoard, settleBoard]
      split <;> rfl
    rw [h1, hPegF.2.2.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact h5HU
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2]
    exact h5DU
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_live_home, Array.size_set]
    exact hH6
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, mul_live_held, Array.size_set, settle_held_eq,
      Array.size_set]
    exact hD6
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, mul_live_held, Array.size_set, settle_held_eq,
      Array.size_set]
    exact d.h7
  · intro h5
    simp [bIdle0, clearHeldBoard, Array.getElem_set]
  · intro h6
    have hsz : bIdle0.sudo_5Board_4held.size = bU.sudo_5Board_4held.size := by
      simp only [bIdle0, clearHeldBoard, Array.size_set]
    have h6u0 : 6 < bU.sudo_5Board_4held.size := by
      rw [← hsz]; exact h6
    have hEq : bIdle0.sudo_5Board_4held[6] = bU.sudo_5Board_4held[6]'h6u0 := by
      simp only [bIdle0, clearHeldBoard]
      rw [Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    rw [hEq]
    have hmulH := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h6u : 6 < bU.sudo_5Board_4held.size := by
      rw [hmulH, Array.size_set, settle_held_eq, Array.size_set]
      exact hD6
    rw [arr_get hmulH 6 h6u, Array.getElem_set, if_pos rfl]
  · have hszH : cIdle.b0.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      rw [hplace]
      simp [placeBoard, parkKeepBoard, Array.size_set]
      split <;> simp [Array.size_set]
    have hszO : cIdle.b0.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
      rw [hplace]
      simp [placeBoard, parkKeepBoard, Array.size_set]
      split <;> simp [Array.size_set]
    have hXD : base.xHome < cIdle.b0.sudo_5Board_4held.size := by
      rw [hszH]; exact h.shape.xD
    have hXH : base.xHome < cIdle.b0.sudo_5Board_4home.size := by
      rw [hszO]; exact h.shape.xH
    have hParkD : base.xHome <
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.size := by
      simp [parkKeepBoard]; exact h.shape.xD
    have hParkH : base.xHome <
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home.size := by
      simp [parkKeepBoard]; exact h.shape.xH
    have hPlaceD : base.xHome <
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held.size :=
      hplace.symm ▸ hXD
    have hPlaceH : base.xHome <
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home.size :=
      hplace.symm ▸ hXH
    have hHeldEq : cIdle.b0.sudo_5Board_4held =
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held :=
      congrArg (fun bd => bd.sudo_5Board_4held) hplace
    have hHomeEq : cIdle.b0.sudo_5Board_4home =
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home :=
      congrArg (fun bd => bd.sudo_5Board_4home) hplace
    have hXheld : cIdle.b0.sudo_5Board_4held[base.xHome] = true :=
      (arr_get hHeldEq base.xHome hXD).trans
        ((place_held_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk (Ne.symm h.shape.xNe6)
          hParkD hPlaceD).trans (by simp [parkKeepBoard]; exact h.shape.xHeld))
    have hXarr : cIdle.b0.sudo_5Board_4home[base.xHome] = embed base.x :=
      (arr_get hHomeEq base.xHome hXH).trans
        ((place_home_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk (Ne.symm h.shape.xNe6)
          hParkH hPlaceH).trans (by simp [parkKeepBoard]; exact h.shape.xArr))
    have hsz0 : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsZ
    have hKeep := pegPack_keep cIdle base.xHome base.x cMul cIdle.m cIdle.hm (Nat.le_refl _)
      hXD hXH (by rw [hsrcI]; exact h.shape.xNe6) hXheld hXarr hsz0 hopZ
    have hKeepB : CellKeep d.b base.xHome base.x :=
      { heldLt := hKeep.heldLt, held := hKeep.held, homeLt := hKeep.homeLt, arr := hKeep.arr }
    have hMulK := mulLive_keep d.b 5 6 base.xHome cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides
      d.hole cIdle.bench d.peak d.peakS cMul base.x hH6 hD6 hkeep.opsLt h.shape.xNe6
      hKeepB.heldLt hKeepB.homeLt hKeepB.held hKeepB.arr
    exact clearCell_keep bU 5 base.xHome cIdle.g mvM base.x h5HU h5DU
      (Ne.symm h.shape.xNe5) hMulK
  · refine ⟨raisedPeak d.peakS
      (countHeld (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).sudo_5Board_4held 7), ?_⟩
    have hI : bIdle0.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      simp only [bIdle0, clearHeldBoard]
    rw [hI]
    exact mul_live_strict d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  · refine ⟨raisedHole d.hole (topIdx (school cIdle.n cIdle.g (d.xs.take cIdle.n)
      (List.replicate cIdle.bench 0) false)), ?_⟩
    have hI : bIdle0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      simp only [bIdle0, clearHeldBoard]
    rw [hI]
    simp only [bU, mulNoLiveBoard, mulNoOffBoard]
    rw [ofNat_eq_natCast]
  · rw [hC.1, mul_live_row d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt, d.hrow, hrowI, htI, hmI]
  · rw [hC.2.2.2.2.2.2.2.1, mul_live_ctrl d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves
      d.slides d.hole cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt, d.hctrl, d.hctrlN,
      hctrlI, hmI]
  · refine
      { moves := ?_
        slides := ?_
        opsSize := ?_
        ops := ?_
        peak := ?_ }
    · refine ⟨mv, mvM + pegCount cIdle.g, hmv, ?_, hpiece⟩
      rw [withPark_moves]
      simp [bIdle0, clearHeldBoard]
    · refine ⟨sl, d.slides + 2 * pegCount (d.xs.take cIdle.n), hsl, ?_, ?_⟩
      · rw [withPark_slides]
        simp [bIdle0, clearHeldBoard]
        exact mul_live_slides d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
          cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
      · have hprev : d.slides ≤ sl + s.tally * (2 * s.n) := by
          have hEq : cIdle.slides0 + cIdle.m * (2 * cIdle.n) = sl + s.tally * (2 * s.n) := by
            rw [hsl0, hmI, hnI]
          exact Nat.le_trans d.hsldB (Nat.le_of_eq hEq)
        have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * s.n := by
          rw [← hnI]
          exact Nat.mul_le_mul_left 2 (pegCount_take_le d.xs cIdle.n)
        have hloc : d.slides + 2 * pegCount (d.xs.take cIdle.n) ≤
            sl + s.tally * (2 * s.n) + 2 * s.n := Nat.add_le_add hprev h2
        have hstep : (s.tally + 1) * (2 * s.n) ≤ rungSlideCharge base.n s.tally := by
          unfold rungSlideCharge
          rw [h.hn]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right (s.tally + 1) 2)
        have hsum : sl + s.tally * (2 * s.n) + 2 * s.n = sl + (s.tally + 1) * (2 * s.n) :=
          (Nat.add_assoc sl (s.tally * (2 * s.n)) (2 * s.n)).trans
            (congrArg (fun z => sl + z) (Nat.succ_mul s.tally (2 * s.n)).symm)
        exact Nat.le_trans hloc (Nat.le_trans (Nat.le_of_eq hsum) (Nat.add_le_add_left hstep sl))
    · rw [withPark_ops]
      have h1 : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        simp [bIdle0, clearHeldBoard]
      have h2 : bU.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [mul_live_ops, Array.size_set, settle_ops]
      have h3 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
          place_ops_delta]
        simp [parkKeepBoard]
      rw [h1, h2, h3]
    · intro i hi
      obtain ⟨c0, hc0, _⟩ := h.ops 0 (by
        have hgt := h.shape.peg.opsGt
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) hgt)
      obtain ⟨c1, hc1, _⟩ := h.ops 1 h.shape.peg.opsGt
      have hszP : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
          place_ops_delta]
        simp [parkKeepBoard]
      have h1p : 1 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hszP]; exact h.shape.peg.opsGt
      have h0p : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
        Nat.lt_trans (by decide : (0 : Nat) < 1) h1p
      have hp1 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((c1 + s.tally : Nat) : Int) := by
        have hArr := pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _)
        have hget := arr_get hArr 1 h1p
        rw [hget, Array.getElem_set, if_pos rfl, hmI]
        have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hplace, place_ops_delta]
          simp [parkKeepBoard]
        have h1b : 1 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hsz]; exact h.shape.peg.opsGt
        have hplaceOps := place_ops_delta
          (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk
        have hgetB := arr_get (hplace ▸ hplaceOps) 1 h1b
        have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
            b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
        have h1k : 1 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hpkOps]; exact h.shape.peg.opsGt
        have hgetK := arr_get hpkOps 1 h1k
        have hcell := hgetB.trans (hgetK.trans hc1)
        have hcOps : cIdle.cOps0 = c1 := by
          apply ofNat_inj_nat
          exact cIdle.hop10.symm.trans hcell
        rw [hcOps, ofNat_eq_natCast]
      have hpNe : ∀ j, j ≠ 1 → ∀ (he : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
          (hp : j < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
        intro j hne he hp
        have hsz0 : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hplace, place_ops_delta]
          simp [parkKeepBoard]
        have hj0 : j < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hsz0]; exact he
        have hpB : j < (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
          hPackB.1.symm ▸ hp
        have hneB := pegBoard_ops_ne cIdle cIdle.m cIdle.hm (Nat.le_refl _) j hne hj0 hpB
        have hplaceOps := place_ops_delta
          (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk
        have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
            b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
        have hjk : j < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hpkOps]; exact he
        have hcellB := (arr_get (hplace ▸ hplaceOps) j hj0).trans (arr_get hpkOps j hjk)
        have hBB : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
            (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops :=
          congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hPackB.1
        exact (arr_get hBB j hp).trans (hneB.trans hcellB)
      have hmulArr : bU.sudo_5Board_4cost.sudo_5Costs_3ops =
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int) := by
        have hlive := mul_live_ops d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
          cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
        have hset := settle_ops d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
        have hcMul : cMul = c0 := by
          apply ofNat_inj_nat
          have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hplace, place_ops_delta]
            simp [parkKeepBoard]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
                b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
              rw [hplace, place_ops_delta]
              simp [parkKeepBoard]
            rw [hsz]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have hplaceOps := place_ops_delta
            (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
            6 h.shape.spareH h.shape.spareD s.gap mv pk
          have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
              b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
          have h0k : 0 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hpkOps]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have hcell := (arr_get (hplace ▸ hplaceOps) 0 h0b).trans
            ((arr_get hpkOps 0 h0k).trans hc0)
          exact hopZ.symm.trans hcell
        rw [hlive]
        have hidx := settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
        exact ops_set_transport hset 0 hidx h0p (Int.ofNat (cMul + 1)) ((c0 + 1 : Nat) : Int)
          (by rw [hcMul, ofNat_eq_natCast])
      have hclrArr : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        simp only [bIdle0, clearHeldBoard]
      have hNat : ∀ j (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          ∃ cN : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = (cN : Int) := by
        intro j hj
        obtain ⟨cN, hcN, _⟩ := h.ops j hj
        exact ⟨cN, hcN⟩
      have hbump := rung_ops_of_bump
        b.sudo_5Board_4cost.sudo_5Costs_3ops
        d.b.sudo_5Board_4cost.sudo_5Costs_3ops
        bU.sudo_5Board_4cost.sudo_5Costs_3ops
        bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops
        s.tally base.mMax c0 c1 hT
        (Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt) h.shape.peg.opsGt
        hc0 hc1 hNat h0p h1p hp1 hpNe hszP hmulArr hclrArr
      have hiI : i < bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops.size := hbump.1 ▸ hi
      obtain ⟨c, c', he, hc, hle⟩ := hbump.2 i hi hiI
      refine ⟨c, c', he, ?_, hle⟩
      have harr : (withPark bIdle0 paint ctrlM fromH ridxH).sudo_5Board_4cost.sudo_5Costs_3ops =
          bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [withPark_ops]
      exact (arr_get harr i (harr ▸ hiI)).symm.trans hc
    · obtain ⟨pk0, hpk0, _⟩ := h.peak
      have hpkSame : pk = pk0 := ofNat_inj_nat (hpk.symm.trans hpk0)
      let occ := countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7
      let pk1 := if pk < occ then occ else pk
      have hpk1 : pk1 ≤ max pk0 7 := by
        rw [← hpkSame]
        change (if pk < occ then occ else pk) ≤ max pk 7
        by_cases hlt : pk < occ
        · simp [hlt]
          exact Nat.le_trans (countHeld_seven _) (Nat.le_max_right _ _)
        · simp [hlt]
          exact Nat.le_max_left _ _
      have hpkNat : cIdle.peak0 = pk1 := by
        apply ofNat_inj_nat
        calc
          ((cIdle.peak0 : Nat) : Int) = cIdle.b0.sudo_5Board_4cost.sudo_5Costs_4peak :=
            cIdle.hpeak0.symm
          _ = (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
              6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4cost.sudo_5Costs_4peak := by
            rw [hplace]
          _ = (pk1 : Int) := by
            simp [placeBoard, parkKeepBoard, pk1, occ]
            split <;> simp [hpk]
      have hpegPk : d.peak ≤ max pk0 7 := by
        have hB := d.hpeakB
        rw [hpkNat] at hB
        exact Nat.le_trans hB (by
          have hmax : max pk1 7 ≤ max pk0 7 := by
            exact Nat.max_le.mpr ⟨hpk1, Nat.le_max_right _ _⟩
          exact hmax)
      let pkS := raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7)
      let bS := settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
      let hFs := settle_held_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
      let pkM := raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨6, hFs⟩ false) 7)
      have hpkS : pkS ≤ max pk0 7 :=
        Nat.le_trans (raisedPeak_carry d.peak _ (countHeld_seven _))
          (Nat.max_le.mpr ⟨hpegPk, Nat.le_max_right _ _⟩)
      have hmulPk : pkM ≤ max pk0 7 :=
        Nat.le_trans (raisedPeak_carry pkS _ (countHeld_seven _))
          (Nat.max_le.mpr ⟨hpkS, Nat.le_max_right _ _⟩)
      refine ⟨pk0, pkM, hpk0, ?_, hmulPk⟩
      rw [withPark_peak]
      have hpkB : bIdle0.sudo_5Board_4cost.sudo_5Costs_4peak =
          bU.sudo_5Board_4cost.sudo_5Costs_4peak := by
        simp only [bIdle0, clearHeldBoard]
      rw [hpkB]
      exact mul_live_peak d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
        cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  · exact clearSlots_cast hslotsIdle (withPark_ops bIdle0 paint ctrlM fromH ridxH).symm
  · refine ⟨mv, mvM + pegCount cIdle.g, hmv, ?_,
      white_clear_move_piece mv d.moves (pegCount s.gap) s.tally base.n base.bench
        (pegCount cIdle.g) mvM hmovD hmulLe hpegC hpegG⟩
    rw [withPark_moves]
    simp [bIdle0, clearHeldBoard]
  · refine ⟨sl, d.slides + 2 * pegCount (d.xs.take cIdle.n), hsl, ?_, ?_⟩
    · rw [withPark_slides]
      simp [bIdle0, clearHeldBoard]
      exact mul_live_slides d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
        cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    · have hprev : d.slides ≤ sl + s.tally * (2 * s.n) := by
        have hEq : cIdle.slides0 + cIdle.m * (2 * cIdle.n) = sl + s.tally * (2 * s.n) := by
          rw [hsl0, hmI, hnI]
        exact Nat.le_trans d.hsldB (Nat.le_of_eq hEq)
      have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * s.n := by
        rw [← hnI]
        exact Nat.mul_le_mul_left 2 (pegCount_take_le d.xs cIdle.n)
      have hloc : d.slides + 2 * pegCount (d.xs.take cIdle.n) ≤
          sl + s.tally * (2 * s.n) + 2 * s.n := Nat.add_le_add hprev h2
      rw [h.hn] at hloc
      exact hloc


theorem final_white_ctrl_fit_ge (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 1 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen ((ctrl + 4 + tally) + 2) ∧
    FitsLen (((ctrl + 4 + tally) + 2) + 2) ∧
    FitsLen ((ctrl + 4 + tally) + tally) := by
  have hx : 2 * (3 * mMax + 5) = 6 * mMax + 10 := by omega
  have hsplit : done * (3 * mMax + 5) + 2 * (3 * mMax + 5) =
      (done + 2) * (3 * mMax + 5) := (Nat.add_mul done 2 (3 * mMax + 5)).symm
  have hge : (done + 2) * (3 * mMax + 5) ≤ (R + 1) * (3 * mMax + 5) :=
    Nat.mul_le_mul_right _ (by omega : done + 2 ≤ R + 1)
  have hcap : ctrl + (6 * mMax + 10) ≤ ctrl0 + (R + 1) * (3 * mMax + 5) := by
    have h1 : ctrl + (6 * mMax + 10) ≤
        ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) := by omega
    have h2 : ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) =
        ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) := by
      rw [← hx]
      exact Nat.add_assoc _ _ _
    have h3 : ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) ≤
        ctrl0 + (R + 1) * (3 * mMax + 5) := by
      rw [hsplit]
      exact Nat.add_le_add_left hge _
    exact Nat.le_trans (Nat.le_trans h1 (Nat.le_of_eq h2)) h3
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega)⟩

/-- A parked final white rung. The clear is the idle clear with the restored
    row and a counter two higher, and that board is the `ClimbInvK` successor. -/
theorem white_final_ge
    {done : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [r] b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done [r] ≤ base.mMax) :
    ∃ b',
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) = .ok b' ∧
      ClimbInvK (done ++ [r]) [] b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) true) base ∧
      RungDelta b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole true
  obtain ⟨b', bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E, hparkE,
      hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
      ⟨ps, hps⟩, ⟨hnat, hhn⟩, _hrowIdle, _hctrlIdle, hδ, _hslots, _hpieceM, _hpieceS⟩ :=
    parked_clear_ge h hge hm hT hhome
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_final_white_ge s base.x r hole hwhite hge
  have hrowE : b'.sudo_5Board_3row =
      embed (paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally) := by
    rw [hframe, withPark_row]
  have hctrlE : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    rw [hframe, withPark_ctrl]
  have hfromE : b'.sudo_5Board_11parked_from = ((hole : Nat) : Int) := by
    rw [hframe, withPark_from]
  have hridxE : b'.sudo_5Board_8rung_idx = Int.ofNat (s.ridx + 1) := by
    rw [hframe, withPark_ridx]
  have hlenB : b'.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hframe, withPark_len, hlenE]
  have ht0B : b'.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hframe, withPark_tally0, ht0E]
  have hparkB : b'.sudo_5Board_9park_hole = (s.parkAt : Int) := by
    rw [hframe, withPark_park, hparkE]
  have hhighB : b'.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hframe, withPark_high, hhighE]
  have hmarkB : b'.sudo_5Board_9marker_on = false := by
    rw [hframe, withPark_marker, hmarkE]
  have hbonB : b'.sudo_5Board_8bench_on = true := by
    rw [hframe, withPark_on, hbonE]
  have htoB : b'.sudo_5Board_8bench_to = (5 : Int) := by
    rw [hframe, withPark_to, htoE]
  have hbenchB : b'.sudo_5Board_5bench = bIdle.sudo_5Board_5bench := by
    rw [hframe, withPark_bench]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [hframe, withPark_tier, htierE]
  have hladB : b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
    rw [hframe, withPark_ladder, hladE]
  have hnrB : b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
    rw [hframe, withPark_nrungs, hnrE]
  have htmaxB : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    rw [hframe, withPark_tmax, htmaxE]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hinv : ClimbInv b' s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := hmarkB
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · rw [hframe, withPark_home]
      exact h5H
    · rw [hframe, withPark_held]
      exact h5D
    · rw [hlenB, htall]
    · rw [hctrlE, hctrlM]
    · rw [hhighB, hhighM]
    · rw [ht0B, ht0M]
    · rw [hrowE, hrowM]
    · rw [hparkB, hparkM]
    · rw [hfromE, hfromM]
    · rw [hridxE, hridxM, ofNat_eq_natCast]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨hbonB, htoB, ?_, ?_⟩
      · rw [hbenchB, hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork]
        exact hgap.symm
  have hseg : RowSeg s'.row s'.t0 s'.tally true := by
    have hsegR := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge))
    rw [hrowM, ht0M, htall]
    exact hsegR
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone base.fitCtrl
  have hpark' : ParkRead b' s' [] base := by
    refine
      { ladder0B := ?_
        nrungsB := ?_
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · rw [hladB, h.shape.park.ladder0B]
    · rw [hnrB, h.shape.park.nrungsB]
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [hladB, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrB, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      exact h.shape.park.parkLe
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _
      rw [hfromM]
      rfl
    · intro _
      rw [hfromM]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hle : hole ≤ s.high := by
          have hhi : hole < s.t0 := h.holeBelow
          have htop : s.high = s.t0 + s.tally - 1 := h.highTop hm
          omega
        rw [hhighM]
        simpa [Int.toNat_ofNat] using hle
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro _ _ hrs
      cases hrs
    · intro _ hk _hlt
      simp at hk
    · rw [hctrlM]
      exact hfits.1
    · rw [hctrlM]
      exact hfits.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  have h6B : 6 < b'.sudo_5Board_4held.size := by
    rw [hframe, withPark_held]; exact h6D
  have h6H' : 6 < b'.sudo_5Board_4home.size := by
    rw [hframe, withPark_home]; exact h6H
  have h7B : 7 ≤ b'.sudo_5Board_4held.size := by
    rw [hframe, withPark_held]; exact h7E
  have h6fB : b'.sudo_5Board_4held[6] = false := by
    have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    exact (arr_get hEq 6 h6B).trans (h6f h6D)
  have h5fB : b'.sudo_5Board_4held[5] = false := by
    have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    have h5B : 5 < b'.sudo_5Board_4held.size := by
      rw [hframe, withPark_held]; exact h5D
    exact (arr_get hEq 5 h5B).trans (h5f h5D)
  have hkeepB : CellKeep b' base.xHome base.x := by
    have hHeld : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    have hHome : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by
      rw [hframe, withPark_home]
    exact
      { heldLt := by rw [hHeld]; exact hkeep.heldLt
        held := (arr_get hHeld base.xHome (by rw [hHeld]; exact hkeep.heldLt)).trans hkeep.held
        homeLt := by rw [hHome]; exact hkeep.homeLt
        arr := (arr_get hHome base.xHome (by rw [hHome]; exact hkeep.homeLt)).trans hkeep.arr }
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := ?_
        cOps := ?_
        peakS := ?_
        holeM := ?_
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · have hsz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ.opsSize
      exact hsz ▸ h.shape.peg.opsGt
    · have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
      obtain ⟨_c, c', _he, hc, _⟩ := hδ.ops 1 h1
      exact ⟨c', hc⟩
    · exact ⟨ps, by rw [hframe, withPark_strict, hps]⟩
    · exact ⟨hnat, by rw [hframe, withPark_hole, hhn]⟩
    · rw [hgap]
      have hspan : 3 * (s.n - 1) < s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have hnle : s.n ≤ s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have htri := fieldMul_trits s.n s.k s.benchlen s.gap
        (cubeBenchIter s.n s.k s.benchlen s.gap s.tally) hspan hnle
      rw [cubeBenchIter_prefix s.n s.k s.benchlen s.gap (h.shape.gapLen)] at htri
      exact htri
    · intro hpos
      rw [ht0M, htall, hhighM]
      exact Nat.le_of_eq (h.highTop (htall.symm ▸ hpos)).symm
    · rw [ht0M, htall]; exact h.shape.peg.fitRow
    · rw [htall]; exact h.shape.peg.fitTall
    · rw [hctrlM, htall]; exact hfits.2.2
    · rw [hnM]; exact h.shape.peg.n_pos
    · rw [hnM, hbM]; exact h.shape.peg.span
    · rw [hbM]; exact h.shape.peg.small
    · rw [hnM]; exact h.shape.peg.n_small
    · rw [hnM]; exact h.shape.peg.fitN
    · rw [hbM]; exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] hnM hkM hbM hgapLen
      hseg h6B h6H' h6fB h7B
      (by intro _; exact h5fB)
      (by intro hOff; rw [hon] at hOff; cases hOff)
      hkeepB.heldLt hkeepB.homeLt hkeepB.held hkeepB.arr
      (by rw [htierB, hnM]; exact h.shape.tierN)
      (by rw [htierB, hkM]; exact h.shape.tierK)
      (by rw [htierB, hbM]; exact h.shape.tierB)
      (by rw [htierB]; exact h.shape.tierW)
      (by rw [htierB]; exact h.shape.tierH)
      (by rw [htierB]; exact h.shape.tierR)
      (by rw [htierB]; exact h.shape.tierCg)
      (by rw [htierB]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, by rw [htmaxB, htm], ?_⟩
    intro hpos
    have hlt := hnote (by rw [← htall]; exact hpos)
    rw [htall]
    exact hlt
  have hK := climbInvK_succ h hinv hδ hCap hshape h.holeBelow htmax rfl
  exact ⟨b', hrun, hK, hδ⟩

theorem open_white_ctrl_fit_ge (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 2 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 4 + 3 * tally) ∧
    FitsLen ((ctrl + 4 + 3 * tally) + 2) ∧
    FitsLen ((ctrl + 4 + 3 * tally) + 4) ∧
    FitsLen (ctrl + 4 + 3 * tally + 2 * tally) := by
  have hmul : (done + 2) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (6 * mMax + 10) := by
    rw [Nat.add_mul]
    omega
  have hbody : ctrl + 6 * mMax + 10 ≤ ctrl0 + (done + 2) * (3 * mMax + 5) := by
    omega
  have hcap : ctrl0 + (done + 2) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega)⟩

/-- A parked non-final white rung. The clear is the idle clear transported
    across the resume frame; doubling that frame is `tally_double_withPark`. -/
theorem white_open_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2) (hrest : rest ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          Ecbs.tally_double b) = .ok b' ∧
      ClimbInvK (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base ∧
      RungDelta b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  have habove := h.srcAbove hge
  obtain ⟨bClear, bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E, hparkE,
      hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
      ⟨ps, hps⟩, ⟨hnat, hhn⟩, hrowIdle, hctrlIdle, hδ, _hslots, _hpieceM, _hpieceS⟩ :=
    parked_clear_ge h hge hm hT hhome
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_open_white_ge s base.x r hole hwhite hge
  let c0 := s.ctrl + 2 + s.tally
  let xs := paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
  let xsP := paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
  have hgeLen : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hgeLen
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax0, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax0 < 2 * s.tally := hNote0 hm
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_white_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hRowLen : s.t0 + 2 * s.tally ≤ s.row.length := by
    rw [h.shape.rowLen]; exact hRoom
  have hRedIdle : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hRedPark : ∀ j (hj : j < s.tally),
      xsP[s.t0 + j]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xsP] using paintRed_get_lo (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZeroIdle : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      exact Nat.lt_of_lt_of_le hlt hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inl (by decide : (-1 : Int) < 0)) hjLen
    have hget := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xs] using hget.trans (hAp.trans hsrc)
  have hZeroPark : ∀ k (hk : k < s.tally),
      xsP[s.t0 + s.tally + k]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      exact Nat.lt_of_lt_of_le hlt hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (by omega))) hjLen
    have hget := paintRed_get_hi (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xsP] using hget.trans (hAp.trans hsrc)
  have hctrlN : bIdle.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    rw [htierE, h.shape.tierC]
  have htallD := tally_double_withPark bIdle xs xsP s.t0 s.tally c0
    (s.t0 + s.tally - 1) base.control tmax0 ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hm hlenE ht0E hrowIdle
    (by simp [xs, paintRed_length, afterPark_length]; exact hRowLen)
    (by simp [xsP, paintRed_length, afterPark_length]; exact hRowLen)
    hRedIdle hRedPark hZeroIdle hZeroPark hctrlN
    (by rw [hhighE, hHighEq]) rfl hctrlIdle hRoom hFitI
    (FitsLen.of_le hfits.1 (by omega))
    (FitsLen.of_le hfits.2.1 (by omega))
    hFitM (htmaxE.trans hMax) hNote
  have hctr : ((c0 + 2 : Nat) : Int) = ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    unfold c0
    exact congrArg (fun n : Nat => (n : Int)) (by omega)
  have hmatch : withPark bIdle (embed xsP) (((c0 + 2 : Nat) : Int))
      ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) = bClear := by
    rw [hctr, hframe]
  rw [hmatch] at htallD
  let bIn :=
    { bIdle with
        sudo_5Board_3row := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
        sudo_5Board_9tally_len := Int.ofNat (2 * s.tally)
        sudo_5Board_4cost := { bIdle.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (c0 + 2 * s.tally)
          sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
          sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally) } }
  have hmvIn : bIn.sudo_5Board_4cost.sudo_5Costs_5moves =
      bIdle.sudo_5Board_4cost.sudo_5Costs_5moves := rfl
  have hslIn : bIn.sudo_5Board_4cost.sudo_5Costs_6slides =
      bIdle.sudo_5Board_4cost.sudo_5Costs_6slides := rfl
  have hopsIn : bIn.sudo_5Board_4cost.sudo_5Costs_3ops =
      bIdle.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  have hpkIn : bIn.sudo_5Board_4cost.sudo_5Costs_4peak =
      bIdle.sudo_5Board_4cost.sudo_5Costs_4peak := rfl
  let b' := withPark bIn
    (embed (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally))
    (Int.ofNat (c0 + 2 + 2 * s.tally))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          Ecbs.tally_double b) = .ok b' := by
    rw [hrun, ok_bind]
    simpa [b', bIn, xs, xsP, c0] using htallD
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hctrlNat : c0 + 2 + 2 * s.tally = s'.ctrl := by
    unfold s' c0
    rw [hctrlM]
    omega
  have hinv : ClimbInv b' s' := by
    refine
      { hG := by unfold b'; rw [withPark_home]; exact h5H
        hGs := by unfold b'; rw [withPark_held]; exact h5D
        marker := by unfold b'; rw [withPark_marker]; exact hmarkE
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · unfold b'; rw [withPark_len, htall]
      rfl
    · unfold b'; rw [withPark_ctrl, hctrlNat, ofNat_eq_natCast]
    · unfold b'; rw [withPark_high, hhighM]
    · unfold b'; rw [withPark_tally0, ht0E, ht0M]
    · unfold b'; rw [withPark_row, hrowM]
    · unfold b'; rw [withPark_park, hparkE, hparkM]
    · unfold b'; rw [withPark_from, hfromM]
    · unfold b'; rw [withPark_ridx, hridxM, ofNat_eq_natCast]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨by unfold b'; rw [withPark_on]; exact hbonE, by unfold b'; rw [withPark_to]; exact htoE, ?_, ?_⟩
      · unfold b'; rw [withPark_bench, hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork]
        exact hgap.symm
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty := by
    rw [hempty]
    have hsegR := rungRow_open_white_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge))
      (by rw [h.shape.rowLen]; exact hRoom) hwhite
    have hrowEq : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
      simp [s', modelRung, rungRow]
    rw [hrowEq, show s'.t0 = s.t0 by simp [s', modelRung], htall]
    exact hsegR
  have hδ' : RungDelta b b' base s.tally := by
    apply rungDelta_cost hδ
    · unfold b'; rw [withPark_moves, hmvIn, hframe, withPark_moves]
    · unfold b'; rw [withPark_slides, hslIn, hframe, withPark_slides]
    · unfold b'; rw [withPark_ops, hopsIn, hframe, withPark_ops]
    · unfold b'; rw [withPark_peak, hpkIn, hframe, withPark_peak]
  have hpark' : ParkRead b' s' rest base := by
    refine
      { ladder0B := by unfold b'; rw [withPark_ladder, hladE, h.shape.park.ladder0B]
        nrungsB := by unfold b'; rw [withPark_nrungs, hnrE, h.shape.park.nrungsB]
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        unfold b'; rw [withPark_ladder, hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        unfold b'; rw [withPark_nrungs, hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      have hhi : s.parkAt < s.t0 := h.parkBelow
      omega
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _
      rw [hfromM]
      rfl
    · intro _
      rw [hfromM]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · rw [hhighM]
        have hhi : hole < s.t0 := h.holeBelow
        simpa [Int.toNat_ofNat] using (by omega : hole ≤ s.t0 + 2 * s.tally - 1)
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rs hrs
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail 1 (by simp [hrs]) hlt0
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1) < s.t0 :=
        climb_below base.ladder0 base.R s.ridx 1 s.t0 h.shape.park.l0pos
          (by omega) h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
      have hneS : s.fromHole.toNat ≠ climbAt base.ladder0 base.R (s.ridx + 1) := by
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        have hi : s.ridx + 1 ≤ base.R := by
          rw [h.idx]
          omega
        have hltC : climbAt base.ladder0 base.R (s.ridx + 1) <
            climbAt base.ladder0 base.R s.ridx := by
          unfold climbAt
          omega
        omega
      have hget := rungRow_white_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1)) hwhite hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      have hhead : (r :: rest)[1]'(by simp [hrs]) = r2 := by simp [hrs]
      refine ⟨?_, ?_⟩
      · simpa [hrowR, hridxM, hhead] using hget.trans hcol
      · simpa [hhead] using hnz
    · intro k hk hlt
      have hoff : s.ridx + (1 + k) ≤ base.R := by
        rw [h.idx]
        have hlenK := h.kLe
        simp [List.length_append, List.length_cons] at hlenK
        omega
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.row.length := by
        rw [← hlenRow, ← hridxM]
        exact hlt
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail (1 + k) (by simp; omega)
        (by simpa [Nat.add_assoc] using hlt0)
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.t0 := by
        simpa [Nat.add_assoc] using
          climb_below base.ladder0 base.R s.ridx (1 + k) s.t0 h.shape.park.l0pos hoff
            h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1 + k) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        intro heq
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        simp [hole, climbAt] at heq
        omega
      have hneS : s.fromHole.toNat ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        have hi : s.ridx + 1 + k ≤ base.R := by
          simpa [Nat.add_assoc] using hoff
        have hltC : climbAt base.ladder0 base.R (s.ridx + 1 + k) <
            climbAt base.ladder0 base.R s.ridx := by
          unfold climbAt
          omega
        omega
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hget := rungRow_white_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hwhite hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
          climbAt base.ladder0 base.R (s.ridx + 1 + k) := by rw [hridxM]
      have hmove := getElem_congr (c := s'.row)
        (i := climbAt base.ladder0 base.R (s'.ridx + k))
        (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := hlt) hixEq
      have hcoll := getElem_congr_coll (c := s'.row)
        (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false)
        (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := by rw [← hixEq]; exact hlt) hrowR
      have hlist := cons_tail r rest k hk
      refine ⟨?_, ?_⟩
      · exact hmove.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((cons_tail r rest k hk).trans hz)
    · rw [hctrlM]
      exact hfits.2.1
    · rw [hctrlM]
      exact hfits.2.2.1
    · have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := by
          have hsz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ'.opsSize
          exact hsz ▸ h.shape.peg.opsGt
        cOps := by
          have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
          obtain ⟨_c, c', _he, hc, _⟩ := hδ'.ops 1 h1
          exact ⟨c', hc⟩
        peakS := ⟨ps, by unfold b'; rw [withPark_strict]; exact hps⟩
        holeM := ⟨hnat, by unfold b'; rw [withPark_hole]; exact hhn⟩
        trits := by
          rw [hgap]
          have hspan : 3 * (s.n - 1) < s.benchlen := by
            have hs := h.shape.peg.span
            omega
          have hnle : s.n ≤ s.benchlen := by
            have hs := h.shape.peg.span
            omega
          have htri := fieldMul_trits s.n s.k s.benchlen s.gap
            (cubeBenchIter s.n s.k s.benchlen s.gap s.tally) hspan hnle
          rw [cubeBenchIter_prefix s.n s.k s.benchlen s.gap h.shape.gapLen] at htri
          exact htri
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · intro hpos
      rw [ht0M, htall, hhighM]
      omega
    · rw [ht0M, htall]; exact hFitI
    · rw [htall]; exact hFitM
    · rw [hctrlM, htall]; exact hfits.2.2.2
    · rw [hnM]; exact h.shape.peg.n_pos
    · rw [hnM, hbM]; exact h.shape.peg.span
    · rw [hbM]; exact h.shape.peg.small
    · rw [hnM]; exact h.shape.peg.n_small
    · rw [hnM]; exact h.shape.peg.fitN
    · rw [hbM]; exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' rest base :=
    shape_refresh h.shape b' s' rest hnM hkM hbM hgapLen hseg
      (by unfold b'; rw [withPark_held]; exact h6D)
      (by unfold b'; rw [withPark_home]; exact h6H)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
          unfold b'; rw [withPark_held]
        have h6 : 6 < b'.sudo_5Board_4held.size := by rw [hEq]; exact h6D
        exact (arr_get hEq 6 h6).trans (h6f h6D))
      (by unfold b'; rw [withPark_held]; exact h7E)
      (by
        intro _
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
          unfold b'; rw [withPark_held]
        have h5 : 5 < b'.sudo_5Board_4held.size := by rw [hEq]; exact h5D
        exact (arr_get hEq 5 h5).trans (h5f h5D))
      (by intro hOff; rw [hon] at hOff; cases hOff)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by unfold b'; rw [withPark_held]
        rw [hEq]; exact hkeep.heldLt)
      (by
        have hEq : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by unfold b'; rw [withPark_home]
        rw [hEq]; exact hkeep.homeLt)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by unfold b'; rw [withPark_held]
        exact (arr_get hEq base.xHome (by rw [hEq]; exact hkeep.heldLt)).trans hkeep.held)
      (by
        have hEq : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by unfold b'; rw [withPark_home]
        exact (arr_get hEq base.xHome (by rw [hEq]; exact hkeep.homeLt)).trans hkeep.arr)
      (by unfold b'; rw [withPark_tier, htierE, hnM]; exact h.shape.tierN)
      (by unfold b'; rw [withPark_tier, htierE, hkM]; exact h.shape.tierK)
      (by unfold b'; rw [withPark_tier, htierE, hbM]; exact h.shape.tierB)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierW)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierH)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierR)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierCg)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally, ?_, ?_⟩
    · unfold b'; rw [withPark_tmax]
      simp
    · intro hpos
      rw [htall]
      omega
  have hK := climbInvK_succ h (by simpa [hempty] using hinv) hδ' hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax) rfl
  exact ⟨b', hprog, by simpa [hempty] using hK, hδ'⟩

/-- The emitted parked clear is `withPark` of the unparked clear. The keep-park
    copy for `fromHole ≥ 0` is `withPark` of the idle entry copy; `withPark`
    then pushes through the peg loop, the gap mul, and `clear`, and a second
    park overwrites the idle frame. -/
theorem parked_clear_unparked
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ bClearU bCube bRed,
      (do
          let b ← Ecbs.park_rung b (r : Int)
          let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
          let _ ← SudoRt.runLoopOn (Int.ofNat 0)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (whiteStep b (Int.ofNat (s.tally - 1)))
              (fun j => .ok (b, j))
              (fun _ => .ok (b, (0 : Int)))
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
              (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
              (cubePegStep 6 (Int.ofNat (s.tally - 1)))
              (fun σ => .ok σ)
              (fun r => .ok ((0 : Int), r))
          let b := out.2
          let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
          Ecbs.clear b (5 : Int)) =
        .ok (withPark bClearU
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.cube (withPark bClearU
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)))
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark bCube
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.mul (withPark bCube
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)))
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withPark bRed
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      (∃ mvE mvR slE slR : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
        mvR ≤ mvE + rungCharge base.n base.bench s.tally ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
        slR ≤ slE + rungSlideCharge base.n s.tally) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      ∃ (bLoop bMul : Ecbs.Board),
        Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
            false false false = .ok bMul ∧
        Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClearU ∧
        (∃ (cU : PegCtx) (ys : List Nat) (moves slides hole peak peakS cOps : Nat)
          (hH : 6 < bLoop.sudo_5Board_4home.size)
          (hD : 6 < bLoop.sudo_5Board_4held.size)
          (hops : 0 < bLoop.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          bLoop = pegBoard cU cU.m ∧
          cU.row0 = s.row ∧ cU.ctrl0 = s.ctrl ∧ cU.g = s.gap ∧ cU.m = s.tally ∧
          cU.n = s.n ∧ cU.k = s.k ∧ cU.bench = s.benchlen ∧ cU.src = 6 ∧
          cU.t0 = s.t0 ∧
          bMul = mulNoLiveBoard bLoop 5 6 cU.g ys cU.n cU.k moves slides hole cU.bench
            peak peakS cOps hH hD hops ∧
          ys = cubeBenchIter cU.n cU.k cU.bench cU.g cU.m ∧
          moves = (pegPack cU cU.m cU.hm (Nat.le_refl _)).moves ∧
          slides = (pegPack cU cU.m cU.hm (Nat.le_refl _)).slides ∧
          hole = (pegPack cU cU.m cU.hm (Nat.le_refl _)).hole ∧
          peak = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peak ∧
          peakS = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peakS ∧
          Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok cU.b0) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨cM, bM, ys, moves, slides, holeM, peak, peakS, cOps, hH, hD, hops,
      hcopyM, hsrcM, hgM, hmM, hnM, hkM, hbM, hpegM, _hys, hGap, _hX, _hFit, _hMov,
      _hSFit, _hSLe, _hOp, _hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, hctrlM, _hhigh,
      _hcontrol, _hlen, _hmax, ht0M, hmul, hrowM, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨_, _, _⟩, ⟨_, _, _⟩, hmulW⟩ :=
    mul_of_shape h hm hT hhome
  obtain ⟨bLoopR, bMulR, bClearU, bCube, bRed, hmulR, hclearR, hcubeU, hredU,
      _bounds, _hlenC, _ht0C, _hrowC, _hctrlN, _hhighC, _hctrlC, _hmaxC,
      _ht0Cube, _ht0Red, _htierCube, _htierRed, _hcubeF, _hmulF,
      honR, htoR, hlenR, hbenchR, hclearP, hcubeP, hmulP,
      _hcubeBoth, _hmulBoth, hpack, hrel, hhighR, htmaxR⟩ :=
    red_cube_mul h hm hT hhome hxLen hxT
  have hpackKeep := hpack
  obtain ⟨cU, _ysU, _mvU, _slU, _hoU, _pkU, _psU, _cOpsU, _hHU, _hDU, _hopsU,
      hloopU, hrowU, hctrlU, hgU, hmU, hnU, hkU, hbU, hsrcU, ht0U, _hnamed,
      _hysU, _hmvU, _hslU, _hhoU, _hpkU, _hpsU, hcopyU⟩ := hpack
  obtain ⟨mv, pk, sl, cE, hmv, hpk, _hsl, _hmvLe, _hslLe, hb0, hcopyE, _hsrcE, _hgE, _hmE,
      _hrowE, _hnE, _hkE, _hbE, _hmv0, _hsl0, _ht0E, _hctrlE, _hhighE, _hcontrolE,
      _hlenE, _hmaxE⟩ :=
    peg_of_shape h hm hT hhome
  have hb0M : cE.b0 = cM.b0 := by injection hcopyE.symm.trans hcopyM
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  let rowI := afterPark s.row (-1) s.parkAt hole r
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  let bKeep := parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hPW := parkKeep_withPark b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH
    h.inv.row h.shape.park.parkLt h.shape.park.holeLt
  have hplI := placeBoard_withPark b (embed rowI) (Int.ofNat (s.ctrl + 2))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hb0p : placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk = cE.b0 := hb0.symm
  have hIdle : placeBoard bKeep 6 h.shape.spareH h.shape.spareD s.gap mv pk =
      withPark cE.b0 (embed rowI) (Int.ofNat (s.ctrl + 2))
        ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    have h1 := place_of_eq hPW 6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hir := placeBoard_irrel
      (withPark b (embed rowI) (Int.ofNat (s.ctrl + 2)) ((hole : Nat) : Int)
        (Int.ofNat (s.ridx + 1)))
      6 (hPW ▸ h.shape.spareH) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hPW ▸ h.shape.spareD) (withPark_held _ _ _ _ _ ▸ h.shape.spareD)
      s.gap mv pk
    rw [h1, hir, hplI, hb0p]
  obtain ⟨bPark, bCopy, mvR, pkR, h6H, h6D, hpark, hcopy, hplaceR, hmvR, hpkR⟩ :=
    resume_copy h hge hm hT hhome
  obtain ⟨bPark', bKeep', hRowP', hRowH', hpark', hkeep', hframe⟩ :=
    resume_park_withPark h hge
  have hParkEq : bPark = bPark' := by injection hpark.symm.trans hpark'
  have hKeepEq : bKeep' = bKeep := by
    rw [hkeep']
  have hmvE : mv = mvR := ofNat_inj_nat (hmv.symm.trans hmvR)
  have hpkE : pk = pkR := ofNat_inj_nat (hpk.symm.trans hpkR)
  have hctrl4 : ((s.ctrl + 4 : Nat) : Int) = Int.ofNat (s.ctrl + 4) := rfl
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  let ctrlReal := ((s.ctrl + 4 : Nat) : Int)
  have hGePlace : placeBoard bPark 6 h6H h6D s.gap mvR pkR =
      withPark cE.b0 (embed rowP) ctrlReal fromH ridxH := by
    have hParkW : bPark = withPark bKeep (embed rowP) ctrlReal fromH ridxH := by
      rw [hParkEq, hframe, hKeepEq]
    have h1 := place_of_eq hParkW 6 h6H h6D s.gap mvR pkR
    have hIH : 6 < bKeep.sudo_5Board_4home.size := by
      simpa [bKeep, parkKeepBoard] using h.shape.spareH
    have hID : 6 < bKeep.sudo_5Board_4held.size := by
      simpa [bKeep, parkKeepBoard] using h.shape.spareD
    have hplP := placeBoard_withPark bKeep (embed rowP) ctrlReal fromH ridxH
      6 hIH hID s.gap mvR pkR
    have hir := placeBoard_irrel
      (withPark bKeep (embed rowP) ctrlReal fromH ridxH)
      6 (hParkW ▸ h6H) (withPark_home _ _ _ _ _ ▸ hIH)
      (hParkW ▸ h6D) (withPark_held _ _ _ _ _ ▸ hID)
      s.gap mvR pkR
    rw [h1, hir, hplP]
    have hmvR : mvR = mv := hmvE.symm
    have hpkR : pkR = pk := hpkE.symm
    rw [hmvR, hpkR, hIdle, withPark_withPark]
  have hFrame : bCopy = withPark cM.b0 (embed rowP) ctrlReal fromH ridxH := by
    rw [hplaceR, hGePlace, hb0M]
  have hRoom0 : cM.t0 + cM.m ≤ rowP.length := by
    rw [ht0M, hmM, afterPark_length]
    exact h.shape.seg.room
  have hRoom : cM.t0 + cM.m ≤ s.row.length := by
    rw [ht0M, hmM]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hCtrlB : FitsLen (s.ctrl + 4 + s.tally) :=
    ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hCtrlM : FitsLen ((s.ctrl + 4) + cM.m) := by
    rw [hmM]; exact hCtrlB
  have hAgree : ∀ j (hj : j < cM.m),
      rowP[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom0) =
        s.row[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom) := by
    intro j hj
    have hjM : j < s.tally := by
      rw [hmM] at hj
      exact hj
    have hix : s.t0 + j < s.row.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) h.shape.seg.room
    have hget := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (Nat.le_add_right s.t0 j)))
      hix
    have ht : cM.t0 = s.t0 := ht0M
    have hL := get_add_eq ht (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom0)
    have hR := get_add_eq ht.symm hix
    exact hL.trans (hget.trans hR)
  have hWhite : ∀ j (hj : j < cM.m),
      s.row[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom) = 1 := by
    intro j hj
    have hjM : j < s.tally := by
      rw [hmM] at hj
      exact hj
    have hcol := h.shape.seg.colour j hjM
    have hfin : (r :: rest).isEmpty = false := by simp
    simpa [hfin, ht0M] using hcol
  have hRowIdle : cM.b0.sudo_5Board_3row = embed s.row := by
    rw [cM.hRow, hrowM]
  have hbLoop : bM = bLoopR := by
    have hb0U : cM.b0 = cU.b0 := by injection hcopyM.symm.trans hcopyU
    have hboards := pegBoard_same_copy cM cU hb0U
      (hsrcU.trans hsrcM.symm) (hgU.trans hgM.symm) (hnU.trans hnM.symm)
      (hkU.trans hkM.symm) (hbU.trans hbM.symm) (hrowU.trans hrowM.symm)
      (ht0U.trans ht0M.symm) (hctrlU.trans hctrlM.symm) (hmU.trans hmM.symm)
    rw [hpegM, hloopU, hboards]
  have hMulIn : mulNoLiveBoard bM 5 6 cM.g ys cM.n cM.k moves slides holeM cM.bench
      peak peakS cOps hH hD hops = bMulR := by
    have hmulR' : Ecbs.mul bM ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
        false false false = .ok bMulR := by
      rw [hbLoop]
      exact hmulR
    have hjoin := hmul.symm.trans hmulR'
    injection hjoin
  let paint := embed (paintRed rowP cM.t0 cM.m)
  let ctrlP := Int.ofNat ((s.ctrl + 4) + cM.m)
  have hMulRun := hmulW paint ctrlP fromH ridxH
  have hMulRun' : Ecbs.mul (withPark bM paint ctrlP fromH ridxH)
      (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (withPark bMulR paint ctrlP fromH ridxH) := by
    simpa [hMulIn] using hMulRun
  have hClearRun := hclearP paint ctrlP fromH ridxH
  have hctrlN : ctrlP = Int.ofNat (s.ctrl + 4 + s.tally) := by
    unfold ctrlP
    rw [hmM]
  have hpaint : paint = embed (paintRed rowP s.t0 s.tally) := by
    unfold paint
    rw [ht0M, hmM]
  have hrun := parked_clear_transport b bPark bCopy r cM s.row rowP (s.ctrl + 4)
    fromH ridxH hpark hcopy hFrame hRoom0 hCtrlM hsrcM cM.hT0 hRowIdle hRoom
    hAgree hWhite
    (withPark bMulR paint ctrlP fromH ridxH)
    (withPark bClearU paint ctrlP fromH ridxH)
    (by
      rw [← hpegM]
      exact hMulRun')
    hClearRun
  rw [hctrlN, hpaint, hmM] at hrun
  unfold rowP hole fromH ridxH at hrun
  let paintF := embed (paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally)
  let ctrlF := Int.ofNat (s.ctrl + 4 + s.tally)
  let fromF := ((hole : Nat) : Int)
  let ridxF := Int.ofNat (s.ridx + 1)
  have hcube := hcubeP paintF ctrlF fromF ridxF
  have hmulF := hmulP paintF ctrlF fromF ridxF
  exact ⟨bClearU, bCube, bRed, hrun, hcube, hmulF, hcubeU, hredU, hrel,
    honR, htoR, hlenR, hbenchR, hhighR, htmaxR, bLoopR, bMulR, hmulR, hclearR, hpackKeep⟩

end EcbsLink2.Link2
