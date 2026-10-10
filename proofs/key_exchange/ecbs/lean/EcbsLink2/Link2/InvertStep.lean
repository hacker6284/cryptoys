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
theorem white_clear_move_le (mv moves0 pegC m n bench pegG mvM : Nat)
    (hmov : moves0 ≤ mv + pegC + m * pegCharge n bench)
    (hmul : mvM ≤ moves0 + mulCharge n bench)
    (hc : pegC ≤ n) (hg : pegG ≤ n) :
    mvM + pegG ≤ mv + rungCharge n bench m := by
  have h := charge_final_white n bench m
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
      RungDelta b bClear base s.tally := by
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
  have hmoveLe : mvM + pegCount c.g ≤ mv + rungCharge base.n base.bench s.tally := by
    have h1 : moves ≤ mv + pegCount s.gap + s.tally * pegCharge c.n c.bench := by
      rw [hmT, hmov0c] at hmovB
      simpa [Nat.add_assoc] using hmovB
    have hcP : pegCount s.gap ≤ c.n := by
      rw [hn, h.hn]; exact hpegN
    have hgP : pegCount c.g ≤ c.n := by
      rw [hg]; exact hcP
    have hpiece := white_clear_move_le mv moves (pegCount s.gap) s.tally c.n c.bench
      (pegCount c.g) mvM h1 hmulLe hcP hgP
    rw [hn, hbch, h.hn, h.hbench] at hpiece
    exact hpiece
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
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have hslideLe : slides + 2 * pegCount (ys.take c.n) ≤
        sl + rungSlideCharge base.n s.tally := by
      have hs : slides ≤ sl + s.tally * (2 * base.n) := by
        have h1 := hsldB
        rw [hsl0c, hmT, hn, h.hn] at h1
        exact h1
      exact white_clear_slide_le sl slides s.tally base.n
        (pegCount (ys.take c.n)) hs hpegTake
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
    refine
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
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) true) base := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole true
  obtain ⟨b', hAll⟩ := gap_clear_emit h hF hm hT hhome hp hh
  rcases hAll with ⟨hrun, hrowE, hctrlE, hfromE, hridxE, hlenE, ht0E, hparkE,
      hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδ⟩
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
  have hK := climbInvK_succ h hinv hδ hCap hshape hh htmax
  exact ⟨b', hrun, hK⟩

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
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  obtain ⟨bClear, hAll⟩ := gap_clear_emit h hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, hrowE, hctrlE, hfromE, hridxE, hlenE, ht0E, hparkE,
      hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδ⟩
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
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax)
  exact ⟨b', hprog, by simpa [hempty] using hK⟩

end EcbsLink2.Link2
