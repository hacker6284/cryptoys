/-
  One climb rung after the idle park: the emitted prefix, then the final white
  successor. Proof-only. Not a security claim. The park hole sits immediately
  after the climb holes (`ladder0 + nrungs`).
-/
import EcbsLink2.Link2.InvertDelta

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem arr_get {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  subst h
  rfl

theorem not_rung_two (rung : Nat) (h : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

theorem climbAt_ge (L R i : Nat) (hi : i < R) : L ≤ climbAt L R i := by
  unfold climbAt
  omega

theorem climbAt_pred (L R i : Nat) (hi : i + 1 < R) :
    climbAt L R (i + 1) = climbAt L R i - 1 := by
  unfold climbAt
  omega

theorem climbAt_end (L R i : Nat) (hL : 0 < L) (hi : i + 1 = R) :
    climbAt L R (i + 1) = L - 1 := by
  unfold climbAt
  omega

theorem climbAt_ne_sum (L R i park : Nat) (hL : 0 < L) (hi : i ≤ R) (hp : park = L + R) :
    climbAt L R i ≠ park := by
  intro h
  unfold climbAt at h
  omega

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

/-- Park, copy, the white scan, the cube-peg loop, the gap mul, and `clear`.
    The result is that clear. Its row, counter, parked-from hole, rung index,
    and tally length are the final white model once the rung is not red; the
    fields below do not depend on that. Counters stay inside one rung charge. -/
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
      (∃ holeN : Nat, bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int)) := by
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
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end EcbsLink2.Link2
