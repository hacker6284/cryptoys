/-
  The five fields `unpark_after_climb` keeps, carried through the final cube,
  the outer settle, and `tally_clear`. Each step is an `obtain` of a compiled
  refinement. Not folded into `final_cube_settle`: that proof is already at the
  heartbeat limit. `tally_max` is the climb board's value, not a closed formula
  and not an export result. `walk_key` returns a point.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.AfterClimb
import EcbsLink2.Link2.TailStay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Ladder, its origin, the rung count, the park hole, and `tally_max`. -/
structure FiveStay (b0 b : Ecbs.Board) : Prop where
  ladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder
  l0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0
  nr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs
  park : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole
  tmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
    b0.sudo_5Board_4cost.sudo_5Costs_9tally_max

theorem FiveStay.trans {a b c : Ecbs.Board} (h : FiveStay a b) (h' : FiveStay b c) :
    FiveStay a c :=
  { ladder := h'.ladder.trans h.ladder
    l0 := h'.l0.trans h.l0
    nr := h'.nr.trans h.nr
    park := h'.park.trans h.park
    tmax := h'.tmax.trans h.tmax }

theorem FiveStay.of_frame {a b : Ecbs.Board} (h : FrameScalar a b) : FiveStay a b :=
  { ladder := h.ladder, l0 := h.l0, nr := h.nr, park := h.park, tmax := h.tmax }

theorem settleBoard_frame (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    FrameScalar b (settleBoard b home hH hD xs n moves slides peak) := by
  unfold settleBoard
  split <;> exact FrameScalar.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem touchRow_frame (b : Ecbs.Board) (row : Array Int) (ctrl : Int) :
    FrameScalar b (touchRow b row ctrl) := by
  unfold touchRow
  exact FrameScalar.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `tally_clear` writes the row and the control counter. The ops array stays. -/
theorem touchRow_ops (b : Ecbs.Board) (row : Array Int) (ctrl : Int) :
    (touchRow b row ctrl).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

private theorem ops_set_move {a b : Array Int} (h : a = b) (i : Nat)
    (ha : i < a.size) (v : Int) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, h ▸ ha⟩ v := by
  cases h
  rfl

/-- `unpark`, the final cube, the outer settle, and `tally_clear`. The five
    unpark equations survive, parked-from stays `-1`, and the rung index stays `0`. -/
theorem settled_unpark_frame
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax)
    (hm : 0 < s.tally) :
    ∃ (bU bC bOut bZ : Ecbs.Board),
      Ecbs.unpark_rung b = .ok bU ∧
      Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC ∧
      Ecbs.settle bC = .ok bOut ∧
      Ecbs.tally_clear bOut = .ok bZ ∧
      bZ.sudo_5Board_6ladder = b.sudo_5Board_6ladder ∧
      bZ.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bZ.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bZ.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      bZ.sudo_5Board_11parked_from = -1 ∧
      bZ.sudo_5Board_8rung_idx = 0 ∧
      bZ.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bZ.sudo_5Board_9tally_len = 0 ∧
      ∃ cOps : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(h.shape.peg.opsGt) = (cOps : Int) ∧
        bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, h.shape.peg.opsGt⟩
            (Int.ofNat (cOps + 1)) := by
  have hk : done.length ≤ base.R := by simpa using h.kLe
  obtain ⟨bU, hun, hfromU, hridxU, hhomeU, hheldU, hbonU, htoU, hbenchU, hmvU, hslU, hpkU,
      hctrlU, ht0U, htierU, hmkU, hopsU, hstrictU, hholeU, hlenU, hhighU,
      _hmarkU, _hmxU, hladU, hl0U, hnrU, hparkU, htmaxU⟩ :=
    unpark_after_climb h hge
  have hfiveU : FiveStay b bU :=
    { ladder := hladU, l0 := hl0U, nr := hnrU, park := hparkU, tmax := htmaxU }
  obtain ⟨mv, hmv, htailM⟩ := tail_move_fit h hon hk
  obtain ⟨sl, hsl, htailS⟩ := tail_slide_fit h hon hk
  have hmvB : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := hmvU.trans hmv
  have hslB : bU.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := hslU.trans hsl
  obtain ⟨pk, hpk, _⟩ := h.peak
  have hpkB : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
    rw [hpkU, hpk, ofNat_eq_natCast]
  have hgapB := h.inv.gapBench hon
  have hbon : bU.sudo_5Board_8bench_on = true := hbonU.trans hgapB.1
  have hto : bU.sudo_5Board_8bench_to = (5 : Int) := htoU.trans hgapB.2.1
  let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
  have hbench : bU.sudo_5Board_5bench = embed xs := by
    simpa [xs] using hbenchU.trans hgapB.2.2.1
  have h5H : 5 < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact h.inv.hG
  have h5D : 5 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact h.inv.hGs
  have h7 : 7 ≤ bU.sudo_5Board_4held.size := by rw [hheldU]; exact h.shape.h7
  have hempty : bU.sudo_5Board_4held[5] = false :=
    cell_eq_of hheldU (h.shape.gapClear hon)
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [htierU]; exact h.shape.tierN
  have hnle : s.n ≤ s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hlenX : xs.length = s.benchlen :=
    bench_pad_len s.gap s.n s.benchlen h.shape.gapLen hnle
  have hposX : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnle
  have hzero := bench_pad_zero s.gap s.n s.benchlen h.shape.gapLen hnle
  have htake : xs.take s.n = s.gap := by
    have hgeN : s.n ≤ s.gap.length := Nat.le_of_eq h.shape.gapLen.symm
    have hpre : s.gap.take s.n = s.gap :=
      List.take_of_length_le (Nat.le_of_eq h.shape.gapLen)
    rw [show xs = s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0 from rfl, hpre,
      List.take_append_of_le_length hgeN]
    exact hpre
  have hpegs : pegCount (xs.take s.n) ≤ s.n := by
    rw [htake, ← h.shape.gapLen]
    exact pegCount_le s.gap
  obtain ⟨mv0, hmv0, hfitM⟩ := pending_move_fit h hon hk (pegCount (xs.take s.n))
    (Nat.le_trans hpegs (Nat.le_of_eq h.hn))
  have hmvSame : mv = mv0 := ofNat_inj_nat (hmv.symm.trans hmv0)
  obtain ⟨sl0, hsl0, hfitS0⟩ := pending_slide_fit h hon hk (pegCount (xs.take s.n))
    (Nat.le_trans hpegs (Nat.le_of_eq h.hn))
  have hslSame : sl = sl0 := ofNat_inj_nat (hsl.symm.trans hsl0)
  have hpeg2 : FitsLen (2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le (by rw [hmvSame]; exact hfitM) (Nat.le_add_left _ mv)
  have hmk : bU.sudo_5Board_9marker_on = false := hmkU.trans h.inv.marker
  have hops1 : 1 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact h.shape.peg.opsGt
  obtain ⟨cOps, hcOps, hfops⟩ := pending_ops_fit h hon hk 1 h.shape.peg.opsGt
  have hop1 : bU.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOps : Int) := by
    have hget := arr_get hopsU 1 hops1
    exact hget.trans ((array_get_irrel (h1 := hopsU ▸ hops1)
      (h2 := h.shape.peg.opsGt)).trans hcOps)
  have _hsetU := settle_refines bU 5 xs s.n mv sl pk h5H h5D h7 hbon hto hempty hbench hnU
    hposX (by rw [hlenX]; exact hnle) hzero h.shape.peg.fitN
    (by rw [hlenX]; exact h.shape.peg.fitBn)
    (by rw [hmvB, ofNat_eq_natCast]) (by rw [hslB, ofNat_eq_natCast]) hpkB
    hpeg2 (by rw [hmvSame]; exact hfitM) (by rw [hslSame]; exact hfitS0)
  let bS := settleBoard bU 5 h5H h5D xs s.n mv sl pk
  have hfiveS : FiveStay b bS :=
    FiveStay.trans hfiveU (FiveStay.of_frame (settleBoard_frame bU 5 h5H h5D xs s.n mv sl pk))
  have hfromS : bS.sudo_5Board_11parked_from = -1 :=
    (settleBoard_frame bU 5 h5H h5D xs s.n mv sl pk).fromH.trans hfromU
  have hridxS : bS.sudo_5Board_8rung_idx = 0 :=
    (settleBoard_frame bU 5 h5H h5D xs s.n mv sl pk).ridx.trans hridxU
  have ht0S : bS.sudo_5Board_6tally0 = (s.t0 : Int) :=
    (settleBoard_frame bU 5 h5H h5D xs s.n mv sl pk).t0.trans (ht0U.trans h.inv.t0)
  have hlenS : bS.sudo_5Board_9tally_len = (s.tally : Int) :=
    (settleBoard_frame bU 5 h5H h5D xs s.n mv sl pk).tlen.trans (hlenU.trans h.inv.len)
  have hhighS : bS.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
    (settle_high_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk).trans (hhighU.trans h.inv.high)
  let pegs := pegCount (xs.take s.n)
  let mvS : Nat := mv + 2 * pegs
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [settle_moves_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, ofNat_eq_natCast]
  let slS : Nat := sl + 2 * pegs
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = (slS : Int) := by
    rw [settle_slides_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, ofNat_eq_natCast]
  let pkS : Nat :=
    if pk < countHeld (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 then
      countHeld (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 else pk
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    rw [settle_peak_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk hpkB, ofNat_eq_natCast]
  have htierS : bS.sudo_5Board_1t = b.sudo_5Board_1t :=
    (settle_tier_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk).trans htierU
  have hmkS : bS.sudo_5Board_9marker_on = false :=
    (settle_marker_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk).trans hmk
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hF : 5 < bS.sudo_5Board_4held.size :=
    settle_held_lt bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hHome : 5 < bS.sudo_5Board_4home.size :=
    settle_home_lt bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hHF : bS.sudo_5Board_4held[5] = true := by
    have heq := settle_held_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hget := arr_get heq 5 hF
    exact hget.trans (Array.getElem_set_eq _ ⟨5, h5D⟩ true rfl
      (by rw [Array.size_set]; exact h5D))
  have hArr : bS.sudo_5Board_4home[5] = embed s.gap := by
    have heq := settle_home_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hget := arr_get heq 5 hHome
    have hset := Array.getElem_set_eq _ ⟨5, h5H⟩ (embed (xs.take s.n)) rfl
      (by rw [Array.size_set]; exact h5H)
    exact (hget.trans hset).trans (congrArg embed htake)
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk]; exact hops1
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOps : Int) := by
    have hget := arr_get (settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk) 1 hopsS
    exact hget.trans hop1
  obtain ⟨peakS, hpeakS0⟩ := h.shape.peg.peakS
  have hpeakS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, hstrictU]
    exact hpeakS0
  obtain ⟨holeN, hhole0⟩ := h.shape.peg.holeM
  have hhole : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    rw [settle_hole_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, hholeU]
    exact hhole0
  have hbody : mvS + 2 * s.n + 3 * (s.benchlen - s.n) ≤
      mv + 2 * base.n + pegCharge base.n base.bench := by
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have hraw := move_tail_bound mv pegs base.n base.bench h2
    rw [show mvS = mv + 2 * pegs from rfl, h.hn, h.hbench, pegCharge]
    exact hraw
  have htop : mvS + 2 * s.n + 3 * (s.benchlen - s.n) + 2 * s.n ≤
      mv + 2 * base.n + pegCharge base.n base.bench := by
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have hraw := move_tail_bound_outer mv pegs base.n base.bench h2
    rw [show mvS = mv + 2 * pegs from rfl, h.hn, h.hbench, pegCharge]
    exact hraw
  have hfoldFit : FitsLen (mvS + 2 * s.n + 3 * (s.benchlen - s.n)) :=
    FitsLen.of_le htailM hbody
  have hfm : FitsLen (mvS + 2 * s.n) :=
    FitsLen.of_le hfoldFit (Nat.le_add_right _ _)
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, Array.size_set]
    exact h7
  obtain ⟨bC, hc0, honC, htoC, hbenchC, _htakeC, hzeroC, hmvC, hpkC, hslC,
      htC, hszC, _hhomeC, hheldC, _hmkC, hrowC, hopsC, _ht0C, hhighC, hctrlC, hscC⟩ :=
    cube_refines bS 5 5 s.gap base.w base.h base.r s.n s.k mvS holeN s.benchlen pkS peakS cOps
      base.cg hmkS hoffS hopsS hopS hfops
      (by rw [htierS, h.shape.tierB, ofNat_eq_natCast])
      (by rw [htierS, h.shape.tierCg, ofNat_eq_natCast])
      h.shape.peg.span hF hHome hHF hArr h7S h.shape.peg.n_pos
      (by rw [htierS]; exact h.shape.tierN) h.shape.gapLen h.shape.peg.fitN
      hmvS hpkS hpeakS h.shape.peg.trits h.shape.peg.fit3 hfm
      ⟨h.shape.w0, h.shape.h0, h.shape.rlt, h.shape.r0, h.shape.n_eq, h.shape.k_le, h.shape.gap_eq⟩
      (by rw [htierS, h.shape.tierW, ofNat_eq_natCast])
      (by rw [htierS, h.shape.tierH, ofNat_eq_natCast])
      (by rw [htierS, h.shape.tierR, ofNat_eq_natCast])
      (by rw [htierS, h.shape.tierK, ofNat_eq_natCast])
      (by rw [hhole, ofNat_eq_natCast])
      h.shape.peg.small h.shape.peg.n_small h.shape.peg.fitBn hfoldFit
  have hslideEq := cube_settle_other bU 5 5 5 xs s.n mv sl pk cOps
    hmk hbon hto h5H h5D h7 hempty hbench hnU hposX (by rw [hlenX]; exact hnle) hzero
    h.shape.peg.fitN (by rw [hlenX]; exact h.shape.peg.fitBn)
    (by rw [hmvB, ofNat_eq_natCast]) (by rw [hslB, ofNat_eq_natCast]) hpkB
    hpeg2 (by rw [hmvSame]; exact hfitM) (by rw [hslSame]; exact hfitS0)
    hops1 hop1 hfops
  have hc : Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC := by
    simpa [bS, Ecbs.gap] using hslideEq.trans hc0
  have hfiveC : FiveStay b bC := FiveStay.trans hfiveS (FiveStay.of_frame hscC)
  have hfromC : bC.sudo_5Board_11parked_from = -1 := hscC.fromH.trans hfromS
  have hridxC : bC.sudo_5Board_8rung_idx = 0 := hscC.ridx.trans hridxS
  have ht0C : bC.sudo_5Board_6tally0 = (s.t0 : Int) := hscC.t0.trans ht0S
  have hlenC : bC.sudo_5Board_9tally_len = (s.tally : Int) := hscC.tlen.trans hlenS
  have hhighCb : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
    hhighC.trans hhighS
  let fold := laneFold s.n (s.n - s.k) (combStrip s.n s.benchlen s.gap)
  have hlenF : fold.length = s.benchlen := by
    rw [laneFold_length _ _ _ (by rw [combStrip_length]; exact hnle), combStrip_length]
  have hzeroF : ∀ i, s.n ≤ i → ∀ hi : i < fold.length, fold[i] = 0 := by
    intro i hi hix
    have hc0 := hzeroC i hi (by rw [hlenF] at hix; exact hix)
    rw [← coeff_eq_get fold i hix]
    exact hc0
  have hmvN : cubeMoves mvS s.gap s.n s.k s.benchlen ≤
      mvS + 2 * s.n + 3 * (s.benchlen - s.n) :=
    cubeMoves_le mvS s.gap s.n s.k s.benchlen
  have hpegF : pegCount (fold.take s.n) ≤ s.n := pegCount_take_le fold s.n
  have hfitOut : FitsLen (cubeMoves mvS s.gap s.n s.k s.benchlen +
      2 * pegCount (fold.take s.n)) := by
    apply FitsLen.of_le htailM
    have hsum := Nat.add_le_add hmvN (Nat.mul_le_mul_left 2 hpegF)
    exact Nat.le_trans hsum htop
  have hfitOutS : FitsLen (slS + 2 * pegCount (fold.take s.n)) := by
    apply FitsLen.of_le htailS
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have h3 : 2 * pegCount (fold.take s.n) ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegF
    rw [show slS = sl + 2 * pegs from rfl]
    exact Nat.add_le_add (Nat.add_le_add_left h2 sl) h3
  have hfitPeg : FitsLen (2 * pegCount (fold.take s.n)) :=
    FitsLen.of_le hfitOut (Nat.le_add_left _ _)
  have h5HC : 5 < bC.sudo_5Board_4home.size := by rw [hszC]; exact hHome
  have h5DC : 5 < bC.sudo_5Board_4held.size := by
    rw [hheldC, Array.size_set]; exact hF
  have hemptyC : bC.sudo_5Board_4held[5] = false := by
    have hget := arr_get hheldC 5 h5DC
    exact hget.trans (Array.getElem_set_eq _ ⟨5, hF⟩ false rfl
      (by rw [Array.size_set]; exact hF))
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    rw [hheldC, Array.size_set]; exact h7S
  have hsetC := settle_refines bC 5 fold s.n
      (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
      (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
      h5HC h5DC h7C honC htoC hemptyC hbenchC
      (by rw [htC, htierS]; exact h.shape.tierN)
      (by rw [hlenF]; exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnle)
      (by rw [hlenF]; exact hnle) hzeroF h.shape.peg.fitN
      (by rw [hlenF]; exact h.shape.peg.fitBn)
      (by rw [hmvC, ofNat_eq_natCast])
      (by rw [hslC, hslS, ofNat_eq_natCast])
      (by rw [hpkC, ofNat_eq_natCast])
      hfitPeg hfitOut hfitOutS
  let bOut := settleBoard bC 5 h5HC h5DC fold s.n
      (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
      (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have hframeO := settleBoard_frame bC 5 h5HC h5DC fold s.n
      (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
      (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have hfiveO : FiveStay b bOut := FiveStay.trans hfiveC (FiveStay.of_frame hframeO)
  have hfromO : bOut.sudo_5Board_11parked_from = -1 := hframeO.fromH.trans hfromC
  have hridxO : bOut.sudo_5Board_8rung_idx = 0 := hframeO.ridx.trans hridxC
  have ht0O : bOut.sudo_5Board_6tally0 = (s.t0 : Int) := hframeO.t0.trans ht0C
  have hlenO : bOut.sudo_5Board_9tally_len = (s.tally : Int) := hframeO.tlen.trans hlenC
  have hrowS : bS.sudo_5Board_3row = bU.sudo_5Board_3row := by
    unfold bS settleBoard
    split <;> rfl
  have hctrlS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = bU.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    unfold bS settleBoard
    split <;> rfl
  have hhighO : bOut.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    have hhO : bOut.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bC.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
      unfold bOut settleBoard
      split <;> rfl
    rw [hhO, hhighC, hhighS]
  have hctrlO : bOut.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 : Nat) : Int) := by
    have hcO : bOut.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        bC.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
      unfold bOut settleBoard
      split <;> rfl
    rw [hcO, hctrlC, hctrlS, hctrlU, ofNat_eq_natCast]
  obtain ⟨bRow, row, hunR, hrowE, _hlist, hlenR⟩ := unpark_row_embed h hge
  have hbU : bU = bRow := Except.ok.inj (hun.symm.trans hunR)
  have hrowO : bOut.sudo_5Board_3row = embed row := by
    have hU : bU.sudo_5Board_3row = embed row := by rw [hbU]; exact hrowE
    have hhO : bOut.sudo_5Board_3row = bC.sudo_5Board_3row := by
      unfold bOut settleBoard
      split <;> rfl
    rw [hhO, hrowC, hrowS, hU]
  have htierO : bOut.sudo_5Board_1t = b.sudo_5Board_1t := by
    have htO : bOut.sudo_5Board_1t = bC.sudo_5Board_1t := by
      unfold bOut settleBoard
      split <;> rfl
    rw [htO, htC, htierS]
  have hroom : s.t0 + s.tally ≤ row.length := by
    rw [hlenR]
    exact h.shape.seg.room
  have hIn : s.t0 + s.tally ≤ base.control := by
    have hlenRow : row.length = base.control := hlenR.trans h.shape.rowLen
    rw [hlenRow] at hroom
    exact hroom
  have hTop : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop]
    exact Nat.le_max_right _ _
  have hclear := tally_clear_refines bOut row s.t0 s.tally (s.ctrl + 2) s.high base.control
    hm hlenO ht0O hrowO hroom
    (by rw [htierO]; exact h.shape.tierC)
    hhighO hTop
    (by simpa [ofNat_eq_natCast] using hctrlO) hIn
    h.shape.peg.fitRow (tail_ctrl_fit h hk ht) h.shape.peg.fitTall
  let bZ := { touchRow bOut (embed (paintZero row s.t0 s.tally))
      (Int.ofNat (s.ctrl + 2 + s.tally)) with sudo_5Board_9tally_len := 0 }
  have hz : Ecbs.tally_clear bOut = .ok bZ := by simpa [bZ] using hclear
  have hfiveZ : FiveStay b bZ :=
    FiveStay.trans hfiveO
      { ladder := by simp [bZ, touchRow]
        l0 := by simp [bZ, touchRow]
        nr := by simp [bZ, touchRow]
        park := by simp [bZ, touchRow]
        tmax := by simp [bZ, touchRow] }
  have hopsSettle : ∃ cOps : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(h.shape.peg.opsGt) = (cOps : Int) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, h.shape.peg.opsGt⟩
          (Int.ofNat (cOps + 1)) := by
    refine ⟨cOps, hcOps, ?_⟩
    have hSops := settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hOops := settle_ops bC 5 ⟨h5HC, h5DC⟩ fold s.n
        (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
        (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
    have hZops : bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
        (touchRow bOut (embed (paintZero row s.t0 s.tally))
          (Int.ofNat (s.ctrl + 2 + s.tally))).sudo_5Board_4cost.sudo_5Costs_3ops := by
      simp [bZ]
    have hstep := hZops.trans ((touchRow_ops bOut _ _).trans (hOops.trans hopsC))
    have harr : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := hSops.trans hopsU
    have hmove := ops_set_move harr 1 hopsS (Int.ofNat (cOps + 1))
    rw [hstep, hmove]
  refine ⟨bU, bC, bOut, bZ, hun, hc, hsetC, hz,
    hfiveZ.ladder, hfiveZ.l0, hfiveZ.nr, hfiveZ.park, hfiveZ.tmax,
    ?_, ?_, ?_, rfl, hopsSettle⟩
  · simp [bZ, touchRow, hfromO]
  · simp [bZ, touchRow, hridxO]
  · simp [bZ, touchRow, ht0O]

/-- The board `tally_clear` returns keeps the climb board's ops array, with
    slot 1 replaced by one more than the value the cube read. The inner settle
    and the outer settle leave the array (`settle_ops`). The cube writes slot 1
    (`cube_off_ops`, through `cube_refines`). `tally_clear` is `touchRow`. -/
theorem settled_ops
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax)
    (hm : 0 < s.tally) :
    ∃ (bZ : Ecbs.Board) (cOps : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(h.shape.peg.opsGt) = (cOps : Int) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, h.shape.peg.opsGt⟩
          (Int.ofNat (cOps + 1)) := by
  obtain ⟨_, _, _, bZ, _, _, _, _, _, _, _, _, _, _, _, _, _, hops⟩ :=
    settled_unpark_frame h hon hge ht hm
  obtain ⟨cOps, hc, hset⟩ := hops
  exact ⟨bZ, cOps, hc, hset⟩

end EcbsLink2.Link2
