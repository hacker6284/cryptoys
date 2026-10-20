/-
  `finish` multiplies twice with `copy_second = false`. The first multiply
  leaves the product on the bench, aimed at across. The second multiply
  settles that bench before it reads the gap and the up. The settle target
  is across, not the up, so `mul_eq_live` does not apply.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Mul

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem array_get_congr {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  induction h
  rfl

/-- `copy_second = false` settles the live bench into `aim`, then multiplies.
    `aim` need not be `second`. -/
theorem mul_live_aim (b : Ecbs.Board) (dst first second aim : Nat) (lane : List Nat)
    (n moves slides peak cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (aim : Int))
    (hH : aim < b.sudo_5Board_4home.size)
    (hD : aim < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[aim] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.mul b (dst : Int) (first : Int) (second : Int) false false false =
      Ecbs.mul (settleBoard b aim hH hD lane n moves slides peak)
        (dst : Int) (first : Int) (second : Int) false false false := by
  let bS := settleBoard b aim hH hD lane n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨aim, hD⟩ true) 7
    · rw [show bS = settleBoard b aim hH hD lane n moves slides peak from rfl,
        settle_peak b aim ⟨hH, hD⟩ lane n moves slides peak hpk, hmk]
    · rw [show bS = settleBoard b aim hH hD lane n moves slides peak from rfl,
        settle_keep b aim ⟨hH, hD⟩ lane n moves slides peak hpk, hmk]
  have hmkRaw :
      (settleBoard b aim hH hD lane n moves slides peak).sudo_5Board_9marker_on = false :=
    hmkS
  unfold Ecbs.mul Ecbs.log_op
  simp only [hmk, hmkRaw, Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 aim hops ⟨hH, hD⟩ lane n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    exact (array_get_congr (settle_ops b aim ⟨hH, hD⟩ lane n moves slides peak) 0 hopsS).trans hop0
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    rhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hopsS, hop0S, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hopsS, ok_bind]
  let bL : Ecbs.Board :=
    { b with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    lhs
    pattern (Ecbs.settle _)
    change Ecbs.settle bL
  have hbL : bL = bumpOp b 0 cOps hops := by
    apply board_ext
    case hmon => simp [bL, bumpOp, hmk]
    all_goals simp [bL, bumpOp]
  rw [hbL]
  have hsetL := settle_refines (bumpOp b 0 cOps hops) aim lane n moves slides peak
      (bump_home_lt b 0 cOps aim hops hH) (bump_held_lt b 0 cOps aim hops hD) h7
      (by simp [bumpOp, hon]) (by simp [bumpOp, hto]) (by simpa [bumpOp] using hempty)
      (by simp [bumpOp, hbench]) hn hpos hnle hzero hf hfitL
      (by simp [bumpOp, hmoves]) (by simp [bumpOp, hslides]) (by simp [bumpOp, hpeak])
      hpeg hfitM hfitS
  rw [hsetL, ok_bind]
  rw [settle_bump_comm b 0 cOps hops aim ⟨hH, hD⟩ lane n moves slides peak]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨aim, hD⟩ true) 7
    · rw [show bS = settleBoard b aim hH hD lane n moves slides peak from rfl,
        settle_peak b aim ⟨hH, hD⟩ lane n moves slides peak hpk]
    · rw [show bS = settleBoard b aim hH hD lane n moves slides peak from rfl,
        settle_keep b aim ⟨hH, hD⟩ lane n moves slides peak hpk]
  let bR : Ecbs.Board :=
    { bS with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { bS.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hopsS⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    rhs
    zeta
    pattern (Ecbs.settle _)
    change Ecbs.settle bR
  have hbR : bR = bumpOp bS 0 cOps hopsS := by
    apply board_ext
    case hmon => simp [bR, bumpOp, hmkS]
    all_goals simp [bR, bumpOp]
  rw [hbR]
  rw [settle_off (bumpOp bS 0 cOps hopsS) (by simp [bumpOp, hoffS]), ok_bind]
  rw [settle_tier_eq b aim ⟨hH, hD⟩ lane n moves slides peak]

private theorem cell_ne {α : Type} (a : Array α) (i j : Nat) (hi : i < a.size) (v : α)
    (hj : j < (a.set ⟨i, hi⟩ v).size) (hne : i ≠ j) (h : j < a.size) :
    (a.set ⟨i, hi⟩ v)[j]'hj = a[j]'h := by
  rw [Array.getElem_set_ne]
  exact hne

theorem settle_other_held (b : Ecbs.Board) (aim second : Nat)
    (hin : HomeIn b aim) (lane : List Nat) (n moves slides peak : Nat)
    (hS : second < b.sudo_5Board_4held.size) :
    second < (settleBoard b aim hin.hH hin.hD lane n moves slides peak).sudo_5Board_4held.size := by
  rw [settle_held_eq b aim hin lane n moves slides peak, Array.size_set]
  exact hS

theorem settle_other_home (b : Ecbs.Board) (aim second : Nat)
    (hin : HomeIn b aim) (lane : List Nat) (n moves slides peak : Nat)
    (hS : second < b.sudo_5Board_4home.size) :
    second < (settleBoard b aim hin.hH hin.hD lane n moves slides peak).sudo_5Board_4home.size := by
  rw [settle_home_eq b aim hin lane n moves slides peak, Array.size_set]
  exact hS

/-- The board `finish`'s second multiply returns. The live bench slides into
    `aim`, then `first` is multiplied by `second`. -/
def mulAimBoard (b : Ecbs.Board) (dst second aim : Nat) (xs yu lane : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hin : HomeIn b aim)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size) : Ecbs.Board :=
  let bS := settleBoard b aim hin.hH hin.hD lane n moves slides peak
  let mv := moves + 2 * pegCount (lane.take n)
  let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨aim, hin.hD⟩ true) 7)
  mulNoOffBoard bS dst second xs yu n k mv hole bench pk peakS cOps
    (settle_ops_lt b 0 aim hops hin lane n moves slides peak)
    (settle_other_held b aim second hin lane n moves slides peak hS)
    (settle_other_home b aim second hin lane n moves slides peak hHomeS)

/-- Settle the live bench into `aim`, then the nocopy multiply of `first` by
    `second`. `finish`'s second multiply is this shape: `aim` is across and
    `second` is up. -/
theorem mul_aim_eq (b : Ecbs.Board) (dst first second aim : Nat)
    (xs yu lane : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (aim : Int))
    (hH : aim < b.sudo_5Board_4home.size)
    (hD : aim < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[aim] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hn0 : 0 < n)
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS0 : b.sudo_5Board_4held[second] = true)
    (hYu : b.sudo_5Board_4home[second] = embed yu)
    (hne : first ≠ second) (hneF : aim ≠ first) (hneS : aim ≠ second)
    (hlenx : xs.length = n) (hleny : yu.length = n)
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1) +
      3 * (bench - n))) :
    Ecbs.mul b (dst : Int) (first : Int) (second : Int) false false false =
      .ok (mulAimBoard b dst second aim xs yu lane n k moves slides hole bench
        peak peakS cOps hops ⟨hH, hD⟩ hS hHomeS) := by
  rw [mul_live_aim b dst first second aim lane n moves slides peak cOps hmk hon hto hH hD h7
      hempty hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
      hops hop0 hfops]
  let bS := settleBoard b aim hH hD lane n moves slides peak
  let mv := moves + 2 * pegCount (lane.take n)
  let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨aim, hD⟩ true) 7)
  have hFs := settle_other_held b aim second ⟨hH, hD⟩ lane n moves slides peak hS
  have hHomes := settle_other_home b aim second ⟨hH, hD⟩ lane n moves slides peak hHomeS
  have htS := settle_tier_eq b aim ⟨hH, hD⟩ lane n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    rw [settle_marker_eq b aim ⟨hH, hD⟩ lane n moves slides peak]; exact hmk
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b aim ⟨hH, hD⟩ lane n moves slides peak
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 aim hops ⟨hH, hD⟩ lane n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    exact (array_get_congr (settle_ops b aim ⟨hH, hD⟩ lane n moves slides peak) 0 hopsS).trans hop0
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b aim ⟨hH, hD⟩ lane n moves slides peak, Array.size_set]; exact h7
  have hHS : bS.sudo_5Board_4held[second]'hFs = true := by
    have hset := settle_held_eq b aim ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_4held[second] =
        (b.sudo_5Board_4held.set ⟨aim, hD⟩ true)[second]'(hset ▸ hFs) from
      array_get_congr hset second hFs]
    have hSz : second < (b.sudo_5Board_4held.set ⟨aim, hD⟩ true).size := by
      rw [Array.size_set]; exact hS
    exact (cell_ne _ aim second hD true hSz hneS hS).trans hHS0
  have hYs : bS.sudo_5Board_4home[second]'hHomes = embed yu := by
    have hset := settle_home_eq b aim ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_4home[second] =
        (b.sudo_5Board_4home.set ⟨aim, hH⟩ (embed (lane.take n)))[second]'(hset ▸ hHomes) from
      array_get_congr hset second hHomes]
    have hSz : second < (b.sudo_5Board_4home.set ⟨aim, hH⟩ (embed (lane.take n))).size := by
      rw [Array.size_set]; exact hHomeS
    exact (cell_ne _ aim second hH (embed (lane.take n)) hSz hneS hHomeS).trans hYu
  have hF1 : first < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b aim ⟨hH, hD⟩ lane n moves slides peak, Array.size_set]; exact hF
  have hHome1 : first < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b aim ⟨hH, hD⟩ lane n moves slides peak, Array.size_set]; exact hHome
  have hHF1 : bS.sudo_5Board_4held[first]'hF1 = true := by
    have hset := settle_held_eq b aim ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_4held[first] =
        (b.sudo_5Board_4held.set ⟨aim, hD⟩ true)[first]'(hset ▸ hF1) from
      array_get_congr hset first hF1]
    have hSz : first < (b.sudo_5Board_4held.set ⟨aim, hD⟩ true).size := by
      rw [Array.size_set]; exact hF
    exact (cell_ne _ aim first hD true hSz hneF hF).trans hHF
  have hArr1 : bS.sudo_5Board_4home[first]'hHome1 = embed xs := by
    have hset := settle_home_eq b aim ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_4home[first] =
        (b.sudo_5Board_4home.set ⟨aim, hH⟩ (embed (lane.take n)))[first]'(hset ▸ hHome1) from
      array_get_congr hset first hHome1]
    have hSz : first < (b.sudo_5Board_4home.set ⟨aim, hH⟩ (embed (lane.take n))).size := by
      rw [Array.size_set]; exact hHome
    exact (cell_ne _ aim first hH (embed (lane.take n)) hSz hneF hHome).trans hArr
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [settle_moves_eq b aim ⟨hH, hD⟩ lane n moves slides peak]
    simp [mv, ofNat_eq_natCast]
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [settle_peak_eq b aim ⟨hH, hD⟩ lane n moves slides peak hpeak]
    simp [pk, raisedPeak, ofNat_eq_natCast]
  have hstrict : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq b aim ⟨hH, hD⟩ lane n moves slides peak]; exact hpeakS
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [htS]; exact hbl
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [htS]; exact hn
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htS]; exact hwF
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htS]; exact hhF
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htS]; exact hrF
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htS]; exact hkF
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b aim ⟨hH, hD⟩ lane n moves slides peak]; exact hHole
  rw [mul_no_eq bS dst first second xs yu w h r n k mv hole bench pk peakS cOps hmkS hoffS
      hopsS hop0S hfops hblS hF1 hHome1 hHF1 hArr1 hFs hHomes hHS hYs h7S hne hn0 hnS
      hlenx hleny hf hmovS hpkS hstrict hspan hxsT hfi hfm
      ⟨shape.hw0, shape.hh0, shape.hrR, shape.hrP, shape.hnE, shape.hkLe, shape.hgap⟩
      hwS hhS hrS hkS hholeS hsm hnsm hfitB hfold]
  unfold mulAimBoard
  rfl

end EcbsLink2.Link2
