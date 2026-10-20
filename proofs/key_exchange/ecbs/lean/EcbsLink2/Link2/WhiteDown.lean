/-
  The cofactor's first white cell, in the shape of the fresh key's copy.
  `chord_fresh_white_down` leaves the marker at `-1`, homes 0 and 1 holding
  the root, and every counter but the moves and the peak as it found them.
  That board is `SpanAt` at index 1. The room is `cofactor_suffix_room`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopyKeep
import EcbsLink2.Link2.ChordAt
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.SuffixInd
import EcbsLink2.Link2.CofactorRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem peg_n (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n :=
  Nat.le_trans (pegCount_le xs) (by omega)

private theorem under_cap (a a0 c : Nat) (ha : a ≤ a0) (h : FitsLen (a0 + c)) :
    FitsLen (a + c) :=
  FitsLen.of_le h (by omega)

private theorem two_n_le_walk (t : Spec.Tier) :
    2 * t.n ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) := by
  have h : 2 * t.n ≤ walkCharge t := by
    unfold walkCharge
    omega
  exact Nat.le_trans h (Nat.le_add_right _ _)

/-- The flagged seated board is the `InLay` the fresh key hands to its first
    white copy. `chordFlag` turns the marker flag on and leaves every counter. -/
private noncomputable abbrev flag_in_lay (t : Spec.Tier) (b : Board) (x y : List Nat) (mv pk : Nat)
    (strict hole sl ctrl mx high tmax ops0 : Nat)
    (hAt : ChordAt b t x y mv pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (strict : Int))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hole : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int))
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = (mx : Int))
    (hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hopsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (hopsB : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = (c : Int) ∧ c ≤ ops0)
    (hStart : (high < tallyOrigin t ∧ tmax = 0) ∨ tallyOrigin t ≤ high) :
    InLay t (chordFlag b) x y mv pk :=
  { szH := (by simpa [chordFlag] using hAt.szH)
    szD := (by simpa [chordFlag] using hAt.szD)
    bench := (by simpa [chordFlag] using hAt.bench)
    marker := (by simpa [chordFlag] using hAt.marker)
    flag := (by simp [chordFlag])
    strict0 := strict
    hole0 := hole
    sl0 := sl
    ctrl0 := ctrl
    mx0 := mx
    high0 := high
    tmax0 := tmax
    ops0 := ops0
    strict := (by simpa [chordFlag, ofNat_eq_natCast] using hstrict)
    hole := (by simpa [chordFlag, ofNat_eq_natCast] using hhole)
    slides := (by simpa [chordFlag, ofNat_eq_natCast] using hsl)
    mx := (by simpa [chordFlag, ofNat_eq_natCast] using hmx)
    ctrl := (by simpa [chordFlag, ofNat_eq_natCast] using hctrl)
    high := (by simpa [chordFlag, ofNat_eq_natCast] using hhigh)
    tmax := (by simpa [chordFlag, ofNat_eq_natCast] using htmax)
    opsSz := (by simpa [chordFlag] using hopsSz)
    opsBound := (by
      intro i hi
      simpa [chordFlag] using hopsB i (by simpa [chordFlag] using hi))
    hStart := hStart
    tier := (by simpa [chordFlag] using hAt.tier)
    row := (by simpa [chordFlag] using hAt.frame.hrow)
    ladder := (by simpa [chordFlag] using hAt.frame.hlad)
    l0 := (by simpa [chordFlag] using hAt.frame.hl0)
    nr := (by simpa [chordFlag] using hAt.frame.hnr)
    park := (by simpa [chordFlag] using hAt.frame.hpark)
    parked := (by simpa [chordFlag] using hAt.frame.hfrom)
    ridx := (by simpa [chordFlag] using hAt.frame.hridx)
    tally := (by simpa [chordFlag] using hAt.frame.htally)
    t0 := (by simpa [chordFlag] using hAt.frame.ht0)
    held0 := (by simpa [chordFlag] using hAt.held0)
    held1 := (by simpa [chordFlag] using hAt.held1)
    held2 := (by simpa [chordFlag] using hAt.held2)
    held3 := (by simpa [chordFlag] using hAt.held3)
    held4 := (by simpa [chordFlag] using hAt.held4)
    held5 := (by simpa [chordFlag] using hAt.held5)
    held6 := (by simpa [chordFlag] using hAt.held6)
    home3 := (by simpa [chordFlag] using hAt.home3)
    home4 := (by simpa [chordFlag] using hAt.home4)
    moves := (by simpa [chordFlag] using hAt.hmoves)
    peak := (by simpa [chordFlag] using hAt.hpeak)
    tierN := (by simpa [chordFlag] using hAt.tierN) }

/-- The board `chord_fresh_white_down` leaves. Homes 0 and 1 are the root, the
    marker is still `-1`, slides, control, ops, strict, and the hole are the
    seated counters, and that board is `SpanAt` at index 1. -/
theorem white_down_spanAt (t : Spec.Tier) (b : Board) (x y : List Nat) (mv pk : Nat)
    (strict hole sl ctrl mx high tmax ops0 : Nat)
    (hAt : ChordAt b t x y mv pk)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hf : FitsLen t.n)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (strict : Int))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hole : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int))
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = (mx : Int))
    (hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hopsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (hopsB : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = (c : Int) ∧ c ≤ ops0)
    (hStart : (high < tallyOrigin t ∧ tmax = 0) ∨ tallyOrigin t ≤ high)
    (hstrict7 : strict ≤ 7) (hholeB : hole ≤ t.benchlen) (hctrlPos : 0 < ctrl)
    (hmvLe : mv ≤ perHole t.n t.benchlen * t.n + 5 * t.n)
    (hslLe : sl ≤ perSlide t.n * t.n + 2 * t.n)
    (hctrlLe : ctrl ≤ tierR t + perCtrl t.n * t.n)
    (hopsLe : ops0 ≤ perOp t.n * t.n)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    ∃ (b2 : Board) (mv2 : Nat),
      (do
          let board ← marker_lift (chordFlag b)
          let board ← copy_band board across base_across false
          copy_band board up base_up false) = .ok b2 ∧
      mv2 = mv + pegCount x + pegCount y ∧
      SpanAt t b2 x y x y 1 mv sl ctrl ops0 ∧
      FitsLen (mv + walkCharge t * (cofactorSpan + 1)) ∧
      FitsLen (sl + cellSlideCharge t * (cofactorSpan + 1)) ∧
      FitsLen (ctrl + cellCtrlCharge t * (cofactorSpan + 1)) ∧
      FitsLen (ops0 + cellOpsCharge t * (cofactorSpan + 1)) := by
  let hlay := flag_in_lay t b x y mv pk strict hole sl ctrl mx high tmax ops0
    hAt hstrict hhole hsl hmx hctrl hhigh htmax hopsSz hopsB hStart
  have hpx := peg_n t.n x hx
  have hpy := peg_n t.n y hy
  have hroom := cofactor_suffix_room t hship
  have hMove : FitsLen (mv + walkCharge t * (cofactorSpan + 1)) :=
    under_cap mv _ _ hmvLe hroom.1
  have hSlideR : FitsLen (sl + cellSlideCharge t * (cofactorSpan + 1)) :=
    under_cap sl _ _ hslLe hroom.2.1
  have hCtrlR : FitsLen (ctrl + cellCtrlCharge t * (cofactorSpan + 1)) :=
    under_cap ctrl _ _ hctrlLe hroom.2.2.1
  have hOpsR : FitsLen (ops0 + cellOpsCharge t * (cofactorSpan + 1)) :=
    under_cap ops0 _ _ hopsLe hroom.2.2.2.1
  have hfity : FitsLen (mv + pegCount x + pegCount y) := by
    apply FitsLen.of_le hMove
    have hpeg : pegCount x + pegCount y ≤ 2 * t.n := by omega
    have hw : 2 * t.n ≤ walkCharge t := by
      unfold walkCharge
      omega
    have hmul : walkCharge t ≤ walkCharge t * (cofactorSpan + 1) := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_left (walkCharge t) (Nat.succ_pos cofactorSpan)
    omega
  have hfitx : FitsLen (mv + pegCount x) :=
    FitsLen.of_le hfity (by omega)
  obtain ⟨b2, pk2, out, hsl0, hctrl0, hops0, hstrict0, hhole0, _hmx0, _hhigh0, _htmax0, hcopy⟩ :=
    white_copy_kept t (chordFlag b) x y mv pk hlay hx hy hf hfitx hfity
  have hml := marker_lift_down (chordFlag b) (by simpa [chordFlag] using hAt.marker)
  have hdo :
      (do
          let board ← marker_lift (chordFlag b)
          let board ← copy_band board across base_across false
          copy_band board up base_up false) = .ok b2 := by
    rw [hml, ok_bind]
    exact hcopy
  let mv2 := mv + pegCount x + pegCount y
  have hmvB : mv2 ≤ mv + 1 * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
    have hpeg : pegCount x + pegCount y ≤ 2 * t.n := by omega
    have hw := two_n_le_walk t
    simp only [mv2, Nat.one_mul]
    omega
  have hslEq : hlay.sl0 = sl := rfl
  have hctrlEq : hlay.ctrl0 = ctrl := rfl
  have hopsEq : hlay.ops0 = ops0 := rfl
  have hstrictEq : hlay.strict0 = strict := rfl
  have hholeEq : hlay.hole0 = hole := rfl
  have hslB : out.sl0 ≤ sl + 1 * (cellSlideCharge t + 4 * t.n) := by
    rw [hsl0, hslEq, Nat.one_mul]
    exact Nat.le_add_right sl _
  have hctrlB : out.ctrl0 ≤ ctrl + 1 * (cellCtrlCharge t + 4) := by
    rw [hctrl0, hctrlEq, Nat.one_mul]
    exact Nat.le_add_right ctrl _
  have hopsBnd : out.ops0 ≤ ops0 + 1 * (cellOpsCharge t + 2) := by
    rw [hops0, hopsEq, Nat.one_mul]
    exact Nat.le_add_right ops0 _
  have hdown : SpanDown t b2 x y x y 1 mv sl ctrl ops0 :=
    ⟨mv2, pk2, out, hmvB, hslB, hctrlB, hopsBnd,
      by rw [hstrict0, hstrictEq]; exact hstrict7,
      by rw [hhole0, hholeEq]; exact hholeB,
      by rw [hctrl0, hctrlEq]; exact hctrlPos,
      hx, htriX, hy, htriY, hy, htriY⟩
  refine ⟨b2, mv2, hdo, rfl, Or.inr hdown, hMove, hSlideR, hCtrlR, hOpsR⟩

end EcbsLink2.Link2
