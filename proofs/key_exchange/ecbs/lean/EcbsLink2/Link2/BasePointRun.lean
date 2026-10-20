/-
  The base-point run on the chord arm. `search_loop_hit` is the root,
  `hit_chordAt` seats it, and this theorem is the walk from that seat:
  the white copy, then `cofactor_tail`, then Demo's `point_back`.
  A miss is line 963. A zero cofactor run and a `walkRun` of `none` are
  `basePoint = none`; a false live flag is the card's assert, the same
  kind of refusal as `base_point_of_refuse`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FinishBranch
import EcbsLink2.Link2.WhiteDown
import EcbsLink2.Link2.SearchGo
import EcbsLink2.Link2.CofactorSplit
import EcbsLink2.Link2.WalkLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- `walkRun = none` is `walkGo = none`. -/
theorem walkRun_none_go (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (cells : List Nat)
    (h : walkRun n k bench base live acc cells = none) :
    walkGo n k bench base live acc cells = none := by
  induction cells generalizing live acc with
  | nil => simp [walkRun] at h
  | cons c cs ih =>
    simp only [walkRun] at h
    cases hstep : walkStep n k bench base live acc c with
    | none => simp [walkGo, hstep]
    | some p =>
      simp only [hstep] at h
      simp [walkGo, hstep, ih p.1 p.2 h]

/-- The search missed every hole. The join is assert 963 and `basePoint` is `none`. -/
theorem base_point_miss {α : Type} (b0 : Board) (t : Spec.Tier)
    (k : Board → Int → Except SudoRt.Trap α)
    (hp : PlantAt b0 t t.n)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t) (hn3 : 3 ≤ t.n)
    (hctrl : ∃ c0, b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t))
    (hmiss : ∀ i, 1 ≤ i → i < t.n →
      rootHit t.n t.k t.benchlen (basisPeg t.n i) = false) :
    SudoRt.runLoopOn (Int.ofNat 1, (b0, (0 : Int)))
        (fuelRange (Int.ofNat 1) (Int.ofNat (t.n - 1)))
        (searchStep t (t.n - 1)) (searchJoin k) (fun r => nomatch r) =
      .error { kind := "AssertFailed", detail := s!"line {963}" } ∧
      basePoint t = none :=
  search_loop_miss b0 t k hp hOk hsh sat hn3 hctrl hmiss

/-- The cofactor run `x − x³` is zero. `basePoint` is `none`, and so is the walk. -/
theorem base_point_zero (t : Spec.Tier) (x y : List Nat)
    (hroot : searchRoot t.n t.k t.benchlen t.n 1 = some (x, y))
    (hn0 : 0 < t.n) (hnb : t.n ≤ t.benchlen)
    (hsub : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) = List.replicate t.n 0) :
    basePoint t = none ∧
      cofactorWalk t.n t.k t.benchlen (x, y) = none :=
  ⟨basePoint_zero_root t x y hroot hn0 hnb hsub,
    cofactor_walk_zero t.n t.k t.benchlen x y hn0 hnb hsub⟩

/-- A false live flag is the card's assert. Line 972 is Demo's walk and line
    975 is the F-form walk. This is the same kind of refusal as
    `base_point_of_refuse`. -/
theorem base_point_flag_refuse (line : Nat) (flag : Bool) {α : Type}
    (k : Except SudoRt.Trap α) (h : flag = false) :
    (do
        let _ ← SudoRt.sudoAssert flag line
        k) =
      .error { kind := "AssertFailed", detail := s!"line {line}" } := by
  rw [h]
  unfold SudoRt.sudoAssert SudoRt.fail
  simp only [Bool.false_eq_true, ite_false, error_bind]

/-- `walkRun = none` on the root the search returned. `basePoint` is `none`. -/
theorem base_point_walk_none (t : Spec.Tier) (x y : List Nat)
    (hroot : searchRoot t.n t.k t.benchlen t.n 1 = some (x, y))
    (h : walkRun t.n t.k t.benchlen (x, y) false (whiteHole0 t.n, whiteHole0 t.n)
      cofactorCells = none) :
    basePoint t = none := by
  rw [basePoint_of_root t (x, y) hroot]
  unfold cofactorWalk
  exact walkRun_none_go t.n t.k t.benchlen (x, y) false
    (whiteHole0 t.n, whiteHole0 t.n) cofactorCells h

private theorem cont_open (b b2 : Board)
    (hstep : chordStep (embed cofactorCells) (Int.ofNat 3)
        (Int.ofNat 0, (b, false)) =
      .ok (SudoRt.Flow.cont (Int.ofNat 1, (b2, true)))) :
    SudoRt.runLoopOn (Int.ofNat 0, (b, false))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (chordStep (embed cofactorCells) (Int.ofNat 3)) chordAfter (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat 1, (b2, true))
        (fuelRange (Int.ofNat 1) (Int.ofNat 3))
        (chordStep (embed cofactorCells) (Int.ofNat 3)) chordAfter (fun r => pure r) := by
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat 3) =
      fuelRange (Int.ofNat 1) (Int.ofNat 3) + 1 := by
    rw [fuelRange_le (by decide : (0 : Nat) ≤ 3), fuelRange_le (by decide : (1 : Nat) ≤ 3)]
  rw [hfuel, runLoopOn_succ, hstep]

private theorem peg_n (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n :=
  Nat.le_trans (pegCount_le xs) (by omega)

/-- The seated root, the four cofactor cells, and Demo's move back.
    `search_loop_hit` is the root in `hroot`. `hit_chordAt` is the seat
    `ChordAt` reads. Homes 0 and 1 of the walk are the point, and on Demo
    `afterWalk` puts that point in homes 3 and 4. -/
theorem base_point_run (t : Spec.Tier) (b : Board) (x y px py : List Nat)
    (mv pk strict hole sl ctrl mx high tmax ops0 : Nat) (found : Int)
    (hAt : ChordAt b t x y mv pk)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hpx : px.length = t.n) (hpy : py.length = t.n)
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
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hnb : t.n ≤ t.benchlen) (hscript : 4 < t.script)
    (hroot : searchRoot t.n t.k t.benchlen t.n 1 = some (x, y))
    (hgo : walkRun t.n t.k t.benchlen (x, y) false (whiteHole0 t.n, whiteHole0 t.n)
      cofactorCells = some (true, (px, py))) :
    ∃ bW,
      walk_chord b (embed cofactorCells) = .ok ((true, true), bW) ∧
      (∀ h : 0 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[0] = embed px) ∧
      (∀ h : 1 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[1] = embed py) ∧
      LastLay bW x y (suffixMoveCap t mv (cofactorSpan - 1))
        (suffixSlideCap t sl (cofactorSpan - 1)) ∧
      bW.sudo_5Board_1t = embTier t ∧
      basePoint t = some (px, py) ∧
      (t.demo = true →
        ∃ b',
          afterWalk bW found = .ok (found, b') ∧
          (∀ h : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3] = embed px) ∧
          (∀ h : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4] = embed py) ∧
          (∀ h : 0 < b'.sudo_5Board_4home.size,
            b'.sudo_5Board_4home[0] = (#[] : Array Int)) ∧
          (∀ h : 1 < b'.sudo_5Board_4home.size,
            b'.sudo_5Board_4home[1] = (#[] : Array Int))) := by
  obtain ⟨b2, mv2, pk2, out, hdo, hmv2, hslO, hctO, hopO, hstO, hhoO, _hspan,
      hMove, hSlide, hCtrl, hOps⟩ :=
    white_down_spanAt t b x y mv pk strict hole sl ctrl mx high tmax ops0
      hAt hx hy htriX htriY hf hstrict hhole hsl hmx hctrl hhigh htmax hopsSz hopsB
      hStart hstrict7 hholeB hctrlPos hmvLe hslLe hctrlLe hopsLe hship
  have hroom := cofactor_suffix_room t hship
  have hmv2le : mv2 ≤ mv + 2 * t.n := by
    rw [hmv2]
    have hxP := peg_n t.n x hx
    have hyP := peg_n t.n y hy
    omega
  have hRoomM : FitsLen (mv + (cofactorSpan + 1) * walkCharge t) := by
    simpa [Nat.mul_comm] using hMove
  have hRoomS : FitsLen (sl + (cofactorSpan + 1) * cellSlideCharge t) := by
    simpa [Nat.mul_comm] using hSlide
  have hRoomC : FitsLen (ctrl + (cofactorSpan + 1) * cellCtrlCharge t) := by
    simpa [Nat.mul_comm] using hCtrl
  have hRoomO : FitsLen (ops0 + (cofactorSpan + 1) * cellOpsCharge t) := by
    simpa [Nat.mul_comm] using hOps
  obtain ⟨bW, htail, h0, h1, hlay, htier⟩ :=
    cofactor_tail t b2 x y px py mv2 pk2 mv sl ctrl ops0 out
      hOk sat hR hsh hx hy htriX htriY hnb hscript hmv2le
      (Nat.le_of_eq hslO) (Nat.le_of_eq hctO) (Nat.le_of_eq hopO)
      (by rw [hstO]; exact hstrict7) (by rw [hhoO]; exact hholeB)
      (by rw [hctO]; exact hctrlPos)
      hRoomM hRoomS hRoomC hRoomO
      hroom.2.2.2.2.1 hroom.2.2.2.2.2.1 hroom.2.2.2.2.2.2.1 hroom.2.2.2.2.2.2.2
      hgo
  have hml := marker_lift_down (chordFlag b) (by simpa [chordFlag] using hAt.marker)
  have hcopies :
      (do
          let board ← copy_band (chordFlag b) across base_across false
          copy_band board up base_up false) = .ok b2 := by
    rw [hml, ok_bind] at hdo
    exact hdo
  have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by decide
  have hcopy :
      (do
          let board ← copy_band (chordFlag b) across base_across false
          copy_band board up base_up
            (SudoRt.SEq.beq (Int.ofNat 1) (2 : Int))) = .ok b2 := by
    simpa [hbeq] using hcopies
  have hlen4 : cofactorCells.length = 4 := by simp [cofactorCells]
  have hstep0 := chordStep_fresh cofactorCells 0 3 1 (chordFlag b) (chordFlag b) b2
    (by decide) (by rw [hlen4]) (by simp [cofactorCells]) (by decide) (by decide)
    hml hcopy (fits_small (by decide))
  have hstep0' :
      chordStep (embed cofactorCells) (Int.ofNat 3)
          (Int.ofNat 0, (chordFlag b, false)) =
        .ok (SudoRt.Flow.cont (Int.ofNat 1, (b2, true))) := by
    simpa [if_neg (by decide : ¬ ((0 : Nat) = 3))] using hstep0
  have hopen := cont_open (chordFlag b) b2 hstep0'
  have hfitL : FitsLen cofactorCells.length := by
    rw [hlen4]
    exact fits_small (by decide)
  have hwalk := walk_chord_loop b cofactorCells (by rw [hlen4]; decide) hfitL
  have hto : cofactorCells.length - 1 = 3 := by rw [hlen4]
  have hloop : walk_chord b (embed cofactorCells) =
      SudoRt.runLoopOn (Int.ofNat 1, (b2, true))
        (fuelRange (Int.ofNat 1) (Int.ofNat 3))
        (chordStep (embed cofactorCells) (Int.ofNat 3)) chordAfter (fun r => pure r) := by
    rw [hto] at hwalk
    exact hwalk.trans hopen
  have hspec : basePoint t = some (px, py) := by
    rw [basePoint_of_root t (x, y) hroot]
    unfold cofactorWalk
    exact walkRun_walkGo t.n t.k t.benchlen (x, y) false
      (whiteHole0 t.n, whiteHole0 t.n) cofactorCells true (px, py) hgo
  refine ⟨bW, hloop.trans htail, h0, h1, hlay, htier, hspec, ?_⟩
  intro hdemo
  have hflag : bW.sudo_5Board_1t.sudo_4Tier_4demo = true := by
    have hfield : bW.sudo_5Board_1t.sudo_4Tier_4demo = t.demo := by
      rw [htier]
      rfl
    exact hfield.trans hdemo
  have h0a : bW.sudo_5Board_4home[0]'(by rw [hlay.szH]; decide) = embed px :=
    h0 (by rw [hlay.szH]; decide)
  have h1a : bW.sudo_5Board_4home[1]'(by rw [hlay.szH]; decide) = embed py :=
    h1 (by rw [hlay.szH]; decide)
  obtain ⟨b', hback, h3, h4, hempty0, hempty1⟩ :=
    demo_point_back t bW px py x y mv sl found hlay h0a h1a hflag hship
      hpx hpy hx hy hmvLe hslLe
  exact ⟨b', hback, h3, h4, hempty0, hempty1⟩

end EcbsLink2.Link2
