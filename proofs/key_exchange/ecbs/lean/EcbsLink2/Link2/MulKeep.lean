/-
  `Ecbs.mul` with each inlined schoolbook stepper replaced by `rowStep` and the
  strip-copy stepper replaced by `bandCopyStep`. The two are definitionally equal.
-/
import EcbsLink2.Link2.RungBody
import EcbsLink2.Link2.RungLadder

set_option linter.unusedVariables false

namespace Ecbs

/-- Copy `r` onto the strip, index `0` through `_toV`. `Ecbs.mul` inlines this once. -/
def bandCopyStep (r : Array Int) (_toV : Int) (σ : Int × (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int)) Board) :=

    let i := σ.1
    let strip := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Board) (i, strip))
      else
        match ← ((do
  let _ix768 := i
  let _t769 ← SudoRt.atL r i
  let _t770 ← SudoRt.putL strip _ix768 _t769
  let strip := _t770
  pure (SudoRt.Flow.cont (ρ := Board) strip)) : Except SudoRt.Trap (SudoRt.Flow _ (Board))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Board) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Board) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Board) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Board) (i', _fs))

/-- One schoolbook loop, then `lane_fold`, the bench write, and `note_peak`. -/
def schoolFinish (n : Int) (a s : Array Int) (mirror : Bool)
    (b : Board) (strip : Array Int) : Except SudoRt.Trap Board :=
  do
    let fromV ← SudoRt.subI n (1 : Int)
    let toV := (0 : Int)
    let fuel : Nat := if fromV < toV then 1 else (fromV - toV).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Board) (fromV, (b, strip)) fuel
      (EcbsLink2.Link2.rowStep a s mirror n toV)
      (fun σ =>
        let b := σ.2.1
        let strip := σ.2.2
        do
          let folded ← lane_fold b strip
          let ⟨b1, strip1⟩ := folded
          let b := ({ b1 with sudo_5Board_5bench := strip1 } : Board)
          let out ← note_peak b
          pure out)
      (fun r => pure r)
    pure out

/-- From the `src != first` check through the schoolbook. `src` is `second` or `spare`. -/
def mulFromSrc (n fst src : Int) (a : Array Int) (mirror : Bool)
    (b : Board) (strip : Array Int) : Except SudoRt.Trap Board :=
  do
    let _ ← SudoRt.sudoAssert (!(SudoRt.SEq.beq src fst)) 575
    let b ← note_strict b
    let held ← SudoRt.atL b.sudo_5Board_4held src
    let _ ← SudoRt.sudoAssert held 577
    let s ← SudoRt.atL b.sudo_5Board_4home src
    let heldA ← SudoRt.putL b.sudo_5Board_4held src false
    let b := ({ b with sudo_5Board_4held := heldA } : Board)
    let homeA ← SudoRt.putL b.sudo_5Board_4home src (#[] : Array Int)
    let b := ({ b with sudo_5Board_4home := homeA } : Board)
    schoolFinish n a s mirror b strip

/-- `assert held[first]`, then the optional spare copy, then `mulFromSrc`. -/
def mulFromHeld (n fst second : Int) (copy_second mirror : Bool)
    (b : Board) (strip : Array Int) : Except SudoRt.Trap Board :=
  do
    let held ← SudoRt.atL b.sudo_5Board_4held fst
    let _ ← SudoRt.sudoAssert held 568
    let a ← SudoRt.atL b.sudo_5Board_4home fst
    if copy_second then
      do
        let _ ← SudoRt.sudoAssert (!(SudoRt.SEq.beq second spare)) 572
        let b ← copy_band b spare second false
        mulFromSrc n fst spare a mirror b strip
    else
      mulFromSrc n fst second a mirror b strip

def mulElse (n dst «first» second : Int) (copy_second onto mirror : Bool)
    (b : Board) : Except SudoRt.Trap Board :=
  do
        let _io748 ← settle b
        let b := _io748
        let _t749 ← SudoRt.filledL ((b).sudo_5Board_1t).sudo_4Tier_8benchlen (0 : Int)
        let strip := _t749
        if onto then
          do
            let _t750 ← SudoRt.atL (b).sudo_5Board_4held dst
            let _as751 ← SudoRt.sudoAssert _t750 556
            let _t752 ← SudoRt.atL (b).sudo_5Board_4home dst
            let r := _t752
            let _ix753 := dst
            let _t754 ← SudoRt.putL (b).sudo_5Board_4held _ix753 false
            let _t755 := ({ b with sudo_5Board_4held := _t754 } : Board)
            let b := _t755
            let _ix756 := dst
            let _t757 ← SudoRt.putL (b).sudo_5Board_4home _ix756 (#[] : Array (Int))
            let _t758 := ({ b with sudo_5Board_4home := _t757 } : Board)
            let b := _t758
            let _t759 ← npeg r
            let _t760 ← SudoRt.mulI (2 : Int) _t759
            let m := _t760
            let _t761 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves m
            let _t762 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t761 } : Costs)
            let _t763 := ({ b with sudo_5Board_4cost := _t762 } : Board)
            let b := _t763
            let _t764 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_6slides m
            let _t765 := ({ (b).sudo_5Board_4cost with sudo_5Costs_6slides := _t764 } : Costs)
            let _t766 := ({ b with sudo_5Board_4cost := _t765 } : Board)
            let b := _t766
            let _t771 ← SudoRt.subI n (1 : Int)
            let _fromV := (0 : Int)
            let _toV := _t771
            let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
            let _init895 := (_fromV, strip)
            let _out ← (SudoRt.runLoopOn (ρ := Board) _init895 fuel (bandCopyStep r _toV) (fun σ =>
    let strip := σ.2
    do
      let _t772 := ({ b with sudo_5Board_8bench_on := true } : Board)
      let b := _t772
      let _t773 := ({ b with sudo_5Board_8bench_to := dst } : Board)
      let b := _t773
      let _t774 := ({ b with sudo_5Board_5bench := strip } : Board)
      let b := _t774
      mulFromHeld n «first» second copy_second mirror b strip) (fun r => pure r))
            pure _out
        else
          do
            let _t896 := ({ b with sudo_5Board_8bench_on := true } : Board)
            let b := _t896
            let _t897 := ({ b with sudo_5Board_8bench_to := dst } : Board)
            let b := _t897
            let _t898 := ({ b with sudo_5Board_5bench := strip } : Board)
            let b := _t898
            mulFromHeld n «first» second copy_second mirror b strip


def mulKeep (b : Board) (dst : Int) («first» : Int) (second : Int) (copy_second : Bool) (onto : Bool) (mirror : Bool) : Except SudoRt.Trap (Board) :=
  do
    let _ix616 := op_mul
    let _t617 ← SudoRt.atL ((b).sudo_5Board_4cost).sudo_5Costs_3ops op_mul
    let _t618 ← SudoRt.addI _t617 (1 : Int)
    let _t619 ← SudoRt.putL ((b).sudo_5Board_4cost).sudo_5Costs_3ops _ix616 _t618
    let _t620 := ({ (b).sudo_5Board_4cost with sudo_5Costs_3ops := _t619 } : Costs)
    let _t621 := ({ b with sudo_5Board_4cost := _t620 } : Board)
    let b := _t621
    let _io622 ← log_op b
    let b := _io622
    let n := ((b).sudo_5Board_1t).sudo_4Tier_1n
    let strip := (#[] : Array (Int))
    let _t623 ← (if onto then (do
  pure (b).sudo_5Board_8bench_on) else pure false)
    let _t624 ← (if _t623 then (do
  pure (SudoRt.SEq.beq (b).sudo_5Board_8bench_to dst)) else pure false)
    let _t626 ← (if _t624 then (do
  let _t627 ← SudoRt.atL (b).sudo_5Board_4held dst
  pure (!( _t627 ))) else pure false)
    if _t626 then
      do
        let strip := (b).sudo_5Board_5bench
        mulFromHeld n «first» second copy_second mirror b strip
    else
      mulElse n dst «first» second copy_second onto mirror b



end Ecbs

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem mul_keep_eq
    (b : Ecbs.Board) (dst first second : Int) (copySecond onto mirror : Bool) :
    Ecbs.mul b dst first second copySecond onto mirror =
      Ecbs.mulKeep b dst first second copySecond onto mirror := by
  unfold Ecbs.mul Ecbs.mulKeep
  rfl

private theorem fold_peak_ladder (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : (do
        let folded ← Ecbs.lane_fold b strip
        let ⟨b1, strip1⟩ := folded
        let b := ({ b1 with sudo_5Board_5bench := strip1 } : Ecbs.Board)
        let out ← Ecbs.note_peak b
        pure out) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  cases hf : Ecbs.lane_fold b strip with
  | error _ =>
    rw [hf] at h; simp only [error_bind] at h; cases h
  | ok folded =>
    rw [hf] at h; simp only [ok_bind] at h
    cases folded with
    | mk bF stripF =>
      cases hk : Ecbs.note_peak
          ({ bF with sudo_5Board_5bench := stripF } : Ecbs.Board) with
      | error _ =>
        rw [hk] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hk] at h; simp only [ok_bind, pure_eq_ok] at h
        cases h
        exact (note_peak_ladder _ b' hk).trans
          ((by rfl : ({ bF with sudo_5Board_5bench := stripF } : Ecbs.Board).sudo_5Board_6ladder
              = bF.sudo_5Board_6ladder).trans
            (lane_fold_ladder b strip bF stripF hf))

theorem schoolFinish_ladder (n : Int) (a s : Array Int) (mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.schoolFinish n a s mirror b strip = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.schoolFinish at h
  dsimp only at h
  cases hsub : SudoRt.subI n (1 : Int) with
  | error _ =>
    rw [hsub] at h; simp only [error_bind] at h; cases h
  | ok fromV =>
    rw [hsub] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    refine row_loop_ladder a s mirror n (0 : Int) fromV _ b strip _ _ ?hafter ?hret b' h
    · intro st q hs hq
      exact (fold_peak_ladder st.2.1 st.2.2 q hq).trans hs
    · intro r q hr hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact hr

theorem mulFromSrc_ladder (n fst src : Int) (a : Array Int) (mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.mulFromSrc n fst src a mirror b strip = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.mulFromSrc at h
  dsimp only at h
  cases ha : SudoRt.sudoAssert (!(SudoRt.SEq.beq src fst)) 575 with
  | error _ =>
    rw [ha] at h; simp only [error_bind] at h; cases h
  | ok _ =>
    rw [ha] at h; simp only [ok_bind] at h
    cases hst : Ecbs.note_strict b with
    | error _ =>
      rw [hst] at h; simp only [error_bind] at h; cases h
    | ok bN =>
      rw [hst] at h; simp only [ok_bind] at h
      have hN := note_strict_ladder b bN hst
      cases hheld : SudoRt.atL bN.sudo_5Board_4held src with
      | error _ =>
        rw [hheld] at h; simp only [error_bind] at h; cases h
      | ok held =>
        rw [hheld] at h; simp only [ok_bind] at h
        cases hassert : SudoRt.sudoAssert held 577 with
        | error _ =>
          rw [hassert] at h; simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hassert] at h; simp only [ok_bind] at h
          cases hs : SudoRt.atL bN.sudo_5Board_4home src with
          | error _ =>
            rw [hs] at h; simp only [error_bind] at h; cases h
          | ok s =>
            rw [hs] at h; simp only [ok_bind] at h
            cases hph : SudoRt.putL bN.sudo_5Board_4held src false with
            | error _ =>
              rw [hph] at h; simp only [error_bind] at h; cases h
            | ok heldA =>
              rw [hph] at h; simp only [ok_bind] at h
              cases hpa : SudoRt.putL
                  ({ bN with sudo_5Board_4held := heldA } : Ecbs.Board).sudo_5Board_4home
                  src (#[] : Array Int) with
              | error _ =>
                rw [hpa] at h; simp only [error_bind] at h; cases h
              | ok homeA =>
                rw [hpa] at h; simp only [ok_bind] at h
                let bC : Ecbs.Board :=
                  { bN with sudo_5Board_4held := heldA, sudo_5Board_4home := homeA }
                exact (schoolFinish_ladder n a s mirror bC strip b' h).trans hN

theorem mulFromHeld_ladder (n fst second : Int) (copySecond mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.mulFromHeld n fst second copySecond mirror b strip = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.mulFromHeld at h
  dsimp only at h
  cases hheld : SudoRt.atL b.sudo_5Board_4held fst with
  | error _ =>
    rw [hheld] at h; simp only [error_bind] at h; cases h
  | ok held =>
    rw [hheld] at h; simp only [ok_bind] at h
    cases ha : SudoRt.sudoAssert held 568 with
    | error _ =>
      rw [ha] at h; simp only [error_bind] at h; cases h
    | ok _ =>
      rw [ha] at h; simp only [ok_bind] at h
      cases hhome : SudoRt.atL b.sudo_5Board_4home fst with
      | error _ =>
        rw [hhome] at h; simp only [error_bind] at h; cases h
      | ok a =>
        rw [hhome] at h; simp only [ok_bind] at h
        by_cases hc : copySecond = true
        · rw [if_pos hc] at h
          cases hs : SudoRt.sudoAssert (!(SudoRt.SEq.beq second Ecbs.spare)) 572 with
          | error _ =>
            rw [hs] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hs] at h; simp only [ok_bind] at h
            cases hcopy : Ecbs.copy_band b Ecbs.spare second false with
            | error _ =>
              rw [hcopy] at h; simp only [error_bind] at h; cases h
            | ok bC =>
              rw [hcopy] at h; simp only [ok_bind] at h
              exact (mulFromSrc_ladder n fst Ecbs.spare a mirror bC strip b' h).trans
                (copy_band_keeps Ecbs.spare second false b bC hcopy)
        · rw [if_neg hc] at h
          exact mulFromSrc_ladder n fst second a mirror b strip b' h

theorem bandCopyStep_no_ret (r : Array Int) (toV : Int) (σ : Int × (Array Int))
    (rb : Ecbs.Board) :
    Ecbs.bandCopyStep r toV σ ≠ .ok (SudoRt.Flow.ret rb) := by
  intro h
  unfold Ecbs.bandCopyStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hv : SudoRt.atL r σ.1 with
    | error _ =>
      rw [hv] at h; simp only [error_bind] at h; cases h
    | ok v =>
      rw [hv] at h; simp only [ok_bind] at h
      cases hp : SudoRt.putL σ.2 σ.1 v with
      | error _ =>
        rw [hp] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hp] at h; simp only [ok_bind, pure_eq_ok] at h
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at h
          cases h
        · rw [if_neg hlast] at h
          cases hi : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hi] at h; simp only [ok_bind, pure_eq_ok] at h
            cases h

theorem mulElse_ladder
    (n dst first second : Int) (copySecond onto mirror : Bool)
    (b0 b' : Ecbs.Board)
    (h : Ecbs.mulElse n dst first second copySecond onto mirror b0 = .ok b') :
    b'.sudo_5Board_6ladder = b0.sudo_5Board_6ladder := by
  unfold Ecbs.mulElse at h
  dsimp only at h
  cases hset : Ecbs.settle b0 with
  | error _ =>
    rw [hset] at h; simp only [error_bind] at h; cases h
  | ok bS =>
    rw [hset] at h; simp only [ok_bind] at h
    have hS := settle_keeps b0 bS hset
    cases hfill : SudoRt.filledL bS.sudo_5Board_1t.sudo_4Tier_8benchlen (0 : Int) with
    | error _ =>
      rw [hfill] at h; simp only [error_bind] at h; cases h
    | ok strip =>
      rw [hfill] at h; simp only [ok_bind] at h
      by_cases hon : onto = true
      · simp only [if_pos hon] at h
        cases hheld : SudoRt.atL bS.sudo_5Board_4held dst with
        | error _ =>
          rw [hheld] at h; simp only [error_bind] at h; cases h
        | ok held =>
          rw [hheld] at h; simp only [ok_bind] at h
          cases hassert : SudoRt.sudoAssert held 556 with
          | error _ =>
            rw [hassert] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hassert] at h; simp only [ok_bind] at h
            cases hr : SudoRt.atL bS.sudo_5Board_4home dst with
            | error _ =>
              rw [hr] at h; simp only [error_bind] at h; cases h
            | ok r =>
              rw [hr] at h; simp only [ok_bind] at h
              cases hph : SudoRt.putL bS.sudo_5Board_4held dst false with
              | error _ =>
                rw [hph] at h; simp only [error_bind] at h; cases h
              | ok heldA =>
                rw [hph] at h; simp only [ok_bind] at h
                cases hpa : SudoRt.putL bS.sudo_5Board_4home dst (#[] : Array Int) with
                | error _ =>
                  rw [hpa] at h; simp only [error_bind] at h; cases h
                | ok homeA =>
                  rw [hpa] at h; simp only [ok_bind] at h
                  cases hpeg : Ecbs.npeg r with
                  | error _ =>
                    rw [hpeg] at h; simp only [error_bind] at h; cases h
                  | ok pegs =>
                    rw [hpeg] at h; simp only [ok_bind] at h
                    cases hm : SudoRt.mulI (2 : Int) pegs with
                    | error _ =>
                      rw [hm] at h; simp only [error_bind] at h; cases h
                    | ok m =>
                      rw [hm] at h; simp only [ok_bind] at h
                      cases hmv : SudoRt.addI bS.sudo_5Board_4cost.sudo_5Costs_5moves m with
                      | error _ =>
                        rw [hmv] at h; simp only [error_bind] at h; cases h
                      | ok mv =>
                        rw [hmv] at h; simp only [ok_bind] at h
                        cases hsl : SudoRt.addI bS.sudo_5Board_4cost.sudo_5Costs_6slides m with
                        | error _ =>
                          rw [hsl] at h; simp only [error_bind] at h; cases h
                        | ok sl =>
                          rw [hsl] at h; simp only [ok_bind] at h
                          cases hsub : SudoRt.subI n (1 : Int) with
                          | error _ =>
                            rw [hsub] at h; simp only [error_bind] at h; cases h
                          | ok toV =>
                            rw [hsub] at h; simp only [ok_bind] at h
                            rw [except_bind_pure] at h
                            cases runLoopOn_ok_after (0, strip)
                                (if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1)
                                (Ecbs.bandCopyStep r toV) _ _ b' h with
                            | inl hex =>
                              rcases hex with ⟨s, hs⟩
                              exact (mulFromHeld_ladder n first second copySecond mirror _ s.2 b' hs).trans hS
                            | inr hex =>
                              rcases hex with ⟨rb, _, s0, hstep⟩
                              exact absurd hstep (bandCopyStep_no_ret r toV s0 rb)
      · simp only [if_neg hon] at h
        exact (mulFromHeld_ladder n first second copySecond mirror _ strip b' h).trans hS

theorem mulKeep_ladder (dst first second : Int) (copySecond onto mirror : Bool)
    (b0 b' : Ecbs.Board)
    (h : Ecbs.mulKeep b0 dst first second copySecond onto mirror = .ok b') :
    b'.sudo_5Board_6ladder = b0.sudo_5Board_6ladder := by
  unfold Ecbs.mulKeep at h
  dsimp only at h
  cases hop : SudoRt.atL b0.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_mul with
  | error _ =>
    rw [hop] at h; simp only [error_bind] at h; cases h
  | ok c0 =>
    rw [hop] at h; simp only [ok_bind] at h
    cases hadd : SudoRt.addI c0 (1 : Int) with
    | error _ =>
      rw [hadd] at h; simp only [error_bind] at h; cases h
    | ok c1 =>
      rw [hadd] at h; simp only [ok_bind] at h
      cases hput : SudoRt.putL b0.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_mul c1 with
      | error _ =>
        rw [hput] at h; simp only [error_bind] at h; cases h
      | ok ops =>
        rw [hput] at h; simp only [ok_bind] at h
        let bOps : Ecbs.Board :=
          { b0 with sudo_5Board_4cost :=
              { b0.sudo_5Board_4cost with sudo_5Costs_3ops := ops } }
        cases hlog : Ecbs.log_op bOps with
        | error _ =>
          rw [hlog] at h; simp only [error_bind] at h; cases h
        | ok bL =>
          rw [hlog] at h; simp only [ok_bind] at h
          have hLL := (log_op_ladder bOps bL hlog).trans
            (by rfl : bOps.sudo_5Board_6ladder = b0.sudo_5Board_6ladder)
          let n := bL.sudo_5Board_1t.sudo_4Tier_1n
          by_cases hon : onto = true
          · rw [if_pos hon, pure_eq_ok, ok_bind] at h
            by_cases hbench : bL.sudo_5Board_8bench_on = true
            · rw [if_pos hbench, pure_eq_ok, ok_bind] at h
              by_cases hto : SudoRt.SEq.beq bL.sudo_5Board_8bench_to dst = true
              · rw [if_pos hto] at h
                cases hheld : SudoRt.atL bL.sudo_5Board_4held dst with
                | error _ =>
                  rw [hheld] at h; simp only [error_bind] at h; cases h
                | ok heldD =>
                  rw [hheld] at h
                  simp only [ok_bind] at h
                  rw [pure_eq_ok, ok_bind] at h
                  by_cases hfree : (!heldD) = true
                  · rw [if_pos hfree] at h
                    exact (mulFromHeld_ladder n first second copySecond mirror bL
                        bL.sudo_5Board_5bench b' h).trans hLL
                  · rw [if_neg hfree] at h
                    exact (mulElse_ladder n dst first second copySecond onto mirror bL b' h).trans hLL
              · rw [if_neg hto, pure_eq_ok, ok_bind] at h
                rw [if_neg Bool.false_ne_true] at h
                exact (mulElse_ladder n dst first second copySecond onto mirror bL b' h).trans hLL
            · rw [if_neg hbench, pure_eq_ok, ok_bind] at h
              rw [if_neg Bool.false_ne_true, ok_bind] at h
              rw [if_neg Bool.false_ne_true] at h
              exact (mulElse_ladder n dst first second copySecond onto mirror bL b' h).trans hLL
          · rw [if_neg hon, pure_eq_ok, ok_bind] at h
            rw [if_neg Bool.false_ne_true, ok_bind] at h
            rw [if_neg Bool.false_ne_true, ok_bind] at h
            rw [if_neg Bool.false_ne_true] at h
            exact (mulElse_ladder n dst first second copySecond onto mirror bL b' h).trans hLL

theorem mul_board_keeps (dst first second : Int) (copySecond onto mirror : Bool) :
    Keeps (fun b => Ecbs.mul b dst first second copySecond onto mirror) := by
  intro b0 b' h
  dsimp only at h
  rw [mul_keep_eq] at h
  exact mulKeep_ladder dst first second copySecond onto mirror b0 b' h

theorem cubePegBody_ladder (src : Nat) (b b' : Ecbs.Board) (j : Int)
    (h : cubePegBody src b j = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold cubePegBody at h
  dsimp only at h
  cases hc : Ecbs.cube b (src : Int) (src : Int) with
  | error _ =>
    rw [hc] at h; simp only [error_bind] at h; cases h
  | ok b1 =>
    rw [hc] at h; simp only [ok_bind] at h
    have h1 := cube_board_keeps (src : Int) (src : Int) b b1 hc
    cases ht : Ecbs.tally_put b1 j (2 : Int) with
    | error _ =>
      rw [ht] at h; simp only [error_bind] at h; cases h
    | ok b2 =>
      rw [ht] at h; simp only [ok_bind] at h
      have h2 := (tally_put_ladder b1 b2 j (2 : Int) ht).trans h1
      cases hv : SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int) with
      | error _ =>
        rw [hv] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hv] at h; simp only [ok_bind, pure_eq_ok] at h
        cases h
        exact h2

theorem cubePegStep_ladder (src : Nat) (toV : Int) (σ : Int × Ecbs.Board)
    (fl : SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board)
    (hst : cubePegStep src toV σ = .ok fl) :
    match fl with
    | .cont s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .brk s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder := by
  unfold cubePegStep at hst
  dsimp only at hst
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hgt] at hst
    cases hb : cubePegBody src σ.2 σ.1 with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok b1 =>
      rw [hb] at hst; simp only [ok_bind, pure_eq_ok] at hst
      have hbody := cubePegBody_ladder src σ.2 b1 σ.1 hb
      by_cases hlast : (σ.1 == toV) = true
      · simp only [if_pos hlast, pure_eq_ok] at hst
        cases hst
        exact hbody
      · rw [if_neg hlast] at hst
        cases hj : SudoRt.addI σ.1 (1 : Int) with
        | error _ =>
          rw [hj] at hst; simp only [error_bind] at hst; cases hst
        | ok _ =>
          rw [hj] at hst; simp only [ok_bind, pure_eq_ok] at hst
          cases hst
          exact hbody

theorem cube_peg_state_ladder (src : Nat) (toV j0 : Int) (fuel : Nat)
    (b : Ecbs.Board) (p : Int × Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, b) fuel (cubePegStep src toV)
        (fun σ => .ok σ) (fun r => .ok ((0 : Int), r)) = .ok p) :
    p.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  apply runLoopOn_ok_inv
      (P := fun s : Int × Ecbs.Board => s.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (Q := fun q : Int × Ecbs.Board => q.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (h := h)
  · rfl
  · intro s s' hs hstep
    exact (cubePegStep_ladder src toV s (.cont s') hstep).trans hs
  · intro s s' hs hstep
    exact (cubePegStep_ladder src toV s (.brk s') hstep).trans hs
  · intro s r q hs hstep hr
    cases hr
    exact (cubePegStep_ladder src toV s (.ret r) hstep).trans hs
  · intro s q hs ha
    cases ha
    exact hs

theorem climbClear_ladder (b : Ecbs.Board) (rung m : Nat) (b' : Ecbs.Board)
    (h : climbClear b rung m = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold climbClear at h
  dsimp only at h
  cases hp : Ecbs.park_rung b (rung : Int) with
  | error _ =>
    rw [hp] at h; simp only [error_bind] at h; cases h
  | ok bP =>
    rw [hp] at h; simp only [ok_bind] at h
    have hP := park_rung_keeps (rung : Int) b bP hp
    cases hc : Ecbs.copy_band bP ((6 : Nat) : Int) ((5 : Nat) : Int) false with
    | error _ =>
      rw [hc] at h; simp only [error_bind] at h; cases h
    | ok bC =>
      rw [hc] at h; simp only [ok_bind] at h
      have hC := (copy_band_keeps ((6 : Nat) : Int) ((5 : Nat) : Int) false bP bC hc).trans hP
      cases hw : SudoRt.runLoopOn (Int.ofNat 0)
          (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (whiteStep bC (Int.ofNat (m - 1)))
          (fun j => .ok (bC, j)) (fun _ => .ok (bC, (0 : Int))) with
      | error _ =>
        rw [hw] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hw] at h; simp only [ok_bind] at h
        cases hcube : SudoRt.runLoopOn (Int.ofNat 0, bC)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1)))
            (fun σ => .ok σ) (fun r => .ok ((0 : Int), r)) with
        | error _ =>
          rw [hcube] at h; simp only [error_bind] at h; cases h
        | ok out =>
          rw [hcube] at h; simp only [ok_bind] at h
          have hpair := cube_peg_state_ladder 6 (Int.ofNat (m - 1)) (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1))) bC out hcube
          cases hm : Ecbs.mul out.2 (5 : Int) (5 : Int) (6 : Int) false false false with
          | error _ =>
            rw [hm] at h; simp only [error_bind] at h; cases h
          | ok bM =>
            rw [hm] at h; simp only [ok_bind] at h
            have hM := (mul_board_keeps (5 : Int) (5 : Int) (6 : Int) false false false
              out.2 bM hm).trans (hpair.trans hC)
            cases hcl : Ecbs.clear bM (5 : Int) with
            | error _ =>
              rw [hcl] at h; cases h
            | ok bc =>
              rw [hcl] at h
              cases h
              exact (clear_board_keeps (5 : Int) bM b' hcl).trans hM

theorem rungNest_ladder (rung x : Int) (last : Bool) (b b' : Ecbs.Board)
    (h : rungNest rung x last b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold rungNest at h
  by_cases hlast : last = true
  · rw [hlast] at h
    simp only [Bool.not_true] at h
    rw [if_neg Bool.false_ne_true] at h
    by_cases hr : SudoRt.SEq.beq rung (2 : Int) = true
    · rw [if_pos hr] at h
      cases hc : Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int) with
      | error _ =>
        rw [hc] at h; simp only [error_bind] at h; cases h
      | ok b1 =>
        rw [hc] at h; simp only [ok_bind] at h
        have h1 := cube_board_keeps ((6 : Nat) : Int) ((5 : Nat) : Int) b b1 hc
        cases hm : Ecbs.mul b1 ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false with
        | error _ =>
          rw [hm] at h; simp only [error_bind] at h; cases h
        | ok b2 =>
          rw [hm] at h; simp only [ok_bind] at h
          rw [if_neg Bool.false_ne_true, pure_eq_ok] at h
          cases h
          exact (mul_board_keeps ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
            b1 b' hm).trans h1
    · rw [if_neg hr, pure_eq_ok] at h
      cases h
      rfl
  · rw [eq_false_of_ne_true hlast] at h
    simp only [Bool.not_false] at h
    rw [if_pos trivial] at h
    cases hd : Ecbs.tally_double b with
    | error _ =>
      rw [hd] at h; simp only [error_bind] at h; cases h
    | ok bD =>
      rw [hd] at h; simp only [ok_bind] at h
      have hD := tally_double_keeps b bD hd
      by_cases hr : SudoRt.SEq.beq rung (2 : Int) = true
      · rw [if_pos hr] at h
        cases hc : Ecbs.cube bD ((6 : Nat) : Int) ((5 : Nat) : Int) with
        | error _ =>
          rw [hc] at h; simp only [error_bind] at h; cases h
        | ok b1 =>
          rw [hc] at h; simp only [ok_bind] at h
          have h1 := (cube_board_keeps ((6 : Nat) : Int) ((5 : Nat) : Int) bD b1 hc).trans hD
          cases hm : Ecbs.mul b1 ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false with
          | error _ =>
            rw [hm] at h; simp only [error_bind] at h; cases h
          | ok b2 =>
            rw [hm] at h; simp only [ok_bind] at h
            rw [if_pos trivial] at h
            cases ha : Ecbs.tally_add_one b2 with
            | error _ =>
              rw [ha] at h; cases h
            | ok ba =>
              rw [ha] at h
              cases h
              exact (tally_add_one_keeps b2 b' ha).trans
                ((mul_board_keeps ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
                  b1 b2 hm).trans h1)
      · rw [if_neg hr, pure_eq_ok] at h
        cases h
        exact hD

theorem climbRung_ladder (b : Ecbs.Board) (rung : Nat) (last : Bool) (x : Int) (m : Nat)
    (b' : Ecbs.Board) (h : climbRung b rung last x m = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  have heq : climbRung b rung last x m =
      (do
        let b ← climbClear b rung m
        rungNest (rung : Int) x last b) := by
    unfold climbRung rungNest
    rfl
  rw [heq] at h
  cases hc : climbClear b rung m with
  | error _ =>
    rw [hc] at h; simp only [error_bind] at h; cases h
  | ok b1 =>
    rw [hc] at h; simp only [ok_bind] at h
    exact (rungNest_ladder (rung : Int) x last b1 b' h).trans (climbClear_ladder b rung m b1 hc)

theorem rungTail_ladder (rung x : Int) (last : Bool) (b b' : Ecbs.Board)
    (h : rungTail rung x last b = .ok (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold rungTail at h
  cases hm : Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false with
  | error _ =>
    rw [hm] at h; simp only [error_bind] at h; cases h
  | ok bM =>
    rw [hm] at h; simp only [ok_bind] at h
    have hM := mul_board_keeps (5 : Int) (5 : Int) (6 : Int) false false false b bM hm
    cases hcl : Ecbs.clear bM (5 : Int) with
    | error _ =>
      rw [hcl] at h; simp only [error_bind] at h; cases h
    | ok bC =>
      rw [hcl] at h; simp only [ok_bind] at h
      have hC := (clear_board_keeps (5 : Int) bM bC hcl).trans hM
      cases hn : rungNest rung x last bC with
      | error _ =>
        rw [hn] at h; simp only [error_bind] at h; cases h
      | ok bN =>
        rw [hn] at h; simp only [ok_bind, pure_eq_ok] at h
        cases h
        exact (rungNest_ladder rung x last bC b' hn).trans hC

end EcbsLink2.Link2
