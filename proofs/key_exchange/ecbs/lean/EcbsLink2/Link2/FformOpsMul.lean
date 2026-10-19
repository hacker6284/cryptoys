/-
  `Ecbs.mul` writes ops slot 0 and leaves every other slot. `Ecbs.clear`
  leaves the whole ops array. The schoolbook, the lane fold, settle, and the
  spare copy never store into `ops`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MulKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

def pegOps (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int)) :
    Array Int :=
  match fl with
  | .cont fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops
  | .brk fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops
  | .ret rp => rp.1.sudo_5Board_4cost.sudo_5Costs_3ops

def foldFlowOps
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)) :
    Array Int :=
  match fl with
  | .cont s => s.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
  | .brk s => s.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
  | .ret rp => rp.1.sudo_5Board_4cost.sudo_5Costs_3ops

def rowFlowOps (fl : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board) : Array Int :=
  match fl with
  | .cont p => p.1.sudo_5Board_4cost.sudo_5Costs_3ops
  | .brk p => p.1.sudo_5Board_4cost.sudo_5Costs_3ops
  | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops

theorem withHole_ops (b : Ecbs.Board) (top : Int) :
    (withHole b top).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem note_peak_ops (b b' : Ecbs.Board) (h : Ecbs.note_peak b = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.note_peak at h
  dsimp only at h
  cases hv : Ecbs.occupied b with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok v =>
    rw [hv] at h
    simp only [ok_bind] at h
    by_cases hc : decide (v > b.sudo_5Board_4cost.sudo_5Costs_4peak) = true
    · rw [if_pos hc, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hc, pure_eq_ok] at h
      cases h
      rfl

theorem note_strict_ops (b b' : Ecbs.Board) (h : Ecbs.note_strict b = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.note_strict at h
  dsimp only at h
  cases hv : Ecbs.occupied b with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok v =>
    rw [hv] at h
    simp only [ok_bind] at h
    by_cases hc : decide (v > b.sudo_5Board_4cost.sudo_5Costs_11peak_strict) = true
    · rw [if_pos hc, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hc, pure_eq_ok] at h
      cases h
      rfl

theorem marker_step_ops (b b' : Ecbs.Board) (h : Ecbs.marker_step b = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.marker_step at h
  dsimp only at h
  by_cases hlt : decide (b.sudo_5Board_6marker < (0 : Int)) = true
  · rw [if_pos hlt] at h
    cases hc : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int) with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h; cases h
    | ok v =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases ha :
          SudoRt.sudoAssert (decide ((0 : Int) < b.sudo_5Board_1t.sudo_4Tier_6script)) 321 with
      | error _ =>
        rw [ha] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [ha] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI (0 : Int) (1 : Int) with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h; cases h
        | ok m =>
          rw [hm] at h
          simp only [ok_bind] at h
          by_cases hmx :
              decide (m > b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) = true
          · rw [if_pos hmx, pure_eq_ok] at h
            cases h
            rfl
          · rw [if_neg hmx, pure_eq_ok] at h
            cases h
            rfl
  · rw [if_neg hlt] at h
    cases hm : SudoRt.addI b.sudo_5Board_6marker (1 : Int) with
    | error _ =>
      rw [hm] at h
      simp only [error_bind] at h; cases h
    | ok m =>
      rw [hm] at h
      simp only [ok_bind] at h
      cases hc : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hc] at h
        simp only [error_bind] at h; cases h
      | ok v =>
        rw [hc] at h
        simp only [ok_bind] at h
        cases ha :
            SudoRt.sudoAssert (decide (m < b.sudo_5Board_1t.sudo_4Tier_6script)) 321 with
        | error _ =>
          rw [ha] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [ha] at h
          simp only [ok_bind] at h
          cases hm2 : SudoRt.addI m (1 : Int) with
          | error _ =>
            rw [hm2] at h
            simp only [error_bind] at h; cases h
          | ok m2 =>
            rw [hm2] at h
            simp only [ok_bind] at h
            by_cases hmx :
                decide (m2 > b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) = true
            · rw [if_pos hmx, pure_eq_ok] at h
              cases h
              rfl
            · rw [if_neg hmx, pure_eq_ok] at h
              cases h
              rfl

theorem log_op_ops (b b' : Ecbs.Board) (h : Ecbs.log_op b = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.log_op at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_9marker_on = true
  · rw [if_pos hon] at h
    cases hs : Ecbs.marker_step b with
    | error _ =>
      rw [hs] at h
      simp only [error_bind] at h; cases h
    | ok b1 =>
      rw [hs] at h
      simp only [ok_bind, pure_eq_ok] at h
      cases h
      exact marker_step_ops b b' hs
  · rw [if_neg hon, pure_eq_ok] at h
    cases h
    rfl

/-- The image writes after the range checks. They touch the strip and the move counter. -/
private theorem lane_after_assert_ops
    (chk : Bool) (strip : Array Int) (d1 d2 c : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let _ ← SudoRt.sudoAssert chk 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegOps fl = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  cases ha : SudoRt.sudoAssert chk 531 with
  | error _ =>
    rw [ha] at h; simp only [error_bind] at h; cases h
  | ok _ =>
    rw [ha] at h; simp only [ok_bind] at h
    cases hc1 : SudoRt.atL strip d1 with
    | error _ =>
      rw [hc1] at h; simp only [error_bind] at h; cases h
    | ok cur1 =>
      rw [hc1] at h; simp only [ok_bind] at h
      cases hs1 : SudoRt.addI cur1 c with
      | error _ =>
        rw [hs1] at h; simp only [error_bind] at h; cases h
      | ok sum1 =>
        rw [hs1] at h; simp only [ok_bind] at h
        cases hr1 : SudoRt.modI sum1 (3 : Int) with
        | error _ =>
          rw [hr1] at h; simp only [error_bind] at h; cases h
        | ok r1 =>
          rw [hr1] at h; simp only [ok_bind] at h
          cases hp1 : SudoRt.putL strip d1 r1 with
          | error _ =>
            rw [hp1] at h; simp only [error_bind] at h; cases h
          | ok strip1 =>
            rw [hp1] at h; simp only [ok_bind] at h
            cases hc2 : SudoRt.atL strip1 d2 with
            | error _ =>
              rw [hc2] at h; simp only [error_bind] at h; cases h
            | ok cur2 =>
              rw [hc2] at h; simp only [ok_bind] at h
              cases hs2 : SudoRt.addI cur2 c with
              | error _ =>
                rw [hs2] at h; simp only [error_bind] at h; cases h
              | ok sum2 =>
                rw [hs2] at h; simp only [ok_bind] at h
                cases hr2 : SudoRt.modI sum2 (3 : Int) with
                | error _ =>
                  rw [hr2] at h; simp only [error_bind] at h; cases h
                | ok r2 =>
                  rw [hr2] at h; simp only [ok_bind] at h
                  cases hp2 : SudoRt.putL strip1 d2 r2 with
                  | error _ =>
                    rw [hp2] at h; simp only [error_bind] at h; cases h
                  | ok _ =>
                    rw [hp2] at h; simp only [ok_bind] at h
                    cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int) with
                    | error _ =>
                      rw [hm] at h; simp only [error_bind] at h; cases h
                    | ok _ =>
                      rw [hm] at h; simp only [ok_bind, pure_eq_ok] at h
                      cases h
                      rfl

/-- `d1` and `d2` are checked, then the image writes run. A failing check is a trap. -/
private theorem lane_from_range_ops
    (d1 d2 e c : Int) (strip : Array Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let g1 ← (if decide (d1 ≥ (0 : Int)) = true then
            pure (decide (d1 < e)) else pure false)
        let g2 ← (if g1 = true then pure (decide (d2 ≥ (0 : Int))) else pure false)
        let g3 ← (if g2 = true then pure (decide (d2 < e)) else pure false)
        let _ ← SudoRt.sudoAssert g3 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegOps fl = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  by_cases hg1 : decide (d1 ≥ (0 : Int)) = true
  · rw [if_pos hg1, pure_eq_ok, ok_bind] at h
    by_cases hlt : decide (d1 < e) = true
    · rw [if_pos hlt, pure_eq_ok, ok_bind] at h
      by_cases hg2 : decide (d2 ≥ (0 : Int)) = true
      · rw [if_pos hg2, pure_eq_ok, ok_bind] at h
        exact lane_after_assert_ops (decide (d2 < e)) strip d1 d2 c b fl h
      · rw [if_neg hg2, pure_eq_ok, ok_bind] at h
        exact lane_after_assert_ops false strip d1 d2 c b fl h
    · rw [if_neg hlt, pure_eq_ok, ok_bind] at h
      exact lane_after_assert_ops false strip d1 d2 c b fl h
  · rw [if_neg hg1, pure_eq_ok, ok_bind] at h
    rw [if_neg Bool.false_ne_true, pure_eq_ok, ok_bind] at h
    exact lane_after_assert_ops false strip d1 d2 c b fl h

/-- The geometry check, then the range checks and the image writes. -/
private theorem lane_peg_images_ops
    (strip : Array Int) (e d1 d2 c n k : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let gap ← SudoRt.subI e n
        let chk ← (if SudoRt.SEq.beq d1 gap = true then do
            let nk ← SudoRt.subI n k
            let eg ← SudoRt.subI e nk
            pure (SudoRt.SEq.beq d2 eg)
          else pure false)
        let _ ← SudoRt.sudoAssert chk 530
        let g1 ← (if decide (d1 ≥ (0 : Int)) = true then
            pure (decide (d1 < e)) else pure false)
        let g2 ← (if g1 = true then pure (decide (d2 ≥ (0 : Int))) else pure false)
        let g3 ← (if g2 = true then pure (decide (d2 < e)) else pure false)
        let _ ← SudoRt.sudoAssert g3 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegOps fl = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  cases hgap : SudoRt.subI e n with
  | error _ =>
    rw [hgap] at h; simp only [error_bind] at h; cases h
  | ok gap =>
    rw [hgap] at h; simp only [ok_bind] at h
    by_cases hbeq : SudoRt.SEq.beq d1 gap = true
    · rw [if_pos hbeq] at h
      cases hnk : SudoRt.subI n k with
      | error _ =>
        rw [hnk] at h; simp only [error_bind] at h; cases h
      | ok nk =>
        rw [hnk] at h; simp only [ok_bind] at h
        cases heg : SudoRt.subI e nk with
        | error _ =>
          rw [heg] at h; simp only [error_bind] at h; cases h
        | ok eg =>
          rw [heg] at h; simp only [ok_bind, pure_eq_ok, ok_bind] at h
          cases hassert : SudoRt.sudoAssert (SudoRt.SEq.beq d2 eg) 530 with
          | error _ =>
            rw [hassert] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hassert] at h; simp only [ok_bind] at h
            exact lane_from_range_ops d1 d2 e c strip b fl h
    · rw [if_neg hbeq, pure_eq_ok, ok_bind] at h
      cases hassert : SudoRt.sudoAssert false 530 with
      | error _ =>
        rw [hassert] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hassert] at h; simp only [ok_bind] at h
        exact lane_from_range_ops d1 d2 e c strip b fl h

theorem lanePeg_ops (strip : Array Int) (e : Int) (b : Ecbs.Board) (w ht r n k : Int)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : lanePeg strip e b w ht r n k = .ok fl) :
    pegOps fl = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold lanePeg at h
  dsimp only at h
  cases hc : SudoRt.atL strip e with
  | error _ =>
    rw [hc] at h; simp only [error_bind] at h; cases h
  | ok c =>
    rw [hc] at h; simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases hp0 : SudoRt.putL strip e (0 : Int) with
      | error _ =>
        rw [hp0] at h; simp only [error_bind] at h; cases h
      | ok strip0 =>
        rw [hp0] at h; simp only [ok_bind] at h
        cases hm1 : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
        | error _ =>
          rw [hm1] at h; simp only [error_bind] at h; cases h
        | ok mv1 =>
          rw [hm1] at h; simp only [ok_bind] at h
          let b1 : Ecbs.Board :=
            { b with sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv1 } }
          cases hdiv : SudoRt.divI e w with
          | error _ =>
            rw [hdiv] at h; simp only [error_bind] at h; cases h
          | ok row =>
            rw [hdiv] at h; simp only [ok_bind] at h
            cases hmod : SudoRt.modI e w with
            | error _ =>
              rw [hmod] at h; simp only [error_bind] at h; cases h
            | ok col =>
              rw [hmod] at h; simp only [ok_bind] at h
              cases hsrow : SudoRt.subI row ht with
              | error _ =>
                rw [hsrow] at h; simp only [error_bind] at h; cases h
              | ok r1 =>
                rw [hsrow] at h; simp only [ok_bind] at h
                cases hc1 : SudoRt.addI col (1 : Int) with
                | error _ =>
                  rw [hc1] at h; simp only [error_bind] at h; cases h
                | ok c1 =>
                  rw [hc1] at h; simp only [ok_bind] at h
                  by_cases hwrap : SudoRt.SEq.beq c1 w = true
                  · rw [if_pos hwrap] at h
                    cases hr1 : SudoRt.addI r1 (1 : Int) with
                    | error _ =>
                      rw [hr1] at h; simp only [error_bind] at h; cases h
                    | ok r1' =>
                      rw [hr1] at h; simp only [ok_bind] at h
                      cases hm : SudoRt.mulI r1' w with
                      | error _ =>
                        rw [hm] at h; simp only [error_bind] at h; cases h
                      | ok m1 =>
                        rw [hm] at h; simp only [ok_bind] at h
                        cases hd1 : SudoRt.addI m1 (0 : Int) with
                        | error _ =>
                          rw [hd1] at h; simp only [error_bind] at h; cases h
                        | ok d1 =>
                          rw [hd1] at h; simp only [ok_bind] at h
                          cases hsr : SudoRt.subI row r with
                          | error _ =>
                            rw [hsr] at h; simp only [error_bind] at h; cases h
                          | ok rowR =>
                            rw [hsr] at h; simp only [ok_bind] at h
                            cases hm2 : SudoRt.mulI rowR w with
                            | error _ =>
                              rw [hm2] at h; simp only [error_bind] at h; cases h
                            | ok m2 =>
                              rw [hm2] at h; simp only [ok_bind] at h
                              cases hd2 : SudoRt.addI m2 col with
                              | error _ =>
                                rw [hd2] at h; simp only [error_bind] at h; cases h
                              | ok d2 =>
                                rw [hd2] at h; simp only [ok_bind] at h
                                exact (lane_peg_images_ops strip0 e d1 d2 c n k b1 fl h).trans
                                  (by rfl : b1.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
                  · rw [if_neg hwrap] at h
                    cases hm : SudoRt.mulI r1 w with
                    | error _ =>
                      rw [hm] at h; simp only [error_bind] at h; cases h
                    | ok m1 =>
                      rw [hm] at h; simp only [ok_bind] at h
                      cases hd1 : SudoRt.addI m1 c1 with
                      | error _ =>
                        rw [hd1] at h; simp only [error_bind] at h; cases h
                      | ok d1 =>
                        rw [hd1] at h; simp only [ok_bind] at h
                        cases hsr : SudoRt.subI row r with
                        | error _ =>
                          rw [hsr] at h; simp only [error_bind] at h; cases h
                        | ok rowR =>
                          rw [hsr] at h; simp only [ok_bind] at h
                          cases hm2 : SudoRt.mulI rowR w with
                          | error _ =>
                            rw [hm2] at h; simp only [error_bind] at h; cases h
                          | ok m2 =>
                            rw [hm2] at h; simp only [ok_bind] at h
                            cases hd2 : SudoRt.addI m2 col with
                            | error _ =>
                              rw [hd2] at h; simp only [error_bind] at h; cases h
                            | ok d2 =>
                              rw [hd2] at h; simp only [ok_bind] at h
                              exact (lane_peg_images_ops strip0 e d1 d2 c n k b1 fl h).trans
                                (by rfl : b1.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)

theorem laneFoldStep_ops (w h r n k toV : Int)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int))
    (hst : laneFoldStep w h r n k toV σ = .ok fl) :
    foldFlowOps fl = σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold laneFoldStep at hst
  dsimp only at hst
  by_cases hlt : σ.1 < toV
  · rw [if_pos hlt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hlt] at hst
    cases hb : lanePeg σ.2.1 σ.1 σ.2.2 w h r n k with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hpeg := lanePeg_ops σ.2.1 σ.1 σ.2.2 w h r n k flb hb
      cases flb with
      | ret rp =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hpeg
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hpeg
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hpeg
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.subI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hi] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hpeg

/-- If every step keeps the ops array, the block's board is the board it started with.
    `after` returns that board; `onRet` returns the board a step returned. -/
theorem descBlock_ops
    (step : Int × (Array Int × Ecbs.Board) →
      Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)))
    (hf : ∀ σ fl, step σ = .ok fl →
      foldFlowOps fl = σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops)
    (nI : Int) (strip : Array Int) (b b' : Ecbs.Board) (strip' : Array Int)
    (h : descBlock step nI strip b = .ok (b', strip')) :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold descBlock at h
  dsimp only at h
  cases hfrom : SudoRt.subI (SudoRt.listLen strip) (1 : Int) with
  | error _ =>
    rw [hfrom] at h; simp only [error_bind] at h; cases h
  | ok fromV =>
    rw [hfrom] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    apply runLoopOn_ok_inv
        (P := fun σ : Int × (Array Int × Ecbs.Board) =>
          σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
        (Q := fun p : Ecbs.Board × Array Int =>
          p.1.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
        (h := h)
    · rfl
    · intro s s' hs hstep
      exact (hf s (.cont s') hstep).trans hs
    · intro s s' hs hstep
      exact (hf s (.brk s') hstep).trans hs
    · intro s rp p hs hstep hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact (hf s (.ret rp) hstep).trans hs
    · intro s p hs hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact hs

theorem lane_fold_ops (b : Ecbs.Board) (strip : Array Int)
    (b' : Ecbs.Board) (strip' : Array Int)
    (h : Ecbs.lane_fold b strip = .ok (b', strip')) :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  rw [laneFold_emit] at h
  unfold laneFoldEmit at h
  dsimp only at h
  cases hlast : SudoRt.subI (SudoRt.listLen strip) (1 : Int) with
  | error _ =>
    rw [hlast] at h; simp only [error_bind] at h; cases h
  | ok last =>
    rw [hlast] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    have hsplit := runLoopOn_ok_after (0, (0 : Int))
      (if (0 : Int) > last then 1 else (last - 0).natAbs + 1)
      (topStep strip last)
      (fun σ =>
        if decide (σ.2 > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) = true then do
          SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515
          descBlock
            (laneFoldStep b.sudo_5Board_1t.sudo_4Tier_1w b.sudo_5Board_1t.sudo_4Tier_1h
              b.sudo_5Board_1t.sudo_4Tier_1r b.sudo_5Board_1t.sudo_4Tier_1n
              b.sudo_5Board_1t.sudo_4Tier_1k b.sudo_5Board_1t.sudo_4Tier_1n)
            b.sudo_5Board_1t.sudo_4Tier_1n strip (withHole b σ.2)
        else do
          SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515
          descBlock
            (laneFoldStep b.sudo_5Board_1t.sudo_4Tier_1w b.sudo_5Board_1t.sudo_4Tier_1h
              b.sudo_5Board_1t.sudo_4Tier_1r b.sudo_5Board_1t.sudo_4Tier_1n
              b.sudo_5Board_1t.sudo_4Tier_1k b.sudo_5Board_1t.sudo_4Tier_1n)
            b.sudo_5Board_1t.sudo_4Tier_1n strip b)
      (fun r => pure r) (b', strip') h
    cases hsplit with
    | inr hret =>
      obtain ⟨rp, _, s, hs⟩ := hret
      exact absurd hs (topStep_no_ret strip last s rp)
    | inl hex =>
      obtain ⟨σ, ha⟩ := hex
      dsimp only at ha
      let w := b.sudo_5Board_1t.sudo_4Tier_1w
      let ht := b.sudo_5Board_1t.sudo_4Tier_1h
      let rt := b.sudo_5Board_1t.sudo_4Tier_1r
      let n := b.sudo_5Board_1t.sudo_4Tier_1n
      let k := b.sudo_5Board_1t.sudo_4Tier_1k
      have hstep : ∀ s fl, laneFoldStep w ht rt n k n s = .ok fl →
          foldFlowOps fl = s.2.2.sudo_5Board_4cost.sudo_5Costs_3ops :=
        fun s fl hs => laneFoldStep_ops w ht rt n k n s fl hs
      by_cases hhi :
          decide (σ.2 > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) = true
      · rw [if_pos hhi] at ha
        cases hassert :
            SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515 with
        | error _ =>
          rw [hassert] at ha; simp only [error_bind] at ha; cases ha
        | ok _ =>
          rw [hassert] at ha; simp only [ok_bind] at ha
          exact (descBlock_ops _ hstep n strip (withHole b σ.2) b' strip' ha).trans
            (withHole_ops b σ.2)
      · rw [if_neg hhi] at ha
        cases hassert :
            SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515 with
        | error _ =>
          rw [hassert] at ha; simp only [error_bind] at ha; cases ha
        | ok _ =>
          rw [hassert] at ha; simp only [ok_bind] at ha
          exact descBlock_ops _ hstep n strip b b' strip' ha

theorem layDo_ops (a strip : Array Int) (i j : Int) (mir : Bool) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board)
    (h : layDo a strip i j mir b = .ok fl) :
    match fl with
    | .cont fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold layDo at h
  dsimp only at h
  cases hd : SudoRt.atL a j with
  | error _ =>
    rw [hd] at h
    simp only [error_bind] at h
    cases h
  | ok d =>
    rw [hd] at h
    simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq d (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq d (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases mir with
      | true =>
        simp only [if_true] at h
        cases hf : Ecbs.flip d with
        | error _ =>
          rw [hf] at h
          simp only [error_bind] at h
          cases h
        | ok d' =>
          rw [hf] at h
          simp only [ok_bind] at h
          cases hi : SudoRt.addI i j with
          | error _ =>
            rw [hi] at h
            simp only [error_bind] at h
            cases h
          | ok ix =>
            rw [hi] at h
            simp only [ok_bind] at h
            cases hc : SudoRt.atL strip ix with
              | error _ =>
                rw [hc] at h
                simp only [error_bind] at h
                cases h
              | ok cur =>
                rw [hc] at h
                simp only [ok_bind] at h
                cases hs : SudoRt.addI cur d' with
                | error _ =>
                  rw [hs] at h
                  simp only [error_bind] at h
                  cases h
                | ok sum =>
                  rw [hs] at h
                  simp only [ok_bind] at h
                  cases hr : SudoRt.modI sum (3 : Int) with
                  | error _ =>
                    rw [hr] at h
                    simp only [error_bind] at h
                    cases h
                  | ok r =>
                    rw [hr] at h
                    simp only [ok_bind] at h
                    cases hp : SudoRt.putL strip ix r with
                    | error _ =>
                      rw [hp] at h
                      simp only [error_bind] at h
                      cases h
                    | ok _ =>
                      rw [hp] at h
                      simp only [ok_bind] at h
                      cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
                      | error _ =>
                        rw [hm] at h
                        simp only [error_bind] at h
                        cases h
                      | ok _ =>
                        rw [hm] at h
                        simp only [ok_bind, pure_eq_ok] at h
                        cases h
                        rfl
      | false =>
        rw [if_neg Bool.false_ne_true] at h
        cases hi : SudoRt.addI i j with
        | error _ =>
          rw [hi] at h
          simp only [error_bind] at h
          cases h
        | ok ix =>
          rw [hi] at h
          simp only [ok_bind] at h
          cases hc : SudoRt.atL strip ix with
            | error _ =>
              rw [hc] at h
              simp only [error_bind] at h
              cases h
            | ok cur =>
              rw [hc] at h
              simp only [ok_bind] at h
              cases hs : SudoRt.addI cur d with
              | error _ =>
                rw [hs] at h
                simp only [error_bind] at h
                cases h
              | ok sum =>
                rw [hs] at h
                simp only [ok_bind] at h
                cases hr : SudoRt.modI sum (3 : Int) with
                | error _ =>
                  rw [hr] at h
                  simp only [error_bind] at h
                  cases h
                | ok r =>
                  rw [hr] at h
                  simp only [ok_bind] at h
                  cases hp : SudoRt.putL strip ix r with
                  | error _ =>
                    rw [hp] at h
                    simp only [error_bind] at h
                    cases h
                  | ok _ =>
                    rw [hp] at h
                    simp only [ok_bind] at h
                    cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
                    | error _ =>
                      rw [hm] at h
                      simp only [error_bind] at h
                      cases h
                    | ok _ =>
                      rw [hm] at h
                      simp only [ok_bind, pure_eq_ok] at h
                      cases h
                      rfl

theorem colStep_ops (a : Array Int) (i toV : Int) (mir : Bool)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board)
    (hst : colStep a i toV mir σ = .ok fl) :
    match fl with
    | .cont s => s.2.2.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk s => s.2.2.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold colStep at hst
  dsimp only at hst
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hgt] at hst
    cases hb : layDo a σ.2.1 i σ.1 mir σ.2.2 with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hlay := layDo_ops a σ.2.1 i σ.1 mir σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hlay
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hlay
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hlay
        · rw [if_neg hlast] at hst
          cases hj : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hj] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hj] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hlay

/-- One schoolbook row. A zero coefficient leaves the board; a nonzero one runs `colStep`. -/
theorem rowBody_ops (a s : Array Int) (mirror : Bool) (nB i : Int)
    (b : Ecbs.Board) (strip : Array Int)
    (fl : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board)
    (hst : rowBody a s mirror nB i b strip = .ok fl) :
    rowFlowOps fl = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold rowBody at hst
  dsimp only at hst
  cases hc : SudoRt.atL s i with
  | error _ =>
    rw [hc] at hst; simp only [error_bind] at hst; cases hst
  | ok c =>
    rw [hc] at hst; simp only [ok_bind] at hst
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at hst
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at hst
      cases hst
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at hst
      simp only [Bool.not_false, if_true] at hst
      cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
      | error _ =>
        rw [hm] at hst; simp only [error_bind] at hst; cases hst
      | ok mv =>
        rw [hm] at hst; simp only [ok_bind] at hst
        cases hto : SudoRt.subI nB (1 : Int) with
        | error _ =>
          rw [hto] at hst; simp only [error_bind] at hst; cases hst
        | ok toJ =>
          rw [hto] at hst; simp only [ok_bind] at hst
          rw [except_bind_pure] at hst
          let b1 := withMoves b mv
          let mir2 := !(SudoRt.SEq.beq (SudoRt.SEq.beq c (2 : Int)) mirror)
          apply runLoopOn_ok_inv
              (P := fun σ : Int × (Array Int × Ecbs.Board) =>
                σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
              (Q := fun flq : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board =>
                rowFlowOps flq = b.sudo_5Board_4cost.sudo_5Costs_3ops)
              (h := hst)
          · rfl
          · intro s0 s1 hs hstep
            have hcol := colStep_ops a i toJ mir2 s0 (.cont s1) hstep
            exact hcol.trans hs
          · intro s0 s1 hs hstep
            have hcol := colStep_ops a i toJ mir2 s0 (.brk s1) hstep
            exact hcol.trans hs
          · intro s0 r q hs hstep hq
            simp only [pure_eq_ok] at hq
            cases hq
            have hcol := colStep_ops a i toJ mir2 s0 (.ret r) hstep
            exact hcol.trans hs
          · intro s0 q hs hq
            simp only [pure_eq_ok] at hq
            cases hq
            exact hs

theorem rowStep_ops (a s : Array Int) (mirror : Bool) (nB toV : Int)
    (σ : Int × (Ecbs.Board × Array Int))
    (fl : SudoRt.Flow (Int × (Ecbs.Board × Array Int)) Ecbs.Board)
    (hst : rowStep a s mirror nB toV σ = .ok fl) :
    match fl with
    | .cont st => st.2.1.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.1.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk st => st.2.1.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.1.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops = σ.2.1.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold rowStep at hst
  dsimp only at hst
  by_cases hlt : σ.1 < toV
  · rw [if_pos hlt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hlt] at hst
    cases hb : rowBody a s mirror nB σ.1 σ.2.1 σ.2.2 with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hrow := rowBody_ops a s mirror nB σ.1 σ.2.1 σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hrow
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hrow
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hrow
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.subI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hi] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hrow

theorem row_loop_ops
    (a s : Array Int) (mirror : Bool) (nB toV j0 : Int) (fuel : Nat)
    (b : Ecbs.Board) (strip : Array Int)
    (after : Int × (Ecbs.Board × Array Int) → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hafter : ∀ st q,
      st.2.1.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops →
        after st = .ok q → q.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hret : ∀ r q,
      r.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops →
        onRet r = .ok q → q.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
    (p : Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, (b, strip)) fuel (rowStep a s mirror nB toV) after onRet = .ok p) :
    p.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  apply runLoopOn_ok_inv
      (P := fun st : Int × (Ecbs.Board × Array Int) =>
        st.2.1.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
      (Q := fun q : Ecbs.Board => q.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
      (h := h)
  · rfl
  · intro st st' hs hstep
    exact (rowStep_ops a s mirror nB toV st (.cont st') hstep).trans hs
  · intro st st' hs hstep
    exact (rowStep_ops a s mirror nB toV st (.brk st') hstep).trans hs
  · intro st r q hs hstep hr
    exact hret r q ((rowStep_ops a s mirror nB toV st (.ret r) hstep).trans hs) hr
  · intro st q hs ha
    exact hafter st q hs ha

private theorem flip_step_no_ret (toV : Int) (σ : Int × Array Int) (r : Ecbs.Board) :
    (do
      let i := σ.1
      let s := σ.2
      if i > toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, s))
      else
        match ← (do
          let c ← SudoRt.atL s i
          let f ← Ecbs.flip c
          let s ← SudoRt.putL s i f
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) s)) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
        | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
        | .cont fs => do
            if i == toV then
              pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))) ≠
      .ok (SudoRt.Flow.ret r) := by
  intro h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hc : SudoRt.atL σ.2 σ.1 with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h; cases h
    | ok c =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases hf : Ecbs.flip c with
      | error _ =>
        rw [hf] at h
        simp only [error_bind] at h; cases h
      | ok f =>
        rw [hf] at h
        simp only [ok_bind] at h
        cases hp : SudoRt.putL σ.2 σ.1 f with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok s' =>
          rw [hp] at h
          simp only [ok_bind, pure_eq_ok, map_ok] at h
          by_cases hbeq : (σ.1 == toV) = true
          · rw [if_pos hbeq] at h
            cases h
          · rw [if_neg hbeq] at h
            cases hi : SudoRt.addI σ.1 (1 : Int) with
            | error _ =>
              rw [hi, error_bind] at h
              cases h
            | ok _ =>
              rw [hi, ok_bind] at h
              cases h

private theorem band_write_ops (b : Ecbs.Board) (dst : Int) (s : Array Int) (b' : Ecbs.Board)
    (h : (do
        let ix := dst
        let home ← SudoRt.putL b.sudo_5Board_4home ix s
        let b := ({ b with sudo_5Board_4home := home } : Ecbs.Board)
        let ix := dst
        let held ← SudoRt.putL b.sudo_5Board_4held ix true
        let b := ({ b with sudo_5Board_4held := held } : Ecbs.Board)
        let n ← Ecbs.npeg s
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        let b ← Ecbs.note_peak b
        pure b) = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  dsimp only at h
  cases hh : SudoRt.putL b.sudo_5Board_4home dst s with
  | error _ =>
    rw [hh] at h
    simp only [error_bind] at h; cases h
  | ok home =>
    rw [hh] at h
    simp only [ok_bind] at h
    cases hd : SudoRt.putL
        ({ b with sudo_5Board_4home := home } : Ecbs.Board).sudo_5Board_4held dst true with
    | error _ =>
      rw [hd] at h
      simp only [error_bind] at h; cases h
    | ok held =>
      rw [hd] at h
      simp only [ok_bind] at h
      cases hn : Ecbs.npeg s with
      | error _ =>
        rw [hn] at h
        simp only [error_bind] at h; cases h
      | ok n =>
        rw [hn] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI
            ({ { b with sudo_5Board_4home := home } with
                sudo_5Board_4held := held } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_5moves
            n with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h; cases h
        | ok mv =>
          rw [hm] at h
          simp only [ok_bind] at h
          let bN : Ecbs.Board :=
            { { { b with sudo_5Board_4home := home } with sudo_5Board_4held := held } with
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } }
          cases hk : Ecbs.note_peak bN with
          | error _ =>
            rw [hk] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hk] at h
            simp only [ok_bind, pure_eq_ok] at h
            cases h
            exact (note_peak_ops bN b' hk).trans rfl

theorem copy_band_ops (dst src : Int) (mirror : Bool)
    (b b' : Ecbs.Board)
    (h : Ecbs.copy_band b dst src mirror = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.copy_band at h
  dsimp only at h
  cases hv : Ecbs.value b src with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok s =>
    rw [hv] at h
    simp only [ok_bind] at h
    cases he : Ecbs.need_empty b dst with
    | error _ =>
      rw [he] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [he] at h
      simp only [ok_bind] at h
      cases mirror with
      | false =>
        exact band_write_ops b dst s b' h
      | true =>
        simp only [if_true] at h
        cases hsub : SudoRt.subI (SudoRt.listLen s) (1 : Int) with
        | error _ =>
          rw [hsub] at h
          simp only [error_bind] at h; cases h
        | ok toV =>
          rw [hsub] at h
          simp only [ok_bind] at h
          rw [except_bind_pure] at h
          apply runLoopOn_ok_inv
            (P := fun _ => True)
            (Q := fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
            (h := h)
          · exact trivial
          · exact fun _ _ _ _ => trivial
          · exact fun _ _ _ _ => trivial
          · intro σ r a _ hstep _
            exact absurd hstep (flip_step_no_ret toV σ r)
          · intro σ a _ ha
            exact band_write_ops b dst σ.2 a ha

private theorem settle_place_ops (b : Ecbs.Board) (b' : Ecbs.Board)
    (h : (do
        let _ ← Ecbs.need_empty b b.sudo_5Board_8bench_to
        let v ← Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n
        let n ← Ecbs.npeg v
        let m ← SudoRt.mulI (2 : Int) n
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m
        let sl ← SudoRt.addI
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
          m
        let home ← SudoRt.putL
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with
                  sudo_5Costs_5moves := mv
                  sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
          b.sudo_5Board_8bench_to v
        let held ← SudoRt.putL
          ({ b with
              sudo_5Board_4home := home
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with
                    sudo_5Costs_5moves := mv
                    sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
          b.sudo_5Board_8bench_to true
        let b ← Ecbs.note_peak
          ({ b with
              sudo_5Board_4home := home
              sudo_5Board_4held := held
              sudo_5Board_8bench_on := false
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with
                    sudo_5Costs_5moves := mv
                    sudo_5Costs_6slides := sl } } : Ecbs.Board)
        pure b) = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  cases he : Ecbs.need_empty b b.sudo_5Board_8bench_to with
  | error _ =>
    rw [he] at h; simp only [error_bind] at h; cases h
  | ok _ =>
    rw [he] at h; simp only [ok_bind] at h
    cases hv : Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n with
    | error _ =>
      rw [hv] at h; simp only [error_bind] at h; cases h
    | ok v =>
      rw [hv] at h; simp only [ok_bind] at h
      cases hn : Ecbs.npeg v with
      | error _ =>
        rw [hn] at h; simp only [error_bind] at h; cases h
      | ok n =>
        rw [hn] at h; simp only [ok_bind] at h
        cases hm : SudoRt.mulI (2 : Int) n with
        | error _ =>
          rw [hm] at h; simp only [error_bind] at h; cases h
        | ok m =>
          rw [hm] at h; simp only [ok_bind] at h
          cases hmv : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m with
          | error _ =>
            rw [hmv] at h; simp only [error_bind] at h; cases h
          | ok mv =>
            rw [hmv] at h; simp only [ok_bind] at h
            cases hsl : SudoRt.addI
                ({ b with sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
                m with
            | error _ =>
              rw [hsl] at h; simp only [error_bind] at h; cases h
            | ok sl =>
              rw [hsl] at h; simp only [ok_bind] at h
              cases hh : SudoRt.putL
                  ({ b with sudo_5Board_4cost :=
                      { b.sudo_5Board_4cost with
                          sudo_5Costs_5moves := mv
                          sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
                  b.sudo_5Board_8bench_to v with
              | error _ =>
                rw [hh] at h; simp only [error_bind] at h; cases h
              | ok home =>
                rw [hh] at h; simp only [ok_bind] at h
                cases hd : SudoRt.putL
                    ({ b with
                        sudo_5Board_4home := home
                        sudo_5Board_4cost :=
                          { b.sudo_5Board_4cost with
                              sudo_5Costs_5moves := mv
                              sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
                    b.sudo_5Board_8bench_to true with
                | error _ =>
                  rw [hd] at h; simp only [error_bind] at h; cases h
                | ok held =>
                  rw [hd] at h; simp only [ok_bind] at h
                  cases hk : Ecbs.note_peak
                      ({ b with
                          sudo_5Board_4home := home
                          sudo_5Board_4held := held
                          sudo_5Board_8bench_on := false
                          sudo_5Board_4cost :=
                            { b.sudo_5Board_4cost with
                                sudo_5Costs_5moves := mv
                                sudo_5Costs_6slides := sl } } : Ecbs.Board) with
                  | error _ =>
                    rw [hk] at h; simp only [error_bind] at h; cases h
                  | ok _ =>
                    rw [hk] at h; simp only [ok_bind, pure_eq_ok] at h
                    cases h
                    exact (note_peak_ops _ b' hk).trans rfl

/-- `settle` writes homes, the held flag, the counters, and the bench flag. -/
theorem settle_board_ops (b b' : Ecbs.Board) (h : Ecbs.settle b = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.settle at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_8bench_on = true
  · rw [hon] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hsub : SudoRt.subI (SudoRt.listLen b.sudo_5Board_5bench) (1 : Int) with
    | error _ =>
      rw [hsub] at h; simp only [error_bind] at h; cases h
    | ok toV =>
      rw [hsub] at h; simp only [ok_bind] at h
      rw [except_bind_pure] at h
      conv at h =>
        pattern (fun i : Int => _)
        change settleIdx b toV
      have hsplit := runLoopOn_ok_after b.sudo_5Board_1t.sudo_4Tier_1n
        (if b.sudo_5Board_1t.sudo_4Tier_1n > toV then 1
          else (toV - b.sudo_5Board_1t.sudo_4Tier_1n).natAbs + 1)
        (settleIdx b toV)
        (fun _ =>
          (do
            let _ ← Ecbs.need_empty b b.sudo_5Board_8bench_to
            let v ← Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n
            let n ← Ecbs.npeg v
            let m ← SudoRt.mulI (2 : Int) n
            let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m
            let sl ← SudoRt.addI
              ({ b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
              m
            let home ← SudoRt.putL
              ({ b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with
                      sudo_5Costs_5moves := mv
                      sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
              b.sudo_5Board_8bench_to v
            let held ← SudoRt.putL
              ({ b with
                  sudo_5Board_4home := home
                  sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with
                        sudo_5Costs_5moves := mv
                        sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
              b.sudo_5Board_8bench_to true
            let b ← Ecbs.note_peak
              ({ b with
                  sudo_5Board_4home := home
                  sudo_5Board_4held := held
                  sudo_5Board_8bench_on := false
                  sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with
                        sudo_5Costs_5moves := mv
                        sudo_5Costs_6slides := sl } } : Ecbs.Board)
            pure b))
        (fun r => pure r) b' h
      cases hsplit with
      | inr hret =>
        obtain ⟨r, _, i, hi⟩ := hret
        exact absurd hi (settleIdx_no_ret b toV i r)
      | inl hex =>
        obtain ⟨_, ha⟩ := hex
        dsimp only at ha
        exact settle_place_ops b b' ha
  · have hoff : b.sudo_5Board_8bench_on = false := eq_false_of_ne_true hon
    rw [hoff] at h
    simp only [Bool.not_false, if_true] at h
    rw [pure_eq_ok] at h
    cases h
    rfl

private theorem clear_held_tail_ops (b : Ecbs.Board) (home : Int) (b' : Ecbs.Board)
    (h : (do
        let held ← SudoRt.atL b.sudo_5Board_4held home
        let _ ← SudoRt.sudoAssert held 477
        let arr ← SudoRt.atL b.sudo_5Board_4home home
        let n ← Ecbs.npeg arr
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        let heldA ← SudoRt.putL b.sudo_5Board_4held home false
        let b := ({ b with sudo_5Board_4held := heldA } : Ecbs.Board)
        let homeA ← SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int)
        pure ({ b with sudo_5Board_4home := homeA } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  dsimp only at h
  cases hh : SudoRt.atL b.sudo_5Board_4held home with
  | error _ =>
    rw [hh] at h
    simp only [error_bind] at h
    cases h
  | ok held =>
    rw [hh] at h
    simp only [ok_bind] at h
    cases ha : SudoRt.sudoAssert held 477 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h
      cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.atL b.sudo_5Board_4home home with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h
        cases h
      | ok arr =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases hn : Ecbs.npeg arr with
        | error _ =>
          rw [hn] at h
          simp only [error_bind] at h
          cases h
        | ok n =>
          rw [hn] at h
          simp only [ok_bind] at h
          cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
          | error _ =>
            rw [hm] at h
            simp only [error_bind] at h
            cases h
          | ok mv =>
            rw [hm] at h
            simp only [ok_bind] at h
            cases hd : SudoRt.putL
                ({ b with sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4held
                home false with
            | error _ =>
              rw [hd] at h
              simp only [error_bind] at h
              cases h
            | ok heldA =>
              rw [hd] at h
              simp only [ok_bind] at h
              cases hp : SudoRt.putL
                  ({ { b with sudo_5Board_4cost :=
                        { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } with
                      sudo_5Board_4held := heldA } : Ecbs.Board).sudo_5Board_4home
                  home (#[] : Array Int) with
              | error _ =>
                rw [hp] at h
                simp only [error_bind] at h
                cases h
              | ok _ =>
                rw [hp] at h
                simp only [ok_bind, pure_eq_ok] at h
                cases h
                rfl

private theorem clear_from_assert_ops (b : Ecbs.Board) (home : Int) (held : Bool) (b' : Ecbs.Board)
    (h : (do
        let _ ← SudoRt.sudoAssert held 477
        let arr ← SudoRt.atL b.sudo_5Board_4home home
        let n ← Ecbs.npeg arr
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let heldA ← SudoRt.putL b.sudo_5Board_4held home false
        let homeA ← SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int)
        pure ({ b with
          sudo_5Board_4home := homeA
          sudo_5Board_4held := heldA
          sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  cases ha : SudoRt.sudoAssert held 477 with
  | error _ =>
    rw [ha] at h
    simp only [error_bind] at h
    cases h
  | ok _ =>
    rw [ha] at h
    simp only [ok_bind] at h
    cases hv : SudoRt.atL b.sudo_5Board_4home home with
    | error _ =>
      rw [hv] at h
      simp only [error_bind] at h
      cases h
    | ok arr =>
      rw [hv] at h
      simp only [ok_bind] at h
      cases hn : Ecbs.npeg arr with
      | error _ =>
        rw [hn] at h
        simp only [error_bind] at h
        cases h
      | ok n =>
        rw [hn] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h
          cases h
        | ok mv =>
          rw [hm] at h
          simp only [ok_bind] at h
          cases hd : SudoRt.putL b.sudo_5Board_4held home false with
          | error _ =>
            rw [hd] at h
            simp only [error_bind] at h
            cases h
          | ok heldA =>
            rw [hd] at h
            simp only [ok_bind] at h
            cases hp : SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int) with
            | error _ =>
              rw [hp] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hp] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl

/-- `Ecbs.clear` writes a home, the held flag, the move counter, or the bench
    flag. The ops array is none of those. -/
theorem clear_ops (b : Ecbs.Board) (home : Int) (b' : Ecbs.Board)
    (h : Ecbs.clear b home = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.clear at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_8bench_on = true
  · rw [if_pos hon, pure_eq_ok, ok_bind] at h
    by_cases hto : SudoRt.SEq.beq b.sudo_5Board_8bench_to home = true
    · rw [if_pos hto] at h
      cases hh : SudoRt.atL b.sudo_5Board_4held home with
      | error _ =>
        rw [hh] at h
        simp only [error_bind] at h
        cases h
      | ok held =>
        rw [hh] at h
        simp only [ok_bind, pure_eq_ok, ok_bind] at h
        by_cases hem : (!held) = true
        · rw [if_pos hem] at h
          cases hn : Ecbs.npeg b.sudo_5Board_5bench with
          | error _ =>
            rw [hn] at h
            simp only [error_bind] at h
            cases h
          | ok n =>
            rw [hn] at h
            simp only [ok_bind] at h
            cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
            | error _ =>
              rw [hm] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hm] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl
        · rw [if_neg hem] at h
          exact clear_from_assert_ops b home held b' h
    · rw [if_neg hto, pure_eq_ok, ok_bind] at h
      simp only [Bool.false_eq_true, if_false, pure_eq_ok, ok_bind] at h
      exact clear_held_tail_ops b home b' h
  · rw [if_neg hon] at h
    simp only [pure_eq_ok, ok_bind, Bool.false_eq_true, if_false] at h
    exact clear_held_tail_ops b home b' h

private theorem fold_peak_ops (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : (do
        let folded ← Ecbs.lane_fold b strip
        let ⟨b1, strip1⟩ := folded
        let b := ({ b1 with sudo_5Board_5bench := strip1 } : Ecbs.Board)
        let out ← Ecbs.note_peak b
        pure out) = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
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
        exact (note_peak_ops _ b' hk).trans
          ((by rfl : ({ bF with sudo_5Board_5bench := stripF } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_3ops
              = bF.sudo_5Board_4cost.sudo_5Costs_3ops).trans
            (lane_fold_ops b strip bF stripF hf))

theorem schoolFinish_ops (n : Int) (a s : Array Int) (mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.schoolFinish n a s mirror b strip = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.schoolFinish at h
  dsimp only at h
  cases hsub : SudoRt.subI n (1 : Int) with
  | error _ =>
    rw [hsub] at h; simp only [error_bind] at h; cases h
  | ok fromV =>
    rw [hsub] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    refine row_loop_ops a s mirror n (0 : Int) fromV _ b strip _ _ ?hafter ?hret b' h
    · intro st q hs hq
      exact (fold_peak_ops st.2.1 st.2.2 q hq).trans hs
    · intro r q hr hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact hr

theorem mulFromSrc_ops (n fst src : Int) (a : Array Int) (mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.mulFromSrc n fst src a mirror b strip = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
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
      have hN := note_strict_ops b bN hst
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
                exact (schoolFinish_ops n a s mirror bC strip b' h).trans hN

theorem mulFromHeld_ops (n fst second : Int) (copySecond mirror : Bool)
    (b : Ecbs.Board) (strip : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.mulFromHeld n fst second copySecond mirror b strip = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
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
              exact (mulFromSrc_ops n fst Ecbs.spare a mirror bC strip b' h).trans
                (copy_band_ops Ecbs.spare second false b bC hcopy)
        · rw [if_neg hc] at h
          exact mulFromSrc_ops n fst second a mirror b strip b' h

theorem mulElse_ops
    (n dst first second : Int) (copySecond onto mirror : Bool)
    (b0 b' : Ecbs.Board)
    (h : Ecbs.mulElse n dst first second copySecond onto mirror b0 = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b0.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.mulElse at h
  dsimp only at h
  cases hset : Ecbs.settle b0 with
  | error _ =>
    rw [hset] at h; simp only [error_bind] at h; cases h
  | ok bS =>
    rw [hset] at h; simp only [ok_bind] at h
    have hS := settle_board_ops b0 bS hset
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
                              exact (mulFromHeld_ops n first second copySecond mirror _ s.2 b' hs).trans hS
                            | inr hex =>
                              rcases hex with ⟨rb, _, s0, hstep⟩
                              exact absurd hstep (bandCopyStep_no_ret r toV s0 rb)
      · simp only [if_neg hon] at h
        exact (mulFromHeld_ops n first second copySecond mirror _ strip b' h).trans hS

/-- A successful `atL` at index 0 puts that index in range. -/
private theorem atL_zero_lt {α : Type} (a : Array α) (v : α)
    (h : SudoRt.atL a (Int.ofNat 0) = .ok v) : 0 < a.size := by
  unfold SudoRt.atL SudoRt.idxCheck at h
  by_cases hout :
      (decide ((Int.ofNat 0) < 0) || decide ((Int.ofNat 0) ≥ Int.ofNat a.size)) = true
  · rw [if_pos hout] at h
    unfold SudoRt.fail at h
    simp only [error_bind] at h
    cases h
  · have hfalse :
        (decide ((Int.ofNat 0) < 0) || decide ((Int.ofNat 0) ≥ Int.ofNat a.size)) = false :=
      eq_false_of_ne_true hout
    have hz : decide ((Int.ofNat 0) < 0) = false :=
      decide_eq_false (fun hlt => Int.lt_irrefl (Int.ofNat 0) hlt)
    rw [hz, Bool.false_or] at hfalse
    have hge : ¬ ((Int.ofNat 0) ≥ Int.ofNat a.size) := of_decide_eq_false hfalse
    have hsz : ¬ a.size ≤ 0 := by
      intro hs
      exact hge (Int.ofNat_le.mpr hs)
    cases hn : a.size with
    | zero =>
      rw [hn] at hsz
      exact False.elim (hsz (Nat.le_refl 0))
    | succ n =>
      exact Nat.succ_pos n

/-- Slot 0 is the only ops cell `Ecbs.mul` writes. -/
theorem mul_ops_other
    (b0 : Ecbs.Board) (dst first second : Int) (copySecond onto mirror : Bool)
    (b' : Ecbs.Board)
    (h : Ecbs.mul b0 dst first second copySecond onto mirror = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b0.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ j, j ≠ 0 →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[j]? =
          b0.sudo_5Board_4cost.sudo_5Costs_3ops[j]?) := by
  rw [mul_keep_eq] at h
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
        have hPut0 :
            SudoRt.putL b0.sudo_5Board_4cost.sudo_5Costs_3ops (Int.ofNat 0) c1 =
              .ok ops := by
          rw [show Ecbs.op_mul = Int.ofNat 0 from rfl] at hput
          exact hput
        have hLt : 0 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          have hop0 :
              SudoRt.atL b0.sudo_5Board_4cost.sudo_5Costs_3ops (Int.ofNat 0) =
                .ok c0 := by
            rw [show Ecbs.op_mul = Int.ofNat 0 from rfl] at hop
            exact hop
          exact atL_zero_lt _ _ hop0
        let bOps : Ecbs.Board :=
          { b0 with sudo_5Board_4cost :=
              { b0.sudo_5Board_4cost with sudo_5Costs_3ops := ops } }
        cases hlog : Ecbs.log_op bOps with
        | error _ =>
          rw [hlog] at h; simp only [error_bind] at h; cases h
        | ok bL =>
          rw [hlog] at h; simp only [ok_bind] at h
          have hLL := log_op_ops bOps bL hlog
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
                    have hEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops = ops :=
                      (mulFromHeld_ops n first second copySecond mirror bL
                        bL.sudo_5Board_5bench b' h).trans hLL
                    rw [putL_ofNat _ 0 c1 hLt] at hPut0
                    cases hPut0
                    refine ⟨?_, ?_⟩
                    · rw [hEq, Array.size_set]
                    · intro j hj
                      rw [hEq, Array.getElem?_set_ne _ _ _ hj.symm]
                  · rw [if_neg hfree] at h
                    have hEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops = ops :=
                      (mulElse_ops n dst first second copySecond onto mirror bL b' h).trans hLL
                    rw [putL_ofNat _ 0 c1 hLt] at hPut0
                    cases hPut0
                    refine ⟨?_, ?_⟩
                    · rw [hEq, Array.size_set]
                    · intro j hj
                      rw [hEq, Array.getElem?_set_ne _ _ _ hj.symm]
              · rw [if_neg hto, pure_eq_ok, ok_bind] at h
                rw [if_neg Bool.false_ne_true] at h
                have hEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops = ops :=
                  (mulElse_ops n dst first second copySecond onto mirror bL b' h).trans hLL
                rw [putL_ofNat _ 0 c1 hLt] at hPut0
                cases hPut0
                refine ⟨?_, ?_⟩
                · rw [hEq, Array.size_set]
                · intro j hj
                  rw [hEq, Array.getElem?_set_ne _ _ _ hj.symm]
            · rw [if_neg hbench, pure_eq_ok, ok_bind] at h
              rw [if_neg Bool.false_ne_true, ok_bind] at h
              rw [if_neg Bool.false_ne_true] at h
              have hEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops = ops :=
                (mulElse_ops n dst first second copySecond onto mirror bL b' h).trans hLL
              rw [putL_ofNat _ 0 c1 hLt] at hPut0
              cases hPut0
              refine ⟨?_, ?_⟩
              · rw [hEq, Array.size_set]
              · intro j hj
                rw [hEq, Array.getElem?_set_ne _ _ _ hj.symm]
          · rw [if_neg hon, pure_eq_ok, ok_bind] at h
            rw [if_neg Bool.false_ne_true, ok_bind] at h
            rw [if_neg Bool.false_ne_true, ok_bind] at h
            rw [if_neg Bool.false_ne_true] at h
            have hEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops = ops :=
              (mulElse_ops n dst first second copySecond onto mirror bL b' h).trans hLL
            rw [putL_ofNat _ 0 c1 hLt] at hPut0
            cases hPut0
            refine ⟨?_, ?_⟩
            · rw [hEq, Array.size_set]
            · intro j hj
              rw [hEq, Array.getElem?_set_ne _ _ _ hj.symm]

end EcbsLink2.Link2
