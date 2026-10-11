-- DO NOT EDIT. Generated from bs.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for bs.sudo
import SudoRt
import Bs
set_option linter.unusedVariables false
open Bs

def test_b1_drop_examples_carry_like_an_odometer : Except SudoRt.Trap Unit :=
  do
    let s := (#[(2 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _io1 ← drop s (0 : Int) (1 : Int)
    let s := _io1
    let _as2 ← SudoRt.sudoAssertEq s (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 746
    let s := (#[(1 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _io3 ← drop s (0 : Int) (2 : Int)
    let s := _io3
    let _as4 ← SudoRt.sudoAssertEq s (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 749
    let s := (#[(2 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _io5 ← drop s (0 : Int) (2 : Int)
    let s := _io5
    let _as6 ← SudoRt.sudoAssertEq s (#[(1 : Int), (1 : Int), (0 : Int)] : Array (Int)) 752
    let s := (#[(2 : Int), (2 : Int), (2 : Int), (0 : Int)] : Array (Int))
    let _io7 ← drop s (0 : Int) (1 : Int)
    let s := _io7
    let _as8 ← SudoRt.sudoAssertEq s (#[(0 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 755
    pure ()

def test_b1_a_carry_past_the_strip_s_last_hole_fails_drop_s_final_assert : Except SudoRt.Trap Unit :=
  do
    let s := (#[(2 : Int), (2 : Int)] : Array (Int))
    let _ex10 := (do
  let _io9 ← drop s (0 : Int) (1 : Int)
  let s := _io9
  pure ()
  pure ())
    match _ex10 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 759: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 759: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_b4_pay_toll_rejects_a_toll_of_n_or_more_trits : Except SudoRt.Trap Unit :=
  do
    let _t11 ← SudoRt.filledL (6 : Int) (0 : Int)
    let s := _t11
    let _ix12 := (5 : Int)
    let _t13 ← SudoRt.putL s _ix12 (1 : Int)
    let s := _t13
    let _ex15 := (do
  let _io14 ← pay_toll ({ sudo_5Field_1n := (3 : Int), sudo_5Field_4toll := (#[(1 : Int), (0 : Int), (1 : Int)] : Array (Int)) } : Field) s
  let s := _io14
  pure ()
  pure ())
    match _ex15 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 765: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 765: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4 : Except SudoRt.Trap Unit :=
  do
    let _t16 ← SudoRt.filledL (36 : Int) (0 : Int)
    let s := _t16
    let _ix17 := (20 : Int)
    let _t18 ← SudoRt.putL s _ix17 (1 : Int)
    let s := _t18
    let _io19 ← pay_toll t1 s
    let s := _io19
    let _t20 ← SudoRt.filledL (36 : Int) (0 : Int)
    let expected := _t20
    let _ix21 := (2 : Int)
    let _t22 ← SudoRt.putL expected _ix21 (1 : Int)
    let expected := _t22
    let _ix23 := (4 : Int)
    let _t24 ← SudoRt.putL expected _ix23 (1 : Int)
    let expected := _t24
    let _as25 ← SudoRt.sudoAssertEq s expected 775
    pure ()

def test_b3_one_times_x_is_x_and_x_times_one_is_x : Except SudoRt.Trap Unit :=
  do
    let _t26 ← empty_register t1
    let one := _t26
    let _ix27 := (0 : Int)
    let _t28 ← SudoRt.putL one _ix27 (1 : Int)
    let one := _t28
    let x := (#[(2 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let _t29 ← multiply t1 one x (0 : Int)
    let _as30 ← SudoRt.sudoAssertEq _t29 x 781
    let _t31 ← multiply t1 x one (0 : Int)
    let _as32 ← SudoRt.sudoAssertEq _t31 x 782
    pure ()

def test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow : Except SudoRt.Trap Unit :=
  do
    let _t33 ← SudoRt.filledL (18 : Int) (2 : Int)
    let red := _t33
    let _t34 ← multiply t1 red red (2 : Int)
    let _as35 ← SudoRt.sudoAssertEq _t34 (#[(0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) 786
    let _t36 ← SudoRt.filledL (35 : Int) (2 : Int)
    let red2 := _t36
    let _t37 ← multiply t2 red2 red2 (2 : Int)
    let _as39 ← SudoRt.sudoAssertEq (SudoRt.listLen _t37) (35 : Int) 788
    pure ()

def test_b5_p_tidies_to_the_empty_register_in_t1_and_t2 : Except SudoRt.Trap Unit :=
  do
    let _t40 ← SudoRt.filledL (18 : Int) (2 : Int)
    let p1 := _t40
    let _ix41 := (2 : Int)
    let _t42 ← SudoRt.putL p1 _ix41 (1 : Int)
    let p1 := _t42
    let _t43 ← tidy t1 p1
    let _t44 ← empty_register t1
    let _as45 ← SudoRt.sudoAssertEq _t43 _t44 793
    let _t46 ← SudoRt.filledL (35 : Int) (2 : Int)
    let p2 := _t46
    let _ix47 := (29 : Int)
    let _t48 ← SudoRt.putL p2 _ix47 (1 : Int)
    let p2 := _t48
    let _t49 ← tidy t2 p2
    let _t50 ← empty_register t2
    let _as51 ← SudoRt.sudoAssertEq _t49 _t50 796
    let _t52 ← SudoRt.filledL (18 : Int) (2 : Int)
    let below := _t52
    let _ix53 := (2 : Int)
    let _t54 ← SudoRt.putL below _ix53 (0 : Int)
    let below := _t54
    let _t55 ← tidy t1 below
    let _as56 ← SudoRt.sudoAssertEq _t55 below 799
    pure ()

def test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length : Except SudoRt.Trap Unit :=
  do
    let _t57 ← empty_register t1
    let zero := _t57
    let _t58 ← empty_register t1
    let one := _t58
    let _ix59 := (0 : Int)
    let _t60 ← SudoRt.putL one _ix59 (1 : Int)
    let one := _t60
    let _t61 ← SudoRt.filledL (18 : Int) (2 : Int)
    let pminus1 := _t61
    let _ix62 := (0 : Int)
    let _t63 ← SudoRt.putL pminus1 _ix62 (1 : Int)
    let pminus1 := _t63
    let _ix64 := (2 : Int)
    let _t65 ← SudoRt.putL pminus1 _ix64 (1 : Int)
    let pminus1 := _t65
    let _t66 ← SudoRt.filledL (18 : Int) (2 : Int)
    let pplus1 := _t66
    let _ix67 := (0 : Int)
    let _t68 ← SudoRt.putL pplus1 _ix67 (0 : Int)
    let pplus1 := _t68
    let _ix69 := (1 : Int)
    let _t70 ← SudoRt.putL pplus1 _ix69 (0 : Int)
    let pplus1 := _t70
    let _ix71 := (2 : Int)
    let _t72 ← SudoRt.putL pplus1 _ix71 (2 : Int)
    let pplus1 := _t72
    let _t73 ← check_received t1 zero
    let _as75 ← SudoRt.sudoAssert (SudoRt.optIsNone _t73) 812
    let _t76 ← check_received t1 one
    let _as78 ← SudoRt.sudoAssert (SudoRt.optIsNone _t76) 813
    let _t79 ← check_received t1 pminus1
    let _as81 ← SudoRt.sudoAssert (SudoRt.optIsNone _t79) 814
    let _t82 ← check_received t1 pplus1
    let _as84 ← SudoRt.sudoAssert (SudoRt.optIsNone _t82) 815
    let _t85 ← SudoRt.filledL (17 : Int) (1 : Int)
    let _t86 ← check_received t1 _t85
    let _as88 ← SudoRt.sudoAssert (SudoRt.optIsNone _t86) 816
    let _t89 ← SudoRt.filledL (18 : Int) (3 : Int)
    let _t90 ← check_received t1 _t89
    let _as92 ← SudoRt.sudoAssert (SudoRt.optIsNone _t90) 817
    pure ()

def test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all : Except SudoRt.Trap Unit :=
  do
    let x := (#[(2 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _t93 ← SudoRt.filledL (18 : Int) (2 : Int)
    let y := _t93
    let _io94 ← call_the_shots t1 x y
    let ⟨_ret95, _iw096⟩ := _io94
    let y := _iw096
    let shots := _ret95
    let _as97 ← SudoRt.sudoAssertEq y x 823
    let _as99 ← SudoRt.sudoAssertEq (SudoRt.listLen shots) (18 : Int) 824
    let _t100 ← SudoRt.atL shots (0 : Int)
    let _as101 ← SudoRt.sudoAssertEq _t100 Shot.Sudo_4Shot_3Hit 825
    let _t102 ← SudoRt.atL shots (1 : Int)
    let _as103 ← SudoRt.sudoAssertEq _t102 Shot.Sudo_4Shot_4Miss 826
    let _t104 ← SudoRt.atL shots (2 : Int)
    let _as105 ← SudoRt.sudoAssertEq _t104 Shot.Sudo_4Shot_7Misfire 827
    let _fromV := (5 : Int)
    let _toV := (17 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init109 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init109 fuel (fun σ =>
    let hole := σ
    do
      if hole > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) hole)
      else
        match ← ((do
  let _t107 ← SudoRt.atL shots hole
  let _as108 ← SudoRt.sudoAssertEq _t107 Shot.Sudo_4Shot_7Misfire 829
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) hole)
        | .cont _fs => do
            if hole == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) hole)
            else do
              let i' ← SudoRt.addI hole (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_3_1_clear_y_the_public_walk_leaves_x_x_x_in_y_and_the_call_clears_it_first : Except SudoRt.Trap Unit :=
  do
    let _t110 ← empty_register t1
    let y := _t110
    let _io111 ← public_walk t1 (#[sample_grid_a] : Array (KeyGrid)) y
    let ⟨_ret112, _iw0113⟩ := _io111
    let y := _iw0113
    let a := _ret112
    let _t114 ← is_empty y
    let _as115 ← SudoRt.sudoAssert (!( _t114 )) 834
    let _io116 ← call_the_shots t1 a y
    let ⟨_ret117, _iw0118⟩ := _io116
    let y := _iw0118
    let shots := _ret117
    let _as119 ← SudoRt.sudoAssertEq y a 836
    let _as121 ← SudoRt.sudoAssertEq (SudoRt.listLen shots) (18 : Int) 837
    pure ()

def test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged : Except SudoRt.Trap Unit :=
  do
    let _t122 ← empty_register t1
    let y := _t122
    let _io123 ← public_walk t1 (#[sample_grid_a] : Array (KeyGrid)) y
    let ⟨_ret124, _iw0125⟩ := _io123
    let y := _iw0125
    let a := _ret124
    let _as126 ← SudoRt.sudoAssertEq y (#[(0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int)] : Array (Int)) 846
    let _t127 ← empty_register t1
    let y := _t127
    let _io128 ← public_walk t1 (#[sample_grid_b] : Array (KeyGrid)) y
    let ⟨_ret129, _iw0130⟩ := _io128
    let y := _iw0130
    let b := _ret129
    let _as131 ← SudoRt.sudoAssertEq b (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 849
    let _as132 ← SudoRt.sudoAssertEq y (#[(2 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) 850
    pure ()

def test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in : Except SudoRt.Trap Unit :=
  do
    let r := (#[(2 : Int), (1 : Int), (2 : Int)] : Array (Int))
    let _io133 ← slide r (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int))
    let r := _io133
    let _as134 ← SudoRt.sudoAssertEq r (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 855
    pure ()

def test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in : Except SudoRt.Trap Unit :=
  do
    let x0 := (#[(2 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let x := x0
    let _t135 ← SudoRt.filledL (18 : Int) (2 : Int)
    let y := _t135
    let _io136 ← cube t1 x (0 : Int) y
    let ⟨_iw0137, _iw1138⟩ := _io136
    let x := _iw0137
    let y := _iw1138
    let _t139 ← multiply t1 x0 x0 (0 : Int)
    let _as140 ← SudoRt.sudoAssertEq y _t139 862
    let _t141 ← multiply t1 x0 x0 (0 : Int)
    let _t142 ← multiply t1 _t141 x0 (0 : Int)
    let _as143 ← SudoRt.sudoAssertEq x _t142 863
    pure ()

def test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register : Except SudoRt.Trap Unit :=
  do
    let _t144 ← SudoRt.filledL (18 : Int) (2 : Int)
    let x := _t144
    let _ix145 := (0 : Int)
    let _t146 ← SudoRt.putL x _ix145 (0 : Int)
    let x := _t146
    let _ix147 := (1 : Int)
    let _t148 ← SudoRt.putL x _ix147 (0 : Int)
    let x := _t148
    let _t149 ← empty_register t1
    let one := _t149
    let _ix150 := (0 : Int)
    let _t151 ← SudoRt.putL one _ix150 (1 : Int)
    let one := _t151
    let _io152 ← tidy_in_place t1 x
    let x := _io152
    let _as153 ← SudoRt.sudoAssertEq x one 874
    let _t154 ← SudoRt.filledL (18 : Int) (2 : Int)
    let below := _t154
    let _ix155 := (2 : Int)
    let _t156 ← SudoRt.putL below _ix155 (0 : Int)
    let below := _t156
    let x := below
    let _io157 ← tidy_in_place t1 x
    let x := _io157
    let _as158 ← SudoRt.sudoAssertEq x below 880
    pure ()

def test_3_1_an_empty_register_is_eighteen_misfires : Except SudoRt.Trap Unit :=
  do
    let _t159 ← empty_register t1
    let _t160 ← send_public_value t1 _t159
    let sent := _t160
    let _t161 ← empty_register t1
    let _as162 ← SudoRt.sudoAssertEq (sent).sudo_6Called_1y _t161 884
    let _t163 ← SudoRt.filledL (18 : Int) Shot.Sudo_4Shot_7Misfire
    let _as164 ← SudoRt.sudoAssertEq (sent).sudo_6Called_5shots _t163 885
    pure ()

def test_4_3_read_start_marker_ship_pass_peg_pass : Except SudoRt.Trap Unit :=
  do
    let _t165 ← read_key (#[sample_grid_a] : Array (KeyGrid))
    let cells := _t165
    let _t167 ← SudoRt.addI (1 : Int) (102 : Int)
    let _t168 ← SudoRt.addI _t167 (100 : Int)
    let _as169 ← SudoRt.sudoAssertEq (SudoRt.listLen cells) _t168 889
    let _t170 ← SudoRt.atL cells (0 : Int)
    let _as171 ← SudoRt.sudoAssertEq _t170 (1 : Int) 890
    let ships := (#[(1 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int)] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (101 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init183 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init183 fuel (fun σ =>
    let j := σ
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) j)
      else
        match ← ((do
  let _t173 ← SudoRt.addI (1 : Int) j
  let _t174 ← SudoRt.atL cells _t173
  let _t175 ← SudoRt.atL ships j
  let _as176 ← SudoRt.sudoAssertEq _t174 _t175 898
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) j)
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) j)
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _fromV := (0 : Int)
      let _toV := (99 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init182 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init182 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t178 ← SudoRt.addI (103 : Int) h
  let _t179 ← SudoRt.atL cells _t178
  let _t180 ← SudoRt.atL (sample_grid_a).sudo_7KeyGrid_4pegs h
  let _as181 ← SudoRt.sudoAssertEq _t179 _t180 900
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) h)
        | .cont _fs => do
            if h == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) h)
            else do
              let i' ← SudoRt.addI h (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_4_3_read_rejects_overlapping_ships : Except SudoRt.Trap Unit :=
  do
    let _t184 ← SudoRt.filledL (100 : Int) (0 : Int)
    let g := ({ sudo_7KeyGrid_5ships := (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship), ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (1 : Int), sudo_4Ship_8bow_last := false } : Ship)] : Array (Ship)), sudo_7KeyGrid_4pegs := _t184 } : KeyGrid)
    let _ex187 := (do
  let _t185 ← read_key (#[g] : Array (KeyGrid))
  let _u186 := _t185
  pure ()
  pure ())
    match _ex187 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 905: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 905: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_b9_t1_exchange_with_the_sample_grids : Except SudoRt.Trap Unit :=
  do
    let _t188 ← exchange t1 (#[sample_grid_a] : Array (KeyGrid)) (#[sample_grid_b] : Array (KeyGrid))
    let r := _t188
    let _as190 ← SudoRt.sudoAssert (SudoRt.resIsOk r) 910
    let _t191 ← SudoRt.resUnwrap r
    let e := _t191
    let _as192 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8public_a (#[(0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)] : Array (Int)) 912
    let _as193 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8public_b (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 913
    let _as194 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_10received_a (e).sudo_8Exchange_8public_a 914
    let _as195 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_10received_b (e).sudo_8Exchange_8public_b 915
    let _as196 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8secret_a (#[(0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)] : Array (Int)) 916
    let _as197 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8secret_b (e).sudo_8Exchange_8secret_a 917
    pure ()

def test_4_2_keypad_row_for_the_first_hole_column_for_the_second : Except SudoRt.Trap Unit :=
  do
    let _t200 ← keypad_first (6 : Int)
    let _t202 ← (if (SudoRt.SEq.beq _t200 (1 : Int)) then (do
  let _t203 ← keypad_second (6 : Int)
  pure (SudoRt.SEq.beq _t203 (2 : Int))) else pure false)
    let _as205 ← SudoRt.sudoAssert _t202 920
    let firsts := (#[] : Array (Int))
    let seconds := (#[] : Array (Int))
    let _fromV := (1 : Int)
    let _toV := (9 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init219 := (_fromV, (firsts, seconds))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init219 fuel (fun σ =>
    let face := σ.1
    let firsts := σ.2.1
    let _sp217 := σ.2.2
    let seconds := _sp217
    do
      if face > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (face, (firsts, seconds)))
      else
        match ← ((do
  let _t207 ← keypad_first face
  let _mb208 := SudoRt.appendL firsts _t207
  let ⟨_nr209, _⟩ := _mb208
  let firsts := _nr209
  let _hm198 := ()
  let _u210 := _hm198
  let _t211 ← keypad_second face
  let _mb212 := SudoRt.appendL seconds _t211
  let ⟨_nr213, _⟩ := _mb212
  let seconds := _nr213
  let _hm199 := ()
  let _u214 := _hm199
  pure (SudoRt.Flow.cont (ρ := Unit) (firsts, seconds))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (face, _fs))
        | .cont _fs => do
            if face == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (face, _fs))
            else do
              let i' ← SudoRt.addI face (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let firsts := σ.2.1
    let _sp218 := σ.2.2
    let seconds := _sp218
    do
      let _as215 ← SudoRt.sudoAssertEq firsts (#[(0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) 926
      let _as216 ← SudoRt.sudoAssertEq seconds (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int)] : Array (Int)) 927
      pure ()) (fun r => pure r))
    pure _out

def test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face : Except SudoRt.Trap Unit :=
  do
    let _t220 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[(0 : Int), (0 : Int), (6 : Int), (3 : Int)] : Array (Int))
    let d := _t220
    let _io221 ← throw_d10 d
    let ⟨_ret222, _iw0223⟩ := _io221
    let d := _iw0223
    let _sudo_h0 := _ret222
    let _as224 ← SudoRt.sudoAssertEq _sudo_h0 (6 : Int) 931
    let _as225 ← SudoRt.sudoAssertEq (d).sudo_4Dice_6next10 (3 : Int) 932
    let _io226 ← throw_d10 d
    let ⟨_ret227, _iw0228⟩ := _io226
    let d := _iw0228
    let _sudo_h1 := _ret227
    let _as229 ← SudoRt.sudoAssertEq _sudo_h1 (3 : Int) 933
    pure ()

def test_4_2_running_out_of_d10_faces_before_a_non_zero_one_fails_throw_d10_s_assert : Except SudoRt.Trap Unit :=
  do
    let _t230 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[(0 : Int), (0 : Int)] : Array (Int))
    let d := _t230
    let _ex234 := (do
  let _io231 ← throw_d10 d
  let ⟨_ret232, _iw0233⟩ := _io231
  let d := _iw0233
  pure ()
  pure ())
    match _ex234 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 937: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 937: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again : Except SudoRt.Trap Unit :=
  do
    let _t235 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[(4 : Int), (0 : Int), (7 : Int), (1 : Int), (0 : Int), (0 : Int), (9 : Int), (2 : Int)] : Array (Int))
    let d := _t235
    let _io236 ← throw_row_cup d
    let ⟨_ret237, _iw0238⟩ := _io236
    let d := _iw0238
    let _sudo_h0 := _ret237
    let _as239 ← SudoRt.sudoAssertEq _sudo_h0 (#[(4 : Int), (7 : Int), (1 : Int), (9 : Int), (2 : Int)] : Array (Int)) 942
    let _as240 ← SudoRt.sudoAssertEq (d).sudo_4Dice_6next10 (8 : Int) 943
    pure ()

def test_4_2_grow_until_it_bumps : Except SudoRt.Trap Unit :=
  do
    let _t241 ← SudoRt.filledL (100 : Int) false
    let «open» := _t241
    let _t242 ← dice (#[(5 : Int)] : Array (Int)) (#[(4 : Int), (6 : Int), (6 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t242
    let _io243 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret244, _iw0245⟩ := _io243
    let d := _iw0245
    let _sudo_h0 := _ret244
    let _as246 ← SudoRt.sudoAssertEq _sudo_h0 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Carrier, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 949
    let _t248 ← (if (SudoRt.SEq.beq (d).sudo_4Dice_6next12 (1 : Int)) then (do
  pure (SudoRt.SEq.beq (d).sudo_4Dice_5next6 (3 : Int))) else pure false)
    let _as250 ← SudoRt.sudoAssert _t248 950
    let _t251 ← dice (#[(10 : Int)] : Array (Int)) (#[(3 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t251
    let _io252 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret253, _iw0254⟩ := _io252
    let d := _iw0254
    let _sudo_h1 := _ret253
    let _as255 ← SudoRt.sudoAssertEq _sudo_h1 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship)) 953
    let _t256 ← dice (#[(9 : Int)] : Array (Int)) (#[(5 : Int), (2 : Int), (3 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t256
    let _io257 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret258, _iw0259⟩ := _io257
    let d := _iw0259
    let _sudo_h2 := _ret258
    let _as260 ← SudoRt.sudoAssertEq _sudo_h2 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_3Sub, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 956
    let _t261 ← dice (#[(4 : Int)] : Array (Int)) (#[] : Array (Int)) (#[] : Array (Int))
    let d := _t261
    let _io262 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret263, _iw0264⟩ := _io262
    let d := _iw0264
    let _sudo_h3 := _ret263
    let _as265 ← SudoRt.sudoAssertEq _sudo_h3 (none : Option (Ship)) 959
    let _t266 ← dice (#[(7 : Int), (8 : Int)] : Array (Int)) (#[(4 : Int), (6 : Int), (6 : Int), (1 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t266
    let _io267 ← grow_until_it_bumps d «open» (9 : Int) (0 : Int)
    let ⟨_ret268, _iw0269⟩ := _io267
    let d := _iw0269
    let _sudo_h4 := _ret268
    let _as270 ← SudoRt.sudoAssertEq _sudo_h4 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Carrier, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 963
    let _io271 ← grow_until_it_bumps d «open» (9 : Int) (5 : Int)
    let ⟨_ret272, _iw0273⟩ := _io271
    let d := _iw0273
    let _sudo_h5 := _ret272
    let _as274 ← SudoRt.sudoAssertEq _sudo_h5 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (5 : Int), sudo_4Ship_8bow_last := true } : Ship)) 964
    let _t275 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[] : Array (Int))
    let d := _t275
    let _io276 ← grow_until_it_bumps d «open» (9 : Int) (9 : Int)
    let ⟨_ret277, _iw0278⟩ := _io276
    let d := _iw0278
    let _sudo_h6 := _ret277
    let _as279 ← SudoRt.sudoAssertEq _sudo_h6 (none : Option (Ship)) 968
    let _t280 ← dice (#[(7 : Int)] : Array (Int)) (#[(4 : Int), (4 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t280
    let _io281 ← grow_until_it_bumps d «open» (9 : Int) (7 : Int)
    let ⟨_ret282, _iw0283⟩ := _io281
    let d := _iw0283
    let _sudo_h7 := _ret282
    let _as284 ← SudoRt.sudoAssertEq _sudo_h7 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Cruiser, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (7 : Int), sudo_4Ship_8bow_last := false } : Ship)) 970
    let _as285 ← SudoRt.sudoAssertEq (d).sudo_4Dice_5next6 (2 : Int) 971
    pure ()

def test_4_2_build_all_sea_and_all_white_pegs : Except SudoRt.Trap Unit :=
  do
    let _t286 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t287 ← SudoRt.filledL (50 : Int) (5 : Int)
    let _t288 ← dice _t286 (#[] : Array (Int)) _t287
    let _t289 ← build_key_grid _t288
    let built := _t289
    let _as291 ← SudoRt.sudoAssertEq (SudoRt.listLen ((built).sudo_5Built_4grid).sudo_7KeyGrid_5ships) (0 : Int) 975
    let _t292 ← SudoRt.filledL (100 : Int) (1 : Int)
    let _as293 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs _t292 976
    let _t295 ← (if (SudoRt.SEq.beq (built).sudo_5Built_6used12 (99 : Int)) then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_5used6 (0 : Int))) else pure false)
    let _t297 ← (if _t295 then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_6used10 (50 : Int))) else pure false)
    let _as299 ← SudoRt.sudoAssert _t297 977
    let _t300 ← read_key (#[(built).sudo_5Built_4grid] : Array (KeyGrid))
    let _as302 ← SudoRt.sudoAssertEq (SudoRt.listLen _t300) (201 : Int) 978
    pure ()

def test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs : Except SudoRt.Trap Unit :=
  do
    let _t303 ← SudoRt.filledL (96 : Int) (1 : Int)
    let _t305 ← SudoRt.filledL (48 : Int) (5 : Int)
    let _t307 ← dice (SudoRt.concatL (#[(1 : Int), (5 : Int)] : Array (Int)) _t303) (#[(1 : Int)] : Array (Int)) (SudoRt.concatL (#[(6 : Int), (2 : Int)] : Array (Int)) _t305)
    let _t308 ← build_key_grid _t307
    let built := _t308
    let _as309 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_5ships (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (1 : Int), sudo_4Ship_8bow_last := false } : Ship)] : Array (Ship)) 987
    let _t310 ← SudoRt.filledL (90 : Int) (1 : Int)
    let _as312 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (SudoRt.concatL (#[(1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)] : Array (Int)) _t310) 988
    let _t314 ← (if (SudoRt.SEq.beq (built).sudo_5Built_6used12 (98 : Int)) then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_5used6 (1 : Int))) else pure false)
    let _t316 ← (if _t314 then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_6used10 (50 : Int))) else pure false)
    let _as318 ← SudoRt.sudoAssert _t316 989
    let _t319 ← read_key (#[(built).sudo_5Built_4grid] : Array (KeyGrid))
    let cells := _t319
    let _t320 ← SudoRt.atL cells (1 : Int)
    let _t322 ← (if (SudoRt.SEq.beq _t320 (0 : Int)) then (do
  let _t323 ← SudoRt.atL cells (2 : Int)
  pure (SudoRt.SEq.beq _t323 (1 : Int))) else pure false)
    let _t325 ← (if _t322 then (do
  let _t326 ← SudoRt.atL cells (3 : Int)
  pure (SudoRt.SEq.beq _t326 (1 : Int))) else pure false)
    let _t328 ← (if _t325 then (do
  let _t329 ← SudoRt.atL cells (4 : Int)
  pure (SudoRt.SEq.beq _t329 (0 : Int))) else pure false)
    let _as331 ← SudoRt.sudoAssert _t328 991
    pure ()

def test_b8_squares_into_c_and_tidies_c : Except SudoRt.Trap Unit :=
  do
    let _t332 ← empty_register t1
    let three := _t332
    let _ix333 := (1 : Int)
    let _t334 ← SudoRt.putL three _ix333 (1 : Int)
    let three := _t334
    let _t335 ← empty_register t1
    let nine := _t335
    let _ix336 := (2 : Int)
    let _t337 ← SudoRt.putL nine _ix336 (1 : Int)
    let nine := _t337
    let _t338 ← check_received t1 three
    let _as339 ← SudoRt.sudoAssertEq _t338 (some nine) 999
    pure ()

def test_trace_twins_drop_lay_pay_toll_multiply_and_tidy_record_what_they_change : Except SudoRt.Trap Unit :=
  do
    let moves := (#[] : Array (PegMove))
    let s := (#[(2 : Int), (2 : Int), (0 : Int)] : Array (Int))
    let _io340 ← trace_drop s (0 : Int) (1 : Int) moves
    let ⟨_iw0341, _iw1342⟩ := _io340
    let s := _iw0341
    let moves := _iw1342
    let _as343 ← SudoRt.sudoAssertEq s (#[(0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 1818
    let _as344 ← SudoRt.sudoAssertEq moves (#[({ sudo_7PegMove_3reg := Reg.Sudo_3Reg_5Strip, sudo_7PegMove_4hole := (0 : Int), sudo_7PegMove_4from := (2 : Int), sudo_7PegMove_4into := (0 : Int), sudo_7PegMove_3why := Why.Sudo_3Why_4Drop } : PegMove), ({ sudo_7PegMove_3reg := Reg.Sudo_3Reg_5Strip, sudo_7PegMove_4hole := (1 : Int), sudo_7PegMove_4from := (2 : Int), sudo_7PegMove_4into := (0 : Int), sudo_7PegMove_3why := Why.Sudo_3Why_5Carry } : PegMove), ({ sudo_7PegMove_3reg := Reg.Sudo_3Reg_5Strip, sudo_7PegMove_4hole := (2 : Int), sudo_7PegMove_4from := (0 : Int), sudo_7PegMove_4into := (1 : Int), sudo_7PegMove_3why := Why.Sudo_3Why_5Carry } : PegMove)] : Array (PegMove)) 1819
    let _t345 ← SudoRt.filledL (t1).sudo_5Field_1n (2 : Int)
    let red := _t345
    let m := (#[] : Array (PegMove))
    let _io346 ← trace_multiply t1 red red (2 : Int) m
    let ⟨_ret347, _iw0348⟩ := _io346
    let m := _iw0348
    let _sudo_h0 := _ret347
    let _t349 ← multiply t1 red red (2 : Int)
    let _as350 ← SudoRt.sudoAssertEq _sudo_h0 _t349 1822
    let _t351 ← empty_register t1
    let x := _t351
    let _ix352 := (0 : Int)
    let _t353 ← SudoRt.putL x _ix352 (1 : Int)
    let x := _t353
    let _ix354 := (1 : Int)
    let _t355 ← SudoRt.putL x _ix354 (1 : Int)
    let x := _t355
    let m := (#[] : Array (PegMove))
    let _io356 ← trace_multiply t1 x x (0 : Int) m
    let ⟨_ret357, _iw0358⟩ := _io356
    let m := _iw0358
    let _sudo_h1 := _ret357
    let _t359 ← multiply t1 x x (0 : Int)
    let _as360 ← SudoRt.sudoAssertEq _sudo_h1 _t359 1827
    let _t361 ← SudoRt.filledL (t1).sudo_5Field_1n (2 : Int)
    let p := _t361
    let _ix362 := (2 : Int)
    let _t363 ← SudoRt.putL p _ix362 (1 : Int)
    let p := _t363
    let _t364 ← tidy t1 p
    let want := _t364
    let m := (#[] : Array (PegMove))
    let _io365 ← trace_tidy t1 Reg.Sudo_3Reg_1X p m
    let ⟨_iw0366, _iw1367⟩ := _io365
    let p := _iw0366
    let m := _iw1367
    let _as368 ← SudoRt.sudoAssertEq p want 1834
    let _t369 ← is_empty p
    let _as370 ← SudoRt.sudoAssert _t369 1835
    let _t372 ← SudoRt.subI (SudoRt.listLen m) (1 : Int)
    let _t373 ← SudoRt.atL m _t372
    let _as374 ← SudoRt.sudoAssertEq (_t373).sudo_7PegMove_3why Why.Sudo_3Why_4Lift 1836
    pure ()

def test_trace_build_build_hole_by_hole_gives_build_key_grid_s_grid_its_dice_and_its_moves : Except SudoRt.Trap Unit :=
  do
    let _t375 ← SudoRt.filledL (96 : Int) (1 : Int)
    let _t377 ← SudoRt.filledL (48 : Int) (5 : Int)
    let _t379 ← dice (SudoRt.concatL (#[(1 : Int), (5 : Int)] : Array (Int)) _t375) (#[(1 : Int)] : Array (Int)) (SudoRt.concatL (#[(6 : Int), (2 : Int)] : Array (Int)) _t377)
    let _t380 ← check_trace_build _t379
    let g := _t380
    let _as381 ← SudoRt.sudoAssertEq (g).sudo_7KeyGrid_5ships (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (1 : Int), sudo_4Ship_8bow_last := false } : Ship)] : Array (Ship)) 1840
    let _t382 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t383 ← SudoRt.filledL (50 : Int) (5 : Int)
    let _t384 ← dice _t382 (#[] : Array (Int)) _t383
    let _t385 ← check_trace_build _t384
    let g := _t385
    let _as387 ← SudoRt.sudoAssertEq (SudoRt.listLen (g).sudo_7KeyGrid_5ships) (0 : Int) 1842
    let reads := (#[] : Array (BuildRead))
    let _t388 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t390 ← SudoRt.filledL (50 : Int) (5 : Int)
    let _t391 ← dice (SudoRt.concatL (#[(12 : Int)] : Array (Int)) _t388) (#[(5 : Int), (1 : Int), (6 : Int)] : Array (Int)) _t390
    let _io392 ← trace_build _t391 reads
    let ⟨_ret393, _iw0394⟩ := _io392
    let reads := _iw0394
    let g := _ret393
    let _t395 ← SudoRt.atL reads (0 : Int)
    let _t396 ← SudoRt.atL (_t395).sudo_9BuildRead_5moves (5 : Int)
    let _as397 ← SudoRt.sudoAssertEq _t396 (BuildMove.Sudo_9BuildMove_7HoleDie (12 : Int)) 1846
    let _t398 ← SudoRt.atL reads (0 : Int)
    let _t399 ← SudoRt.atL (_t398).sudo_9BuildRead_5moves (6 : Int)
    let _as400 ← SudoRt.sudoAssertEq _t399 (BuildMove.Sudo_9BuildMove_5Piece ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship) (#[(0 : Int), (10 : Int)] : Array (Int))) 1847
    let _t401 ← SudoRt.atL reads (0 : Int)
    let _t402 ← SudoRt.atL (_t401).sudo_9BuildRead_5moves (7 : Int)
    let _as403 ← SudoRt.sudoAssertEq _t402 (BuildMove.Sudo_9BuildMove_4Grow (5 : Int)) 1848
    let _t404 ← SudoRt.atL reads (0 : Int)
    let _t405 ← SudoRt.atL (_t404).sudo_9BuildRead_5moves (8 : Int)
    let _as406 ← SudoRt.sudoAssertEq _t405 (BuildMove.Sudo_9BuildMove_5Piece ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_3Sub, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship) (#[(0 : Int), (10 : Int), (20 : Int)] : Array (Int))) 1849
    let _t407 ← SudoRt.atL reads (0 : Int)
    let _t408 ← SudoRt.atL (_t407).sudo_9BuildRead_5moves (9 : Int)
    let _as409 ← SudoRt.sudoAssertEq _t408 (BuildMove.Sudo_9BuildMove_4Grow (1 : Int)) 1850
    let _t410 ← SudoRt.atL reads (0 : Int)
    let _t411 ← SudoRt.atL (_t410).sudo_9BuildRead_5moves (10 : Int)
    let _as412 ← SudoRt.sudoAssertEq _t411 (BuildMove.Sudo_9BuildMove_4Pick (6 : Int)) 1851
    let _t413 ← SudoRt.atL reads (0 : Int)
    let _t414 ← SudoRt.atL (_t413).sudo_9BuildRead_5moves (11 : Int)
    let _as415 ← SudoRt.sudoAssertEq _t414 (BuildMove.Sudo_9BuildMove_5Piece ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Cruiser, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship) (#[(0 : Int), (10 : Int), (20 : Int)] : Array (Int))) 1852
    let _t416 ← SudoRt.atL reads (0 : Int)
    let _as417 ← SudoRt.sudoAssertEq (_t416).sudo_9BuildRead_7covered (#[(0 : Int), (10 : Int), (20 : Int)] : Array (Int)) 1853
    let _as418 ← SudoRt.sudoAssertEq (g).sudo_7KeyGrid_5ships (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Cruiser, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship)] : Array (Ship)) 1854
    pure ()

def test_cell_holes_one_hole_per_cell_of_read_key_the_extra_cell_at_the_3_holer_s_last_hole : Except SudoRt.Trap Unit :=
  do
    let g := sample_grid_a
    let _t419 ← cell_holes g
    let holes := _t419
    let _t420 ← read_key (#[g] : Array (KeyGrid))
    let cells := _t420
    let _as423 ← SudoRt.sudoAssertEq (SudoRt.listLen holes) (SudoRt.listLen cells) 1860
    let _t424 ← SudoRt.atL holes (0 : Int)
    let _t425 ← SudoRt.negI (1 : Int)
    let _as426 ← SudoRt.sudoAssertEq _t424 _t425 1861
    let _t427 ← SudoRt.atL holes (1 : Int)
    let _t429 ← (if (SudoRt.SEq.beq _t427 (0 : Int)) then (do
  let _t430 ← SudoRt.atL holes (3 : Int)
  pure (SudoRt.SEq.beq _t430 (2 : Int))) else pure false)
    let _t432 ← (if _t429 then (do
  let _t433 ← SudoRt.atL holes (4 : Int)
  pure (SudoRt.SEq.beq _t433 (2 : Int))) else pure false)
    let _t435 ← (if _t432 then (do
  let _t436 ← SudoRt.atL holes (5 : Int)
  pure (SudoRt.SEq.beq _t436 (3 : Int))) else pure false)
    let _as438 ← SudoRt.sudoAssert _t435 1863
    let _t440 ← SudoRt.subI (SudoRt.listLen holes) (1 : Int)
    let _t441 ← SudoRt.atL holes _t440
    let _as442 ← SudoRt.sudoAssertEq _t441 (199 : Int) 1864
    let _t443 ← cell_holes sample_grid_b
    let _t445 ← read_key (#[sample_grid_b] : Array (KeyGrid))
    let _as447 ← SudoRt.sudoAssertEq (SudoRt.listLen _t443) (SudoRt.listLen _t445) 1865
    let _t457 ← SudoRt.subI (SudoRt.listLen cells) (1 : Int)
    let _fromV := (1 : Int)
    let _toV := _t457
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init564 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init564 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t449 ← SudoRt.atL holes i
  if (decide (_t449 ≥ (100 : Int))) then
    do
      let _t451 ← SudoRt.atL cells i
      let _t452 ← SudoRt.atL holes i
      let _t453 ← SudoRt.subI _t452 (100 : Int)
      let _t454 ← SudoRt.atL (g).sudo_7KeyGrid_4pegs _t453
      let _as455 ← SudoRt.sudoAssertEq _t451 _t454 1869
      pure (SudoRt.Flow.cont (ρ := Unit) ())
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) i)
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) i)
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _t458 ← SudoRt.negI (1 : Int)
      let _t459 ← SudoRt.filledL (100 : Int) _t458
      let «first» := _t459
      let _t460 ← SudoRt.negI (1 : Int)
      let _t461 ← SudoRt.filledL (100 : Int) _t460
      let last := _t461
      let _t462 ← SudoRt.negI (1 : Int)
      let _t463 ← SudoRt.filledL (100 : Int) _t462
      let extra := _t463
      let _t534 ← SudoRt.subI (SudoRt.listLen (g).sudo_7KeyGrid_5ships) (1 : Int)
      let _fromV := (0 : Int)
      let _toV := _t534
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init563 := (_fromV, («first», last, extra))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init563 fuel (fun σ =>
    let k := σ.1
    let «first» := σ.2.1
    let _sp559 := σ.2.2
    let last := _sp559.1
    let _sp560 := _sp559.2
    let extra := _sp560
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, («first», last, extra)))
      else
        match ← ((do
  let _t465 ← SudoRt.atL (g).sudo_7KeyGrid_5ships k
  let s := _t465
  let _t466 ← ship_holes s
  let under := _t466
  let _t467 ← SudoRt.atL under (0 : Int)
  let _ix468 := _t467
  let _t469 ← SudoRt.putL «first» _ix468 (1 : Int)
  let «first» := _t469
  if (s).sudo_4Ship_4down then
    do
      let _t470 ← SudoRt.atL under (0 : Int)
      let _ix471 := _t470
      let _t472 ← SudoRt.putL «first» _ix471 (2 : Int)
      let «first» := _t472
      let _t474 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
      let _t475 ← SudoRt.atL under _t474
      let _ix476 := _t475
      let _t477 ← SudoRt.putL last _ix476 (1 : Int)
      let last := _t477
      if (s).sudo_4Ship_8bow_last then
        do
          let _t479 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
          let _t480 ← SudoRt.atL under _t479
          let _ix481 := _t480
          let _t482 ← SudoRt.putL last _ix481 (2 : Int)
          let last := _t482
          match ((s).sudo_4Ship_4kind : Kind) with
          | .Sudo_4Kind_3Sub =>
            do
              let _t484 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
              let _t485 ← SudoRt.atL under _t484
              let _ix486 := _t485
              let _t487 ← SudoRt.putL extra _ix486 (0 : Int)
              let extra := _t487
              pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
          | _ =>
            do
              match ((s).sudo_4Ship_4kind : Kind) with
              | .Sudo_4Kind_7Cruiser =>
                do
                  let _t489 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
                  let _t490 ← SudoRt.atL under _t489
                  let _ix491 := _t490
                  let _t492 ← SudoRt.putL extra _ix491 (1 : Int)
                  let extra := _t492
                  pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
              | _ =>
                do
                  match ((s).sudo_4Ship_4kind : Kind) with
                  | _ =>
                    do
                      pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
      else
        do
          match ((s).sudo_4Ship_4kind : Kind) with
          | .Sudo_4Kind_3Sub =>
            do
              let _t494 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
              let _t495 ← SudoRt.atL under _t494
              let _ix496 := _t495
              let _t497 ← SudoRt.putL extra _ix496 (0 : Int)
              let extra := _t497
              pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
          | _ =>
            do
              match ((s).sudo_4Ship_4kind : Kind) with
              | .Sudo_4Kind_7Cruiser =>
                do
                  let _t499 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
                  let _t500 ← SudoRt.atL under _t499
                  let _ix501 := _t500
                  let _t502 ← SudoRt.putL extra _ix501 (1 : Int)
                  let extra := _t502
                  pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
              | _ =>
                do
                  match ((s).sudo_4Ship_4kind : Kind) with
                  | _ =>
                    do
                      pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
  else
    do
      let _t504 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
      let _t505 ← SudoRt.atL under _t504
      let _ix506 := _t505
      let _t507 ← SudoRt.putL last _ix506 (1 : Int)
      let last := _t507
      if (s).sudo_4Ship_8bow_last then
        do
          let _t509 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
          let _t510 ← SudoRt.atL under _t509
          let _ix511 := _t510
          let _t512 ← SudoRt.putL last _ix511 (2 : Int)
          let last := _t512
          match ((s).sudo_4Ship_4kind : Kind) with
          | .Sudo_4Kind_3Sub =>
            do
              let _t514 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
              let _t515 ← SudoRt.atL under _t514
              let _ix516 := _t515
              let _t517 ← SudoRt.putL extra _ix516 (0 : Int)
              let extra := _t517
              pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
          | _ =>
            do
              match ((s).sudo_4Ship_4kind : Kind) with
              | .Sudo_4Kind_7Cruiser =>
                do
                  let _t519 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
                  let _t520 ← SudoRt.atL under _t519
                  let _ix521 := _t520
                  let _t522 ← SudoRt.putL extra _ix521 (1 : Int)
                  let extra := _t522
                  pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
              | _ =>
                do
                  match ((s).sudo_4Ship_4kind : Kind) with
                  | _ =>
                    do
                      pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
      else
        do
          match ((s).sudo_4Ship_4kind : Kind) with
          | .Sudo_4Kind_3Sub =>
            do
              let _t524 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
              let _t525 ← SudoRt.atL under _t524
              let _ix526 := _t525
              let _t527 ← SudoRt.putL extra _ix526 (0 : Int)
              let extra := _t527
              pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
          | _ =>
            do
              match ((s).sudo_4Ship_4kind : Kind) with
              | .Sudo_4Kind_7Cruiser =>
                do
                  let _t529 ← SudoRt.subI (SudoRt.listLen under) (1 : Int)
                  let _t530 ← SudoRt.atL under _t529
                  let _ix531 := _t530
                  let _t532 ← SudoRt.putL extra _ix531 (1 : Int)
                  let extra := _t532
                  pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))
              | _ =>
                do
                  match ((s).sudo_4Ship_4kind : Kind) with
                  | _ =>
                    do
                      pure (SudoRt.Flow.cont (ρ := Unit) («first», last, extra))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let «first» := σ.2.1
    let _sp561 := σ.2.2
    let last := _sp561.1
    let _sp562 := _sp561.2
    let extra := _sp562
    do
      let _t557 ← SudoRt.subI (SudoRt.listLen cells) (1 : Int)
      let _fromV := (1 : Int)
      let _toV := _t557
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init558 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init558 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t536 ← SudoRt.atL holes i
  let h := _t536
  if (decide (h < (100 : Int))) then
    do
      let _t538 ← SudoRt.atL «first» h
      let _t543 ← SudoRt.atL last h
      if (decide (_t538 ≥ (0 : Int))) then
        do
          let _t540 ← SudoRt.atL cells i
          let _t541 ← SudoRt.atL «first» h
          let _as542 ← SudoRt.sudoAssertEq _t540 _t541 1896
          pure (SudoRt.Flow.cont (ρ := Unit) ())
      else
        do
          if (decide (_t543 ≥ (0 : Int))) then
            do
              let _t545 ← SudoRt.subI i (1 : Int)
              let _t546 ← SudoRt.atL holes _t545
              if (SudoRt.SEq.beq _t546 h) then
                do
                  let _t548 ← SudoRt.atL cells i
                  let _t549 ← SudoRt.atL extra h
                  let _as550 ← SudoRt.sudoAssertEq _t548 _t549 1899
                  pure (SudoRt.Flow.cont (ρ := Unit) ())
              else
                do
                  let _t551 ← SudoRt.atL cells i
                  let _t552 ← SudoRt.atL last h
                  let _as553 ← SudoRt.sudoAssertEq _t551 _t552 1901
                  pure (SudoRt.Flow.cont (ρ := Unit) ())
          else
            do
              let _t554 ← SudoRt.atL cells i
              let _as555 ← SudoRt.sudoAssertEq _t554 (0 : Int) 1903
              pure (SudoRt.Flow.cont (ρ := Unit) ())
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) i)
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) i)
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_trace_steps_matches_exchange_on_the_sample_grids_step_by_step : Except SudoRt.Trap Unit :=
  do
    let _t565 ← trace_steps t1 sample_grid_a sample_grid_b
    let steps := _t565
    let _t566 ← check_trace_steps t1 steps
    let _u567 := _t566
    let _t568 ← exchange t1 (#[sample_grid_a] : Array (KeyGrid)) (#[sample_grid_b] : Array (KeyGrid))
    let _t569 ← SudoRt.resUnwrap _t568
    let e := _t569
    let _t571 ← walk_end steps (0 : Int) (SudoRt.listLen steps)
    let _as572 ← SudoRt.sudoAssertEq _t571 (e).sudo_8Exchange_8secret_a 1909
    let _t574 ← walk_end steps (1 : Int) (SudoRt.listLen steps)
    let _as575 ← SudoRt.sudoAssertEq _t574 (e).sudo_8Exchange_8secret_b 1910
    pure ()

def test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t1_exchange_vectors : Except SudoRt.Trap Unit :=
  do
    let _t576 ← dice_exchange_t1_run0_a
    let _t577 ← dice_exchange_t1_run0_b
    let _t578 ← check_trace_exchange t1 _t576 _t577
    let _u579 := _t578
    let _t580 ← dice_exchange_t1_run3_a
    let _t581 ← dice_exchange_t1_run3_b
    let _t582 ← check_trace_exchange t1 _t580 _t581
    let _u583 := _t582
    pure ()

def test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t2_exchange_vector : Except SudoRt.Trap Unit :=
  do
    let _t584 ← dice_exchange_t2_run3_a
    let _t585 ← dice_exchange_t2_run3_b
    let _t586 ← check_trace_exchange t2 _t584 _t585
    let _u587 := _t586
    pure ()

def test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t6_exchange_vector : Except SudoRt.Trap Unit :=
  do
    let _t588 ← dice_exchange_t6_run0_a
    let _t589 ← dice_exchange_t6_run0_b
    let _t590 ← check_trace_exchange t6 _t588 _t589
    let _u591 := _t590
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_b1_drop_examples_carry_like_an_odometer", fun _ => test_b1_drop_examples_carry_like_an_odometer), ("test_b1_a_carry_past_the_strip_s_last_hole_fails_drop_s_final_assert", fun _ => test_b1_a_carry_past_the_strip_s_last_hole_fails_drop_s_final_assert), ("test_b4_pay_toll_rejects_a_toll_of_n_or_more_trits", fun _ => test_b4_pay_toll_rejects_a_toll_of_n_or_more_trits), ("test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4", fun _ => test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4), ("test_b3_one_times_x_is_x_and_x_times_one_is_x", fun _ => test_b3_one_times_x_is_x_and_x_times_one_is_x), ("test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow", fun _ => test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow), ("test_b5_p_tidies_to_the_empty_register_in_t1_and_t2", fun _ => test_b5_p_tidies_to_the_empty_register_in_t1_and_t2), ("test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length", fun _ => test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length), ("test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all", fun _ => test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all), ("test_3_1_clear_y_the_public_walk_leaves_x_x_x_in_y_and_the_call_clears_it_first", fun _ => test_3_1_clear_y_the_public_walk_leaves_x_x_x_in_y_and_the_call_clears_it_first), ("test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged", fun _ => test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged), ("test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in", fun _ => test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in), ("test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in", fun _ => test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in), ("test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register", fun _ => test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register), ("test_3_1_an_empty_register_is_eighteen_misfires", fun _ => test_3_1_an_empty_register_is_eighteen_misfires), ("test_4_3_read_start_marker_ship_pass_peg_pass", fun _ => test_4_3_read_start_marker_ship_pass_peg_pass), ("test_4_3_read_rejects_overlapping_ships", fun _ => test_4_3_read_rejects_overlapping_ships), ("test_b9_t1_exchange_with_the_sample_grids", fun _ => test_b9_t1_exchange_with_the_sample_grids), ("test_4_2_keypad_row_for_the_first_hole_column_for_the_second", fun _ => test_4_2_keypad_row_for_the_first_hole_column_for_the_second), ("test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face", fun _ => test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face), ("test_4_2_running_out_of_d10_faces_before_a_non_zero_one_fails_throw_d10_s_assert", fun _ => test_4_2_running_out_of_d10_faces_before_a_non_zero_one_fails_throw_d10_s_assert), ("test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again", fun _ => test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again), ("test_4_2_grow_until_it_bumps", fun _ => test_4_2_grow_until_it_bumps), ("test_4_2_build_all_sea_and_all_white_pegs", fun _ => test_4_2_build_all_sea_and_all_white_pegs), ("test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs", fun _ => test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs), ("test_b8_squares_into_c_and_tidies_c", fun _ => test_b8_squares_into_c_and_tidies_c), ("test_trace_twins_drop_lay_pay_toll_multiply_and_tidy_record_what_they_change", fun _ => test_trace_twins_drop_lay_pay_toll_multiply_and_tidy_record_what_they_change), ("test_trace_build_build_hole_by_hole_gives_build_key_grid_s_grid_its_dice_and_its_moves", fun _ => test_trace_build_build_hole_by_hole_gives_build_key_grid_s_grid_its_dice_and_its_moves), ("test_cell_holes_one_hole_per_cell_of_read_key_the_extra_cell_at_the_3_holer_s_last_hole", fun _ => test_cell_holes_one_hole_per_cell_of_read_key_the_extra_cell_at_the_3_holer_s_last_hole), ("test_trace_steps_matches_exchange_on_the_sample_grids_step_by_step", fun _ => test_trace_steps_matches_exchange_on_the_sample_grids_step_by_step), ("test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t1_exchange_vectors", fun _ => test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t1_exchange_vectors), ("test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t2_exchange_vector", fun _ => test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t2_exchange_vector), ("test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t6_exchange_vector", fun _ => test_trace_exchange_matches_build_key_grid_and_exchange_on_the_t6_exchange_vector)]
