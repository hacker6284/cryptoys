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
    let _as2 ← SudoRt.sudoAssertEq s (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 783
    let s := (#[(1 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _io3 ← drop s (0 : Int) (2 : Int)
    let s := _io3
    let _as4 ← SudoRt.sudoAssertEq s (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 786
    let s := (#[(2 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _io5 ← drop s (0 : Int) (2 : Int)
    let s := _io5
    let _as6 ← SudoRt.sudoAssertEq s (#[(1 : Int), (1 : Int), (0 : Int)] : Array (Int)) 789
    let s := (#[(2 : Int), (2 : Int), (2 : Int), (0 : Int)] : Array (Int))
    let _io7 ← drop s (0 : Int) (1 : Int)
    let s := _io7
    let _as8 ← SudoRt.sudoAssertEq s (#[(0 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 792
    pure ()

def test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4 : Except SudoRt.Trap Unit :=
  do
    let _t9 ← SudoRt.filledL (36 : Int) (0 : Int)
    let s := _t9
    let _ix10 := (20 : Int)
    let _t11 ← SudoRt.putL s _ix10 (1 : Int)
    let s := _t11
    let _io12 ← pay_toll t1 s
    let s := _io12
    let _t13 ← SudoRt.filledL (36 : Int) (0 : Int)
    let expected := _t13
    let _ix14 := (2 : Int)
    let _t15 ← SudoRt.putL expected _ix14 (1 : Int)
    let expected := _t15
    let _ix16 := (4 : Int)
    let _t17 ← SudoRt.putL expected _ix16 (1 : Int)
    let expected := _t17
    let _as18 ← SudoRt.sudoAssertEq s expected 801
    pure ()

def test_b3_one_times_x_is_x_and_x_times_one_is_x : Except SudoRt.Trap Unit :=
  do
    let _t19 ← empty_register t1
    let one := _t19
    let _ix20 := (0 : Int)
    let _t21 ← SudoRt.putL one _ix20 (1 : Int)
    let one := _t21
    let x := (#[(2 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let _t22 ← multiply t1 one x (0 : Int)
    let _as23 ← SudoRt.sudoAssertEq _t22 x 807
    let _t24 ← multiply t1 x one (0 : Int)
    let _as25 ← SudoRt.sudoAssertEq _t24 x 808
    pure ()

def test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow : Except SudoRt.Trap Unit :=
  do
    let _t26 ← SudoRt.filledL (18 : Int) (2 : Int)
    let red := _t26
    let _t27 ← multiply t1 red red (2 : Int)
    let _as28 ← SudoRt.sudoAssertEq _t27 (#[(0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) 812
    let _t29 ← SudoRt.filledL (35 : Int) (2 : Int)
    let red2 := _t29
    let _t30 ← multiply t2 red2 red2 (2 : Int)
    let _as32 ← SudoRt.sudoAssertEq (SudoRt.listLen _t30) (35 : Int) 814
    pure ()

def test_b5_p_tidies_to_the_empty_register_in_t1_and_t2 : Except SudoRt.Trap Unit :=
  do
    let _t33 ← SudoRt.filledL (18 : Int) (2 : Int)
    let p1 := _t33
    let _ix34 := (2 : Int)
    let _t35 ← SudoRt.putL p1 _ix34 (1 : Int)
    let p1 := _t35
    let _t36 ← tidy t1 p1
    let _t37 ← empty_register t1
    let _as38 ← SudoRt.sudoAssertEq _t36 _t37 819
    let _t39 ← SudoRt.filledL (35 : Int) (2 : Int)
    let p2 := _t39
    let _ix40 := (29 : Int)
    let _t41 ← SudoRt.putL p2 _ix40 (1 : Int)
    let p2 := _t41
    let _t42 ← tidy t2 p2
    let _t43 ← empty_register t2
    let _as44 ← SudoRt.sudoAssertEq _t42 _t43 822
    let _t45 ← SudoRt.filledL (18 : Int) (2 : Int)
    let below := _t45
    let _ix46 := (2 : Int)
    let _t47 ← SudoRt.putL below _ix46 (0 : Int)
    let below := _t47
    let _t48 ← tidy t1 below
    let _as49 ← SudoRt.sudoAssertEq _t48 below 825
    pure ()

def test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length : Except SudoRt.Trap Unit :=
  do
    let _t50 ← empty_register t1
    let zero := _t50
    let _t51 ← empty_register t1
    let one := _t51
    let _ix52 := (0 : Int)
    let _t53 ← SudoRt.putL one _ix52 (1 : Int)
    let one := _t53
    let _t54 ← SudoRt.filledL (18 : Int) (2 : Int)
    let pminus1 := _t54
    let _ix55 := (0 : Int)
    let _t56 ← SudoRt.putL pminus1 _ix55 (1 : Int)
    let pminus1 := _t56
    let _ix57 := (2 : Int)
    let _t58 ← SudoRt.putL pminus1 _ix57 (1 : Int)
    let pminus1 := _t58
    let _t59 ← SudoRt.filledL (18 : Int) (2 : Int)
    let pplus1 := _t59
    let _ix60 := (0 : Int)
    let _t61 ← SudoRt.putL pplus1 _ix60 (0 : Int)
    let pplus1 := _t61
    let _ix62 := (1 : Int)
    let _t63 ← SudoRt.putL pplus1 _ix62 (0 : Int)
    let pplus1 := _t63
    let _ix64 := (2 : Int)
    let _t65 ← SudoRt.putL pplus1 _ix64 (2 : Int)
    let pplus1 := _t65
    let _t66 ← check_received t1 zero
    let _as68 ← SudoRt.sudoAssert (SudoRt.optIsNone _t66) 838
    let _t69 ← check_received t1 one
    let _as71 ← SudoRt.sudoAssert (SudoRt.optIsNone _t69) 839
    let _t72 ← check_received t1 pminus1
    let _as74 ← SudoRt.sudoAssert (SudoRt.optIsNone _t72) 840
    let _t75 ← check_received t1 pplus1
    let _as77 ← SudoRt.sudoAssert (SudoRt.optIsNone _t75) 841
    let _t78 ← SudoRt.filledL (17 : Int) (1 : Int)
    let _t79 ← check_received t1 _t78
    let _as81 ← SudoRt.sudoAssert (SudoRt.optIsNone _t79) 842
    let _t82 ← SudoRt.filledL (18 : Int) (3 : Int)
    let _t83 ← check_received t1 _t82
    let _as85 ← SudoRt.sudoAssert (SudoRt.optIsNone _t83) 843
    pure ()

def test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all : Except SudoRt.Trap Unit :=
  do
    let x := (#[(2 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _t86 ← SudoRt.filledL (18 : Int) (2 : Int)
    let y := _t86
    let _io87 ← call_the_shots t1 x y
    let ⟨_ret88, _iw089⟩ := _io87
    let y := _iw089
    let shots := _ret88
    let _as90 ← SudoRt.sudoAssertEq y x 849
    let _as92 ← SudoRt.sudoAssertEq (SudoRt.listLen shots) (18 : Int) 850
    let _t93 ← SudoRt.atL shots (0 : Int)
    let _as94 ← SudoRt.sudoAssertEq _t93 Shot.Sudo_4Shot_3Hit 851
    let _t95 ← SudoRt.atL shots (1 : Int)
    let _as96 ← SudoRt.sudoAssertEq _t95 Shot.Sudo_4Shot_4Miss 852
    let _t97 ← SudoRt.atL shots (2 : Int)
    let _as98 ← SudoRt.sudoAssertEq _t97 Shot.Sudo_4Shot_7Misfire 853
    let _fromV := (5 : Int)
    let _toV := (17 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init102 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init102 fuel (fun σ =>
    let hole := σ
    do
      if hole > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) hole)
      else
        match ← ((do
  let _t100 ← SudoRt.atL shots hole
  let _as101 ← SudoRt.sudoAssertEq _t100 Shot.Sudo_4Shot_7Misfire 855
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
    let _t103 ← empty_register t1
    let y := _t103
    let _io104 ← public_walk t1 (#[sample_grid_a] : Array (KeyGrid)) y
    let ⟨_ret105, _iw0106⟩ := _io104
    let y := _iw0106
    let a := _ret105
    let _t107 ← is_empty y
    let _as108 ← SudoRt.sudoAssert (!( _t107 )) 860
    let _io109 ← call_the_shots t1 a y
    let ⟨_ret110, _iw0111⟩ := _io109
    let y := _iw0111
    let shots := _ret110
    let _as112 ← SudoRt.sudoAssertEq y a 862
    let _as114 ← SudoRt.sudoAssertEq (SudoRt.listLen shots) (18 : Int) 863
    pure ()

def test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged : Except SudoRt.Trap Unit :=
  do
    let _t115 ← empty_register t1
    let y := _t115
    let _io116 ← public_walk t1 (#[sample_grid_a] : Array (KeyGrid)) y
    let ⟨_ret117, _iw0118⟩ := _io116
    let y := _iw0118
    let a := _ret117
    let _as119 ← SudoRt.sudoAssertEq y (#[(0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int)] : Array (Int)) 872
    let _t120 ← empty_register t1
    let y := _t120
    let _io121 ← public_walk t1 (#[sample_grid_b] : Array (KeyGrid)) y
    let ⟨_ret122, _iw0123⟩ := _io121
    let y := _iw0123
    let b := _ret122
    let _as124 ← SudoRt.sudoAssertEq b (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 875
    let _as125 ← SudoRt.sudoAssertEq y (#[(2 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) 876
    pure ()

def test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in : Except SudoRt.Trap Unit :=
  do
    let r := (#[(2 : Int), (1 : Int), (2 : Int)] : Array (Int))
    let _io126 ← slide r (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int))
    let r := _io126
    let _as127 ← SudoRt.sudoAssertEq r (#[(0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 881
    pure ()

def test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in : Except SudoRt.Trap Unit :=
  do
    let x0 := (#[(2 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let x := x0
    let _t128 ← SudoRt.filledL (18 : Int) (2 : Int)
    let y := _t128
    let _io129 ← cube t1 x (0 : Int) y
    let ⟨_iw0130, _iw1131⟩ := _io129
    let x := _iw0130
    let y := _iw1131
    let _t132 ← multiply t1 x0 x0 (0 : Int)
    let _as133 ← SudoRt.sudoAssertEq y _t132 888
    let _t134 ← multiply t1 x0 x0 (0 : Int)
    let _t135 ← multiply t1 _t134 x0 (0 : Int)
    let _as136 ← SudoRt.sudoAssertEq x _t135 889
    pure ()

def test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register : Except SudoRt.Trap Unit :=
  do
    let _t137 ← SudoRt.filledL (18 : Int) (2 : Int)
    let x := _t137
    let _ix138 := (0 : Int)
    let _t139 ← SudoRt.putL x _ix138 (0 : Int)
    let x := _t139
    let _ix140 := (1 : Int)
    let _t141 ← SudoRt.putL x _ix140 (0 : Int)
    let x := _t141
    let _t142 ← empty_register t1
    let one := _t142
    let _ix143 := (0 : Int)
    let _t144 ← SudoRt.putL one _ix143 (1 : Int)
    let one := _t144
    let _io145 ← tidy_in_place t1 x
    let x := _io145
    let _as146 ← SudoRt.sudoAssertEq x one 900
    let _t147 ← SudoRt.filledL (18 : Int) (2 : Int)
    let below := _t147
    let _ix148 := (2 : Int)
    let _t149 ← SudoRt.putL below _ix148 (0 : Int)
    let below := _t149
    let x := below
    let _io150 ← tidy_in_place t1 x
    let x := _io150
    let _as151 ← SudoRt.sudoAssertEq x below 906
    pure ()

def test_3_1_an_empty_register_is_eighteen_misfires : Except SudoRt.Trap Unit :=
  do
    let _t152 ← empty_register t1
    let _t153 ← send_public_value t1 _t152
    let sent := _t153
    let _t154 ← empty_register t1
    let _as155 ← SudoRt.sudoAssertEq (sent).sudo_6Called_1y _t154 910
    let _t156 ← SudoRt.filledL (18 : Int) Shot.Sudo_4Shot_7Misfire
    let _as157 ← SudoRt.sudoAssertEq (sent).sudo_6Called_5shots _t156 911
    pure ()

def test_4_3_read_start_marker_ship_pass_peg_pass : Except SudoRt.Trap Unit :=
  do
    let _t158 ← read_key (#[sample_grid_a] : Array (KeyGrid))
    let cells := _t158
    let _t160 ← SudoRt.addI (1 : Int) (102 : Int)
    let _t161 ← SudoRt.addI _t160 (100 : Int)
    let _as162 ← SudoRt.sudoAssertEq (SudoRt.listLen cells) _t161 915
    let _t163 ← SudoRt.atL cells (0 : Int)
    let _as164 ← SudoRt.sudoAssertEq _t163 (1 : Int) 916
    let ships := (#[(1 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int)] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (101 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init176 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init176 fuel (fun σ =>
    let j := σ
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) j)
      else
        match ← ((do
  let _t166 ← SudoRt.addI (1 : Int) j
  let _t167 ← SudoRt.atL cells _t166
  let _t168 ← SudoRt.atL ships j
  let _as169 ← SudoRt.sudoAssertEq _t167 _t168 924
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
      let _init175 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init175 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t171 ← SudoRt.addI (103 : Int) h
  let _t172 ← SudoRt.atL cells _t171
  let _t173 ← SudoRt.atL (sample_grid_a).sudo_7KeyGrid_4pegs h
  let _as174 ← SudoRt.sudoAssertEq _t172 _t173 926
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
    let _t177 ← SudoRt.filledL (100 : Int) (0 : Int)
    let g := ({ sudo_7KeyGrid_5ships := (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship), ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (1 : Int), sudo_4Ship_8bow_last := false } : Ship)] : Array (Ship)), sudo_7KeyGrid_4pegs := _t177 } : KeyGrid)
    let _ex180 := (do
  let _t178 ← read_key (#[g] : Array (KeyGrid))
  let _u179 := _t178
  pure ()
  pure ())
    match _ex180 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 931: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 931: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_b9_t1_exchange_with_the_sample_grids : Except SudoRt.Trap Unit :=
  do
    let _t181 ← exchange t1 (#[sample_grid_a] : Array (KeyGrid)) (#[sample_grid_b] : Array (KeyGrid))
    let r := _t181
    let _as183 ← SudoRt.sudoAssert (SudoRt.resIsOk r) 936
    let _t184 ← SudoRt.resUnwrap r
    let e := _t184
    let _as185 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8public_a (#[(0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)] : Array (Int)) 938
    let _as186 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8public_b (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)] : Array (Int)) 939
    let _as187 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_10received_a (e).sudo_8Exchange_8public_a 940
    let _as188 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_10received_b (e).sudo_8Exchange_8public_b 941
    let _as189 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8secret_a (#[(0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)] : Array (Int)) 942
    let _as190 ← SudoRt.sudoAssertEq (e).sudo_8Exchange_8secret_b (e).sudo_8Exchange_8secret_a 943
    pure ()

def test_4_2_keypad_row_for_the_first_hole_column_for_the_second : Except SudoRt.Trap Unit :=
  do
    let _t193 ← keypad_first (6 : Int)
    let _t195 ← (if (SudoRt.SEq.beq _t193 (1 : Int)) then (do
  let _t196 ← keypad_second (6 : Int)
  pure (SudoRt.SEq.beq _t196 (2 : Int))) else pure false)
    let _as198 ← SudoRt.sudoAssert _t195 946
    let firsts := (#[] : Array (Int))
    let seconds := (#[] : Array (Int))
    let _fromV := (1 : Int)
    let _toV := (9 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init212 := (_fromV, (firsts, seconds))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init212 fuel (fun σ =>
    let face := σ.1
    let firsts := σ.2.1
    let _sp210 := σ.2.2
    let seconds := _sp210
    do
      if face > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (face, (firsts, seconds)))
      else
        match ← ((do
  let _t200 ← keypad_first face
  let _mb201 := SudoRt.appendL firsts _t200
  let ⟨_nr202, _⟩ := _mb201
  let firsts := _nr202
  let _hm191 := ()
  let _u203 := _hm191
  let _t204 ← keypad_second face
  let _mb205 := SudoRt.appendL seconds _t204
  let ⟨_nr206, _⟩ := _mb205
  let seconds := _nr206
  let _hm192 := ()
  let _u207 := _hm192
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
    let _sp211 := σ.2.2
    let seconds := _sp211
    do
      let _as208 ← SudoRt.sudoAssertEq firsts (#[(0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) 952
      let _as209 ← SudoRt.sudoAssertEq seconds (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int)] : Array (Int)) 953
      pure ()) (fun r => pure r))
    pure _out

def test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face : Except SudoRt.Trap Unit :=
  do
    let _t213 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[(0 : Int), (0 : Int), (6 : Int), (3 : Int)] : Array (Int))
    let d := _t213
    let _io214 ← throw_d10 d
    let ⟨_ret215, _iw0216⟩ := _io214
    let d := _iw0216
    let _sudo_h0 := _ret215
    let _as217 ← SudoRt.sudoAssertEq _sudo_h0 (6 : Int) 957
    let _as218 ← SudoRt.sudoAssertEq (d).sudo_4Dice_6next10 (3 : Int) 958
    let _io219 ← throw_d10 d
    let ⟨_ret220, _iw0221⟩ := _io219
    let d := _iw0221
    let _sudo_h1 := _ret220
    let _as222 ← SudoRt.sudoAssertEq _sudo_h1 (3 : Int) 959
    pure ()

def test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again : Except SudoRt.Trap Unit :=
  do
    let _t223 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[(4 : Int), (0 : Int), (7 : Int), (1 : Int), (0 : Int), (0 : Int), (9 : Int), (2 : Int)] : Array (Int))
    let d := _t223
    let _io224 ← throw_row_cup d
    let ⟨_ret225, _iw0226⟩ := _io224
    let d := _iw0226
    let _sudo_h0 := _ret225
    let _as227 ← SudoRt.sudoAssertEq _sudo_h0 (#[(4 : Int), (7 : Int), (1 : Int), (9 : Int), (2 : Int)] : Array (Int)) 963
    let _as228 ← SudoRt.sudoAssertEq (d).sudo_4Dice_6next10 (8 : Int) 964
    pure ()

def test_4_2_grow_until_it_bumps : Except SudoRt.Trap Unit :=
  do
    let _t229 ← SudoRt.filledL (100 : Int) false
    let «open» := _t229
    let _t230 ← dice (#[(5 : Int)] : Array (Int)) (#[(4 : Int), (6 : Int), (6 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t230
    let _io231 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret232, _iw0233⟩ := _io231
    let d := _iw0233
    let _sudo_h0 := _ret232
    let _as234 ← SudoRt.sudoAssertEq _sudo_h0 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Carrier, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 970
    let _t236 ← (if (SudoRt.SEq.beq (d).sudo_4Dice_6next12 (1 : Int)) then (do
  pure (SudoRt.SEq.beq (d).sudo_4Dice_5next6 (3 : Int))) else pure false)
    let _as238 ← SudoRt.sudoAssert _t236 971
    let _t239 ← dice (#[(10 : Int)] : Array (Int)) (#[(3 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t239
    let _io240 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret241, _iw0242⟩ := _io240
    let d := _iw0242
    let _sudo_h1 := _ret241
    let _as243 ← SudoRt.sudoAssertEq _sudo_h1 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := true } : Ship)) 974
    let _t244 ← dice (#[(9 : Int)] : Array (Int)) (#[(5 : Int), (2 : Int), (3 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t244
    let _io245 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret246, _iw0247⟩ := _io245
    let d := _iw0247
    let _sudo_h2 := _ret246
    let _as248 ← SudoRt.sudoAssertEq _sudo_h2 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_3Sub, sudo_4Ship_4down := true, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 977
    let _t249 ← dice (#[(4 : Int)] : Array (Int)) (#[] : Array (Int)) (#[] : Array (Int))
    let d := _t249
    let _io250 ← grow_until_it_bumps d «open» (0 : Int) (0 : Int)
    let ⟨_ret251, _iw0252⟩ := _io250
    let d := _iw0252
    let _sudo_h3 := _ret251
    let _as253 ← SudoRt.sudoAssertEq _sudo_h3 (none : Option (Ship)) 980
    let _t254 ← dice (#[(7 : Int), (8 : Int)] : Array (Int)) (#[(4 : Int), (6 : Int), (6 : Int), (1 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t254
    let _io255 ← grow_until_it_bumps d «open» (9 : Int) (0 : Int)
    let ⟨_ret256, _iw0257⟩ := _io255
    let d := _iw0257
    let _sudo_h4 := _ret256
    let _as258 ← SudoRt.sudoAssertEq _sudo_h4 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Carrier, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (0 : Int), sudo_4Ship_8bow_last := false } : Ship)) 984
    let _io259 ← grow_until_it_bumps d «open» (9 : Int) (5 : Int)
    let ⟨_ret260, _iw0261⟩ := _io259
    let d := _iw0261
    let _sudo_h5 := _ret260
    let _as262 ← SudoRt.sudoAssertEq _sudo_h5 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (5 : Int), sudo_4Ship_8bow_last := true } : Ship)) 985
    let _t263 ← dice (#[] : Array (Int)) (#[] : Array (Int)) (#[] : Array (Int))
    let d := _t263
    let _io264 ← grow_until_it_bumps d «open» (9 : Int) (9 : Int)
    let ⟨_ret265, _iw0266⟩ := _io264
    let d := _iw0266
    let _sudo_h6 := _ret265
    let _as267 ← SudoRt.sudoAssertEq _sudo_h6 (none : Option (Ship)) 989
    let _t268 ← dice (#[(7 : Int)] : Array (Int)) (#[(4 : Int), (4 : Int)] : Array (Int)) (#[] : Array (Int))
    let d := _t268
    let _io269 ← grow_until_it_bumps d «open» (9 : Int) (7 : Int)
    let ⟨_ret270, _iw0271⟩ := _io269
    let d := _iw0271
    let _sudo_h7 := _ret270
    let _as272 ← SudoRt.sudoAssertEq _sudo_h7 (some ({ sudo_4Ship_4kind := Kind.Sudo_4Kind_7Cruiser, sudo_4Ship_4down := false, sudo_4Ship_3row := (9 : Int), sudo_4Ship_3col := (7 : Int), sudo_4Ship_8bow_last := false } : Ship)) 991
    let _as273 ← SudoRt.sudoAssertEq (d).sudo_4Dice_5next6 (2 : Int) 992
    pure ()

def test_4_2_build_all_sea_and_all_white_pegs : Except SudoRt.Trap Unit :=
  do
    let _t274 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t275 ← SudoRt.filledL (50 : Int) (5 : Int)
    let _t276 ← dice _t274 (#[] : Array (Int)) _t275
    let _t277 ← build_key_grid _t276
    let built := _t277
    let _as279 ← SudoRt.sudoAssertEq (SudoRt.listLen ((built).sudo_5Built_4grid).sudo_7KeyGrid_5ships) (0 : Int) 996
    let _t280 ← SudoRt.filledL (100 : Int) (1 : Int)
    let _as281 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs _t280 997
    let _t283 ← (if (SudoRt.SEq.beq (built).sudo_5Built_6used12 (99 : Int)) then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_5used6 (0 : Int))) else pure false)
    let _t285 ← (if _t283 then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_6used10 (50 : Int))) else pure false)
    let _as287 ← SudoRt.sudoAssert _t285 998
    let _t288 ← read_key (#[(built).sudo_5Built_4grid] : Array (KeyGrid))
    let _as290 ← SudoRt.sudoAssertEq (SudoRt.listLen _t288) (201 : Int) 999
    pure ()

def test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs : Except SudoRt.Trap Unit :=
  do
    let _t291 ← SudoRt.filledL (96 : Int) (1 : Int)
    let _t293 ← SudoRt.filledL (48 : Int) (5 : Int)
    let _t295 ← dice (SudoRt.concatL (#[(1 : Int), (5 : Int)] : Array (Int)) _t291) (#[(1 : Int)] : Array (Int)) (SudoRt.concatL (#[(6 : Int), (2 : Int)] : Array (Int)) _t293)
    let _t296 ← build_key_grid _t295
    let built := _t296
    let _as297 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_5ships (#[({ sudo_4Ship_4kind := Kind.Sudo_4Kind_9Destroyer, sudo_4Ship_4down := false, sudo_4Ship_3row := (0 : Int), sudo_4Ship_3col := (1 : Int), sudo_4Ship_8bow_last := false } : Ship)] : Array (Ship)) 1008
    let _t298 ← SudoRt.filledL (90 : Int) (1 : Int)
    let _as300 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (SudoRt.concatL (#[(1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)] : Array (Int)) _t298) 1009
    let _t302 ← (if (SudoRt.SEq.beq (built).sudo_5Built_6used12 (98 : Int)) then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_5used6 (1 : Int))) else pure false)
    let _t304 ← (if _t302 then (do
  pure (SudoRt.SEq.beq (built).sudo_5Built_6used10 (50 : Int))) else pure false)
    let _as306 ← SudoRt.sudoAssert _t304 1010
    let _t307 ← read_key (#[(built).sudo_5Built_4grid] : Array (KeyGrid))
    let cells := _t307
    let _t308 ← SudoRt.atL cells (1 : Int)
    let _t310 ← (if (SudoRt.SEq.beq _t308 (0 : Int)) then (do
  let _t311 ← SudoRt.atL cells (2 : Int)
  pure (SudoRt.SEq.beq _t311 (1 : Int))) else pure false)
    let _t313 ← (if _t310 then (do
  let _t314 ← SudoRt.atL cells (3 : Int)
  pure (SudoRt.SEq.beq _t314 (1 : Int))) else pure false)
    let _t316 ← (if _t313 then (do
  let _t317 ← SudoRt.atL cells (4 : Int)
  pure (SudoRt.SEq.beq _t317 (0 : Int))) else pure false)
    let _as319 ← SudoRt.sudoAssert _t316 1012
    pure ()

def test_4_2_build_letting_go_throws_the_unread_tray_dice_again : Except SudoRt.Trap Unit :=
  do
    let _t321 ← SudoRt.filledL (45 : Int) (5 : Int)
    let faces := (SudoRt.concatL (SudoRt.concatL (#[(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : Array (Int)) (#[(9 : Int), (8 : Int), (7 : Int)] : Array (Int))) _t321)
    let _t323 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t324 ← dice _t323 (#[] : Array (Int)) faces
    let _t325 ← build_letting_go _t324 (#[({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo)] : Array (LetGo))
    let built := _t325
    let _t326 ← SudoRt.filledL (90 : Int) (1 : Int)
    let _as328 ← SudoRt.sudoAssertEq ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (SudoRt.concatL (#[(0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int)] : Array (Int)) _t326) 1019
    let _as329 ← SudoRt.sudoAssertEq (built).sudo_5Built_6used10 (53 : Int) 1020
    let _t330 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t331 ← dice _t330 (#[] : Array (Int)) faces
    let _t332 ← build_key_grid _t331
    let plain := _t332
    let _t333 ← SudoRt.atL ((plain).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (4 : Int)
    let _as334 ← SudoRt.sudoAssertEq _t333 (0 : Int) 1023
    let _as335 ← SudoRt.sudoAssertEq (plain).sudo_5Built_6used10 (50 : Int) 1024
    let _t336 ← SudoRt.filledL (5 : Int) (5 : Int)
    let _t339 ← SudoRt.filledL (40 : Int) (5 : Int)
    let faces := (SudoRt.concatL (SudoRt.concatL (SudoRt.concatL _t336 (#[(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : Array (Int))) (#[(0 : Int), (6 : Int), (6 : Int), (6 : Int), (6 : Int)] : Array (Int))) _t339)
    let _t341 ← SudoRt.filledL (99 : Int) (1 : Int)
    let _t342 ← dice _t341 (#[] : Array (Int)) faces
    let _t343 ← build_letting_go _t342 (#[({ sudo_5LetGo_4hole := (12 : Int), sudo_5LetGo_3gap := true } : LetGo)] : Array (LetGo))
    let built := _t343
    let _t344 ← SudoRt.atL ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (10 : Int)
    let _as345 ← SudoRt.sudoAssertEq _t344 (0 : Int) 1029
    let _t346 ← SudoRt.atL ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs (11 : Int)
    let _as347 ← SudoRt.sudoAssertEq _t346 (0 : Int) 1030
    let _fromV := (12 : Int)
    let _toV := (19 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init354 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init354 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t349 ← SudoRt.atL ((built).sudo_5Built_4grid).sudo_7KeyGrid_4pegs h
  let _t350 ← SudoRt.modI h (2 : Int)
  let _t351 ← SudoRt.addI _t350 (1 : Int)
  let _as352 ← SudoRt.sudoAssertEq _t349 _t351 1032
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
      let _as353 ← SudoRt.sudoAssertEq (built).sudo_5Built_6used10 (55 : Int) 1033
      pure ()) (fun r => pure r))
    pure _out

def test_4_2_build_let_go_points_are_only_at_a_die_s_first_hole : Except SudoRt.Trap Unit :=
  do
    let _ex360 := (do
  let _t355 ← SudoRt.filledL (99 : Int) (1 : Int)
  let _t356 ← SudoRt.filledL (50 : Int) (5 : Int)
  let _t357 ← dice _t355 (#[] : Array (Int)) _t356
  let _t358 ← build_letting_go _t357 (#[({ sudo_5LetGo_4hole := (5 : Int), sudo_5LetGo_3gap := false } : LetGo)] : Array (LetGo))
  let _u359 := _t358
  pure ()
  pure ())
    match _ex360 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 1036: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 1036: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_4_2_build_each_let_go_point_is_listed_once : Except SudoRt.Trap Unit :=
  do
    let _t361 ← letgo_unique (#[({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo), ({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := true } : LetGo)] : Array (LetGo))
    let _as362 ← SudoRt.sudoAssert _t361 1040
    let _t363 ← letgo_unique (#[({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo), ({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo)] : Array (LetGo))
    let _as364 ← SudoRt.sudoAssert (!( _t363 )) 1041
    let _ex370 := (do
  let _t365 ← SudoRt.filledL (99 : Int) (1 : Int)
  let _t366 ← SudoRt.filledL (56 : Int) (5 : Int)
  let _t367 ← dice _t365 (#[] : Array (Int)) _t366
  let _t368 ← build_letting_go _t367 (#[({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo), ({ sudo_5LetGo_4hole := (4 : Int), sudo_5LetGo_3gap := false } : LetGo)] : Array (LetGo))
  let _u369 := _t368
  pure ()
  pure ())
    match _ex370 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 1042: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 1042: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_b8_squares_into_c_and_tidies_c : Except SudoRt.Trap Unit :=
  do
    let _t371 ← empty_register t1
    let three := _t371
    let _ix372 := (1 : Int)
    let _t373 ← SudoRt.putL three _ix372 (1 : Int)
    let three := _t373
    let _t374 ← empty_register t1
    let nine := _t374
    let _ix375 := (2 : Int)
    let _t376 ← SudoRt.putL nine _ix375 (1 : Int)
    let nine := _t376
    let _t377 ← check_received t1 three
    let _as378 ← SudoRt.sudoAssertEq _t377 (some nine) 1051
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_b1_drop_examples_carry_like_an_odometer", fun _ => test_b1_drop_examples_carry_like_an_odometer), ("test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4", fun _ => test_b4_t1_example_a_white_at_hole_20_folds_to_whites_at_holes_2_and_4), ("test_b3_one_times_x_is_x_and_x_times_one_is_x", fun _ => test_b3_one_times_x_is_x_and_x_times_one_is_x), ("test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow", fun _ => test_b3_worst_case_all_red_times_all_red_with_nudge_2_does_not_overflow), ("test_b5_p_tidies_to_the_empty_register_in_t1_and_t2", fun _ => test_b5_p_tidies_to_the_empty_register_in_t1_and_t2), ("test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length", fun _ => test_b8_rejects_0_1_p_1_p_1_and_a_wrong_length), ("test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all", fun _ => test_3_1_calling_the_shots_copies_the_value_into_y_misfires_and_all), ("test_3_1_clear_y_the_public_walk_leaves_x_x_x_in_y_and_the_call_clears_it_first", fun _ => test_3_1_clear_y_the_public_walk_leaves_x_x_x_in_y_and_the_call_clears_it_first), ("test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged", fun _ => test_b6_the_public_walk_leaves_the_last_square_x_x_x_in_y_unnudged), ("test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in", fun _ => test_b3_slide_lifts_the_register_s_old_pegs_then_slides_the_answer_in), ("test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in", fun _ => test_b6_stale_pegs_in_y_are_lifted_before_the_square_slides_in), ("test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register", fun _ => test_b5_on_a_spill_the_tidy_answer_slides_back_into_the_register), ("test_3_1_an_empty_register_is_eighteen_misfires", fun _ => test_3_1_an_empty_register_is_eighteen_misfires), ("test_4_3_read_start_marker_ship_pass_peg_pass", fun _ => test_4_3_read_start_marker_ship_pass_peg_pass), ("test_4_3_read_rejects_overlapping_ships", fun _ => test_4_3_read_rejects_overlapping_ships), ("test_b9_t1_exchange_with_the_sample_grids", fun _ => test_b9_t1_exchange_with_the_sample_grids), ("test_4_2_keypad_row_for_the_first_hole_column_for_the_second", fun _ => test_4_2_keypad_row_for_the_first_hole_column_for_the_second), ("test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face", fun _ => test_4_2_a_row_cup_d10_is_thrown_again_on_its_zero_face), ("test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again", fun _ => test_4_2_the_row_cup_is_five_dice_in_rainbow_order_zero_faces_thrown_again), ("test_4_2_grow_until_it_bumps", fun _ => test_4_2_grow_until_it_bumps), ("test_4_2_build_all_sea_and_all_white_pegs", fun _ => test_4_2_build_all_sea_and_all_white_pegs), ("test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs", fun _ => test_4_2_build_a_ship_across_a_die_pair_takes_both_pairs_pegs), ("test_4_2_build_letting_go_throws_the_unread_tray_dice_again", fun _ => test_4_2_build_letting_go_throws_the_unread_tray_dice_again), ("test_4_2_build_let_go_points_are_only_at_a_die_s_first_hole", fun _ => test_4_2_build_let_go_points_are_only_at_a_die_s_first_hole), ("test_4_2_build_each_let_go_point_is_listed_once", fun _ => test_4_2_build_each_let_go_point_is_listed_once), ("test_b8_squares_into_c_and_tidies_c", fun _ => test_b8_squares_into_c_and_tidies_c)]
