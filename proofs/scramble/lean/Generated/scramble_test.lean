-- DO NOT EDIT. Generated from scramble.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for scramble.sudo
import SudoRt
import Scramble
set_option linter.unusedVariables false
open Scramble

def test_solved_facelets_are_the_start_pose : Except SudoRt.Trap Unit :=
  do
    let _t1 ← solved_facelets
    let _as2 ← SudoRt.sudoAssertEq _t1 (#[87, 87, 87, 87, 87, 87, 87, 87, 87, 82, 82, 82, 82, 82, 82, 82, 82, 82, 71, 71, 71, 71, 71, 71, 71, 71, 71, 89, 89, 89, 89, 89, 89, 89, 89, 89, 79, 79, 79, 79, 79, 79, 79, 79, 79, 66, 66, 66, 66, 66, 66, 66, 66, 66] : Array Int) 600
    pure ()

def test_empty_v1 : Except SudoRt.Trap Unit :=
  do
    let _t3 ← check (1 : Int) (#[] : Array (Int)) (#[(0 : Int), (154 : Int), (92 : Int), (23 : Int), (209 : Int), (157 : Int), (221 : Int), (190 : Int), (180 : Int)] : Array (Int)) (#[89, 89, 71, 71, 87, 87, 87, 87, 87, 79, 79, 79, 71, 82, 89, 79, 89, 66, 82, 66, 66, 71, 71, 79, 66, 89, 71, 82, 66, 87, 82, 89, 71, 66, 66, 82, 71, 87, 71, 79, 79, 82, 89, 87, 87, 89, 79, 82, 82, 66, 66, 89, 82, 79] : Array Int) (30 : Int)
    let _u4 := _t3
    pure ()

def test_empty_v2 : Except SudoRt.Trap Unit :=
  do
    let _t5 ← check (2 : Int) (#[] : Array (Int)) (#[(0 : Int), (96 : Int), (36 : Int), (233 : Int), (182 : Int), (16 : Int), (82 : Int), (244 : Int), (97 : Int)] : Array (Int)) (#[82, 82, 79, 82, 87, 66, 79, 89, 79, 87, 82, 66, 71, 82, 87, 82, 79, 79, 66, 71, 71, 87, 71, 82, 89, 89, 87, 71, 66, 71, 71, 89, 87, 87, 79, 89, 66, 87, 87, 79, 79, 71, 82, 79, 82, 89, 89, 89, 66, 66, 66, 71, 89, 66] : Array Int) (39 : Int)
    let _u6 := _t5
    pure ()

def test_byte_a7_v1 : Except SudoRt.Trap Unit :=
  do
    let _t7 ← check (1 : Int) (#[(167 : Int)] : Array (Int)) (#[(1 : Int), (35 : Int), (38 : Int), (254 : Int), (10 : Int), (8 : Int), (167 : Int), (108 : Int), (65 : Int)] : Array (Int)) (#[87, 87, 66, 87, 87, 71, 89, 82, 87, 66, 87, 89, 79, 82, 71, 89, 82, 71, 82, 87, 82, 79, 71, 89, 79, 71, 71, 66, 89, 79, 66, 89, 89, 82, 82, 87, 82, 79, 66, 79, 79, 71, 71, 89, 87, 79, 66, 71, 82, 66, 66, 79, 66, 89] : Array Int) (30 : Int)
    let _u8 := _t7
    pure ()

def test_byte_a7_v2 : Except SudoRt.Trap Unit :=
  do
    let _t9 ← check (2 : Int) (#[(167 : Int)] : Array (Int)) (#[(1 : Int), (85 : Int), (43 : Int), (110 : Int), (247 : Int), (218 : Int), (16 : Int), (194 : Int), (232 : Int)] : Array (Int)) (#[79, 71, 66, 89, 87, 89, 66, 87, 82, 89, 79, 82, 87, 82, 79, 71, 87, 82, 82, 71, 71, 66, 71, 82, 79, 82, 79, 87, 71, 89, 66, 89, 79, 66, 66, 87, 89, 82, 87, 66, 79, 87, 79, 79, 71, 89, 89, 66, 71, 66, 82, 71, 89, 87] : Array Int) (39 : Int)
    let _u10 := _t9
    pure ()

def test_hello_v1 : Except SudoRt.Trap Unit :=
  do
    let _t11 ← check (1 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int)) (#[(0 : Int), (223 : Int), (121 : Int), (2 : Int), (237 : Int), (32 : Int), (109 : Int), (248 : Int), (140 : Int)] : Array (Int)) (#[66, 66, 87, 66, 87, 87, 82, 82, 66, 87, 66, 71, 71, 82, 82, 87, 71, 71, 66, 87, 79, 87, 71, 89, 89, 89, 82, 79, 82, 66, 79, 89, 87, 89, 71, 87, 79, 79, 89, 79, 79, 79, 82, 71, 71, 82, 89, 89, 66, 66, 89, 79, 82, 71] : Array Int) (30 : Int)
    let _u12 := _t11
    pure ()

def test_hello_v2 : Except SudoRt.Trap Unit :=
  do
    let _t13 ← check (2 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int)) (#[(0 : Int), (82 : Int), (163 : Int), (199 : Int), (209 : Int), (34 : Int), (145 : Int), (209 : Int), (64 : Int)] : Array (Int)) (#[79, 82, 87, 87, 87, 87, 87, 89, 87, 71, 82, 82, 79, 82, 87, 71, 66, 79, 82, 79, 79, 82, 71, 66, 79, 66, 89, 66, 82, 82, 71, 89, 89, 89, 87, 89, 89, 79, 71, 71, 79, 71, 66, 89, 87, 66, 89, 66, 66, 66, 79, 71, 71, 82] : Array Int) (39 : Int)
    let _u14 := _t13
    pure ()

def test_cube_v1 : Except SudoRt.Trap Unit :=
  do
    let _t15 ← check (1 : Int) (#[(99 : Int), (117 : Int), (98 : Int), (101 : Int)] : Array (Int)) (#[(0 : Int), (31 : Int), (45 : Int), (137 : Int), (218 : Int), (17 : Int), (50 : Int), (217 : Int), (69 : Int)] : Array (Int)) (#[89, 82, 82, 66, 87, 71, 87, 82, 87, 82, 87, 71, 89, 82, 66, 87, 82, 89, 66, 66, 71, 87, 71, 71, 87, 79, 66, 71, 89, 79, 71, 89, 89, 89, 87, 79, 82, 87, 82, 66, 79, 79, 71, 79, 79, 89, 71, 66, 89, 66, 79, 66, 82, 79] : Array Int) (30 : Int)
    let _u16 := _t15
    pure ()

def test_cube_v2 : Except SudoRt.Trap Unit :=
  do
    let _t17 ← check (2 : Int) (#[(99 : Int), (117 : Int), (98 : Int), (101 : Int)] : Array (Int)) (#[(1 : Int), (50 : Int), (253 : Int), (206 : Int), (11 : Int), (242 : Int), (110 : Int), (88 : Int), (152 : Int)] : Array (Int)) (#[79, 71, 66, 89, 87, 87, 87, 89, 89, 71, 66, 82, 66, 82, 87, 71, 82, 79, 82, 71, 82, 79, 71, 79, 66, 82, 87, 79, 89, 79, 82, 89, 71, 82, 66, 87, 71, 79, 71, 87, 79, 87, 66, 66, 89, 89, 79, 89, 71, 66, 82, 66, 89, 87] : Array Int) (39 : Int)
    let _u18 := _t17
    pure ()

def test_letter_a_v1 : Except SudoRt.Trap Unit :=
  do
    let _t19 ← check (1 : Int) (#[(97 : Int)] : Array (Int)) (#[(0 : Int), (139 : Int), (168 : Int), (193 : Int), (110 : Int), (128 : Int), (116 : Int), (53 : Int), (77 : Int)] : Array (Int)) (#[87, 66, 66, 66, 87, 71, 82, 87, 71, 79, 82, 79, 82, 82, 82, 89, 79, 66, 66, 79, 87, 89, 71, 66, 89, 71, 79, 71, 79, 66, 71, 89, 89, 89, 89, 87, 82, 87, 89, 89, 79, 82, 71, 87, 82, 87, 79, 71, 87, 66, 66, 82, 71, 79] : Array Int) (30 : Int)
    let _u20 := _t19
    pure ()

def test_letter_a_v2 : Except SudoRt.Trap Unit :=
  do
    let _t21 ← check (2 : Int) (#[(97 : Int)] : Array (Int)) (#[(1 : Int), (88 : Int), (138 : Int), (100 : Int), (105 : Int), (207 : Int), (231 : Int), (178 : Int), (134 : Int)] : Array (Int)) (#[82, 82, 89, 66, 87, 89, 71, 71, 71, 82, 79, 66, 71, 82, 89, 66, 87, 87, 89, 87, 89, 71, 71, 79, 71, 66, 79, 79, 79, 87, 82, 89, 82, 66, 66, 82, 71, 82, 79, 87, 79, 89, 89, 71, 87, 82, 89, 87, 66, 66, 79, 66, 87, 79] : Array Int) (39 : Int)
    let _u22 := _t21
    pure ()

def test_split_updates_match_one_shot : Except SudoRt.Trap Unit :=
  do
    let _t23 ← run (2 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int))
    let whole := _t23
    let _t24 ← scramble_v2
    let s := _t24
    let _io25 ← update s (#[(104 : Int), (101 : Int)] : Array (Int))
    let s := _io25
    let _io26 ← update s (#[(108 : Int), (108 : Int), (111 : Int)] : Array (Int))
    let s := _io26
    let _io27 ← evaluate s
    let ⟨_ret28, _iw029⟩ := _io27
    let s := _iw029
    let part := _ret28
    let _as30 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_6digest (whole).sudo_10Evaluation_6digest 638
    let _as31 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_5trace (whole).sudo_10Evaluation_5trace 639
    let _t32 ← run (1 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int))
    let whole1 := _t32
    let _t33 ← scramble_v1
    let s1 := _t33
    let _io34 ← update s1 (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int)] : Array (Int))
    let s1 := _io34
    let _as36 ← SudoRt.sudoAssertEq (SudoRt.listLen (s1).sudo_8Scramble_5steps) (9 : Int) 643
    let _io37 ← update s1 (#[(111 : Int)] : Array (Int))
    let s1 := _io37
    let _io38 ← evaluate s1
    let ⟨_ret39, _iw040⟩ := _io38
    let s1 := _iw040
    let part1 := _ret39
    let _as41 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_6digest (whole1).sudo_10Evaluation_6digest 646
    let _as42 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_5trace (whole1).sudo_10Evaluation_5trace 647
    pure ()

def test_second_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t43 ← scramble_v2
    let s := _t43
    let _io44 ← evaluate s
    let ⟨_ret45, _iw046⟩ := _io44
    let s := _iw046
    let _ex50 := (do
  let _io47 ← evaluate s
  let ⟨_ret48, _iw049⟩ := _io47
  let s := _iw049
  pure ()
  pure ())
    match _ex50 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 652: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 652: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_update_after_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t51 ← scramble_v1
    let s := _t51
    let _io52 ← evaluate s
    let ⟨_ret53, _iw054⟩ := _io52
    let s := _iw054
    let _ex56 := (do
  let _io55 ← update s (#[(1 : Int)] : Array (Int))
  let s := _io55
  pure ()
  pure ())
    match _ex56 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 658: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 658: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_a_byte_above_255_traps : Except SudoRt.Trap Unit :=
  do
    let _t57 ← scramble_v2
    let s := _t57
    let _ex59 := (do
  let _io58 ← update s (#[(256 : Int)] : Array (Int))
  let s := _io58
  pure ()
  pure ())
    match _ex59 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 663: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 663: expected trap AssertFailed, but nothing trapped"
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_solved_facelets_are_the_start_pose", fun _ => test_solved_facelets_are_the_start_pose), ("test_empty_v1", fun _ => test_empty_v1), ("test_empty_v2", fun _ => test_empty_v2), ("test_byte_a7_v1", fun _ => test_byte_a7_v1), ("test_byte_a7_v2", fun _ => test_byte_a7_v2), ("test_hello_v1", fun _ => test_hello_v1), ("test_hello_v2", fun _ => test_hello_v2), ("test_cube_v1", fun _ => test_cube_v1), ("test_cube_v2", fun _ => test_cube_v2), ("test_letter_a_v1", fun _ => test_letter_a_v1), ("test_letter_a_v2", fun _ => test_letter_a_v2), ("test_split_updates_match_one_shot", fun _ => test_split_updates_match_one_shot), ("test_second_evaluate_traps", fun _ => test_second_evaluate_traps), ("test_update_after_evaluate_traps", fun _ => test_update_after_evaluate_traps), ("test_a_byte_above_255_traps", fun _ => test_a_byte_above_255_traps)]
