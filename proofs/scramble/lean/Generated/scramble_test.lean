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
    let _as2 ← SudoRt.sudoAssertEq _t1 (#[87, 87, 87, 87, 87, 87, 87, 87, 87, 82, 82, 82, 82, 82, 82, 82, 82, 82, 71, 71, 71, 71, 71, 71, 71, 71, 71, 89, 89, 89, 89, 89, 89, 89, 89, 89, 79, 79, 79, 79, 79, 79, 79, 79, 79, 66, 66, 66, 66, 66, 66, 66, 66, 66] : Array Int) 583
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
    let _as30 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_6digest (whole).sudo_10Evaluation_6digest 621
    let _as31 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_5trace (whole).sudo_10Evaluation_5trace 622
    let _t32 ← run (1 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int))
    let whole1 := _t32
    let _t33 ← scramble_v1
    let s1 := _t33
    let _io34 ← update s1 (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int)] : Array (Int))
    let s1 := _io34
    let _as36 ← SudoRt.sudoAssertEq (SudoRt.listLen (s1).sudo_8Scramble_5steps) (9 : Int) 626
    let _io37 ← update s1 (#[(111 : Int)] : Array (Int))
    let s1 := _io37
    let _io38 ← evaluate s1
    let ⟨_ret39, _iw040⟩ := _io38
    let s1 := _iw040
    let part1 := _ret39
    let _as41 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_6digest (whole1).sudo_10Evaluation_6digest 629
    let _as42 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_5trace (whole1).sudo_10Evaluation_5trace 630
    pure ()

def test_update_keeps_only_the_unwalked_nybbles : Except SudoRt.Trap Unit :=
  do
    let _t44 ← scramble_v1
    let s1 := _t44
    let _t45 ← scramble_v2
    let s2 := _t45
    let msg := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (19 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init84 := (_fromV, (s1, s2, msg))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init84 fuel (fun σ =>
    let i := σ.1
    let s1 := σ.2.1
    let _sp80 := σ.2.2
    let s2 := _sp80.1
    let _sp81 := _sp80.2
    let msg := _sp81
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (s1, s2, msg)))
      else
        match ← ((do
  let _t47 ← SudoRt.subI (255 : Int) i
  let _t48 ← SudoRt.mulI (7 : Int) i
  let chunk := (#[i, _t47, _t48] : Array (Int))
  let _io49 ← update s1 chunk
  let s1 := _io49
  let _io50 ← update s2 chunk
  let s2 := _io50
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init63 := (_fromV, msg)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init63 fuel (fun σ =>
    let j := σ.1
    let msg := σ.2
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, msg))
      else
        match ← ((do
  let _t52 ← SudoRt.atL chunk j
  let _mb53 := SudoRt.appendL msg _t52
  let ⟨_nr54, _⟩ := _mb53
  let msg := _nr54
  let _hm43 := ()
  let _u55 := _hm43
  pure (SudoRt.Flow.cont (ρ := Unit) msg)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let msg := σ.2
    do
      let _t57 ← SudoRt.addI i (1 : Int)
      let _t58 ← SudoRt.mulI (6 : Int) _t57
      let _t59 ← SudoRt.modI _t58 (8 : Int)
      let _as60 ← SudoRt.sudoAssertEq (SudoRt.listLen (s1).sudo_8Scramble_7pending) _t59 642
      let _as62 ← SudoRt.sudoAssertEq (SudoRt.listLen (s2).sudo_8Scramble_7pending) (0 : Int) 643
      pure (SudoRt.Flow.cont (ρ := Unit) (s1, s2, msg))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let s1 := σ.2.1
    let _sp82 := σ.2.2
    let s2 := _sp82.1
    let _sp83 := _sp82.2
    let msg := _sp83
    do
      let _t65 ← (if (SudoRt.SEq.beq (s1).sudo_8Scramble_5total (120 : Int)) then (do
  pure (SudoRt.SEq.beq (s2).sudo_8Scramble_5total (120 : Int))) else pure false)
      let _as67 ← SudoRt.sudoAssert _t65 644
      let _t68 ← run (1 : Int) msg
      let whole1 := _t68
      let _io69 ← evaluate s1
      let ⟨_ret70, _iw071⟩ := _io69
      let s1 := _iw071
      let part1 := _ret70
      let _as72 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_6digest (whole1).sudo_10Evaluation_6digest 647
      let _as73 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_5trace (whole1).sudo_10Evaluation_5trace 648
      let _t74 ← run (2 : Int) msg
      let whole2 := _t74
      let _io75 ← evaluate s2
      let ⟨_ret76, _iw077⟩ := _io75
      let s2 := _iw077
      let part2 := _ret76
      let _as78 ← SudoRt.sudoAssertEq (part2).sudo_10Evaluation_6digest (whole2).sudo_10Evaluation_6digest 651
      let _as79 ← SudoRt.sudoAssertEq (part2).sudo_10Evaluation_5trace (whole2).sudo_10Evaluation_5trace 652
      pure ()) (fun r => pure r))
    pure _out

def test_second_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t85 ← scramble_v2
    let s := _t85
    let _io86 ← evaluate s
    let ⟨_ret87, _iw088⟩ := _io86
    let s := _iw088
    let _ex92 := (do
  let _io89 ← evaluate s
  let ⟨_ret90, _iw091⟩ := _io89
  let s := _iw091
  pure ()
  pure ())
    match _ex92 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 657: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 657: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_update_after_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t93 ← scramble_v1
    let s := _t93
    let _io94 ← evaluate s
    let ⟨_ret95, _iw096⟩ := _io94
    let s := _iw096
    let _ex98 := (do
  let _io97 ← update s (#[(1 : Int)] : Array (Int))
  let s := _io97
  pure ()
  pure ())
    match _ex98 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 663: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 663: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_a_byte_above_255_traps : Except SudoRt.Trap Unit :=
  do
    let _t99 ← scramble_v2
    let s := _t99
    let _ex101 := (do
  let _io100 ← update s (#[(256 : Int)] : Array (Int))
  let s := _io100
  pure ()
  pure ())
    match _ex101 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 668: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 668: expected trap AssertFailed, but nothing trapped"
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_solved_facelets_are_the_start_pose", fun _ => test_solved_facelets_are_the_start_pose), ("test_empty_v1", fun _ => test_empty_v1), ("test_empty_v2", fun _ => test_empty_v2), ("test_byte_a7_v1", fun _ => test_byte_a7_v1), ("test_byte_a7_v2", fun _ => test_byte_a7_v2), ("test_hello_v1", fun _ => test_hello_v1), ("test_hello_v2", fun _ => test_hello_v2), ("test_cube_v1", fun _ => test_cube_v1), ("test_cube_v2", fun _ => test_cube_v2), ("test_letter_a_v1", fun _ => test_letter_a_v1), ("test_letter_a_v2", fun _ => test_letter_a_v2), ("test_split_updates_match_one_shot", fun _ => test_split_updates_match_one_shot), ("test_update_keeps_only_the_unwalked_nybbles", fun _ => test_update_keeps_only_the_unwalked_nybbles), ("test_second_evaluate_traps", fun _ => test_second_evaluate_traps), ("test_update_after_evaluate_traps", fun _ => test_update_after_evaluate_traps), ("test_a_byte_above_255_traps", fun _ => test_a_byte_above_255_traps)]
