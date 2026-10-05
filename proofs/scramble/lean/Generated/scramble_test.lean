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
    let _as2 ← SudoRt.sudoAssertEq _t1 (#[87, 87, 87, 87, 87, 87, 87, 87, 87, 82, 82, 82, 82, 82, 82, 82, 82, 82, 71, 71, 71, 71, 71, 71, 71, 71, 71, 89, 89, 89, 89, 89, 89, 89, 89, 89, 79, 79, 79, 79, 79, 79, 79, 79, 79, 66, 66, 66, 66, 66, 66, 66, 66, 66] : Array Int) 629
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
    let _as30 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_6digest (whole).sudo_10Evaluation_6digest 667
    let _as31 ← SudoRt.sudoAssertEq (part).sudo_10Evaluation_5trace (whole).sudo_10Evaluation_5trace 668
    let _t32 ← run (1 : Int) (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int), (111 : Int)] : Array (Int))
    let whole1 := _t32
    let _t33 ← scramble_v1
    let s1 := _t33
    let _io34 ← update s1 (#[(104 : Int), (101 : Int), (108 : Int), (108 : Int)] : Array (Int))
    let s1 := _io34
    let _as36 ← SudoRt.sudoAssertEq (SudoRt.listLen (s1).sudo_8Scramble_5steps) (9 : Int) 672
    let _io37 ← update s1 (#[(111 : Int)] : Array (Int))
    let s1 := _io37
    let _io38 ← evaluate s1
    let ⟨_ret39, _iw040⟩ := _io38
    let s1 := _iw040
    let part1 := _ret39
    let _as41 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_6digest (whole1).sudo_10Evaluation_6digest 675
    let _as42 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_5trace (whole1).sudo_10Evaluation_5trace 676
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
      let _as60 ← SudoRt.sudoAssertEq (SudoRt.listLen (s1).sudo_8Scramble_7pending) _t59 688
      let _as62 ← SudoRt.sudoAssertEq (SudoRt.listLen (s2).sudo_8Scramble_7pending) (0 : Int) 689
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
      let _as67 ← SudoRt.sudoAssert _t65 690
      let _t68 ← run (1 : Int) msg
      let whole1 := _t68
      let _io69 ← evaluate s1
      let ⟨_ret70, _iw071⟩ := _io69
      let s1 := _iw071
      let part1 := _ret70
      let _as72 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_6digest (whole1).sudo_10Evaluation_6digest 693
      let _as73 ← SudoRt.sudoAssertEq (part1).sudo_10Evaluation_5trace (whole1).sudo_10Evaluation_5trace 694
      let _t74 ← run (2 : Int) msg
      let whole2 := _t74
      let _io75 ← evaluate s2
      let ⟨_ret76, _iw077⟩ := _io75
      let s2 := _iw077
      let part2 := _ret76
      let _as78 ← SudoRt.sudoAssertEq (part2).sudo_10Evaluation_6digest (whole2).sudo_10Evaluation_6digest 697
      let _as79 ← SudoRt.sudoAssertEq (part2).sudo_10Evaluation_5trace (whole2).sudo_10Evaluation_5trace 698
      pure ()) (fun r => pure r))
    pure _out

def test_digest_only_states_match_traced_digests_and_keep_no_trace : Except SudoRt.Trap Unit :=
  do
    let seed := (7 : Int)
    let _fromV := (1 : Int)
    let _toV := (2 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init171 := (_fromV, seed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init171 fuel (fun σ =>
    let v := σ.1
    let seed := σ.2
    do
      if v > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (v, seed))
      else
        match ← ((do
  let _t88 ← scramble_v1_digest
  let q := _t88
  if (SudoRt.SEq.beq v (2 : Int)) then
    do
      let _t90 ← scramble_v2_digest
      let q := _t90
      let msg := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (39 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init130 := (_fromV, (seed, q, msg))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init130 fuel (fun σ =>
    let i := σ.1
    let seed := σ.2.1
    let _sp126 := σ.2.2
    let q := _sp126.1
    let _sp127 := _sp126.2
    let msg := _sp127
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (seed, q, msg)))
      else
        match ← ((do
  let chunk := (#[] : Array (Int))
  let _t100 ← SudoRt.modI seed (9 : Int)
  let _t101 ← SudoRt.subI _t100 (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t101
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init118 := (_fromV, (seed, chunk))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init118 fuel (fun σ =>
    let j := σ.1
    let seed := σ.2.1
    let _sp116 := σ.2.2
    let chunk := _sp116
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (seed, chunk)))
      else
        match ← ((do
  let _t93 ← SudoRt.mulI seed (1103515245 : Int)
  let _t94 ← SudoRt.addI _t93 (12345 : Int)
  let _t95 ← SudoRt.modI _t94 (2147483648 : Int)
  let seed := _t95
  let _t96 ← SudoRt.divI seed (8388608 : Int)
  let _mb97 := SudoRt.appendL chunk _t96
  let ⟨_nr98, _⟩ := _mb97
  let chunk := _nr98
  let _hm85 := ()
  let _u99 := _hm85
  pure (SudoRt.Flow.cont (ρ := Unit) (seed, chunk))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seed := σ.2.1
    let _sp117 := σ.2.2
    let chunk := _sp117
    do
      let _io102 ← update q chunk
      let q := _io102
      let _t109 ← SudoRt.subI (SudoRt.listLen chunk) (1 : Int)
      let _fromV := (0 : Int)
      let _toV := _t109
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init115 := (_fromV, msg)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init115 fuel (fun σ =>
    let j := σ.1
    let msg := σ.2
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, msg))
      else
        match ← ((do
  let _t104 ← SudoRt.atL chunk j
  let _mb105 := SudoRt.appendL msg _t104
  let ⟨_nr106, _⟩ := _mb105
  let msg := _nr106
  let _hm86 := ()
  let _u107 := _hm86
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
      let _as111 ← SudoRt.sudoAssertEq (SudoRt.listLen (q).sudo_8Scramble_5steps) (0 : Int) 715
      let _as114 ← SudoRt.sudoAssert (decide ((SudoRt.listLen (q).sudo_8Scramble_7pending) < (8 : Int))) 716
      pure (SudoRt.Flow.cont (ρ := Unit) (seed, q, msg))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seed := σ.2.1
    let _sp128 := σ.2.2
    let q := _sp128.1
    let _sp129 := _sp128.2
    let msg := _sp129
    do
      let _t119 ← run v msg
      let whole := _t119
      let _io120 ← evaluate q
      let ⟨_ret121, _iw0122⟩ := _io120
      let q := _iw0122
      let got := _ret121
      let _as123 ← SudoRt.sudoAssertEq (got).sudo_10Evaluation_6digest (whole).sudo_10Evaluation_6digest 719
      let _as125 ← SudoRt.sudoAssertEq (SudoRt.listLen (got).sudo_10Evaluation_5trace) (0 : Int) 720
      pure (SudoRt.Flow.cont (ρ := Unit) seed)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out
  else
    do
      let msg := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (39 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init170 := (_fromV, (seed, q, msg))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init170 fuel (fun σ =>
    let i := σ.1
    let seed := σ.2.1
    let _sp166 := σ.2.2
    let q := _sp166.1
    let _sp167 := _sp166.2
    let msg := _sp167
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (seed, q, msg)))
      else
        match ← ((do
  let chunk := (#[] : Array (Int))
  let _t140 ← SudoRt.modI seed (9 : Int)
  let _t141 ← SudoRt.subI _t140 (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t141
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init158 := (_fromV, (seed, chunk))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init158 fuel (fun σ =>
    let j := σ.1
    let seed := σ.2.1
    let _sp156 := σ.2.2
    let chunk := _sp156
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (seed, chunk)))
      else
        match ← ((do
  let _t133 ← SudoRt.mulI seed (1103515245 : Int)
  let _t134 ← SudoRt.addI _t133 (12345 : Int)
  let _t135 ← SudoRt.modI _t134 (2147483648 : Int)
  let seed := _t135
  let _t136 ← SudoRt.divI seed (8388608 : Int)
  let _mb137 := SudoRt.appendL chunk _t136
  let ⟨_nr138, _⟩ := _mb137
  let chunk := _nr138
  let _hm85 := ()
  let _u139 := _hm85
  pure (SudoRt.Flow.cont (ρ := Unit) (seed, chunk))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seed := σ.2.1
    let _sp157 := σ.2.2
    let chunk := _sp157
    do
      let _io142 ← update q chunk
      let q := _io142
      let _t149 ← SudoRt.subI (SudoRt.listLen chunk) (1 : Int)
      let _fromV := (0 : Int)
      let _toV := _t149
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init155 := (_fromV, msg)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init155 fuel (fun σ =>
    let j := σ.1
    let msg := σ.2
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, msg))
      else
        match ← ((do
  let _t144 ← SudoRt.atL chunk j
  let _mb145 := SudoRt.appendL msg _t144
  let ⟨_nr146, _⟩ := _mb145
  let msg := _nr146
  let _hm86 := ()
  let _u147 := _hm86
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
      let _as151 ← SudoRt.sudoAssertEq (SudoRt.listLen (q).sudo_8Scramble_5steps) (0 : Int) 715
      let _as154 ← SudoRt.sudoAssert (decide ((SudoRt.listLen (q).sudo_8Scramble_7pending) < (8 : Int))) 716
      pure (SudoRt.Flow.cont (ρ := Unit) (seed, q, msg))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seed := σ.2.1
    let _sp168 := σ.2.2
    let q := _sp168.1
    let _sp169 := _sp168.2
    let msg := _sp169
    do
      let _t159 ← run v msg
      let whole := _t159
      let _io160 ← evaluate q
      let ⟨_ret161, _iw0162⟩ := _io160
      let q := _iw0162
      let got := _ret161
      let _as163 ← SudoRt.sudoAssertEq (got).sudo_10Evaluation_6digest (whole).sudo_10Evaluation_6digest 719
      let _as165 ← SudoRt.sudoAssertEq (SudoRt.listLen (got).sudo_10Evaluation_5trace) (0 : Int) 720
      pure (SudoRt.Flow.cont (ρ := Unit) seed)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (v, _fs))
        | .cont _fs => do
            if v == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (v, _fs))
            else do
              let i' ← SudoRt.addI v (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seed := σ.2
    do
      pure ()) (fun r => pure r))
    pure _out

def test_second_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t172 ← scramble_v2
    let s := _t172
    let _io173 ← evaluate s
    let ⟨_ret174, _iw0175⟩ := _io173
    let s := _iw0175
    let _ex179 := (do
  let _io176 ← evaluate s
  let ⟨_ret177, _iw0178⟩ := _io176
  let s := _iw0178
  pure ()
  pure ())
    match _ex179 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 725: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 725: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_update_after_evaluate_traps : Except SudoRt.Trap Unit :=
  do
    let _t180 ← scramble_v1
    let s := _t180
    let _io181 ← evaluate s
    let ⟨_ret182, _iw0183⟩ := _io181
    let s := _iw0183
    let _ex185 := (do
  let _io184 ← update s (#[(1 : Int)] : Array (Int))
  let s := _io184
  pure ()
  pure ())
    match _ex185 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 731: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 731: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_a_byte_above_255_traps : Except SudoRt.Trap Unit :=
  do
    let _t186 ← scramble_v2
    let s := _t186
    let _ex188 := (do
  let _io187 ← update s (#[(256 : Int)] : Array (Int))
  let s := _io187
  pure ()
  pure ())
    match _ex188 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 736: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 736: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_apply_move : Except SudoRt.Trap Unit :=
  do
    let letters := (#[48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82] : Array Int)
    let _t189 ← «apply_move» letters (#[85] : Array Int)
    let _as190 ← SudoRt.sudoAssertEq _t189 (#[50, 53, 56, 49, 52, 55, 48, 51, 54, 105, 106, 107, 99, 100, 101, 102, 103, 104, 65, 66, 67, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 74, 75, 76, 68, 69, 70, 71, 72, 73, 57, 97, 98, 77, 78, 79, 80, 81, 82] : Array Int) 741
    let _t191 ← «apply_move» (#[87, 87, 87, 87, 87, 87, 87, 87, 87, 82, 82, 82, 82, 82, 82, 82, 82, 82, 71, 71, 71, 71, 71, 71, 71, 71, 71, 89, 89, 89, 89, 89, 89, 89, 89, 89, 79, 79, 79, 79, 79, 79, 79, 79, 79, 66, 66, 66, 66, 66, 66, 66, 66, 66] : Array Int) (#[82] : Array Int)
    let got := _t191
    let _t192 ← «apply_move» got (#[85] : Array Int)
    let _as193 ← SudoRt.sudoAssertEq _t192 (#[71, 71, 71, 87, 87, 87, 87, 87, 87, 71, 71, 89, 82, 82, 82, 82, 82, 82, 79, 79, 79, 71, 71, 89, 71, 71, 89, 89, 89, 66, 89, 89, 66, 89, 89, 66, 87, 66, 66, 79, 79, 79, 79, 79, 79, 82, 82, 82, 87, 66, 66, 87, 66, 66] : Array Int) 743
    let _ex196 := (do
  let _t194 ← «apply_move» letters (#[88] : Array Int)
  let _u195 := _t194
  pure ()
  pure ())
    match _ex196 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 744: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 744: expected trap AssertFailed, but nothing trapped"
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_solved_facelets_are_the_start_pose", fun _ => test_solved_facelets_are_the_start_pose), ("test_empty_v1", fun _ => test_empty_v1), ("test_empty_v2", fun _ => test_empty_v2), ("test_byte_a7_v1", fun _ => test_byte_a7_v1), ("test_byte_a7_v2", fun _ => test_byte_a7_v2), ("test_hello_v1", fun _ => test_hello_v1), ("test_hello_v2", fun _ => test_hello_v2), ("test_cube_v1", fun _ => test_cube_v1), ("test_cube_v2", fun _ => test_cube_v2), ("test_letter_a_v1", fun _ => test_letter_a_v1), ("test_letter_a_v2", fun _ => test_letter_a_v2), ("test_split_updates_match_one_shot", fun _ => test_split_updates_match_one_shot), ("test_update_keeps_only_the_unwalked_nybbles", fun _ => test_update_keeps_only_the_unwalked_nybbles), ("test_digest_only_states_match_traced_digests_and_keep_no_trace", fun _ => test_digest_only_states_match_traced_digests_and_keep_no_trace), ("test_second_evaluate_traps", fun _ => test_second_evaluate_traps), ("test_update_after_evaluate_traps", fun _ => test_update_after_evaluate_traps), ("test_a_byte_above_255_traps", fun _ => test_a_byte_above_255_traps), ("test_apply_move", fun _ => test_apply_move)]
