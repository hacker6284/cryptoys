-- DO NOT EDIT. Generated from ecbs.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for ecbs.sudo
import SudoRt
import Ecbs
set_option linter.unusedVariables false
open Ecbs

def test_1_demo_multiply_cube_and_inverse_agree_with_pari : Except SudoRt.Trap Unit :=
  do
    let _t1 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t1
    let x := (#[(1 : Int), (2 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let y := (#[(0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (2 : Int)] : Array (Int))
    let _t2 ← multiply t x y
    let _as3 ← SudoRt.sudoAssertEq _t2 (#[(1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int)] : Array (Int)) 1582
    let _t4 ← cube_number t x
    let _as5 ← SudoRt.sudoAssertEq _t4 (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 1583
    let _t6 ← invert_number t x
    let _as7 ← SudoRt.sudoAssertEq _t6 (#[(1 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) 1584
    pure ()

def test_1_toy_multiply_cube_and_inverse_agree_with_pari : Except SudoRt.Trap Unit :=
  do
    let _t8 ← tier (#[84, 111, 121] : Array Int)
    let t := _t8
    let x := (#[(1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let y := (#[(2 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int)] : Array (Int))
    let _t9 ← multiply t x y
    let _as10 ← SudoRt.sudoAssertEq _t9 (#[(1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)] : Array (Int)) 1590
    let _t11 ← cube_number t x
    let _as12 ← SudoRt.sudoAssertEq _t11 (#[(1 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (2 : Int)] : Array (Int)) 1591
    let _t13 ← invert_number t x
    let _as14 ← SudoRt.sudoAssertEq _t13 (#[(0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)] : Array (Int)) 1592
    pure ()

def test_3_r6_the_ladder_and_tally_inverse_times_the_number_is_one_demo_every_37th_number : Except SudoRt.Trap Unit :=
  do
    let _t15 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t15
    let _t16 ← SudoRt.filledL (7 : Int) (0 : Int)
    let one := _t16
    let _ix17 := (0 : Int)
    let _t18 ← SudoRt.putL one _ix17 (1 : Int)
    let one := _t18
    let _fromV := (1 : Int)
    let _toV := (59 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init33 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init33 fuel (fun σ =>
    let v := σ
    do
      if v > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) v)
      else
        match ← ((do
  let _t20 ← SudoRt.filledL (7 : Int) (0 : Int)
  let x := _t20
  let _t21 ← SudoRt.mulI (37 : Int) v
  let r := _t21
  let _fromV := (0 : Int)
  let _toV := (6 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init32 := (_fromV, (x, r))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init32 fuel (fun σ =>
    let i := σ.1
    let x := σ.2.1
    let _sp30 := σ.2.2
    let r := _sp30
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (x, r)))
      else
        match ← ((do
  let _ix23 := i
  let _t24 ← SudoRt.modI r (3 : Int)
  let _t25 ← SudoRt.putL x _ix23 _t24
  let x := _t25
  let _t26 ← SudoRt.divI r (3 : Int)
  let r := _t26
  pure (SudoRt.Flow.cont (ρ := Unit) (x, r))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let x := σ.2.1
    let _sp31 := σ.2.2
    let r := _sp31
    do
      let _t27 ← invert_number t x
      let _t28 ← multiply t x _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 one 1604
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) v)
        | .cont _fs => do
            if v == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) v)
            else do
              let i' ← SudoRt.addI v (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_3_r6_the_ladder_is_the_halving_strip_of_n_1 : Except SudoRt.Trap Unit :=
  do
    let _t34 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t35 ← new_board _t34
    let b := _t35
    let _as36 ← SudoRt.sudoAssertEq (b).sudo_5Board_6nrungs (2 : Int) 1608
    let _t37 ← SudoRt.atL (b).sudo_5Board_3row (b).sudo_5Board_7ladder0
    let _t39 ← (if (SudoRt.SEq.beq _t37 (1 : Int)) then (do
  let _t40 ← SudoRt.addI (b).sudo_5Board_7ladder0 (1 : Int)
  let _t41 ← SudoRt.atL (b).sudo_5Board_3row _t40
  pure (SudoRt.SEq.beq _t41 (2 : Int))) else pure false)
    let _as43 ← SudoRt.sudoAssert _t39 1609
    let _t44 ← tier (#[84, 111, 121] : Array Int)
    let _t45 ← new_board _t44
    let c := _t45
    let _as46 ← SudoRt.sudoAssertEq (c).sudo_5Board_6nrungs (4 : Int) 1611
    let _t47 ← SudoRt.atL (c).sudo_5Board_3row (c).sudo_5Board_7ladder0
    let _t48 ← SudoRt.addI (c).sudo_5Board_7ladder0 (1 : Int)
    let _t49 ← SudoRt.atL (c).sudo_5Board_3row _t48
    let _t50 ← SudoRt.addI (c).sudo_5Board_7ladder0 (2 : Int)
    let _t51 ← SudoRt.atL (c).sudo_5Board_3row _t50
    let _t52 ← SudoRt.addI (c).sudo_5Board_7ladder0 (3 : Int)
    let _t53 ← SudoRt.atL (c).sudo_5Board_3row _t52
    let _as54 ← SudoRt.sudoAssertEq (#[_t47, _t49, _t51, _t53] : Array (Int)) (#[(1 : Int), (2 : Int), (2 : Int), (1 : Int)] : Array (Int)) 1612
    pure ()

def test_5_1_the_base_point_by_rule_is_p_at_demo_and_toy : Except SudoRt.Trap Unit :=
  do
    let _t55 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t56 ← base_point_of _t55
    let p := _t56
    let _as57 ← SudoRt.sudoAssertEq (p).sudo_5Point_1x (#[(0 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)] : Array (Int)) 1616
    let _as58 ← SudoRt.sudoAssertEq (p).sudo_5Point_1y (#[(2 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int)] : Array (Int)) 1617
    let _t59 ← tier (#[84, 111, 121] : Array Int)
    let _t60 ← base_point_of _t59
    let q := _t60
    let _as61 ← SudoRt.sudoAssertEq (q).sudo_5Point_1x (#[(2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (2 : Int)] : Array (Int)) 1619
    let _as62 ← SudoRt.sudoAssertEq (q).sudo_5Point_1y (#[(2 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)] : Array (Int)) 1620
    let _t63 ← tier (#[84, 111, 121] : Array Int)
    let _t64 ← curve_test _t63 q
    let _as65 ← SudoRt.sudoAssert _t64 1621
    pure ()

def test_5_3_the_certificate_of_p_is_pi_p_p_and_an_order_5_point_has_none : Except SudoRt.Trap Unit :=
  do
    let _t66 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t66
    let _t67 ← base_point_of t
    let _t68 ← make_certificate t _t67
    let a := _t68
    let _t69 ← pt (#[(0 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) (#[(2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let _as70 ← SudoRt.sudoAssertEq a (some _t69) 1626
    let _t71 ← SudoRt.filledL (7 : Int) (0 : Int)
    let _t72 ← pt _t71 (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _t73 ← make_certificate t _t72
    let _as74 ← SudoRt.sudoAssertEq _t73 (none : Option (Point)) 1627
    let _t75 ← SudoRt.filledL (7 : Int) (0 : Int)
    let _t76 ← pt (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) _t75
    let _t77 ← curve_test t _t76
    let _as78 ← SudoRt.sudoAssert (!( _t77 )) 1628
    let _t79 ← pt (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) (#[(2 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let _t80 ← curve_test t _t79
    let _as81 ← SudoRt.sudoAssert _t80 1629
    pure ()

def test_5_3_the_receiver_s_verdicts_accept_mismatch_empty_certificate_curve_fails : Except SudoRt.Trap Unit :=
  do
    let _t82 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t82
    let _t83 ← base_point_of t
    let p := _t83
    let _t84 ← pt (#[(0 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) (#[(2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let ap := _t84
    let _t85 ← receive_check t ap p ap
    let honest := _t85
    let _as86 ← SudoRt.sudoAssertEq (honest).sudo_7Checked_7verdict Verdict.Sudo_7Verdict_6Accept 1636
    let _as87 ← SudoRt.sudoAssertEq (honest).sudo_7Checked_7rebuilt ap 1637
    let _as89 ← SudoRt.sudoAssert (decide ((honest).sudo_7Checked_4peak ≤ (7 : Int))) 1638
    let _t90 ← receive_check t ap p p
    let _as91 ← SudoRt.sudoAssertEq (_t90).sudo_7Checked_7verdict Verdict.Sudo_7Verdict_8Mismatch 1639
    let _t92 ← pt (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int))
    let o5 := _t92
    let _t93 ← receive_check t ap o5 o5
    let _as94 ← SudoRt.sudoAssertEq (_t93).sudo_7Checked_7verdict Verdict.Sudo_7Verdict_16EmptyCertificate 1641
    let _t95 ← SudoRt.filledL (7 : Int) (0 : Int)
    let _t96 ← pt (#[(1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) _t95
    let off := _t96
    let _t97 ← receive_check t ap off off
    let _as98 ← SudoRt.sudoAssertEq (_t97).sudo_7Checked_7verdict Verdict.Sudo_7Verdict_10CurveFails 1643
    pure ()

def test_5_a_demo_exchange_agrees_with_pari_c_a_shared_key_and_fold : Except SudoRt.Trap Unit :=
  do
    let _t99 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t99
    let _t100 ← exchange t (#[(0 : Int), (1 : Int)] : Array (Int)) (#[(2 : Int), (1 : Int)] : Array (Int))
    let r := _t100
    match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
    | SudoRt.SResult.ok e =>
      do
        let _t101 ← base_point_of t
        let _as102 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_4base _t101 1650
        let _t103 ← base_point_of t
        let _as104 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6sent_c _t103 1651
        let _t105 ← pt (#[(0 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int)] : Array (Int)) (#[(2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int)] : Array (Int))
        let _as106 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6sent_a _t105 1652
        let _t107 ← (if ((e).sudo_8Exchange_1a).sudo_6Player_7matched then (do
  pure ((e).sudo_8Exchange_1b).sudo_6Player_7matched) else pure false)
        let _t108 ← (if _t107 then (do
  pure ((e).sudo_8Exchange_1a).sudo_6Player_8on_curve) else pure false)
        let _t109 ← (if _t108 then (do
  pure ((e).sudo_8Exchange_1b).sudo_6Player_8on_curve) else pure false)
        let _as110 ← SudoRt.sudoAssert _t109 1653
        let _t111 ← pt (#[(2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int)] : Array (Int)) (#[(2 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (0 : Int)] : Array (Int))
        let _as112 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6shared _t111 1654
        let _as113 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1b).sudo_6Player_6shared ((e).sudo_8Exchange_1a).sudo_6Player_6shared 1655
        let _as114 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6folded (#[(2 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 1656
        let _as115 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1b).sudo_6Player_6folded ((e).sudo_8Exchange_1a).sudo_6Player_6folded 1657
        let _as116 ← SudoRt.sudoAssertEq (((e).sudo_8Exchange_1a).sudo_6Player_4cost).sudo_5Costs_4peak (7 : Int) 1658
        let _as117 ← SudoRt.sudoAssertEq (((e).sudo_8Exchange_1a).sudo_6Player_4cost).sudo_5Costs_5calls (28 : Int) 1659
        pure ()
    | _ =>
      do
        match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
        | SudoRt.SResult.err m =>
          do
            let _as118 ← SudoRt.sudoAssert false 1661
            pure ()
        | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"

def test_5_a_toy_exchange_agrees_with_pari : Except SudoRt.Trap Unit :=
  do
    let _t119 ← tier (#[84, 111, 121] : Array Int)
    let t := _t119
    let a := (#[(1 : Int), (0 : Int), (2 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int)] : Array (Int))
    let b := (#[(0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)] : Array (Int))
    let _t120 ← exchange t a b
    let r := _t120
    match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
    | SudoRt.SResult.ok e =>
      do
        let _as121 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_9base_hole (2 : Int) 1670
        let _t122 ← pt (#[(2 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)] : Array (Int)) (#[(1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int)] : Array (Int))
        let _as123 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6sent_c _t122 1671
        let _t124 ← pt (#[(0 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int)] : Array (Int)) (#[(1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (0 : Int), (2 : Int)] : Array (Int))
        let _as125 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6sent_a _t124 1672
        let _t126 ← (if ((e).sudo_8Exchange_1a).sudo_6Player_7matched then (do
  pure ((e).sudo_8Exchange_1b).sudo_6Player_7matched) else pure false)
        let _as127 ← SudoRt.sudoAssert _t126 1673
        let _t128 ← pt (#[(2 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int)] : Array (Int)) (#[(0 : Int), (1 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int)] : Array (Int))
        let _as129 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6shared _t128 1674
        let _as130 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1b).sudo_6Player_6shared ((e).sudo_8Exchange_1a).sudo_6Player_6shared 1675
        let _as131 ← SudoRt.sudoAssertEq ((e).sudo_8Exchange_1a).sudo_6Player_6folded (#[(2 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (2 : Int), (0 : Int)] : Array (Int)) 1676
        let _as132 ← SudoRt.sudoAssertEq (((e).sudo_8Exchange_1a).sudo_6Player_4cost).sudo_5Costs_4peak (7 : Int) 1677
        let _as134 ← SudoRt.sudoAssert (decide ((((e).sudo_8Exchange_1a).sudo_6Player_4cost).sudo_5Costs_14max_bench_hole ≤ (72 : Int))) 1678
        pure ()
    | _ =>
      do
        match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
        | SudoRt.SResult.err m =>
          do
            let _as135 ← SudoRt.sudoAssert false 1680
            pure ()
        | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"

def test_5_an_empty_key_is_refused : Except SudoRt.Trap Unit :=
  do
    let _t136 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t137 ← exchange _t136 (#[(0 : Int), (0 : Int)] : Array (Int)) (#[(1 : Int), (0 : Int)] : Array (Int))
    let r := _t137
    match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
    | SudoRt.SResult.ok e =>
      do
        let _as138 ← SudoRt.sudoAssert false 1686
        pure ()
    | _ =>
      do
        match (r : SudoRt.SResult (Array (Int)) (Exchange)) with
        | SudoRt.SResult.err m =>
          do
            let _as139 ← SudoRt.sudoAssert true 1688
            pure ()
        | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"

def test_5_2_a_call_names_the_sender_s_published_hole_never_a_key_grid_or_row_j : Except SudoRt.Trap Unit :=
  do
    let _t140 ← tier (#[84, 111, 121] : Array Int)
    let t := _t140
    let _t141 ← coordinate t across (0 : Int)
    let _as142 ← SudoRt.sudoAssertEq _t141 ({ sudo_4Hole_4grid := (2 : Int), sudo_4Hole_3row := (0 : Int), sudo_4Hole_3col := (1 : Int) } : Hole) 1692
    let _t143 ← coordinate t up (22 : Int)
    let _as144 ← SudoRt.sudoAssertEq _t143 ({ sudo_4Hole_4grid := (2 : Int), sudo_4Hole_3row := (5 : Int), sudo_4Hole_3col := (7 : Int) } : Hole) 1693
    let _t145 ← tier (#[72, 111, 98, 98, 121] : Array Int)
    let h := _t145
    let _t146 ← coordinate h across (58 : Int)
    let _as147 ← SudoRt.sudoAssertEq _t146 ({ sudo_4Hole_4grid := (4 : Int), sudo_4Hole_3row := (2 : Int), sudo_4Hole_3col := (9 : Int) } : Hole) 1695
    let _t148 ← tier (#[83, 101, 114, 105, 111, 117, 115] : Array Int)
    let s := _t148
    let _t149 ← coordinate s up (178 : Int)
    let _as150 ← SudoRt.sudoAssertEq _t149 ({ sudo_4Hole_4grid := (10 : Int), sudo_4Hole_3row := (8 : Int), sudo_4Hole_3col := (9 : Int) } : Hole) 1697
    let _t151 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t152 ← coordinate _t151 across (6 : Int)
    let _as153 ← SudoRt.sudoAssertEq _t152 ({ sudo_4Hole_4grid := (1 : Int), sudo_4Hole_3row := (3 : Int), sudo_4Hole_3col := (3 : Int) } : Hole) 1698
    pure ()

def test_5_2_calling_clears_a_stale_home_first : Except SudoRt.Trap Unit :=
  do
    let _t154 ← tier (#[84, 111, 121] : Array Int)
    let t := _t154
    let _t155 ← new_board t
    let snd := _t155
    let _t156 ← place snd across (#[(1 : Int), (0 : Int), (2 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int)] : Array (Int))
    let snd := _t156
    let _t157 ← place snd up (#[(0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (2 : Int), (2 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int))
    let snd := _t157
    let _t158 ← new_board t
    let «rec» := _t158
    let _t159 ← SudoRt.filledL (23 : Int) (2 : Int)
    let _t160 ← place «rec» base_up _t159
    let «rec» := _t160
    let _t161 ← call_in «rec» snd
    let «rec» := _t161
    let _as162 ← SudoRt.sudoAssertEq ((«rec»).sudo_5Board_4cost).sudo_5Costs_13stale_cleared (23 : Int) 1708
    let _as163 ← SudoRt.sudoAssertEq ((«rec»).sudo_5Board_4cost).sudo_5Costs_5calls (46 : Int) 1709
    let _t164 ← SudoRt.atL («rec»).sudo_5Board_3row («rec»).sudo_5Board_12calling_hole
    let _as165 ← SudoRt.sudoAssertEq _t164 (0 : Int) 1710
    let _t166 ← band «rec» base_across
    let _t167 ← band snd across
    let _as168 ← SudoRt.sudoAssertEq _t166 _t167 1711
    let _t169 ← band «rec» base_up
    let _t170 ← band snd up
    let _as171 ← SudoRt.sudoAssertEq _t169 _t170 1712
    pure ()

def test_6_the_fold_drops_rows_c_and_d_onto_rows_a_and_b_at_demo : Except SudoRt.Trap Unit :=
  do
    let _t172 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t173 ← fold _t172 (#[(2 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int)] : Array (Int))
    let _as174 ← SudoRt.sudoAssertEq _t173 (#[(2 : Int), (0 : Int), (0 : Int), (1 : Int)] : Array (Int)) 1715
    pure ()

def test_4_the_d10_row_cup_keypad_rows_and_columns_a_0_thrown_again : Except SudoRt.Trap Unit :=
  do
    let _t175 ← tier (#[84, 111, 121] : Array Int)
    let _t176 ← roll_key _t175 (#[(0 : Int), (5 : Int), (9 : Int), (1 : Int), (3 : Int), (7 : Int), (2 : Int), (4 : Int), (8 : Int), (6 : Int)] : Array (Int))
    let r := _t176
    let _as177 ← SudoRt.sudoAssertEq r (some ({ sudo_6Rolled_5cells := (#[(1 : Int), (1 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (0 : Int), (2 : Int), (2 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)] : Array (Int)), sudo_6Rolled_4used := (9 : Int), sudo_6Rolled_5rolls := (1 : Int) } : Rolled)) 1719
    pure ()

def test_4_an_all_empty_key_is_rolled_again_running_out_of_faces_gives_none : Except SudoRt.Trap Unit :=
  do
    let _t178 ← tier (#[68, 101, 109, 111] : Array Int)
    let t := _t178
    let _t179 ← roll_key t (#[(1 : Int), (5 : Int)] : Array (Int))
    let _as180 ← SudoRt.sudoAssertEq _t179 (some ({ sudo_6Rolled_5cells := (#[(1 : Int), (1 : Int)] : Array (Int)), sudo_6Rolled_4used := (2 : Int), sudo_6Rolled_5rolls := (2 : Int) } : Rolled)) 1723
    let _t181 ← roll_key t (#[(1 : Int)] : Array (Int))
    let _as182 ← SudoRt.sudoAssertEq _t181 (none : Option (Rolled)) 1724
    pure ()

def test_1_demo_s_16_hole_control_row_overruns_with_a_15_hole_script : Except SudoRt.Trap Unit :=
  do
    let _t183 ← tier (#[68, 101, 109, 111] : Array Int)
    let _t184 ← «with_script» _t183 (15 : Int)
    let t := _t184
    let _ex187 := (do
  let _t185 ← new_board t
  let _u186 := _t185
  pure ()
  pure ())
    match _ex187 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 1728: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 1728: expected trap AssertFailed, but nothing trapped"
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_1_demo_multiply_cube_and_inverse_agree_with_pari", fun _ => test_1_demo_multiply_cube_and_inverse_agree_with_pari), ("test_1_toy_multiply_cube_and_inverse_agree_with_pari", fun _ => test_1_toy_multiply_cube_and_inverse_agree_with_pari), ("test_3_r6_the_ladder_and_tally_inverse_times_the_number_is_one_demo_every_37th_number", fun _ => test_3_r6_the_ladder_and_tally_inverse_times_the_number_is_one_demo_every_37th_number), ("test_3_r6_the_ladder_is_the_halving_strip_of_n_1", fun _ => test_3_r6_the_ladder_is_the_halving_strip_of_n_1), ("test_5_1_the_base_point_by_rule_is_p_at_demo_and_toy", fun _ => test_5_1_the_base_point_by_rule_is_p_at_demo_and_toy), ("test_5_3_the_certificate_of_p_is_pi_p_p_and_an_order_5_point_has_none", fun _ => test_5_3_the_certificate_of_p_is_pi_p_p_and_an_order_5_point_has_none), ("test_5_3_the_receiver_s_verdicts_accept_mismatch_empty_certificate_curve_fails", fun _ => test_5_3_the_receiver_s_verdicts_accept_mismatch_empty_certificate_curve_fails), ("test_5_a_demo_exchange_agrees_with_pari_c_a_shared_key_and_fold", fun _ => test_5_a_demo_exchange_agrees_with_pari_c_a_shared_key_and_fold), ("test_5_a_toy_exchange_agrees_with_pari", fun _ => test_5_a_toy_exchange_agrees_with_pari), ("test_5_an_empty_key_is_refused", fun _ => test_5_an_empty_key_is_refused), ("test_5_2_a_call_names_the_sender_s_published_hole_never_a_key_grid_or_row_j", fun _ => test_5_2_a_call_names_the_sender_s_published_hole_never_a_key_grid_or_row_j), ("test_5_2_calling_clears_a_stale_home_first", fun _ => test_5_2_calling_clears_a_stale_home_first), ("test_6_the_fold_drops_rows_c_and_d_onto_rows_a_and_b_at_demo", fun _ => test_6_the_fold_drops_rows_c_and_d_onto_rows_a_and_b_at_demo), ("test_4_the_d10_row_cup_keypad_rows_and_columns_a_0_thrown_again", fun _ => test_4_the_d10_row_cup_keypad_rows_and_columns_a_0_thrown_again), ("test_4_an_all_empty_key_is_rolled_again_running_out_of_faces_gives_none", fun _ => test_4_an_all_empty_key_is_rolled_again_running_out_of_faces_gives_none), ("test_1_demo_s_16_hole_control_row_overruns_with_a_15_hole_script", fun _ => test_1_demo_s_16_hole_control_row_overruns_with_a_15_hole_script)]
