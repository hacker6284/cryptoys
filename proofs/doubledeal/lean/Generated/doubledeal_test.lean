-- DO NOT EDIT. Generated from doubledeal.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for doubledeal.sudo
import SudoRt
import Doubledeal
set_option linter.unusedVariables false
open Doubledeal

def test_column_and_row_deals_are_inverses : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init12 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init12 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _mb3 := SudoRt.appendL deck i
  let ⟨_nr4, _⟩ := _mb3
  let deck := _nr4
  let _hm1 := ()
  let _u5 := _hm1
  pure (SudoRt.Flow.cont (ρ := Unit) deck)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2
    do
      let _t6 ← lay_cm deck
      let _t7 ← scoop_cm _t6
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 773
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 774
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_and_shift_rows_invert : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init30 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init30 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _t15 ← SudoRt.mulI i (17 : Int)
  let _t16 ← SudoRt.modI _t15 (52 : Int)
  let _mb17 := SudoRt.appendL deck _t16
  let ⟨_nr18, _⟩ := _mb17
  let deck := _nr18
  let _hm13 := ()
  let _u19 := _hm13
  pure (SudoRt.Flow.cont (ρ := Unit) deck)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2
    do
      let _t20 ← lay_cm deck
      let _t21 ← sum_ranks _t20
      let _t22 ← inv_sum_ranks _t21
      let _t23 ← scoop_cm _t22
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 780
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 781
      pure ()) (fun r => pure r))
    pure _out

def test_grid_cycle_inverts : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init40 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init40 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _t33 ← SudoRt.subI (51 : Int) i
  let _mb34 := SudoRt.appendL deck _t33
  let ⟨_nr35, _⟩ := _mb34
  let deck := _nr35
  let _hm31 := ()
  let _u36 := _hm31
  pure (SudoRt.Flow.cont (ρ := Unit) deck)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2
    do
      let _t37 ← mix_columns deck
      let _t38 ← inv_mix_columns _t37
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 787
      pure ()) (fun r => pure r))
    pure _out

def test_compose_inverts_and_passkey_keeps_the_deck : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let key := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init61 := (_fromV, (deck, key))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init61 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2.1
    let _sp59 := σ.2.2
    let key := _sp59
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (deck, key)))
      else
        match ← ((do
  let _mb44 := SudoRt.appendL deck i
  let ⟨_nr45, _⟩ := _mb44
  let deck := _nr45
  let _hm41 := ()
  let _u46 := _hm41
  let _t47 ← SudoRt.subI (51 : Int) i
  let _mb48 := SudoRt.appendL key _t47
  let ⟨_nr49, _⟩ := _mb48
  let key := _nr49
  let _hm42 := ()
  let _u50 := _hm42
  pure (SudoRt.Flow.cont (ρ := Unit) (deck, key))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2.1
    let _sp60 := σ.2.2
    let key := _sp60
    do
      let _t51 ← compose deck key
      let _t52 ← inverse_compose _t51 key
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 795
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 797
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 798
      pure ()) (fun r => pure r))
    pure _out

def test_passkey_inverse_is_a_two_sided_inverse : Except SudoRt.Trap Unit :=
  do
    let identity := (#[] : Array (Int))
    let reversed := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init105 := (_fromV, (identity, reversed))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init105 fuel (fun σ =>
    let i := σ.1
    let identity := σ.2.1
    let _sp103 := σ.2.2
    let reversed := _sp103
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (identity, reversed)))
      else
        match ← ((do
  let _mb65 := SudoRt.appendL identity i
  let ⟨_nr66, _⟩ := _mb65
  let identity := _nr66
  let _hm62 := ()
  let _u67 := _hm62
  let _t68 ← SudoRt.subI (51 : Int) i
  let _mb69 := SudoRt.appendL reversed _t68
  let ⟨_nr70, _⟩ := _mb69
  let reversed := _nr70
  let _hm63 := ()
  let _u71 := _hm63
  pure (SudoRt.Flow.cont (ρ := Unit) (identity, reversed))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let identity := σ.2.1
    let _sp104 := σ.2.2
    let reversed := _sp104
    do
      let mixed := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
      let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
      let _t72 ← passkey identity
      let _t73 ← passkey_inv _t72
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 808
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 809
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 810
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 811
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 812
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 813
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 814
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 815
      let built := key
      let _fromV := (1 : Int)
      let _toV := (6 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init102 := (_fromV, built)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init102 fuel (fun σ =>
    let r := σ.1
    let built := σ.2
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, built))
      else
        match ← ((do
  let _t97 ← passkey built
  let built := _t97
  pure (SudoRt.Flow.cont (ρ := Unit) built)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let built := σ.2
    do
      let _fromV := (1 : Int)
      let _toV := (6 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init101 := (_fromV, built)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init101 fuel (fun σ =>
    let r := σ.1
    let built := σ.2
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, built))
      else
        match ← ((do
  let _t99 ← passkey_inv built
  let built := _t99
  pure (SudoRt.Flow.cont (ρ := Unit) built)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let built := σ.2
    do
      let _as100 ← SudoRt.sudoAssertEq built key 821
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_sum_ranks_columns_read_suit : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init135 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init135 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _mb108 := SudoRt.appendL deck i
  let ⟨_nr109, _⟩ := _mb108
  let deck := _nr109
  let _hm106 := ()
  let _u110 := _hm106
  pure (SudoRt.Flow.cont (ρ := Unit) deck)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2
    do
      let _t111 ← lay_rm deck
      let _t112 ← sum_ranks _t111
      let g := _t112
      let _fromV := (0 : Int)
      let _toV := (12 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init134 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init134 fuel (fun σ =>
    let j := σ
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) j)
      else
        match ← ((do
  let _t114 ← SudoRt.atL g (0 : Int)
  let _t115 ← SudoRt.atL _t114 j
  let _t116 ← SudoRt.addI (26 : Int) j
  let _as117 ← SudoRt.sudoAssertEq _t115 _t116 833
  let _t118 ← SudoRt.atL g (1 : Int)
  let _t119 ← SudoRt.atL _t118 j
  let _t120 ← SudoRt.addI (39 : Int) j
  let _as121 ← SudoRt.sudoAssertEq _t119 _t120 834
  let _t122 ← SudoRt.atL g (2 : Int)
  let _t123 ← SudoRt.atL _t122 j
  let _as124 ← SudoRt.sudoAssertEq _t123 j 835
  let _t125 ← SudoRt.atL g (3 : Int)
  let _t126 ← SudoRt.atL _t125 j
  let _t127 ← SudoRt.addI (13 : Int) j
  let _as128 ← SudoRt.sudoAssertEq _t126 _t127 836
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
      let _t129 ← column_weight (51 : Int)
      let _as130 ← SudoRt.sudoAssertEq _t129 (16 : Int) 837
      let _t131 ← inv_sum_ranks g
      let _t132 ← lay_rm deck
      let _as133 ← SudoRt.sudoAssertEq _t131 _t132 838
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_overflow_scan_starts_at_the_blocked_column : Except SudoRt.Trap Unit :=
  do
    let occ := (#[] : Array (Array (Int)))
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init171 := (_fromV, occ)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init171 fuel (fun σ =>
    let r := σ.1
    let occ := σ.2
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, occ))
      else
        match ← ((do
  let marks := (#[] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (12 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init155 := (_fromV, marks)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init155 fuel (fun σ =>
    let c := σ.1
    let marks := σ.2
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (c, marks))
      else
        match ← ((do
  let _t142 ← (if (SudoRt.SEq.beq r (1 : Int)) then (do
  let _t144 ← (if (SudoRt.SEq.beq c (2 : Int)) then pure true else (do
  pure (SudoRt.SEq.beq c (7 : Int))))
  pure _t144) else pure false)
  if _t142 then
    do
      let _mb146 := SudoRt.appendL marks (0 : Int)
      let ⟨_nr147, _⟩ := _mb146
      let marks := _nr147
      let _hm136 := ()
      let _u148 := _hm136
      pure (SudoRt.Flow.cont (ρ := Unit) marks)
  else
    do
      let _mb149 := SudoRt.appendL marks (1 : Int)
      let ⟨_nr150, _⟩ := _mb149
      let marks := _nr150
      let _hm137 := ()
      let _u151 := _hm137
      pure (SudoRt.Flow.cont (ρ := Unit) marks)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (c, _fs))
        | .cont _fs => do
            if c == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (c, _fs))
            else do
              let i' ← SudoRt.addI c (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let marks := σ.2
    do
      let _mb152 := SudoRt.appendL occ marks
      let ⟨_nr153, _⟩ := _mb152
      let occ := _nr153
      let _hm138 := ()
      let _u154 := _hm138
      pure (SudoRt.Flow.cont (ρ := Unit) occ)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let occ := σ.2
    do
      let _t156 ← scan_row occ (1 : Int) (5 : Int)
      let _as157 ← SudoRt.sudoAssertEq _t156 (7 : Int) 852
      let _t158 ← scan_row occ (1 : Int) (8 : Int)
      let _as159 ← SudoRt.sudoAssertEq _t158 (2 : Int) 853
      let _t160 ← scan_row occ (0 : Int) (5 : Int)
      let _t161 ← SudoRt.negI (1 : Int)
      let _as162 ← SudoRt.sudoAssertEq _t160 _t161 854
      let _t163 ← overflow_seat occ (1 : Int) (5 : Int)
      let ⟨r, c, t⟩ := _t163
      let _as164 ← SudoRt.sudoAssertEq r (1 : Int) 856
      let _as165 ← SudoRt.sudoAssertEq c (7 : Int) 857
      let _as166 ← SudoRt.sudoAssertEq t (2 : Int) 858
      let _t167 ← overflow_seat occ (0 : Int) (5 : Int)
      let ⟨r2, c2, t2⟩ := _t167
      let _as168 ← SudoRt.sudoAssertEq r2 (1 : Int) 860
      let _as169 ← SudoRt.sudoAssertEq c2 (7 : Int) 861
      let _as170 ← SudoRt.sudoAssertEq t2 (2 : Int) 862
      pure ()) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(25 : Int), (31 : Int), (24 : Int), (6 : Int), (36 : Int), (26 : Int), (40 : Int), (9 : Int), (44 : Int), (10 : Int), (28 : Int), (23 : Int), (50 : Int), (7 : Int), (22 : Int), (45 : Int), (11 : Int), (46 : Int), (39 : Int), (27 : Int), (43 : Int), (29 : Int), (5 : Int), (48 : Int), (3 : Int), (42 : Int), (17 : Int), (37 : Int), (35 : Int), (49 : Int), (15 : Int), (2 : Int), (34 : Int), (51 : Int), (20 : Int), (8 : Int), (41 : Int), (14 : Int), (32 : Int), (16 : Int), (47 : Int), (19 : Int), (33 : Int), (21 : Int), (0 : Int), (38 : Int), (30 : Int), (12 : Int), (4 : Int), (1 : Int), (18 : Int), (13 : Int)] : Array (Int))
    let _t172 ← encrypt message key
    let _as173 ← SudoRt.sudoAssertEq _t172 cipher 868
    let _t174 ← decrypt cipher key
    let _as175 ← SudoRt.sudoAssertEq _t174 message 869
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t176 ← encrypt message key
    let cipher := _t176
    let _t177 ← expand_keys key
    let keys := _t177
    let _t178 ← SudoRt.atL keys (6 : Int)
    let _t179 ← inv_final_round cipher _t178
    let listed := _t179
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init188 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init188 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t181 ← SudoRt.atL keys r
  let _t182 ← inv_full_round listed _t181
  let listed := _t182
  pure (SudoRt.Flow.cont (ρ := Unit) listed)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.subI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let listed := σ.2
    do
      let _t183 ← SudoRt.atL keys (0 : Int)
      let _t184 ← inverse_compose listed _t183
      let listed := _t184
      let _t185 ← decrypt cipher key
      let _as186 ← SudoRt.sudoAssertEq listed _t185 880
      let _as187 ← SudoRt.sudoAssertEq listed message 881
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t189 ← trace_encrypt message key
    let traced := _t189
    let _t191 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t192 ← SudoRt.atL traced _t191
    let last := _t192
    let _t193 ← encrypt message key
    let _as194 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t193 888
    let _as195 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 889
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t237 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t237
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init245 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init245 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp241 := σ.2.2
    let held := _sp241.1
    let _sp242 := _sp241.2
    let passes := _sp242
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t197 ← SudoRt.atL traced n
  let _t199 ← (if (SudoRt.SEq.beq (_t197).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t200 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t200).sudo_4Step_3row (2 : Int))) else pure false)
  let _t202 ← (if _t199 then (do
  let _t203 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t203).sudo_4Step_3col (0 : Int))) else pure false)
  if _t202 then
    do
      let _t205 ← SudoRt.addI marked (1 : Int)
      let marked := _t205
      let _t206 ← SudoRt.atL traced n
      let _t208 ← (if (SudoRt.SEq.beq (_t206).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t209 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t209).sudo_4Step_3row (0 : Int))) else pure false)
      let _t211 ← (if _t208 then (do
  let _t212 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t212).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t211 then
        do
          let _t214 ← SudoRt.addI held (1 : Int)
          let held := _t214
          let _t215 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t215).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t217 ← SudoRt.addI passes (1 : Int)
              let passes := _t217
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t218 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t218).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t220 ← SudoRt.addI passes (1 : Int)
              let passes := _t220
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t221 ← SudoRt.atL traced n
      let _t223 ← (if (SudoRt.SEq.beq (_t221).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t224 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t224).sudo_4Step_3row (0 : Int))) else pure false)
      let _t226 ← (if _t223 then (do
  let _t227 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t227).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t226 then
        do
          let _t229 ← SudoRt.addI held (1 : Int)
          let held := _t229
          let _t230 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t230).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t232 ← SudoRt.addI passes (1 : Int)
              let passes := _t232
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t233 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t233).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t235 ← SudoRt.addI passes (1 : Int)
              let passes := _t235
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (n, _fs))
        | .cont _fs => do
            if n == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (n, _fs))
            else do
              let i' ← SudoRt.addI n (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let marked := σ.2.1
    let _sp243 := σ.2.2
    let held := _sp243.1
    let _sp244 := _sp243.2
    let passes := _sp244
    do
      let _as238 ← SudoRt.sudoAssertEq marked (5 : Int) 900
      let _as239 ← SudoRt.sudoAssertEq held (6 : Int) 901
      let _as240 ← SudoRt.sudoAssertEq passes (312 : Int) 902
      pure ()) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init267 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init267 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb248 := SudoRt.appendL nonce i
  let ⟨_nr249, _⟩ := _mb248
  let nonce := _nr249
  let _hm246 := ()
  let _u250 := _hm246
  pure (SudoRt.Flow.cont (ρ := Unit) nonce)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let nonce := σ.2
    do
      let _t251 ← counter_deck nonce (0 : Int)
      let a := _t251
      let _t252 ← counter_deck nonce (1 : Int)
      let b := _t252
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init266 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init266 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t254 ← SudoRt.atL a i
  let _as255 ← SudoRt.sudoAssertEq _t254 i 976
  let _t256 ← SudoRt.atL b i
  let _as257 ← SudoRt.sudoAssertEq _t256 i 977
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
      let _t258 ← SudoRt.atL a (50 : Int)
      let _as259 ← SudoRt.sudoAssertEq _t258 (50 : Int) 978
      let _t260 ← SudoRt.atL a (51 : Int)
      let _as261 ← SudoRt.sudoAssertEq _t260 (51 : Int) 979
      let _t262 ← SudoRt.atL b (50 : Int)
      let _as263 ← SudoRt.sudoAssertEq _t262 (51 : Int) 980
      let _t264 ← SudoRt.atL b (51 : Int)
      let _as265 ← SudoRt.sudoAssertEq _t264 (50 : Int) 981
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb271 := SudoRt.appendL blocks block
    let ⟨_nr272, _⟩ := _mb271
    let blocks := _nr272
    let _hm268 := ()
    let _u273 := _hm268
    let _mb274 := SudoRt.appendL blocks block
    let ⟨_nr275, _⟩ := _mb274
    let blocks := _nr275
    let _hm269 := ()
    let _u276 := _hm269
    let _t277 ← ecb_encrypt blocks key
    let ecb := _t277
    let _t278 ← SudoRt.atL ecb (0 : Int)
    let _t279 ← SudoRt.atL ecb (1 : Int)
    let _as280 ← SudoRt.sudoAssertEq _t278 _t279 990
    let _t281 ← ecb_decrypt ecb key
    let _as282 ← SudoRt.sudoAssertEq _t281 blocks 991
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init295 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init295 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t284 ← SudoRt.subI (38 : Int) i
  let _mb285 := SudoRt.appendL nonce _t284
  let ⟨_nr286, _⟩ := _mb285
  let nonce := _nr286
  let _hm270 := ()
  let _u287 := _hm270
  pure (SudoRt.Flow.cont (ρ := Unit) nonce)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let nonce := σ.2
    do
      let _t288 ← ctr_encrypt blocks key nonce
      let ctr := _t288
      let _t289 ← SudoRt.atL ctr (0 : Int)
      let _t290 ← SudoRt.atL ctr (1 : Int)
      let _as292 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t289 _t290)) 996
      let _t293 ← ctr_decrypt ctr key nonce
      let _as294 ← SudoRt.sudoAssertEq _t293 blocks 997
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_sum_ranks_columns_read_suit", fun _ => test_sum_ranks_columns_read_suit), ("test_overflow_scan_starts_at_the_blocked_column", fun _ => test_overflow_scan_starts_at_the_blocked_column), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
