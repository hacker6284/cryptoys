-- DO NOT EDIT. Generated from doubledeal_v11.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for doubledeal_v11.sudo
import SudoRt
import Doubledeal_v11
set_option linter.unusedVariables false
open Doubledeal_v11

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
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 831
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 832
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
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 838
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 839
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
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 845
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
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 853
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 855
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 856
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
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 866
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 867
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 868
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 869
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 870
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 871
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 872
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 873
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
      let _as100 ← SudoRt.sudoAssertEq built key 879
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_suit_labels_add_and_multiply_in_gf_4 : Except SudoRt.Trap Unit :=
  do
    let _t106 ← suit_label (0 : Int)
    let _as107 ← SudoRt.sudoAssertEq _t106 (0 : Int) 883
    let _t108 ← suit_label (13 : Int)
    let _as109 ← SudoRt.sudoAssertEq _t108 (2 : Int) 884
    let _t110 ← suit_label (26 : Int)
    let _as111 ← SudoRt.sudoAssertEq _t110 (3 : Int) 885
    let _t112 ← suit_label (51 : Int)
    let _as113 ← SudoRt.sudoAssertEq _t112 (1 : Int) 886
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init137 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init137 fuel (fun σ =>
    let x := σ
    do
      if x > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) x)
      else
        match ← ((do
  let _t115 ← gf_add x x
  let _as116 ← SudoRt.sudoAssertEq _t115 (0 : Int) 888
  let _t117 ← gf_add (0 : Int) x
  let _as118 ← SudoRt.sudoAssertEq _t117 x 889
  let _t119 ← gf_times_w x
  let _t120 ← gf_times_w _t119
  let _t121 ← gf_times_w _t120
  let _as122 ← SudoRt.sudoAssertEq _t121 x 890
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) x)
        | .cont _fs => do
            if x == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) x)
            else do
              let i' ← SudoRt.addI x (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _t123 ← gf_add (1 : Int) (2 : Int)
      let _as124 ← SudoRt.sudoAssertEq _t123 (3 : Int) 891
      let _t125 ← gf_add (2 : Int) (3 : Int)
      let _as126 ← SudoRt.sudoAssertEq _t125 (1 : Int) 892
      let _t127 ← gf_add (3 : Int) (1 : Int)
      let _as128 ← SudoRt.sudoAssertEq _t127 (2 : Int) 893
      let _t129 ← gf_times_w (0 : Int)
      let _as130 ← SudoRt.sudoAssertEq _t129 (0 : Int) 894
      let _t131 ← gf_times_w (1 : Int)
      let _as132 ← SudoRt.sudoAssertEq _t131 (2 : Int) 895
      let _t133 ← gf_times_w (2 : Int)
      let _as134 ← SudoRt.sudoAssertEq _t133 (3 : Int) 896
      let _t135 ← gf_times_w (3 : Int)
      let _as136 ← SudoRt.sudoAssertEq _t135 (1 : Int) 897
      pure ()) (fun r => pure r))
    pure _out

def test_row_total_is_the_two_running_totals : Except SudoRt.Trap Unit :=
  do
    let row := (#[(5 : Int), (30 : Int), (12 : Int), (44 : Int), (0 : Int), (19 : Int), (38 : Int), (7 : Int), (25 : Int), (51 : Int), (13 : Int), (2 : Int), (33 : Int)] : Array (Int))
    let t := (0 : Int)
    let u := (0 : Int)
    let _fromV := (0 : Int)
    let _toV := (12 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init150 := (_fromV, (t, u))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init150 fuel (fun σ =>
    let j := σ.1
    let t := σ.2.1
    let _sp148 := σ.2.2
    let u := _sp148
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (t, u)))
      else
        match ← ((do
  let _t139 ← SudoRt.atL row j
  let _t140 ← rank_of _t139
  let _t141 ← SudoRt.addI t _t140
  let t := _t141
  let _t142 ← SudoRt.addI u t
  let u := _t142
  pure (SudoRt.Flow.cont (ρ := Unit) (t, u))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let t := σ.2.1
    let _sp149 := σ.2.2
    let u := _sp149
    do
      let _t143 ← row_total row
      let _as144 ← SudoRt.sudoAssertEq _t143 u 906
      let _t145 ← row_turn row
      let _t146 ← SudoRt.modI u (13 : Int)
      let _as147 ← SudoRt.sudoAssertEq _t145 _t146 907
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_leaves_whole_suit_rows_alone : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init168 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init168 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _mb153 := SudoRt.appendL deck i
  let ⟨_nr154, _⟩ := _mb153
  let deck := _nr154
  let _hm151 := ()
  let _u155 := _hm151
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
      let _t156 ← lay_rm deck
      let g := _t156
      let _t157 ← SudoRt.atL g (0 : Int)
      let _t158 ← row_total _t157
      let _as159 ← SudoRt.sudoAssertEq _t158 (455 : Int) 918
      let _t160 ← column_value g (12 : Int)
      let _as161 ← SudoRt.sudoAssertEq _t160 (0 : Int) 919
      let _t162 ← column_suits g (0 : Int)
      let _as163 ← SudoRt.sudoAssertEq _t162 (0 : Int) 920
      let _t164 ← sum_ranks g
      let _as165 ← SudoRt.sudoAssertEq _t164 g 921
      let _t166 ← inv_sum_ranks g
      let _as167 ← SudoRt.sudoAssertEq _t166 g 922
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_sees_a_k_q_swap_that_v9_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(16 : Int), (10 : Int), (36 : Int), (14 : Int), (8 : Int), (41 : Int), (0 : Int), (45 : Int), (51 : Int), (7 : Int), (28 : Int), (26 : Int), (24 : Int), (11 : Int), (3 : Int), (39 : Int), (12 : Int), (35 : Int), (43 : Int), (1 : Int), (50 : Int), (15 : Int), (30 : Int), (22 : Int), (38 : Int), (4 : Int), (31 : Int), (44 : Int), (25 : Int), (33 : Int), (48 : Int), (20 : Int), (19 : Int), (42 : Int), (34 : Int), (17 : Int), (40 : Int), (9 : Int), (46 : Int), (32 : Int), (21 : Int), (13 : Int), (5 : Int), (27 : Int), (2 : Int), (18 : Int), (23 : Int), (47 : Int), (37 : Int), (6 : Int), (29 : Int), (49 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init196 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init196 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t172 ← SudoRt.atL deck k
  let _t173 ← swap_card _t172 (12 : Int) (24 : Int)
  let _mb174 := SudoRt.appendL swapped _t173
  let ⟨_nr175, _⟩ := _mb174
  let swapped := _nr175
  let _hm169 := ()
  let _u176 := _hm169
  pure (SudoRt.Flow.cont (ρ := Unit) swapped)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let swapped := σ.2
    do
      let _t177 ← lay_cm deck
      let _t178 ← sum_ranks _t177
      let _t179 ← scoop_cm _t178
      let out := _t179
      let _t180 ← lay_cm swapped
      let _t181 ← sum_ranks _t180
      let _t182 ← scoop_cm _t181
      let out_swapped := _t182
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init195 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init195 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t184 ← SudoRt.atL out k
  let _t185 ← swap_card _t184 (12 : Int) (24 : Int)
  let _mb186 := SudoRt.appendL relabelled _t185
  let ⟨_nr187, _⟩ := _mb186
  let relabelled := _nr187
  let _hm170 := ()
  let _u188 := _hm170
  pure (SudoRt.Flow.cont (ρ := Unit) relabelled)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let relabelled := σ.2
    do
      let _as190 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 936
      let _t191 ← lay_cm out_swapped
      let _t192 ← inv_sum_ranks _t191
      let _t193 ← scoop_cm _t192
      let _as194 ← SudoRt.sudoAssertEq _t193 swapped 937
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_overflow_scan_drops_a_row_when_the_row_is_full : Except SudoRt.Trap Unit :=
  do
    let occ := (#[] : Array (Array (Int)))
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init230 := (_fromV, occ)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init230 fuel (fun σ =>
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
  let _init216 := (_fromV, marks)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init216 fuel (fun σ =>
    let c := σ.1
    let marks := σ.2
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (c, marks))
      else
        match ← ((do
  let _t203 ← (if (SudoRt.SEq.beq r (1 : Int)) then (do
  let _t205 ← (if (SudoRt.SEq.beq c (2 : Int)) then pure true else (do
  pure (SudoRt.SEq.beq c (7 : Int))))
  pure _t205) else pure false)
  if _t203 then
    do
      let _mb207 := SudoRt.appendL marks (0 : Int)
      let ⟨_nr208, _⟩ := _mb207
      let marks := _nr208
      let _hm197 := ()
      let _u209 := _hm197
      pure (SudoRt.Flow.cont (ρ := Unit) marks)
  else
    do
      let _mb210 := SudoRt.appendL marks (1 : Int)
      let ⟨_nr211, _⟩ := _mb210
      let marks := _nr211
      let _hm198 := ()
      let _u212 := _hm198
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
      let _mb213 := SudoRt.appendL occ marks
      let ⟨_nr214, _⟩ := _mb213
      let occ := _nr214
      let _hm199 := ()
      let _u215 := _hm199
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
      let _t217 ← scan_row occ (1 : Int) (5 : Int)
      let _as218 ← SudoRt.sudoAssertEq _t217 (7 : Int) 952
      let _t219 ← scan_row occ (1 : Int) (8 : Int)
      let _as220 ← SudoRt.sudoAssertEq _t219 (2 : Int) 953
      let _t221 ← scan_row occ (0 : Int) (5 : Int)
      let _t222 ← SudoRt.negI (1 : Int)
      let _as223 ← SudoRt.sudoAssertEq _t221 _t222 954
      let _t224 ← overflow_seat occ (1 : Int) (5 : Int)
      let ⟨r, c⟩ := _t224
      let _as225 ← SudoRt.sudoAssertEq r (1 : Int) 956
      let _as226 ← SudoRt.sudoAssertEq c (7 : Int) 957
      let _t227 ← overflow_seat occ (3 : Int) (8 : Int)
      let ⟨r2, c2⟩ := _t227
      let _as228 ← SudoRt.sudoAssertEq r2 (1 : Int) 959
      let _as229 ← SudoRt.sudoAssertEq c2 (2 : Int) 960
      pure ()) (fun r => pure r))
    pure _out

def test_the_finger_stays_on_the_target_after_a_block : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(12 : Int), (13 : Int), (0 : Int)] : Array (Int))
    let _fromV := (1 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init248 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init248 fuel (fun σ =>
    let k := σ.1
    let deck := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, deck))
      else
        match ← ((do
  let _t234 ← (if (!(SudoRt.SEq.beq k (12 : Int))) then (do
  pure (!(SudoRt.SEq.beq k (13 : Int)))) else pure false)
  if _t234 then
    do
      let _mb236 := SudoRt.appendL deck k
      let ⟨_nr237, _⟩ := _mb236
      let deck := _nr237
      let _hm231 := ()
      let _u238 := _hm231
      pure (SudoRt.Flow.cont (ρ := Unit) deck)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) deck)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deck := σ.2
    do
      let _t239 ← mix_columns deck
      let out := _t239
      let _t240 ← SudoRt.atL out (26 : Int)
      let _as241 ← SudoRt.sudoAssertEq _t240 (12 : Int) 973
      let _t242 ← SudoRt.atL out (0 : Int)
      let _as243 ← SudoRt.sudoAssertEq _t242 (13 : Int) 974
      let _t244 ← SudoRt.atL out (40 : Int)
      let _as245 ← SudoRt.sudoAssertEq _t244 (0 : Int) 975
      let _t246 ← inv_mix_columns out
      let _as247 ← SudoRt.sudoAssertEq _t246 deck 976
      pure ()) (fun r => pure r))
    pure _out

def test_grid_cycle_sees_the_k_k_swap_that_v10_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(32 : Int), (23 : Int), (6 : Int), (21 : Int), (13 : Int), (31 : Int), (9 : Int), (37 : Int), (16 : Int), (22 : Int), (30 : Int), (19 : Int), (38 : Int), (41 : Int), (25 : Int), (51 : Int), (17 : Int), (50 : Int), (39 : Int), (2 : Int), (36 : Int), (15 : Int), (28 : Int), (20 : Int), (12 : Int), (45 : Int), (5 : Int), (33 : Int), (29 : Int), (14 : Int), (18 : Int), (40 : Int), (34 : Int), (10 : Int), (44 : Int), (26 : Int), (42 : Int), (27 : Int), (47 : Int), (4 : Int), (24 : Int), (46 : Int), (11 : Int), (43 : Int), (3 : Int), (49 : Int), (7 : Int), (0 : Int), (8 : Int), (1 : Int), (48 : Int), (35 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init270 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init270 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t252 ← SudoRt.atL deck k
  let _t253 ← swap_card _t252 (12 : Int) (51 : Int)
  let _mb254 := SudoRt.appendL swapped _t253
  let ⟨_nr255, _⟩ := _mb254
  let swapped := _nr255
  let _hm249 := ()
  let _u256 := _hm249
  pure (SudoRt.Flow.cont (ρ := Unit) swapped)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let swapped := σ.2
    do
      let _t257 ← mix_columns deck
      let out := _t257
      let _t258 ← mix_columns swapped
      let out_swapped := _t258
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init269 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init269 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t260 ← SudoRt.atL out k
  let _t261 ← swap_card _t260 (12 : Int) (51 : Int)
  let _mb262 := SudoRt.appendL relabelled _t261
  let ⟨_nr263, _⟩ := _mb262
  let relabelled := _nr263
  let _hm250 := ()
  let _u264 := _hm250
  pure (SudoRt.Flow.cont (ρ := Unit) relabelled)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let relabelled := σ.2
    do
      let _as266 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 990
      let _t267 ← inv_mix_columns out_swapped
      let _as268 ← SudoRt.sudoAssertEq _t267 swapped 991
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(19 : Int), (39 : Int), (37 : Int), (16 : Int), (40 : Int), (15 : Int), (25 : Int), (30 : Int), (5 : Int), (6 : Int), (22 : Int), (9 : Int), (42 : Int), (23 : Int), (51 : Int), (21 : Int), (31 : Int), (47 : Int), (28 : Int), (24 : Int), (48 : Int), (38 : Int), (29 : Int), (2 : Int), (50 : Int), (20 : Int), (11 : Int), (41 : Int), (18 : Int), (12 : Int), (32 : Int), (44 : Int), (17 : Int), (7 : Int), (35 : Int), (49 : Int), (36 : Int), (34 : Int), (13 : Int), (33 : Int), (1 : Int), (43 : Int), (0 : Int), (46 : Int), (4 : Int), (10 : Int), (8 : Int), (14 : Int), (27 : Int), (26 : Int), (3 : Int), (45 : Int)] : Array (Int))
    let _t271 ← encrypt message key
    let _as272 ← SudoRt.sudoAssertEq _t271 cipher 997
    let _t273 ← decrypt cipher key
    let _as274 ← SudoRt.sudoAssertEq _t273 message 998
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t275 ← encrypt message key
    let cipher := _t275
    let _t276 ← expand_keys key
    let keys := _t276
    let _t277 ← SudoRt.atL keys (6 : Int)
    let _t278 ← inv_final_round cipher _t277
    let listed := _t278
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init287 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init287 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t280 ← SudoRt.atL keys r
  let _t281 ← inv_full_round listed _t280
  let listed := _t281
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
      let _t282 ← SudoRt.atL keys (0 : Int)
      let _t283 ← inverse_compose listed _t282
      let listed := _t283
      let _t284 ← decrypt cipher key
      let _as285 ← SudoRt.sudoAssertEq listed _t284 1009
      let _as286 ← SudoRt.sudoAssertEq listed message 1010
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t288 ← trace_encrypt message key
    let traced := _t288
    let _t290 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t291 ← SudoRt.atL traced _t290
    let last := _t291
    let _t292 ← encrypt message key
    let _as293 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t292 1017
    let _as294 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 1018
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t336 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t336
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init344 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init344 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp340 := σ.2.2
    let held := _sp340.1
    let _sp341 := _sp340.2
    let passes := _sp341
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t296 ← SudoRt.atL traced n
  let _t298 ← (if (SudoRt.SEq.beq (_t296).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t299 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t299).sudo_4Step_3row (2 : Int))) else pure false)
  let _t301 ← (if _t298 then (do
  let _t302 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t302).sudo_4Step_3col (0 : Int))) else pure false)
  if _t301 then
    do
      let _t304 ← SudoRt.addI marked (1 : Int)
      let marked := _t304
      let _t305 ← SudoRt.atL traced n
      let _t307 ← (if (SudoRt.SEq.beq (_t305).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t308 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t308).sudo_4Step_3row (0 : Int))) else pure false)
      let _t310 ← (if _t307 then (do
  let _t311 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t311).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t310 then
        do
          let _t313 ← SudoRt.addI held (1 : Int)
          let held := _t313
          let _t314 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t314).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t316 ← SudoRt.addI passes (1 : Int)
              let passes := _t316
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t317 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t317).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t319 ← SudoRt.addI passes (1 : Int)
              let passes := _t319
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t320 ← SudoRt.atL traced n
      let _t322 ← (if (SudoRt.SEq.beq (_t320).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t323 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t323).sudo_4Step_3row (0 : Int))) else pure false)
      let _t325 ← (if _t322 then (do
  let _t326 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t326).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t325 then
        do
          let _t328 ← SudoRt.addI held (1 : Int)
          let held := _t328
          let _t329 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t329).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t331 ← SudoRt.addI passes (1 : Int)
              let passes := _t331
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t332 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t332).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t334 ← SudoRt.addI passes (1 : Int)
              let passes := _t334
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
    let _sp342 := σ.2.2
    let held := _sp342.1
    let _sp343 := _sp342.2
    let passes := _sp343
    do
      let _as337 ← SudoRt.sudoAssertEq marked (5 : Int) 1029
      let _as338 ← SudoRt.sudoAssertEq held (6 : Int) 1030
      let _as339 ← SudoRt.sudoAssertEq passes (312 : Int) 1031
      pure ()) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init366 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init366 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb347 := SudoRt.appendL nonce i
  let ⟨_nr348, _⟩ := _mb347
  let nonce := _nr348
  let _hm345 := ()
  let _u349 := _hm345
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
      let _t350 ← counter_deck nonce (0 : Int)
      let a := _t350
      let _t351 ← counter_deck nonce (1 : Int)
      let b := _t351
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init365 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init365 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t353 ← SudoRt.atL a i
  let _as354 ← SudoRt.sudoAssertEq _t353 i 1107
  let _t355 ← SudoRt.atL b i
  let _as356 ← SudoRt.sudoAssertEq _t355 i 1108
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
      let _t357 ← SudoRt.atL a (50 : Int)
      let _as358 ← SudoRt.sudoAssertEq _t357 (50 : Int) 1109
      let _t359 ← SudoRt.atL a (51 : Int)
      let _as360 ← SudoRt.sudoAssertEq _t359 (51 : Int) 1110
      let _t361 ← SudoRt.atL b (50 : Int)
      let _as362 ← SudoRt.sudoAssertEq _t361 (51 : Int) 1111
      let _t363 ← SudoRt.atL b (51 : Int)
      let _as364 ← SudoRt.sudoAssertEq _t363 (50 : Int) 1112
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb370 := SudoRt.appendL blocks block
    let ⟨_nr371, _⟩ := _mb370
    let blocks := _nr371
    let _hm367 := ()
    let _u372 := _hm367
    let _mb373 := SudoRt.appendL blocks block
    let ⟨_nr374, _⟩ := _mb373
    let blocks := _nr374
    let _hm368 := ()
    let _u375 := _hm368
    let _t376 ← ecb_encrypt blocks key
    let ecb := _t376
    let _t377 ← SudoRt.atL ecb (0 : Int)
    let _t378 ← SudoRt.atL ecb (1 : Int)
    let _as379 ← SudoRt.sudoAssertEq _t377 _t378 1121
    let _t380 ← ecb_decrypt ecb key
    let _as381 ← SudoRt.sudoAssertEq _t380 blocks 1122
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init394 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init394 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t383 ← SudoRt.subI (38 : Int) i
  let _mb384 := SudoRt.appendL nonce _t383
  let ⟨_nr385, _⟩ := _mb384
  let nonce := _nr385
  let _hm369 := ()
  let _u386 := _hm369
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
      let _t387 ← ctr_encrypt blocks key nonce
      let ctr := _t387
      let _t388 ← SudoRt.atL ctr (0 : Int)
      let _t389 ← SudoRt.atL ctr (1 : Int)
      let _as391 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t388 _t389)) 1127
      let _t392 ← ctr_decrypt ctr key nonce
      let _as393 ← SudoRt.sudoAssertEq _t392 blocks 1128
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_suit_labels_add_and_multiply_in_gf_4", fun _ => test_suit_labels_add_and_multiply_in_gf_4), ("test_row_total_is_the_two_running_totals", fun _ => test_row_total_is_the_two_running_totals), ("test_sum_ranks_leaves_whole_suit_rows_alone", fun _ => test_sum_ranks_leaves_whole_suit_rows_alone), ("test_sum_ranks_sees_a_k_q_swap_that_v9_missed", fun _ => test_sum_ranks_sees_a_k_q_swap_that_v9_missed), ("test_overflow_scan_drops_a_row_when_the_row_is_full", fun _ => test_overflow_scan_drops_a_row_when_the_row_is_full), ("test_the_finger_stays_on_the_target_after_a_block", fun _ => test_the_finger_stays_on_the_target_after_a_block), ("test_grid_cycle_sees_the_k_k_swap_that_v10_missed", fun _ => test_grid_cycle_sees_the_k_k_swap_that_v10_missed), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
