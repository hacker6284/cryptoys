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
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 809
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 810
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
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 816
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 817
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
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 823
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
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 831
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 833
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 834
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
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 844
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 845
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 846
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 847
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 848
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 849
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 850
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 851
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
      let _as100 ← SudoRt.sudoAssertEq built key 857
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_suit_labels_add_and_multiply_in_gf_4 : Except SudoRt.Trap Unit :=
  do
    let _t106 ← suit_label (0 : Int)
    let _as107 ← SudoRt.sudoAssertEq _t106 (0 : Int) 861
    let _t108 ← suit_label (13 : Int)
    let _as109 ← SudoRt.sudoAssertEq _t108 (2 : Int) 862
    let _t110 ← suit_label (26 : Int)
    let _as111 ← SudoRt.sudoAssertEq _t110 (3 : Int) 863
    let _t112 ← suit_label (51 : Int)
    let _as113 ← SudoRt.sudoAssertEq _t112 (1 : Int) 864
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
  let _as116 ← SudoRt.sudoAssertEq _t115 (0 : Int) 866
  let _t117 ← gf_add (0 : Int) x
  let _as118 ← SudoRt.sudoAssertEq _t117 x 867
  let _t119 ← gf_times_w x
  let _t120 ← gf_times_w _t119
  let _t121 ← gf_times_w _t120
  let _as122 ← SudoRt.sudoAssertEq _t121 x 868
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
      let _as124 ← SudoRt.sudoAssertEq _t123 (3 : Int) 869
      let _t125 ← gf_add (2 : Int) (3 : Int)
      let _as126 ← SudoRt.sudoAssertEq _t125 (1 : Int) 870
      let _t127 ← gf_add (3 : Int) (1 : Int)
      let _as128 ← SudoRt.sudoAssertEq _t127 (2 : Int) 871
      let _t129 ← gf_times_w (0 : Int)
      let _as130 ← SudoRt.sudoAssertEq _t129 (0 : Int) 872
      let _t131 ← gf_times_w (1 : Int)
      let _as132 ← SudoRt.sudoAssertEq _t131 (2 : Int) 873
      let _t133 ← gf_times_w (2 : Int)
      let _as134 ← SudoRt.sudoAssertEq _t133 (3 : Int) 874
      let _t135 ← gf_times_w (3 : Int)
      let _as136 ← SudoRt.sudoAssertEq _t135 (1 : Int) 875
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
      let _as144 ← SudoRt.sudoAssertEq _t143 u 884
      let _t145 ← row_turn row
      let _t146 ← SudoRt.modI u (13 : Int)
      let _as147 ← SudoRt.sudoAssertEq _t145 _t146 885
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
      let _as159 ← SudoRt.sudoAssertEq _t158 (455 : Int) 896
      let _t160 ← column_value g (12 : Int)
      let _as161 ← SudoRt.sudoAssertEq _t160 (0 : Int) 897
      let _t162 ← column_suits g (0 : Int)
      let _as163 ← SudoRt.sudoAssertEq _t162 (0 : Int) 898
      let _t164 ← sum_ranks g
      let _as165 ← SudoRt.sudoAssertEq _t164 g 899
      let _t166 ← inv_sum_ranks g
      let _as167 ← SudoRt.sudoAssertEq _t166 g 900
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
      let _as190 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 914
      let _t191 ← lay_cm out_swapped
      let _t192 ← inv_sum_ranks _t191
      let _t193 ← scoop_cm _t192
      let _as194 ← SudoRt.sudoAssertEq _t193 swapped 915
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_overflow_scan_starts_at_the_blocked_column : Except SudoRt.Trap Unit :=
  do
    let occ := (#[] : Array (Array (Int)))
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init232 := (_fromV, occ)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init232 fuel (fun σ =>
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
      let _as218 ← SudoRt.sudoAssertEq _t217 (7 : Int) 929
      let _t219 ← scan_row occ (1 : Int) (8 : Int)
      let _as220 ← SudoRt.sudoAssertEq _t219 (2 : Int) 930
      let _t221 ← scan_row occ (0 : Int) (5 : Int)
      let _t222 ← SudoRt.negI (1 : Int)
      let _as223 ← SudoRt.sudoAssertEq _t221 _t222 931
      let _t224 ← overflow_seat occ (1 : Int) (5 : Int)
      let ⟨r, c, t⟩ := _t224
      let _as225 ← SudoRt.sudoAssertEq r (1 : Int) 933
      let _as226 ← SudoRt.sudoAssertEq c (7 : Int) 934
      let _as227 ← SudoRt.sudoAssertEq t (2 : Int) 935
      let _t228 ← overflow_seat occ (0 : Int) (5 : Int)
      let ⟨r2, c2, t2⟩ := _t228
      let _as229 ← SudoRt.sudoAssertEq r2 (1 : Int) 937
      let _as230 ← SudoRt.sudoAssertEq c2 (7 : Int) 938
      let _as231 ← SudoRt.sudoAssertEq t2 (2 : Int) 939
      pure ()) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(37 : Int), (19 : Int), (15 : Int), (33 : Int), (31 : Int), (13 : Int), (46 : Int), (4 : Int), (48 : Int), (8 : Int), (24 : Int), (43 : Int), (45 : Int), (0 : Int), (3 : Int), (18 : Int), (7 : Int), (44 : Int), (32 : Int), (10 : Int), (35 : Int), (51 : Int), (42 : Int), (41 : Int), (29 : Int), (40 : Int), (20 : Int), (23 : Int), (12 : Int), (26 : Int), (36 : Int), (27 : Int), (34 : Int), (1 : Int), (9 : Int), (6 : Int), (49 : Int), (39 : Int), (50 : Int), (11 : Int), (28 : Int), (47 : Int), (21 : Int), (2 : Int), (38 : Int), (5 : Int), (25 : Int), (22 : Int), (16 : Int), (14 : Int), (30 : Int), (17 : Int)] : Array (Int))
    let _t233 ← encrypt message key
    let _as234 ← SudoRt.sudoAssertEq _t233 cipher 945
    let _t235 ← decrypt cipher key
    let _as236 ← SudoRt.sudoAssertEq _t235 message 946
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t237 ← encrypt message key
    let cipher := _t237
    let _t238 ← expand_keys key
    let keys := _t238
    let _t239 ← SudoRt.atL keys (6 : Int)
    let _t240 ← inv_final_round cipher _t239
    let listed := _t240
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init249 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init249 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t242 ← SudoRt.atL keys r
  let _t243 ← inv_full_round listed _t242
  let listed := _t243
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
      let _t244 ← SudoRt.atL keys (0 : Int)
      let _t245 ← inverse_compose listed _t244
      let listed := _t245
      let _t246 ← decrypt cipher key
      let _as247 ← SudoRt.sudoAssertEq listed _t246 957
      let _as248 ← SudoRt.sudoAssertEq listed message 958
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t250 ← trace_encrypt message key
    let traced := _t250
    let _t252 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t253 ← SudoRt.atL traced _t252
    let last := _t253
    let _t254 ← encrypt message key
    let _as255 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t254 965
    let _as256 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 966
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t298 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t298
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init306 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init306 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp302 := σ.2.2
    let held := _sp302.1
    let _sp303 := _sp302.2
    let passes := _sp303
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t258 ← SudoRt.atL traced n
  let _t260 ← (if (SudoRt.SEq.beq (_t258).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t261 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t261).sudo_4Step_3row (2 : Int))) else pure false)
  let _t263 ← (if _t260 then (do
  let _t264 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t264).sudo_4Step_3col (0 : Int))) else pure false)
  if _t263 then
    do
      let _t266 ← SudoRt.addI marked (1 : Int)
      let marked := _t266
      let _t267 ← SudoRt.atL traced n
      let _t269 ← (if (SudoRt.SEq.beq (_t267).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t270 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t270).sudo_4Step_3row (0 : Int))) else pure false)
      let _t272 ← (if _t269 then (do
  let _t273 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t273).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t272 then
        do
          let _t275 ← SudoRt.addI held (1 : Int)
          let held := _t275
          let _t276 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t276).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t278 ← SudoRt.addI passes (1 : Int)
              let passes := _t278
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t279 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t279).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t281 ← SudoRt.addI passes (1 : Int)
              let passes := _t281
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t282 ← SudoRt.atL traced n
      let _t284 ← (if (SudoRt.SEq.beq (_t282).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t285 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t285).sudo_4Step_3row (0 : Int))) else pure false)
      let _t287 ← (if _t284 then (do
  let _t288 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t288).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t287 then
        do
          let _t290 ← SudoRt.addI held (1 : Int)
          let held := _t290
          let _t291 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t291).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t293 ← SudoRt.addI passes (1 : Int)
              let passes := _t293
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t294 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t294).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t296 ← SudoRt.addI passes (1 : Int)
              let passes := _t296
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
    let _sp304 := σ.2.2
    let held := _sp304.1
    let _sp305 := _sp304.2
    let passes := _sp305
    do
      let _as299 ← SudoRt.sudoAssertEq marked (5 : Int) 977
      let _as300 ← SudoRt.sudoAssertEq held (6 : Int) 978
      let _as301 ← SudoRt.sudoAssertEq passes (312 : Int) 979
      pure ()) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init328 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init328 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb309 := SudoRt.appendL nonce i
  let ⟨_nr310, _⟩ := _mb309
  let nonce := _nr310
  let _hm307 := ()
  let _u311 := _hm307
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
      let _t312 ← counter_deck nonce (0 : Int)
      let a := _t312
      let _t313 ← counter_deck nonce (1 : Int)
      let b := _t313
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init327 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init327 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t315 ← SudoRt.atL a i
  let _as316 ← SudoRt.sudoAssertEq _t315 i 1055
  let _t317 ← SudoRt.atL b i
  let _as318 ← SudoRt.sudoAssertEq _t317 i 1056
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
      let _t319 ← SudoRt.atL a (50 : Int)
      let _as320 ← SudoRt.sudoAssertEq _t319 (50 : Int) 1057
      let _t321 ← SudoRt.atL a (51 : Int)
      let _as322 ← SudoRt.sudoAssertEq _t321 (51 : Int) 1058
      let _t323 ← SudoRt.atL b (50 : Int)
      let _as324 ← SudoRt.sudoAssertEq _t323 (51 : Int) 1059
      let _t325 ← SudoRt.atL b (51 : Int)
      let _as326 ← SudoRt.sudoAssertEq _t325 (50 : Int) 1060
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb332 := SudoRt.appendL blocks block
    let ⟨_nr333, _⟩ := _mb332
    let blocks := _nr333
    let _hm329 := ()
    let _u334 := _hm329
    let _mb335 := SudoRt.appendL blocks block
    let ⟨_nr336, _⟩ := _mb335
    let blocks := _nr336
    let _hm330 := ()
    let _u337 := _hm330
    let _t338 ← ecb_encrypt blocks key
    let ecb := _t338
    let _t339 ← SudoRt.atL ecb (0 : Int)
    let _t340 ← SudoRt.atL ecb (1 : Int)
    let _as341 ← SudoRt.sudoAssertEq _t339 _t340 1069
    let _t342 ← ecb_decrypt ecb key
    let _as343 ← SudoRt.sudoAssertEq _t342 blocks 1070
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init356 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init356 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t345 ← SudoRt.subI (38 : Int) i
  let _mb346 := SudoRt.appendL nonce _t345
  let ⟨_nr347, _⟩ := _mb346
  let nonce := _nr347
  let _hm331 := ()
  let _u348 := _hm331
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
      let _t349 ← ctr_encrypt blocks key nonce
      let ctr := _t349
      let _t350 ← SudoRt.atL ctr (0 : Int)
      let _t351 ← SudoRt.atL ctr (1 : Int)
      let _as353 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t350 _t351)) 1075
      let _t354 ← ctr_decrypt ctr key nonce
      let _as355 ← SudoRt.sudoAssertEq _t354 blocks 1076
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_suit_labels_add_and_multiply_in_gf_4", fun _ => test_suit_labels_add_and_multiply_in_gf_4), ("test_row_total_is_the_two_running_totals", fun _ => test_row_total_is_the_two_running_totals), ("test_sum_ranks_leaves_whole_suit_rows_alone", fun _ => test_sum_ranks_leaves_whole_suit_rows_alone), ("test_sum_ranks_sees_a_k_q_swap_that_v9_missed", fun _ => test_sum_ranks_sees_a_k_q_swap_that_v9_missed), ("test_overflow_scan_starts_at_the_blocked_column", fun _ => test_overflow_scan_starts_at_the_blocked_column), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
