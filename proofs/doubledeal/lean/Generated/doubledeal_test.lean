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
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 874
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 875
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
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 881
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 882
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
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 888
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
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 896
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 898
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 899
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
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 909
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 910
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 911
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 912
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 913
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 914
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 915
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 916
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
      let _as100 ← SudoRt.sudoAssertEq built key 922
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_deal_under_reverses_the_packet_and_undeal_puts_it_back : Except SudoRt.Trap Unit :=
  do
    let xs := (#[(10 : Int), (11 : Int), (12 : Int), (13 : Int), (14 : Int), (15 : Int)] : Array (Int))
    let _t106 ← deal_under xs (3 : Int)
    let _as107 ← SudoRt.sudoAssertEq _t106 (#[(13 : Int), (14 : Int), (15 : Int), (12 : Int), (11 : Int), (10 : Int)] : Array (Int)) 926
    let _t108 ← undeal_under (#[(13 : Int), (14 : Int), (15 : Int), (12 : Int), (11 : Int), (10 : Int)] : Array (Int)) (3 : Int)
    let _as109 ← SudoRt.sudoAssertEq _t108 xs 927
    let _t110 ← deal_under xs (0 : Int)
    let _as111 ← SudoRt.sudoAssertEq _t110 xs 928
    let _fromV := (0 : Int)
    let _toV := (6 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init119 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init119 fuel (fun σ =>
    let m := σ
    do
      if m > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) m)
      else
        match ← ((do
  let _t113 ← deal_under xs m
  let _t114 ← undeal_under _t113 m
  let _as115 ← SudoRt.sudoAssertEq _t114 xs 930
  let _t116 ← undeal_under xs m
  let _t117 ← deal_under _t116 m
  let _as118 ← SudoRt.sudoAssertEq _t117 xs 931
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) m)
        | .cont _fs => do
            if m == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) m)
            else do
              let i' ← SudoRt.addI m (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_one_pass_step_by_hand_2_of_hearts_deals_3_then_cuts_2 : Except SudoRt.Trap Unit :=
  do
    let hand := (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)] : Array (Int))
    let empty := (#[] : Array (Int))
    let _t120 ← deal_step (14 : Int) hand empty
    let ⟨dealt, key⟩ := _t120
    let _as121 ← SudoRt.sudoAssertEq dealt (#[(3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (2 : Int), (1 : Int), (0 : Int)] : Array (Int)) 938
    let _as123 ← SudoRt.sudoAssertEq (SudoRt.listLen key) (0 : Int) 939
    let _t124 ← rank_of (14 : Int)
    let _t125 ← left_rotate dealt _t124
    let _as126 ← SudoRt.sudoAssertEq _t125 (#[(5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (2 : Int), (1 : Int), (0 : Int), (3 : Int), (4 : Int)] : Array (Int)) 940
    let _t127 ← deal_step (39 : Int) (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) (#[(20 : Int), (21 : Int), (22 : Int), (23 : Int), (24 : Int), (25 : Int)] : Array (Int))
    let ⟨small, pile⟩ := _t127
    let _as128 ← SudoRt.sudoAssertEq small (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) 943
    let _as129 ← SudoRt.sudoAssertEq pile (#[(25 : Int), (24 : Int), (23 : Int), (22 : Int), (21 : Int), (20 : Int)] : Array (Int)) 944
    let _t130 ← undeal_step (39 : Int) small pile
    let ⟨back_h, back_k⟩ := _t130
    let _as131 ← SudoRt.sudoAssertEq back_h (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) 946
    let _as132 ← SudoRt.sudoAssertEq back_k (#[(20 : Int), (21 : Int), (22 : Int), (23 : Int), (24 : Int), (25 : Int)] : Array (Int)) 947
    pure ()

def test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move : Except SudoRt.Trap Unit :=
  do
    let base := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init182 := (_fromV, base)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init182 fuel (fun σ =>
    let i := σ.1
    let base := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, base))
      else
        match ← ((do
  let _t139 ← (if (!(SudoRt.SEq.beq i (14 : Int))) then (do
  pure (!(SudoRt.SEq.beq i (26 : Int)))) else pure false)
  if _t139 then
    do
      let _mb141 := SudoRt.appendL base i
      let ⟨_nr142, _⟩ := _mb141
      let base := _nr142
      let _hm133 := ()
      let _u143 := _hm133
      pure (SudoRt.Flow.cont (ρ := Unit) base)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) base)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let base := σ.2
    do
      let _fromV := (0 : Int)
      let _toV := (10 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init181 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init181 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t145 ← SudoRt.mulI k (4 : Int)
  let _t146 ← left_rotate base _t145
  let order := _t146
  let _t147 ← SudoRt.mulI (4 : Int) k
  let _t148 ← SudoRt.addI (6 : Int) _t147
  let size := _t148
  let hand := (#[] : Array (Int))
  let key := (#[] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (49 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init170 := (_fromV, (hand, key))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init170 fuel (fun σ =>
    let i := σ.1
    let hand := σ.2.1
    let _sp168 := σ.2.2
    let key := _sp168
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (hand, key)))
      else
        match ← ((do
  if (decide (i < size)) then
    do
      let _t151 ← SudoRt.atL order i
      let _mb152 := SudoRt.appendL hand _t151
      let ⟨_nr153, _⟩ := _mb152
      let hand := _nr153
      let _hm134 := ()
      let _u154 := _hm134
      pure (SudoRt.Flow.cont (ρ := Unit) (hand, key))
  else
    do
      let _t155 ← SudoRt.atL order i
      let _mb156 := SudoRt.appendL key _t155
      let ⟨_nr157, _⟩ := _mb156
      let key := _nr157
      let _hm135 := ()
      let _u158 := _hm135
      pure (SudoRt.Flow.cont (ρ := Unit) (hand, key))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let hand := σ.2.1
    let _sp169 := σ.2.2
    let key := _sp169
    do
      let _t159 ← deal_step (14 : Int) hand key
      let ⟨a, ka⟩ := _t159
      let _t160 ← deal_step (26 : Int) hand key
      let ⟨b, kb⟩ := _t160
      let _as161 ← SudoRt.sudoAssertEq ka kb 970
      let _t162 ← rank_of (14 : Int)
      let _t163 ← left_rotate a _t162
      let _t164 ← rank_of (26 : Int)
      let _t165 ← left_rotate b _t164
      let _as167 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t163 _t165)) 971
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) k)
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) k)
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let small := (#[(0 : Int), (1 : Int), (2 : Int)] : Array (Int))
      let rest := (#[] : Array (Int))
      let _fromV := (3 : Int)
      let _toV := (49 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init180 := (_fromV, rest)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init180 fuel (fun σ =>
    let i := σ.1
    let rest := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, rest))
      else
        match ← ((do
  let _t172 ← SudoRt.atL base i
  let _mb173 := SudoRt.appendL rest _t172
  let ⟨_nr174, _⟩ := _mb173
  let rest := _nr174
  let _hm136 := ()
  let _u175 := _hm136
  pure (SudoRt.Flow.cont (ρ := Unit) rest)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let rest := σ.2
    do
      let _t176 ← deal_step (14 : Int) small rest
      let ⟨a, ka⟩ := _t176
      let _t177 ← deal_step (26 : Int) small rest
      let ⟨b, kb⟩ := _t177
      let _as179 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq ka kb)) 979
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_suit_labels_add_and_multiply_in_gf_4 : Except SudoRt.Trap Unit :=
  do
    let _t183 ← suit_label (0 : Int)
    let _as184 ← SudoRt.sudoAssertEq _t183 (0 : Int) 983
    let _t185 ← suit_label (13 : Int)
    let _as186 ← SudoRt.sudoAssertEq _t185 (2 : Int) 984
    let _t187 ← suit_label (26 : Int)
    let _as188 ← SudoRt.sudoAssertEq _t187 (3 : Int) 985
    let _t189 ← suit_label (51 : Int)
    let _as190 ← SudoRt.sudoAssertEq _t189 (1 : Int) 986
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init214 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init214 fuel (fun σ =>
    let x := σ
    do
      if x > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) x)
      else
        match ← ((do
  let _t192 ← gf_add x x
  let _as193 ← SudoRt.sudoAssertEq _t192 (0 : Int) 988
  let _t194 ← gf_add (0 : Int) x
  let _as195 ← SudoRt.sudoAssertEq _t194 x 989
  let _t196 ← gf_times_w x
  let _t197 ← gf_times_w _t196
  let _t198 ← gf_times_w _t197
  let _as199 ← SudoRt.sudoAssertEq _t198 x 990
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
      let _t200 ← gf_add (1 : Int) (2 : Int)
      let _as201 ← SudoRt.sudoAssertEq _t200 (3 : Int) 991
      let _t202 ← gf_add (2 : Int) (3 : Int)
      let _as203 ← SudoRt.sudoAssertEq _t202 (1 : Int) 992
      let _t204 ← gf_add (3 : Int) (1 : Int)
      let _as205 ← SudoRt.sudoAssertEq _t204 (2 : Int) 993
      let _t206 ← gf_times_w (0 : Int)
      let _as207 ← SudoRt.sudoAssertEq _t206 (0 : Int) 994
      let _t208 ← gf_times_w (1 : Int)
      let _as209 ← SudoRt.sudoAssertEq _t208 (2 : Int) 995
      let _t210 ← gf_times_w (2 : Int)
      let _as211 ← SudoRt.sudoAssertEq _t210 (3 : Int) 996
      let _t212 ← gf_times_w (3 : Int)
      let _as213 ← SudoRt.sudoAssertEq _t212 (1 : Int) 997
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
    let _init227 := (_fromV, (t, u))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init227 fuel (fun σ =>
    let j := σ.1
    let t := σ.2.1
    let _sp225 := σ.2.2
    let u := _sp225
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (t, u)))
      else
        match ← ((do
  let _t216 ← SudoRt.atL row j
  let _t217 ← rank_of _t216
  let _t218 ← SudoRt.addI t _t217
  let t := _t218
  let _t219 ← SudoRt.addI u t
  let u := _t219
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
    let _sp226 := σ.2.2
    let u := _sp226
    do
      let _t220 ← row_total row
      let _as221 ← SudoRt.sudoAssertEq _t220 u 1006
      let _t222 ← row_turn row
      let _t223 ← SudoRt.modI u (13 : Int)
      let _as224 ← SudoRt.sudoAssertEq _t222 _t223 1007
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_leaves_whole_suit_rows_alone : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init245 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init245 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _mb230 := SudoRt.appendL deck i
  let ⟨_nr231, _⟩ := _mb230
  let deck := _nr231
  let _hm228 := ()
  let _u232 := _hm228
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
      let _t233 ← lay_rm deck
      let g := _t233
      let _t234 ← SudoRt.atL g (0 : Int)
      let _t235 ← row_total _t234
      let _as236 ← SudoRt.sudoAssertEq _t235 (455 : Int) 1018
      let _t237 ← column_value g (12 : Int)
      let _as238 ← SudoRt.sudoAssertEq _t237 (0 : Int) 1019
      let _t239 ← column_suits g (0 : Int)
      let _as240 ← SudoRt.sudoAssertEq _t239 (0 : Int) 1020
      let _t241 ← sum_ranks g
      let _as242 ← SudoRt.sudoAssertEq _t241 g 1021
      let _t243 ← inv_sum_ranks g
      let _as244 ← SudoRt.sudoAssertEq _t243 g 1022
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_sees_a_k_q_swap_that_v9_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(16 : Int), (10 : Int), (36 : Int), (14 : Int), (8 : Int), (41 : Int), (0 : Int), (45 : Int), (51 : Int), (7 : Int), (28 : Int), (26 : Int), (24 : Int), (11 : Int), (3 : Int), (39 : Int), (12 : Int), (35 : Int), (43 : Int), (1 : Int), (50 : Int), (15 : Int), (30 : Int), (22 : Int), (38 : Int), (4 : Int), (31 : Int), (44 : Int), (25 : Int), (33 : Int), (48 : Int), (20 : Int), (19 : Int), (42 : Int), (34 : Int), (17 : Int), (40 : Int), (9 : Int), (46 : Int), (32 : Int), (21 : Int), (13 : Int), (5 : Int), (27 : Int), (2 : Int), (18 : Int), (23 : Int), (47 : Int), (37 : Int), (6 : Int), (29 : Int), (49 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init273 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init273 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t249 ← SudoRt.atL deck k
  let _t250 ← swap_card _t249 (12 : Int) (24 : Int)
  let _mb251 := SudoRt.appendL swapped _t250
  let ⟨_nr252, _⟩ := _mb251
  let swapped := _nr252
  let _hm246 := ()
  let _u253 := _hm246
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
      let _t254 ← lay_cm deck
      let _t255 ← sum_ranks _t254
      let _t256 ← scoop_cm _t255
      let out := _t256
      let _t257 ← lay_cm swapped
      let _t258 ← sum_ranks _t257
      let _t259 ← scoop_cm _t258
      let out_swapped := _t259
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init272 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init272 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t261 ← SudoRt.atL out k
  let _t262 ← swap_card _t261 (12 : Int) (24 : Int)
  let _mb263 := SudoRt.appendL relabelled _t262
  let ⟨_nr264, _⟩ := _mb263
  let relabelled := _nr264
  let _hm247 := ()
  let _u265 := _hm247
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
      let _as267 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 1036
      let _t268 ← lay_cm out_swapped
      let _t269 ← inv_sum_ranks _t268
      let _t270 ← scoop_cm _t269
      let _as271 ← SudoRt.sudoAssertEq _t270 swapped 1037
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_overflow_scan_drops_a_row_when_the_row_is_full : Except SudoRt.Trap Unit :=
  do
    let occ := (#[] : Array (Array (Int)))
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init307 := (_fromV, occ)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init307 fuel (fun σ =>
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
  let _init293 := (_fromV, marks)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init293 fuel (fun σ =>
    let c := σ.1
    let marks := σ.2
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (c, marks))
      else
        match ← ((do
  let _t280 ← (if (SudoRt.SEq.beq r (1 : Int)) then (do
  let _t282 ← (if (SudoRt.SEq.beq c (2 : Int)) then pure true else (do
  pure (SudoRt.SEq.beq c (7 : Int))))
  pure _t282) else pure false)
  if _t280 then
    do
      let _mb284 := SudoRt.appendL marks (0 : Int)
      let ⟨_nr285, _⟩ := _mb284
      let marks := _nr285
      let _hm274 := ()
      let _u286 := _hm274
      pure (SudoRt.Flow.cont (ρ := Unit) marks)
  else
    do
      let _mb287 := SudoRt.appendL marks (1 : Int)
      let ⟨_nr288, _⟩ := _mb287
      let marks := _nr288
      let _hm275 := ()
      let _u289 := _hm275
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
      let _mb290 := SudoRt.appendL occ marks
      let ⟨_nr291, _⟩ := _mb290
      let occ := _nr291
      let _hm276 := ()
      let _u292 := _hm276
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
      let _t294 ← scan_row occ (1 : Int) (5 : Int)
      let _as295 ← SudoRt.sudoAssertEq _t294 (7 : Int) 1052
      let _t296 ← scan_row occ (1 : Int) (8 : Int)
      let _as297 ← SudoRt.sudoAssertEq _t296 (2 : Int) 1053
      let _t298 ← scan_row occ (0 : Int) (5 : Int)
      let _t299 ← SudoRt.negI (1 : Int)
      let _as300 ← SudoRt.sudoAssertEq _t298 _t299 1054
      let _t301 ← overflow_seat occ (1 : Int) (5 : Int)
      let ⟨r, c⟩ := _t301
      let _as302 ← SudoRt.sudoAssertEq r (1 : Int) 1056
      let _as303 ← SudoRt.sudoAssertEq c (7 : Int) 1057
      let _t304 ← overflow_seat occ (3 : Int) (8 : Int)
      let ⟨r2, c2⟩ := _t304
      let _as305 ← SudoRt.sudoAssertEq r2 (1 : Int) 1059
      let _as306 ← SudoRt.sudoAssertEq c2 (2 : Int) 1060
      pure ()) (fun r => pure r))
    pure _out

def test_the_finger_stays_on_the_target_after_a_block : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(12 : Int), (13 : Int), (0 : Int)] : Array (Int))
    let _fromV := (1 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init325 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init325 fuel (fun σ =>
    let k := σ.1
    let deck := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, deck))
      else
        match ← ((do
  let _t311 ← (if (!(SudoRt.SEq.beq k (12 : Int))) then (do
  pure (!(SudoRt.SEq.beq k (13 : Int)))) else pure false)
  if _t311 then
    do
      let _mb313 := SudoRt.appendL deck k
      let ⟨_nr314, _⟩ := _mb313
      let deck := _nr314
      let _hm308 := ()
      let _u315 := _hm308
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
      let _t316 ← mix_columns deck
      let out := _t316
      let _t317 ← SudoRt.atL out (26 : Int)
      let _as318 ← SudoRt.sudoAssertEq _t317 (12 : Int) 1073
      let _t319 ← SudoRt.atL out (0 : Int)
      let _as320 ← SudoRt.sudoAssertEq _t319 (13 : Int) 1074
      let _t321 ← SudoRt.atL out (40 : Int)
      let _as322 ← SudoRt.sudoAssertEq _t321 (0 : Int) 1075
      let _t323 ← inv_mix_columns out
      let _as324 ← SudoRt.sudoAssertEq _t323 deck 1076
      pure ()) (fun r => pure r))
    pure _out

def test_grid_cycle_sees_the_k_k_swap_that_v10_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(32 : Int), (23 : Int), (6 : Int), (21 : Int), (13 : Int), (31 : Int), (9 : Int), (37 : Int), (16 : Int), (22 : Int), (30 : Int), (19 : Int), (38 : Int), (41 : Int), (25 : Int), (51 : Int), (17 : Int), (50 : Int), (39 : Int), (2 : Int), (36 : Int), (15 : Int), (28 : Int), (20 : Int), (12 : Int), (45 : Int), (5 : Int), (33 : Int), (29 : Int), (14 : Int), (18 : Int), (40 : Int), (34 : Int), (10 : Int), (44 : Int), (26 : Int), (42 : Int), (27 : Int), (47 : Int), (4 : Int), (24 : Int), (46 : Int), (11 : Int), (43 : Int), (3 : Int), (49 : Int), (7 : Int), (0 : Int), (8 : Int), (1 : Int), (48 : Int), (35 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init347 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init347 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t329 ← SudoRt.atL deck k
  let _t330 ← swap_card _t329 (12 : Int) (51 : Int)
  let _mb331 := SudoRt.appendL swapped _t330
  let ⟨_nr332, _⟩ := _mb331
  let swapped := _nr332
  let _hm326 := ()
  let _u333 := _hm326
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
      let _t334 ← mix_columns deck
      let out := _t334
      let _t335 ← mix_columns swapped
      let out_swapped := _t335
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init346 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init346 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t337 ← SudoRt.atL out k
  let _t338 ← swap_card _t337 (12 : Int) (51 : Int)
  let _mb339 := SudoRt.appendL relabelled _t338
  let ⟨_nr340, _⟩ := _mb339
  let relabelled := _nr340
  let _hm327 := ()
  let _u341 := _hm327
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
      let _as343 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 1090
      let _t344 ← inv_mix_columns out_swapped
      let _as345 ← SudoRt.sudoAssertEq _t344 swapped 1091
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(36 : Int), (38 : Int), (18 : Int), (25 : Int), (37 : Int), (12 : Int), (8 : Int), (29 : Int), (2 : Int), (51 : Int), (30 : Int), (39 : Int), (6 : Int), (21 : Int), (27 : Int), (11 : Int), (20 : Int), (19 : Int), (4 : Int), (49 : Int), (34 : Int), (17 : Int), (40 : Int), (48 : Int), (15 : Int), (26 : Int), (16 : Int), (7 : Int), (35 : Int), (23 : Int), (1 : Int), (3 : Int), (31 : Int), (43 : Int), (9 : Int), (50 : Int), (10 : Int), (33 : Int), (22 : Int), (24 : Int), (28 : Int), (5 : Int), (47 : Int), (46 : Int), (14 : Int), (13 : Int), (45 : Int), (44 : Int), (42 : Int), (41 : Int), (0 : Int), (32 : Int)] : Array (Int))
    let _t348 ← encrypt message key
    let _as349 ← SudoRt.sudoAssertEq _t348 cipher 1097
    let _t350 ← decrypt cipher key
    let _as351 ← SudoRt.sudoAssertEq _t350 message 1098
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t352 ← encrypt message key
    let cipher := _t352
    let _t353 ← expand_keys key
    let keys := _t353
    let _t354 ← SudoRt.atL keys (6 : Int)
    let _t355 ← inv_final_round cipher _t354
    let listed := _t355
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init364 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init364 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t357 ← SudoRt.atL keys r
  let _t358 ← inv_full_round listed _t357
  let listed := _t358
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
      let _t359 ← SudoRt.atL keys (0 : Int)
      let _t360 ← inverse_compose listed _t359
      let listed := _t360
      let _t361 ← decrypt cipher key
      let _as362 ← SudoRt.sudoAssertEq listed _t361 1109
      let _as363 ← SudoRt.sudoAssertEq listed message 1110
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t365 ← trace_encrypt message key
    let traced := _t365
    let _t367 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t368 ← SudoRt.atL traced _t367
    let last := _t368
    let _t369 ← encrypt message key
    let _as370 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t369 1117
    let _as371 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 1118
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t413 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t413
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init421 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init421 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp417 := σ.2.2
    let held := _sp417.1
    let _sp418 := _sp417.2
    let passes := _sp418
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t373 ← SudoRt.atL traced n
  let _t375 ← (if (SudoRt.SEq.beq (_t373).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t376 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t376).sudo_4Step_3row (2 : Int))) else pure false)
  let _t378 ← (if _t375 then (do
  let _t379 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t379).sudo_4Step_3col (0 : Int))) else pure false)
  if _t378 then
    do
      let _t381 ← SudoRt.addI marked (1 : Int)
      let marked := _t381
      let _t382 ← SudoRt.atL traced n
      let _t384 ← (if (SudoRt.SEq.beq (_t382).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t385 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t385).sudo_4Step_3row (0 : Int))) else pure false)
      let _t387 ← (if _t384 then (do
  let _t388 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t388).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t387 then
        do
          let _t390 ← SudoRt.addI held (1 : Int)
          let held := _t390
          let _t391 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t391).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t393 ← SudoRt.addI passes (1 : Int)
              let passes := _t393
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t394 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t394).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t396 ← SudoRt.addI passes (1 : Int)
              let passes := _t396
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t397 ← SudoRt.atL traced n
      let _t399 ← (if (SudoRt.SEq.beq (_t397).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t400 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t400).sudo_4Step_3row (0 : Int))) else pure false)
      let _t402 ← (if _t399 then (do
  let _t403 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t403).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t402 then
        do
          let _t405 ← SudoRt.addI held (1 : Int)
          let held := _t405
          let _t406 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t406).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t408 ← SudoRt.addI passes (1 : Int)
              let passes := _t408
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t409 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t409).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t411 ← SudoRt.addI passes (1 : Int)
              let passes := _t411
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
    let _sp419 := σ.2.2
    let held := _sp419.1
    let _sp420 := _sp419.2
    let passes := _sp420
    do
      let _as414 ← SudoRt.sudoAssertEq marked (5 : Int) 1129
      let _as415 ← SudoRt.sudoAssertEq held (6 : Int) 1130
      let _as416 ← SudoRt.sudoAssertEq passes (312 : Int) 1131
      pure ()) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init443 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init443 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb424 := SudoRt.appendL nonce i
  let ⟨_nr425, _⟩ := _mb424
  let nonce := _nr425
  let _hm422 := ()
  let _u426 := _hm422
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
      let _t427 ← counter_deck nonce (0 : Int)
      let a := _t427
      let _t428 ← counter_deck nonce (1 : Int)
      let b := _t428
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init442 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init442 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t430 ← SudoRt.atL a i
  let _as431 ← SudoRt.sudoAssertEq _t430 i 1207
  let _t432 ← SudoRt.atL b i
  let _as433 ← SudoRt.sudoAssertEq _t432 i 1208
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
      let _t434 ← SudoRt.atL a (50 : Int)
      let _as435 ← SudoRt.sudoAssertEq _t434 (50 : Int) 1209
      let _t436 ← SudoRt.atL a (51 : Int)
      let _as437 ← SudoRt.sudoAssertEq _t436 (51 : Int) 1210
      let _t438 ← SudoRt.atL b (50 : Int)
      let _as439 ← SudoRt.sudoAssertEq _t438 (51 : Int) 1211
      let _t440 ← SudoRt.atL b (51 : Int)
      let _as441 ← SudoRt.sudoAssertEq _t440 (50 : Int) 1212
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb447 := SudoRt.appendL blocks block
    let ⟨_nr448, _⟩ := _mb447
    let blocks := _nr448
    let _hm444 := ()
    let _u449 := _hm444
    let _mb450 := SudoRt.appendL blocks block
    let ⟨_nr451, _⟩ := _mb450
    let blocks := _nr451
    let _hm445 := ()
    let _u452 := _hm445
    let _t453 ← ecb_encrypt blocks key
    let ecb := _t453
    let _t454 ← SudoRt.atL ecb (0 : Int)
    let _t455 ← SudoRt.atL ecb (1 : Int)
    let _as456 ← SudoRt.sudoAssertEq _t454 _t455 1221
    let _t457 ← ecb_decrypt ecb key
    let _as458 ← SudoRt.sudoAssertEq _t457 blocks 1222
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init471 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init471 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t460 ← SudoRt.subI (38 : Int) i
  let _mb461 := SudoRt.appendL nonce _t460
  let ⟨_nr462, _⟩ := _mb461
  let nonce := _nr462
  let _hm446 := ()
  let _u463 := _hm446
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
      let _t464 ← ctr_encrypt blocks key nonce
      let ctr := _t464
      let _t465 ← SudoRt.atL ctr (0 : Int)
      let _t466 ← SudoRt.atL ctr (1 : Int)
      let _as468 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t465 _t466)) 1227
      let _t469 ← ctr_decrypt ctr key nonce
      let _as470 ← SudoRt.sudoAssertEq _t469 blocks 1228
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_deal_under_reverses_the_packet_and_undeal_puts_it_back", fun _ => test_deal_under_reverses_the_packet_and_undeal_puts_it_back), ("test_one_pass_step_by_hand_2_of_hearts_deals_3_then_cuts_2", fun _ => test_one_pass_step_by_hand_2_of_hearts_deals_3_then_cuts_2), ("test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move", fun _ => test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move), ("test_suit_labels_add_and_multiply_in_gf_4", fun _ => test_suit_labels_add_and_multiply_in_gf_4), ("test_row_total_is_the_two_running_totals", fun _ => test_row_total_is_the_two_running_totals), ("test_sum_ranks_leaves_whole_suit_rows_alone", fun _ => test_sum_ranks_leaves_whole_suit_rows_alone), ("test_sum_ranks_sees_a_k_q_swap_that_v9_missed", fun _ => test_sum_ranks_sees_a_k_q_swap_that_v9_missed), ("test_overflow_scan_drops_a_row_when_the_row_is_full", fun _ => test_overflow_scan_drops_a_row_when_the_row_is_full), ("test_the_finger_stays_on_the_target_after_a_block", fun _ => test_the_finger_stays_on_the_target_after_a_block), ("test_grid_cycle_sees_the_k_k_swap_that_v10_missed", fun _ => test_grid_cycle_sees_the_k_k_swap_that_v10_missed), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
