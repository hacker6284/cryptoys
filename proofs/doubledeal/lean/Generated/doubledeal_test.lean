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
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 871
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 872
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
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 878
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 879
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
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 885
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
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 893
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 895
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 896
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
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 906
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 907
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 908
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 909
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 910
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 911
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 912
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 913
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
      let _as100 ← SudoRt.sudoAssertEq built key 919
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_deal_under_reverses_the_packet_and_undeal_puts_it_back : Except SudoRt.Trap Unit :=
  do
    let xs := (#[(10 : Int), (11 : Int), (12 : Int), (13 : Int), (14 : Int), (15 : Int)] : Array (Int))
    let _t106 ← deal_under xs (3 : Int)
    let _as107 ← SudoRt.sudoAssertEq _t106 (#[(13 : Int), (14 : Int), (15 : Int), (12 : Int), (11 : Int), (10 : Int)] : Array (Int)) 923
    let _t108 ← undeal_under (#[(13 : Int), (14 : Int), (15 : Int), (12 : Int), (11 : Int), (10 : Int)] : Array (Int)) (3 : Int)
    let _as109 ← SudoRt.sudoAssertEq _t108 xs 924
    let _t110 ← deal_under xs (0 : Int)
    let _as111 ← SudoRt.sudoAssertEq _t110 xs 925
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
  let _as115 ← SudoRt.sudoAssertEq _t114 xs 927
  let _t116 ← undeal_under xs m
  let _t117 ← deal_under _t116 m
  let _as118 ← SudoRt.sudoAssertEq _t117 xs 928
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
    let _as121 ← SudoRt.sudoAssertEq dealt (#[(3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (2 : Int), (1 : Int), (0 : Int)] : Array (Int)) 935
    let _as123 ← SudoRt.sudoAssertEq (SudoRt.listLen key) (0 : Int) 936
    let _t124 ← rank_of (14 : Int)
    let _t125 ← left_rotate dealt _t124
    let _as126 ← SudoRt.sudoAssertEq _t125 (#[(5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (2 : Int), (1 : Int), (0 : Int), (3 : Int), (4 : Int)] : Array (Int)) 937
    let _t127 ← deal_step (39 : Int) (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) (#[(20 : Int), (21 : Int), (22 : Int), (23 : Int), (24 : Int), (25 : Int)] : Array (Int))
    let ⟨small, pile⟩ := _t127
    let _as128 ← SudoRt.sudoAssertEq small (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) 940
    let _as129 ← SudoRt.sudoAssertEq pile (#[(25 : Int), (24 : Int), (23 : Int), (22 : Int), (21 : Int), (20 : Int)] : Array (Int)) 941
    let _t130 ← undeal_step (39 : Int) small pile
    let ⟨back_h, back_k⟩ := _t130
    let _as131 ← SudoRt.sudoAssertEq back_h (#[(0 : Int), (1 : Int), (2 : Int), (3 : Int)] : Array (Int)) 943
    let _as132 ← SudoRt.sudoAssertEq back_k (#[(20 : Int), (21 : Int), (22 : Int), (23 : Int), (24 : Int), (25 : Int)] : Array (Int)) 944
    pure ()

def test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move : Except SudoRt.Trap Unit :=
  do
    let hand := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init149 := (_fromV, hand)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init149 fuel (fun σ =>
    let i := σ.1
    let hand := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, hand))
      else
        match ← ((do
  let _t136 ← (if (!(SudoRt.SEq.beq i (14 : Int))) then (do
  pure (!(SudoRt.SEq.beq i (26 : Int)))) else pure false)
  if _t136 then
    do
      let _mb138 := SudoRt.appendL hand i
      let ⟨_nr139, _⟩ := _mb138
      let hand := _nr139
      let _hm133 := ()
      let _u140 := _hm133
      pure (SudoRt.Flow.cont (ρ := Unit) hand)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) hand)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let hand := σ.2
    do
      let empty := (#[] : Array (Int))
      let _t141 ← deal_step (14 : Int) hand empty
      let ⟨a, ka⟩ := _t141
      let _t142 ← deal_step (26 : Int) hand empty
      let ⟨b, kb⟩ := _t142
      let _t143 ← rank_of (14 : Int)
      let _t144 ← left_rotate a _t143
      let _t145 ← rank_of (26 : Int)
      let _t146 ← left_rotate b _t145
      let _as148 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t144 _t146)) 955
      pure ()) (fun r => pure r))
    pure _out

def test_suit_labels_add_and_multiply_in_gf_4 : Except SudoRt.Trap Unit :=
  do
    let _t150 ← suit_label (0 : Int)
    let _as151 ← SudoRt.sudoAssertEq _t150 (0 : Int) 959
    let _t152 ← suit_label (13 : Int)
    let _as153 ← SudoRt.sudoAssertEq _t152 (2 : Int) 960
    let _t154 ← suit_label (26 : Int)
    let _as155 ← SudoRt.sudoAssertEq _t154 (3 : Int) 961
    let _t156 ← suit_label (51 : Int)
    let _as157 ← SudoRt.sudoAssertEq _t156 (1 : Int) 962
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init181 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init181 fuel (fun σ =>
    let x := σ
    do
      if x > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) x)
      else
        match ← ((do
  let _t159 ← gf_add x x
  let _as160 ← SudoRt.sudoAssertEq _t159 (0 : Int) 964
  let _t161 ← gf_add (0 : Int) x
  let _as162 ← SudoRt.sudoAssertEq _t161 x 965
  let _t163 ← gf_times_w x
  let _t164 ← gf_times_w _t163
  let _t165 ← gf_times_w _t164
  let _as166 ← SudoRt.sudoAssertEq _t165 x 966
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
      let _t167 ← gf_add (1 : Int) (2 : Int)
      let _as168 ← SudoRt.sudoAssertEq _t167 (3 : Int) 967
      let _t169 ← gf_add (2 : Int) (3 : Int)
      let _as170 ← SudoRt.sudoAssertEq _t169 (1 : Int) 968
      let _t171 ← gf_add (3 : Int) (1 : Int)
      let _as172 ← SudoRt.sudoAssertEq _t171 (2 : Int) 969
      let _t173 ← gf_times_w (0 : Int)
      let _as174 ← SudoRt.sudoAssertEq _t173 (0 : Int) 970
      let _t175 ← gf_times_w (1 : Int)
      let _as176 ← SudoRt.sudoAssertEq _t175 (2 : Int) 971
      let _t177 ← gf_times_w (2 : Int)
      let _as178 ← SudoRt.sudoAssertEq _t177 (3 : Int) 972
      let _t179 ← gf_times_w (3 : Int)
      let _as180 ← SudoRt.sudoAssertEq _t179 (1 : Int) 973
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
    let _init194 := (_fromV, (t, u))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init194 fuel (fun σ =>
    let j := σ.1
    let t := σ.2.1
    let _sp192 := σ.2.2
    let u := _sp192
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (t, u)))
      else
        match ← ((do
  let _t183 ← SudoRt.atL row j
  let _t184 ← rank_of _t183
  let _t185 ← SudoRt.addI t _t184
  let t := _t185
  let _t186 ← SudoRt.addI u t
  let u := _t186
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
    let _sp193 := σ.2.2
    let u := _sp193
    do
      let _t187 ← row_total row
      let _as188 ← SudoRt.sudoAssertEq _t187 u 982
      let _t189 ← row_turn row
      let _t190 ← SudoRt.modI u (13 : Int)
      let _as191 ← SudoRt.sudoAssertEq _t189 _t190 983
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_leaves_whole_suit_rows_alone : Except SudoRt.Trap Unit :=
  do
    let deck := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init212 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init212 fuel (fun σ =>
    let i := σ.1
    let deck := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, deck))
      else
        match ← ((do
  let _mb197 := SudoRt.appendL deck i
  let ⟨_nr198, _⟩ := _mb197
  let deck := _nr198
  let _hm195 := ()
  let _u199 := _hm195
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
      let _t200 ← lay_rm deck
      let g := _t200
      let _t201 ← SudoRt.atL g (0 : Int)
      let _t202 ← row_total _t201
      let _as203 ← SudoRt.sudoAssertEq _t202 (455 : Int) 994
      let _t204 ← column_value g (12 : Int)
      let _as205 ← SudoRt.sudoAssertEq _t204 (0 : Int) 995
      let _t206 ← column_suits g (0 : Int)
      let _as207 ← SudoRt.sudoAssertEq _t206 (0 : Int) 996
      let _t208 ← sum_ranks g
      let _as209 ← SudoRt.sudoAssertEq _t208 g 997
      let _t210 ← inv_sum_ranks g
      let _as211 ← SudoRt.sudoAssertEq _t210 g 998
      pure ()) (fun r => pure r))
    pure _out

def test_sum_ranks_sees_a_k_q_swap_that_v9_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(16 : Int), (10 : Int), (36 : Int), (14 : Int), (8 : Int), (41 : Int), (0 : Int), (45 : Int), (51 : Int), (7 : Int), (28 : Int), (26 : Int), (24 : Int), (11 : Int), (3 : Int), (39 : Int), (12 : Int), (35 : Int), (43 : Int), (1 : Int), (50 : Int), (15 : Int), (30 : Int), (22 : Int), (38 : Int), (4 : Int), (31 : Int), (44 : Int), (25 : Int), (33 : Int), (48 : Int), (20 : Int), (19 : Int), (42 : Int), (34 : Int), (17 : Int), (40 : Int), (9 : Int), (46 : Int), (32 : Int), (21 : Int), (13 : Int), (5 : Int), (27 : Int), (2 : Int), (18 : Int), (23 : Int), (47 : Int), (37 : Int), (6 : Int), (29 : Int), (49 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init240 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init240 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t216 ← SudoRt.atL deck k
  let _t217 ← swap_card _t216 (12 : Int) (24 : Int)
  let _mb218 := SudoRt.appendL swapped _t217
  let ⟨_nr219, _⟩ := _mb218
  let swapped := _nr219
  let _hm213 := ()
  let _u220 := _hm213
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
      let _t221 ← lay_cm deck
      let _t222 ← sum_ranks _t221
      let _t223 ← scoop_cm _t222
      let out := _t223
      let _t224 ← lay_cm swapped
      let _t225 ← sum_ranks _t224
      let _t226 ← scoop_cm _t225
      let out_swapped := _t226
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init239 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init239 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t228 ← SudoRt.atL out k
  let _t229 ← swap_card _t228 (12 : Int) (24 : Int)
  let _mb230 := SudoRt.appendL relabelled _t229
  let ⟨_nr231, _⟩ := _mb230
  let relabelled := _nr231
  let _hm214 := ()
  let _u232 := _hm214
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
      let _as234 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 1012
      let _t235 ← lay_cm out_swapped
      let _t236 ← inv_sum_ranks _t235
      let _t237 ← scoop_cm _t236
      let _as238 ← SudoRt.sudoAssertEq _t237 swapped 1013
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_overflow_scan_drops_a_row_when_the_row_is_full : Except SudoRt.Trap Unit :=
  do
    let occ := (#[] : Array (Array (Int)))
    let _fromV := (0 : Int)
    let _toV := (3 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init274 := (_fromV, occ)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init274 fuel (fun σ =>
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
  let _init260 := (_fromV, marks)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init260 fuel (fun σ =>
    let c := σ.1
    let marks := σ.2
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (c, marks))
      else
        match ← ((do
  let _t247 ← (if (SudoRt.SEq.beq r (1 : Int)) then (do
  let _t249 ← (if (SudoRt.SEq.beq c (2 : Int)) then pure true else (do
  pure (SudoRt.SEq.beq c (7 : Int))))
  pure _t249) else pure false)
  if _t247 then
    do
      let _mb251 := SudoRt.appendL marks (0 : Int)
      let ⟨_nr252, _⟩ := _mb251
      let marks := _nr252
      let _hm241 := ()
      let _u253 := _hm241
      pure (SudoRt.Flow.cont (ρ := Unit) marks)
  else
    do
      let _mb254 := SudoRt.appendL marks (1 : Int)
      let ⟨_nr255, _⟩ := _mb254
      let marks := _nr255
      let _hm242 := ()
      let _u256 := _hm242
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
      let _mb257 := SudoRt.appendL occ marks
      let ⟨_nr258, _⟩ := _mb257
      let occ := _nr258
      let _hm243 := ()
      let _u259 := _hm243
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
      let _t261 ← scan_row occ (1 : Int) (5 : Int)
      let _as262 ← SudoRt.sudoAssertEq _t261 (7 : Int) 1028
      let _t263 ← scan_row occ (1 : Int) (8 : Int)
      let _as264 ← SudoRt.sudoAssertEq _t263 (2 : Int) 1029
      let _t265 ← scan_row occ (0 : Int) (5 : Int)
      let _t266 ← SudoRt.negI (1 : Int)
      let _as267 ← SudoRt.sudoAssertEq _t265 _t266 1030
      let _t268 ← overflow_seat occ (1 : Int) (5 : Int)
      let ⟨r, c⟩ := _t268
      let _as269 ← SudoRt.sudoAssertEq r (1 : Int) 1032
      let _as270 ← SudoRt.sudoAssertEq c (7 : Int) 1033
      let _t271 ← overflow_seat occ (3 : Int) (8 : Int)
      let ⟨r2, c2⟩ := _t271
      let _as272 ← SudoRt.sudoAssertEq r2 (1 : Int) 1035
      let _as273 ← SudoRt.sudoAssertEq c2 (2 : Int) 1036
      pure ()) (fun r => pure r))
    pure _out

def test_the_finger_stays_on_the_target_after_a_block : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(12 : Int), (13 : Int), (0 : Int)] : Array (Int))
    let _fromV := (1 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init292 := (_fromV, deck)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init292 fuel (fun σ =>
    let k := σ.1
    let deck := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, deck))
      else
        match ← ((do
  let _t278 ← (if (!(SudoRt.SEq.beq k (12 : Int))) then (do
  pure (!(SudoRt.SEq.beq k (13 : Int)))) else pure false)
  if _t278 then
    do
      let _mb280 := SudoRt.appendL deck k
      let ⟨_nr281, _⟩ := _mb280
      let deck := _nr281
      let _hm275 := ()
      let _u282 := _hm275
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
      let _t283 ← mix_columns deck
      let out := _t283
      let _t284 ← SudoRt.atL out (26 : Int)
      let _as285 ← SudoRt.sudoAssertEq _t284 (12 : Int) 1049
      let _t286 ← SudoRt.atL out (0 : Int)
      let _as287 ← SudoRt.sudoAssertEq _t286 (13 : Int) 1050
      let _t288 ← SudoRt.atL out (40 : Int)
      let _as289 ← SudoRt.sudoAssertEq _t288 (0 : Int) 1051
      let _t290 ← inv_mix_columns out
      let _as291 ← SudoRt.sudoAssertEq _t290 deck 1052
      pure ()) (fun r => pure r))
    pure _out

def test_grid_cycle_sees_the_k_k_swap_that_v10_missed : Except SudoRt.Trap Unit :=
  do
    let deck := (#[(32 : Int), (23 : Int), (6 : Int), (21 : Int), (13 : Int), (31 : Int), (9 : Int), (37 : Int), (16 : Int), (22 : Int), (30 : Int), (19 : Int), (38 : Int), (41 : Int), (25 : Int), (51 : Int), (17 : Int), (50 : Int), (39 : Int), (2 : Int), (36 : Int), (15 : Int), (28 : Int), (20 : Int), (12 : Int), (45 : Int), (5 : Int), (33 : Int), (29 : Int), (14 : Int), (18 : Int), (40 : Int), (34 : Int), (10 : Int), (44 : Int), (26 : Int), (42 : Int), (27 : Int), (47 : Int), (4 : Int), (24 : Int), (46 : Int), (11 : Int), (43 : Int), (3 : Int), (49 : Int), (7 : Int), (0 : Int), (8 : Int), (1 : Int), (48 : Int), (35 : Int)] : Array (Int))
    let swapped := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init314 := (_fromV, swapped)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init314 fuel (fun σ =>
    let k := σ.1
    let swapped := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, swapped))
      else
        match ← ((do
  let _t296 ← SudoRt.atL deck k
  let _t297 ← swap_card _t296 (12 : Int) (51 : Int)
  let _mb298 := SudoRt.appendL swapped _t297
  let ⟨_nr299, _⟩ := _mb298
  let swapped := _nr299
  let _hm293 := ()
  let _u300 := _hm293
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
      let _t301 ← mix_columns deck
      let out := _t301
      let _t302 ← mix_columns swapped
      let out_swapped := _t302
      let relabelled := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init313 := (_fromV, relabelled)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init313 fuel (fun σ =>
    let k := σ.1
    let relabelled := σ.2
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, relabelled))
      else
        match ← ((do
  let _t304 ← SudoRt.atL out k
  let _t305 ← swap_card _t304 (12 : Int) (51 : Int)
  let _mb306 := SudoRt.appendL relabelled _t305
  let ⟨_nr307, _⟩ := _mb306
  let relabelled := _nr307
  let _hm294 := ()
  let _u308 := _hm294
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
      let _as310 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq out_swapped relabelled)) 1066
      let _t311 ← inv_mix_columns out_swapped
      let _as312 ← SudoRt.sudoAssertEq _t311 swapped 1067
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(36 : Int), (38 : Int), (18 : Int), (25 : Int), (37 : Int), (12 : Int), (8 : Int), (29 : Int), (2 : Int), (51 : Int), (30 : Int), (39 : Int), (6 : Int), (21 : Int), (27 : Int), (11 : Int), (20 : Int), (19 : Int), (4 : Int), (49 : Int), (34 : Int), (17 : Int), (40 : Int), (48 : Int), (15 : Int), (26 : Int), (16 : Int), (7 : Int), (35 : Int), (23 : Int), (1 : Int), (3 : Int), (31 : Int), (43 : Int), (9 : Int), (50 : Int), (10 : Int), (33 : Int), (22 : Int), (24 : Int), (28 : Int), (5 : Int), (47 : Int), (46 : Int), (14 : Int), (13 : Int), (45 : Int), (44 : Int), (42 : Int), (41 : Int), (0 : Int), (32 : Int)] : Array (Int))
    let _t315 ← encrypt message key
    let _as316 ← SudoRt.sudoAssertEq _t315 cipher 1073
    let _t317 ← decrypt cipher key
    let _as318 ← SudoRt.sudoAssertEq _t317 message 1074
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t319 ← encrypt message key
    let cipher := _t319
    let _t320 ← expand_keys key
    let keys := _t320
    let _t321 ← SudoRt.atL keys (6 : Int)
    let _t322 ← inv_final_round cipher _t321
    let listed := _t322
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init331 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init331 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t324 ← SudoRt.atL keys r
  let _t325 ← inv_full_round listed _t324
  let listed := _t325
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
      let _t326 ← SudoRt.atL keys (0 : Int)
      let _t327 ← inverse_compose listed _t326
      let listed := _t327
      let _t328 ← decrypt cipher key
      let _as329 ← SudoRt.sudoAssertEq listed _t328 1085
      let _as330 ← SudoRt.sudoAssertEq listed message 1086
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t332 ← trace_encrypt message key
    let traced := _t332
    let _t334 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t335 ← SudoRt.atL traced _t334
    let last := _t335
    let _t336 ← encrypt message key
    let _as337 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t336 1093
    let _as338 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 1094
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t380 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t380
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init388 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init388 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp384 := σ.2.2
    let held := _sp384.1
    let _sp385 := _sp384.2
    let passes := _sp385
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t340 ← SudoRt.atL traced n
  let _t342 ← (if (SudoRt.SEq.beq (_t340).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t343 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t343).sudo_4Step_3row (2 : Int))) else pure false)
  let _t345 ← (if _t342 then (do
  let _t346 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t346).sudo_4Step_3col (0 : Int))) else pure false)
  if _t345 then
    do
      let _t348 ← SudoRt.addI marked (1 : Int)
      let marked := _t348
      let _t349 ← SudoRt.atL traced n
      let _t351 ← (if (SudoRt.SEq.beq (_t349).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t352 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t352).sudo_4Step_3row (0 : Int))) else pure false)
      let _t354 ← (if _t351 then (do
  let _t355 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t355).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t354 then
        do
          let _t357 ← SudoRt.addI held (1 : Int)
          let held := _t357
          let _t358 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t358).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t360 ← SudoRt.addI passes (1 : Int)
              let passes := _t360
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t361 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t361).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t363 ← SudoRt.addI passes (1 : Int)
              let passes := _t363
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t364 ← SudoRt.atL traced n
      let _t366 ← (if (SudoRt.SEq.beq (_t364).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t367 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t367).sudo_4Step_3row (0 : Int))) else pure false)
      let _t369 ← (if _t366 then (do
  let _t370 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t370).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t369 then
        do
          let _t372 ← SudoRt.addI held (1 : Int)
          let held := _t372
          let _t373 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t373).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t375 ← SudoRt.addI passes (1 : Int)
              let passes := _t375
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t376 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t376).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t378 ← SudoRt.addI passes (1 : Int)
              let passes := _t378
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
    let _sp386 := σ.2.2
    let held := _sp386.1
    let _sp387 := _sp386.2
    let passes := _sp387
    do
      let _as381 ← SudoRt.sudoAssertEq marked (5 : Int) 1105
      let _as382 ← SudoRt.sudoAssertEq held (6 : Int) 1106
      let _as383 ← SudoRt.sudoAssertEq passes (312 : Int) 1107
      pure ()) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init410 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init410 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb391 := SudoRt.appendL nonce i
  let ⟨_nr392, _⟩ := _mb391
  let nonce := _nr392
  let _hm389 := ()
  let _u393 := _hm389
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
      let _t394 ← counter_deck nonce (0 : Int)
      let a := _t394
      let _t395 ← counter_deck nonce (1 : Int)
      let b := _t395
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init409 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init409 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t397 ← SudoRt.atL a i
  let _as398 ← SudoRt.sudoAssertEq _t397 i 1183
  let _t399 ← SudoRt.atL b i
  let _as400 ← SudoRt.sudoAssertEq _t399 i 1184
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
      let _t401 ← SudoRt.atL a (50 : Int)
      let _as402 ← SudoRt.sudoAssertEq _t401 (50 : Int) 1185
      let _t403 ← SudoRt.atL a (51 : Int)
      let _as404 ← SudoRt.sudoAssertEq _t403 (51 : Int) 1186
      let _t405 ← SudoRt.atL b (50 : Int)
      let _as406 ← SudoRt.sudoAssertEq _t405 (51 : Int) 1187
      let _t407 ← SudoRt.atL b (51 : Int)
      let _as408 ← SudoRt.sudoAssertEq _t407 (50 : Int) 1188
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb414 := SudoRt.appendL blocks block
    let ⟨_nr415, _⟩ := _mb414
    let blocks := _nr415
    let _hm411 := ()
    let _u416 := _hm411
    let _mb417 := SudoRt.appendL blocks block
    let ⟨_nr418, _⟩ := _mb417
    let blocks := _nr418
    let _hm412 := ()
    let _u419 := _hm412
    let _t420 ← ecb_encrypt blocks key
    let ecb := _t420
    let _t421 ← SudoRt.atL ecb (0 : Int)
    let _t422 ← SudoRt.atL ecb (1 : Int)
    let _as423 ← SudoRt.sudoAssertEq _t421 _t422 1197
    let _t424 ← ecb_decrypt ecb key
    let _as425 ← SudoRt.sudoAssertEq _t424 blocks 1198
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init438 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init438 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t427 ← SudoRt.subI (38 : Int) i
  let _mb428 := SudoRt.appendL nonce _t427
  let ⟨_nr429, _⟩ := _mb428
  let nonce := _nr429
  let _hm413 := ()
  let _u430 := _hm413
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
      let _t431 ← ctr_encrypt blocks key nonce
      let ctr := _t431
      let _t432 ← SudoRt.atL ctr (0 : Int)
      let _t433 ← SudoRt.atL ctr (1 : Int)
      let _as435 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t432 _t433)) 1203
      let _t436 ← ctr_decrypt ctr key nonce
      let _as437 ← SudoRt.sudoAssertEq _t436 blocks 1204
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_deal_under_reverses_the_packet_and_undeal_puts_it_back", fun _ => test_deal_under_reverses_the_packet_and_undeal_puts_it_back), ("test_one_pass_step_by_hand_2_of_hearts_deals_3_then_cuts_2", fun _ => test_one_pass_step_by_hand_2_of_hearts_deals_3_then_cuts_2), ("test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move", fun _ => test_2_of_hearts_and_ace_of_spades_no_longer_make_the_same_move), ("test_suit_labels_add_and_multiply_in_gf_4", fun _ => test_suit_labels_add_and_multiply_in_gf_4), ("test_row_total_is_the_two_running_totals", fun _ => test_row_total_is_the_two_running_totals), ("test_sum_ranks_leaves_whole_suit_rows_alone", fun _ => test_sum_ranks_leaves_whole_suit_rows_alone), ("test_sum_ranks_sees_a_k_q_swap_that_v9_missed", fun _ => test_sum_ranks_sees_a_k_q_swap_that_v9_missed), ("test_overflow_scan_drops_a_row_when_the_row_is_full", fun _ => test_overflow_scan_drops_a_row_when_the_row_is_full), ("test_the_finger_stays_on_the_target_after_a_block", fun _ => test_the_finger_stays_on_the_target_after_a_block), ("test_grid_cycle_sees_the_k_k_swap_that_v10_missed", fun _ => test_grid_cycle_sees_the_k_k_swap_that_v10_missed), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
