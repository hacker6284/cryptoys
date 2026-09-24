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
      let _as8 ← SudoRt.sudoAssertEq _t7 deck 765
      let _t9 ← lay_rm deck
      let _t10 ← scoop_rm _t9
      let _as11 ← SudoRt.sudoAssertEq _t10 deck 766
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
      let _as24 ← SudoRt.sudoAssertEq _t23 deck 772
      let _t25 ← lay_cm deck
      let _t26 ← shift_rows _t25
      let _t27 ← inv_shift_rows _t26
      let _t28 ← scoop_cm _t27
      let _as29 ← SudoRt.sudoAssertEq _t28 deck 773
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
      let _as39 ← SudoRt.sudoAssertEq _t38 deck 779
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
      let _as53 ← SudoRt.sudoAssertEq _t52 deck 787
      let _t54 ← passkey deck
      let derived := _t54
      let _as56 ← SudoRt.sudoAssertEq (SudoRt.listLen derived) (52 : Int) 789
      let _t57 ← same_cards derived deck
      let _as58 ← SudoRt.sudoAssert _t57 790
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
      let _as74 ← SudoRt.sudoAssertEq _t73 identity 800
      let _t75 ← passkey_inv identity
      let _t76 ← passkey _t75
      let _as77 ← SudoRt.sudoAssertEq _t76 identity 801
      let _t78 ← passkey reversed
      let _t79 ← passkey_inv _t78
      let _as80 ← SudoRt.sudoAssertEq _t79 reversed 802
      let _t81 ← passkey_inv reversed
      let _t82 ← passkey _t81
      let _as83 ← SudoRt.sudoAssertEq _t82 reversed 803
      let _t84 ← passkey mixed
      let _t85 ← passkey_inv _t84
      let _as86 ← SudoRt.sudoAssertEq _t85 mixed 804
      let _t87 ← passkey_inv mixed
      let _t88 ← passkey _t87
      let _as89 ← SudoRt.sudoAssertEq _t88 mixed 805
      let _t90 ← passkey key
      let _t91 ← passkey_inv _t90
      let _as92 ← SudoRt.sudoAssertEq _t91 key 806
      let _t93 ← passkey_inv key
      let _t94 ← passkey _t93
      let _as95 ← SudoRt.sudoAssertEq _t94 key 807
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
      let _as100 ← SudoRt.sudoAssertEq built key 813
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_decrypt_undoes_encrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let cipher := (#[(49 : Int), (48 : Int), (9 : Int), (39 : Int), (29 : Int), (37 : Int), (22 : Int), (0 : Int), (16 : Int), (44 : Int), (24 : Int), (43 : Int), (8 : Int), (23 : Int), (33 : Int), (14 : Int), (12 : Int), (17 : Int), (41 : Int), (4 : Int), (19 : Int), (46 : Int), (34 : Int), (26 : Int), (50 : Int), (13 : Int), (51 : Int), (20 : Int), (10 : Int), (28 : Int), (1 : Int), (35 : Int), (6 : Int), (7 : Int), (38 : Int), (31 : Int), (47 : Int), (36 : Int), (5 : Int), (30 : Int), (3 : Int), (27 : Int), (11 : Int), (2 : Int), (18 : Int), (42 : Int), (15 : Int), (40 : Int), (25 : Int), (32 : Int), (45 : Int), (21 : Int)] : Array (Int))
    let _t106 ← encrypt message key
    let _as107 ← SudoRt.sudoAssertEq _t106 cipher 819
    let _t108 ← decrypt cipher key
    let _as109 ← SudoRt.sudoAssertEq _t108 message 820
    pure ()

def test_walking_decrypt_matches_expand_keys_decrypt : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t110 ← encrypt message key
    let cipher := _t110
    let _t111 ← expand_keys key
    let keys := _t111
    let _t112 ← SudoRt.atL keys (6 : Int)
    let _t113 ← inv_final_round cipher _t112
    let listed := _t113
    let _fromV := (5 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
    let _init122 := (_fromV, listed)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init122 fuel (fun σ =>
    let r := σ.1
    let listed := σ.2
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, listed))
      else
        match ← ((do
  let _t115 ← SudoRt.atL keys r
  let _t116 ← inv_full_round listed _t115
  let listed := _t116
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
      let _t117 ← SudoRt.atL keys (0 : Int)
      let _t118 ← inverse_compose listed _t117
      let listed := _t118
      let _t119 ← decrypt cipher key
      let _as120 ← SudoRt.sudoAssertEq listed _t119 831
      let _as121 ← SudoRt.sudoAssertEq listed message 832
      pure ()) (fun r => pure r))
    pure _out

def test_trace_ends_at_the_ciphertext : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t123 ← trace_encrypt message key
    let traced := _t123
    let _t125 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t126 ← SudoRt.atL traced _t125
    let last := _t126
    let _t127 ← encrypt message key
    let _as128 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t127 839
    let _as129 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 840
    let marked := (0 : Int)
    let held := (0 : Int)
    let passes := (0 : Int)
    let _t171 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t171
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init179 := (_fromV, (marked, held, passes))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init179 fuel (fun σ =>
    let n := σ.1
    let marked := σ.2.1
    let _sp175 := σ.2.2
    let held := _sp175.1
    let _sp176 := _sp175.2
    let passes := _sp176
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (n, (marked, held, passes)))
      else
        match ← ((do
  let _t131 ← SudoRt.atL traced n
  let _t133 ← (if (SudoRt.SEq.beq (_t131).sudo_4Step_4kind (#[109, 97, 114, 107] : Array Int)) then (do
  let _t134 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t134).sudo_4Step_3row (2 : Int))) else pure false)
  let _t136 ← (if _t133 then (do
  let _t137 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t137).sudo_4Step_3col (0 : Int))) else pure false)
  if _t136 then
    do
      let _t139 ← SudoRt.addI marked (1 : Int)
      let marked := _t139
      let _t140 ← SudoRt.atL traced n
      let _t142 ← (if (SudoRt.SEq.beq (_t140).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t143 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t143).sudo_4Step_3row (0 : Int))) else pure false)
      let _t145 ← (if _t142 then (do
  let _t146 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t146).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t145 then
        do
          let _t148 ← SudoRt.addI held (1 : Int)
          let held := _t148
          let _t149 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t149).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t151 ← SudoRt.addI passes (1 : Int)
              let passes := _t151
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t152 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t152).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t154 ← SudoRt.addI passes (1 : Int)
              let passes := _t154
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
  else
    do
      let _t155 ← SudoRt.atL traced n
      let _t157 ← (if (SudoRt.SEq.beq (_t155).sudo_4Step_4kind (#[115, 104, 105, 102, 116] : Array Int)) then (do
  let _t158 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t158).sudo_4Step_3row (0 : Int))) else pure false)
      let _t160 ← (if _t157 then (do
  let _t161 ← SudoRt.atL traced n
  pure (SudoRt.SEq.beq (_t161).sudo_4Step_6amount (0 : Int))) else pure false)
      if _t160 then
        do
          let _t163 ← SudoRt.addI held (1 : Int)
          let held := _t163
          let _t164 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t164).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t166 ← SudoRt.addI passes (1 : Int)
              let passes := _t166
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
          else
            do
              pure (SudoRt.Flow.cont (ρ := Unit) (marked, held, passes))
      else
        do
          let _t167 ← SudoRt.atL traced n
          if (SudoRt.SEq.beq (_t167).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int)) then
            do
              let _t169 ← SudoRt.addI passes (1 : Int)
              let passes := _t169
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
    let _sp177 := σ.2.2
    let held := _sp177.1
    let _sp178 := _sp177.2
    let passes := _sp178
    do
      let _as172 ← SudoRt.sudoAssertEq marked (5 : Int) 851
      let _as173 ← SudoRt.sudoAssertEq held (6 : Int) 852
      let _as174 ← SudoRt.sudoAssertEq passes (312 : Int) 853
      pure ()) (fun r => pure r))
    pure _out

def test_one_key_deck_is_passed_between_the_rounds_that_use_it : Except SudoRt.Trap Unit :=
  do
    let message := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t180 ← trace_encrypt message key
    let traced := _t180
    let _t181 ← SudoRt.atL traced (0 : Int)
    let _as182 ← SudoRt.sudoAssertEq (_t181).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int) 859
    let _t183 ← SudoRt.atL traced (0 : Int)
    let _as184 ← SudoRt.sudoAssertEq (_t183).sudo_4Step_3key key 860
    let i := (1 : Int)
    let built := key
    let _fromV := (1 : Int)
    let _toV := (6 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init211 := (_fromV, (built, i))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init211 fuel (fun σ =>
    let r := σ.1
    let built := σ.2.1
    let _sp209 := σ.2.2
    let i := _sp209
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, (built, i)))
      else
        match ← ((do
  let _t186 ← passkey built
  let built := _t186
  let _fromV := (0 : Int)
  let _toV := (51 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init206 := (_fromV, i)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init206 fuel (fun σ =>
    let p := σ.1
    let i := σ.2
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (p, i))
      else
        match ← ((do
  let _t188 ← SudoRt.atL traced i
  let _as189 ← SudoRt.sudoAssertEq (_t188).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int) 866
  let _t190 ← SudoRt.addI i (1 : Int)
  let i := _t190
  pure (SudoRt.Flow.cont (ρ := Unit) i)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
        | .cont _fs => do
            if p == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
            else do
              let i' ← SudoRt.addI p (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let i := σ.2
    do
      let _t191 ← SudoRt.atL traced i
      let _as192 ← SudoRt.sudoAssertEq (_t191).sudo_4Step_4kind (#[100, 101, 97, 108] : Array Int) 868
      let _t193 ← SudoRt.atL traced i
      let _as194 ← SudoRt.sudoAssertEq (_t193).sudo_4Step_3key built 869
      let _t195 ← SudoRt.addI i (1 : Int)
      let i := _t195
      let _init205 := i
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init205 (2 ^ 32) (fun σ =>
    let i := σ
    do
      let _t200 ← SudoRt.atL traced i
      if !((!(SudoRt.SEq.beq (_t200).sudo_4Step_4kind (#[99, 111, 109, 112, 111, 115, 101] : Array Int)))) then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t196 ← SudoRt.atL traced i
  let _as198 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq (_t196).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int))) 872
  let _t199 ← SudoRt.addI i (1 : Int)
  let i := _t199
  pure (SudoRt.Flow.cont (ρ := Unit) i)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) _fs)
        | .cont _fs => (let i := _fs; pure (SudoRt.Flow.cont (ρ := Unit) i))) (fun σ =>
    let i := σ
    do
      let _t202 ← SudoRt.atL traced i
      let _as203 ← SudoRt.sudoAssertEq (_t202).sudo_4Step_3key built 874
      let _t204 ← SudoRt.addI i (1 : Int)
      let i := _t204
      pure (SudoRt.Flow.cont (ρ := Unit) (built, i))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let built := σ.2.1
    let _sp210 := σ.2.2
    let i := _sp210
    do
      let _as208 ← SudoRt.sudoAssertEq i (SudoRt.listLen traced) 876
      pure ()) (fun r => pure r))
    pure _out

def test_decrypt_trace_un_passes_from_k6 : Except SudoRt.Trap Unit :=
  do
    let cipher := (#[(49 : Int), (48 : Int), (9 : Int), (39 : Int), (29 : Int), (37 : Int), (22 : Int), (0 : Int), (16 : Int), (44 : Int), (24 : Int), (43 : Int), (8 : Int), (23 : Int), (33 : Int), (14 : Int), (12 : Int), (17 : Int), (41 : Int), (4 : Int), (19 : Int), (46 : Int), (34 : Int), (26 : Int), (50 : Int), (13 : Int), (51 : Int), (20 : Int), (10 : Int), (28 : Int), (1 : Int), (35 : Int), (6 : Int), (7 : Int), (38 : Int), (31 : Int), (47 : Int), (36 : Int), (5 : Int), (30 : Int), (3 : Int), (27 : Int), (11 : Int), (2 : Int), (18 : Int), (42 : Int), (15 : Int), (40 : Int), (25 : Int), (32 : Int), (45 : Int), (21 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let _t212 ← trace_decrypt cipher key
    let traced := _t212
    let _t214 ← SudoRt.subI (SudoRt.listLen traced) (1 : Int)
    let _t215 ← SudoRt.atL traced _t214
    let last := _t215
    let _as216 ← SudoRt.sudoAssertEq (last).sudo_4Step_4kind (#[117, 110, 99, 111, 109, 112, 111, 115, 101] : Array Int) 883
    let _as217 ← SudoRt.sudoAssertEq (last).sudo_4Step_3key key 884
    let _t218 ← decrypt cipher key
    let _as219 ← SudoRt.sudoAssertEq (last).sudo_4Step_4hand _t218 885
    let i := (0 : Int)
    let passes := (0 : Int)
    let unpasses := (0 : Int)
    let built := key
    let _fromV := (1 : Int)
    let _toV := (6 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init279 := (_fromV, (built, passes, i))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init279 fuel (fun σ =>
    let r := σ.1
    let built := σ.2.1
    let _sp275 := σ.2.2
    let passes := _sp275.1
    let _sp276 := _sp275.2
    let i := _sp276
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, (built, passes, i)))
      else
        match ← ((do
  let _t221 ← passkey built
  let built := _t221
  let _fromV := (0 : Int)
  let _toV := (51 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init229 := (_fromV, (passes, i))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init229 fuel (fun σ =>
    let p := σ.1
    let passes := σ.2.1
    let _sp227 := σ.2.2
    let i := _sp227
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (p, (passes, i)))
      else
        match ← ((do
  let _t223 ← SudoRt.atL traced i
  let _as224 ← SudoRt.sudoAssertEq (_t223).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int) 893
  let _t225 ← SudoRt.addI passes (1 : Int)
  let passes := _t225
  let _t226 ← SudoRt.addI i (1 : Int)
  let i := _t226
  pure (SudoRt.Flow.cont (ρ := Unit) (passes, i))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
        | .cont _fs => do
            if p == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
            else do
              let i' ← SudoRt.addI p (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let passes := σ.2.1
    let _sp228 := σ.2.2
    let i := _sp228
    do
      pure (SudoRt.Flow.cont (ρ := Unit) (built, passes, i))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let built := σ.2.1
    let _sp277 := σ.2.2
    let passes := _sp277.1
    let _sp278 := _sp277.2
    let i := _sp278
    do
      let _t230 ← SudoRt.atL traced i
      let _as231 ← SudoRt.sudoAssertEq (_t230).sudo_4Step_4kind (#[117, 110, 99, 111, 109, 112, 111, 115, 101] : Array Int) 896
      let _t232 ← SudoRt.atL traced i
      let _as233 ← SudoRt.sudoAssertEq (_t232).sudo_4Step_3key built 897
      let _t234 ← SudoRt.addI i (1 : Int)
      let i := _t234
      let _init274 := i
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init274 (2 ^ 32) (fun σ =>
    let i := σ
    do
      let _t239 ← SudoRt.atL traced i
      if !((!(SudoRt.SEq.beq (_t239).sudo_4Step_4kind (#[117, 110, 112, 97, 115, 115] : Array Int)))) then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t235 ← SudoRt.atL traced i
  let _as237 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq (_t235).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int))) 900
  let _t238 ← SudoRt.addI i (1 : Int)
  let i := _t238
  pure (SudoRt.Flow.cont (ρ := Unit) i)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) _fs)
        | .cont _fs => (let i := _fs; pure (SudoRt.Flow.cont (ρ := Unit) i))) (fun σ =>
    let i := σ
    do
      let _fromV := (5 : Int)
      let _toV := (0 : Int)
      let fuel : Nat := if _fromV < _toV then 1 else (_fromV - _toV).natAbs + 1
      let _init273 := (_fromV, (built, unpasses, i))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init273 fuel (fun σ =>
    let r := σ.1
    let built := σ.2.1
    let _sp269 := σ.2.2
    let unpasses := _sp269.1
    let _sp270 := _sp269.2
    let i := _sp270
    do
      if r < _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (r, (built, unpasses, i)))
      else
        match ← ((do
  let _t242 ← passkey_inv built
  let built := _t242
  let _fromV := (0 : Int)
  let _toV := (51 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init263 := (_fromV, (unpasses, i))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init263 fuel (fun σ =>
    let p := σ.1
    let unpasses := σ.2.1
    let _sp261 := σ.2.2
    let i := _sp261
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (p, (unpasses, i)))
      else
        match ← ((do
  let _t244 ← SudoRt.atL traced i
  let _as245 ← SudoRt.sudoAssertEq (_t244).sudo_4Step_4kind (#[117, 110, 112, 97, 115, 115] : Array Int) 905
  let _t246 ← SudoRt.addI unpasses (1 : Int)
  let unpasses := _t246
  let _t247 ← SudoRt.addI i (1 : Int)
  let i := _t247
  pure (SudoRt.Flow.cont (ρ := Unit) (unpasses, i))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
        | .cont _fs => do
            if p == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (p, _fs))
            else do
              let i' ← SudoRt.addI p (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let unpasses := σ.2.1
    let _sp262 := σ.2.2
    let i := _sp262
    do
      let _t248 ← SudoRt.atL traced i
      let _as249 ← SudoRt.sudoAssertEq (_t248).sudo_4Step_4kind (#[117, 110, 99, 111, 109, 112, 111, 115, 101] : Array Int) 908
      let _t250 ← SudoRt.atL traced i
      let _as251 ← SudoRt.sudoAssertEq (_t250).sudo_4Step_3key built 909
      let _t252 ← SudoRt.addI i (1 : Int)
      let i := _t252
      if (decide (r > (0 : Int))) then
        do
          let _init260 := i
          let _out ← (SudoRt.runLoopOn (ρ := Unit) _init260 (2 ^ 32) (fun σ =>
    let i := σ
    do
      let _t258 ← SudoRt.atL traced i
      if !((!(SudoRt.SEq.beq (_t258).sudo_4Step_4kind (#[117, 110, 112, 97, 115, 115] : Array Int)))) then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t254 ← SudoRt.atL traced i
  let _as256 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq (_t254).sudo_4Step_4kind (#[112, 97, 115, 115] : Array Int))) 913
  let _t257 ← SudoRt.addI i (1 : Int)
  let i := _t257
  pure (SudoRt.Flow.cont (ρ := Unit) i)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) _fs)
        | .cont _fs => (let i := _fs; pure (SudoRt.Flow.cont (ρ := Unit) i))) (fun σ =>
    let i := σ
    do
      pure (SudoRt.Flow.cont (ρ := Unit) (built, unpasses, i))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
          pure _out
      else
        do
          pure (SudoRt.Flow.cont (ρ := Unit) (built, unpasses, i))) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (r, _fs))
            else do
              let i' ← SudoRt.subI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let built := σ.2.1
    let _sp271 := σ.2.2
    let unpasses := _sp271.1
    let _sp272 := _sp271.2
    let i := _sp272
    do
      let _as265 ← SudoRt.sudoAssertEq i (SudoRt.listLen traced) 915
      let _as266 ← SudoRt.sudoAssertEq built key 916
      let _as267 ← SudoRt.sudoAssertEq passes (312 : Int) 917
      let _as268 ← SudoRt.sudoAssertEq unpasses (312 : Int) 918
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_counter_rail_keeps_the_nonce_and_permutes_diamonds : Except SudoRt.Trap Unit :=
  do
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init301 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init301 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _mb282 := SudoRt.appendL nonce i
  let ⟨_nr283, _⟩ := _mb282
  let nonce := _nr283
  let _hm280 := ()
  let _u284 := _hm280
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
      let _t285 ← counter_deck nonce (0 : Int)
      let a := _t285
      let _t286 ← counter_deck nonce (1 : Int)
      let b := _t286
      let _fromV := (0 : Int)
      let _toV := (38 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init300 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init300 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t288 ← SudoRt.atL a i
  let _as289 ← SudoRt.sudoAssertEq _t288 i 927
  let _t290 ← SudoRt.atL b i
  let _as291 ← SudoRt.sudoAssertEq _t290 i 928
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
      let _t292 ← SudoRt.atL a (50 : Int)
      let _as293 ← SudoRt.sudoAssertEq _t292 (50 : Int) 929
      let _t294 ← SudoRt.atL a (51 : Int)
      let _as295 ← SudoRt.sudoAssertEq _t294 (51 : Int) 930
      let _t296 ← SudoRt.atL b (50 : Int)
      let _as297 ← SudoRt.sudoAssertEq _t296 (51 : Int) 931
      let _t298 ← SudoRt.atL b (51 : Int)
      let _as299 ← SudoRt.sudoAssertEq _t298 (50 : Int) 932
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_ecb_repeats_a_block_and_ctr_does_not : Except SudoRt.Trap Unit :=
  do
    let block := (#[(0 : Int), (32 : Int), (38 : Int), (42 : Int), (13 : Int), (19 : Int), (17 : Int), (5 : Int), (41 : Int), (25 : Int), (48 : Int), (6 : Int), (31 : Int), (44 : Int), (3 : Int), (16 : Int), (7 : Int), (4 : Int), (34 : Int), (40 : Int), (18 : Int), (49 : Int), (14 : Int), (51 : Int), (20 : Int), (46 : Int), (28 : Int), (11 : Int), (10 : Int), (15 : Int), (45 : Int), (43 : Int), (2 : Int), (26 : Int), (22 : Int), (8 : Int), (37 : Int), (33 : Int), (12 : Int), (35 : Int), (24 : Int), (50 : Int), (39 : Int), (30 : Int), (21 : Int), (1 : Int), (27 : Int), (47 : Int), (36 : Int), (23 : Int), (29 : Int), (9 : Int)] : Array (Int))
    let key := (#[(48 : Int), (42 : Int), (25 : Int), (26 : Int), (3 : Int), (37 : Int), (39 : Int), (50 : Int), (11 : Int), (2 : Int), (43 : Int), (8 : Int), (10 : Int), (7 : Int), (40 : Int), (38 : Int), (34 : Int), (0 : Int), (49 : Int), (51 : Int), (22 : Int), (27 : Int), (23 : Int), (9 : Int), (12 : Int), (15 : Int), (44 : Int), (41 : Int), (21 : Int), (28 : Int), (20 : Int), (13 : Int), (19 : Int), (14 : Int), (45 : Int), (31 : Int), (35 : Int), (18 : Int), (17 : Int), (30 : Int), (6 : Int), (36 : Int), (47 : Int), (16 : Int), (1 : Int), (33 : Int), (29 : Int), (5 : Int), (46 : Int), (32 : Int), (24 : Int), (4 : Int)] : Array (Int))
    let blocks := (#[] : Array (Array (Int)))
    let _mb305 := SudoRt.appendL blocks block
    let ⟨_nr306, _⟩ := _mb305
    let blocks := _nr306
    let _hm302 := ()
    let _u307 := _hm302
    let _mb308 := SudoRt.appendL blocks block
    let ⟨_nr309, _⟩ := _mb308
    let blocks := _nr309
    let _hm303 := ()
    let _u310 := _hm303
    let _t311 ← ecb_encrypt blocks key
    let ecb := _t311
    let _t312 ← SudoRt.atL ecb (0 : Int)
    let _t313 ← SudoRt.atL ecb (1 : Int)
    let _as314 ← SudoRt.sudoAssertEq _t312 _t313 941
    let _t315 ← ecb_decrypt ecb key
    let _as316 ← SudoRt.sudoAssertEq _t315 blocks 942
    let nonce := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (38 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init329 := (_fromV, nonce)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init329 fuel (fun σ =>
    let i := σ.1
    let nonce := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, nonce))
      else
        match ← ((do
  let _t318 ← SudoRt.subI (38 : Int) i
  let _mb319 := SudoRt.appendL nonce _t318
  let ⟨_nr320, _⟩ := _mb319
  let nonce := _nr320
  let _hm304 := ()
  let _u321 := _hm304
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
      let _t322 ← ctr_encrypt blocks key nonce
      let ctr := _t322
      let _t323 ← SudoRt.atL ctr (0 : Int)
      let _t324 ← SudoRt.atL ctr (1 : Int)
      let _as326 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t323 _t324)) 947
      let _t327 ← ctr_decrypt ctr key nonce
      let _as328 ← SudoRt.sudoAssertEq _t327 blocks 948
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_column_and_row_deals_are_inverses", fun _ => test_column_and_row_deals_are_inverses), ("test_sum_ranks_and_shift_rows_invert", fun _ => test_sum_ranks_and_shift_rows_invert), ("test_grid_cycle_inverts", fun _ => test_grid_cycle_inverts), ("test_compose_inverts_and_passkey_keeps_the_deck", fun _ => test_compose_inverts_and_passkey_keeps_the_deck), ("test_passkey_inverse_is_a_two_sided_inverse", fun _ => test_passkey_inverse_is_a_two_sided_inverse), ("test_decrypt_undoes_encrypt", fun _ => test_decrypt_undoes_encrypt), ("test_walking_decrypt_matches_expand_keys_decrypt", fun _ => test_walking_decrypt_matches_expand_keys_decrypt), ("test_trace_ends_at_the_ciphertext", fun _ => test_trace_ends_at_the_ciphertext), ("test_one_key_deck_is_passed_between_the_rounds_that_use_it", fun _ => test_one_key_deck_is_passed_between_the_rounds_that_use_it), ("test_decrypt_trace_un_passes_from_k6", fun _ => test_decrypt_trace_un_passes_from_k6), ("test_counter_rail_keeps_the_nonce_and_permutes_diamonds", fun _ => test_counter_rail_keeps_the_nonce_and_permutes_diamonds), ("test_ecb_repeats_a_block_and_ctr_does_not", fun _ => test_ecb_repeats_a_block_and_ctr_does_not)]
