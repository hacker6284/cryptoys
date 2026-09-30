-- DO NOT EDIT. Generated from megadreifach.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for megadreifach.sudo
import SudoRt
import Megadreifach
set_option linter.unusedVariables false
open Megadreifach

def test_identity_rank_is_29_zero_bytes : Except SudoRt.Trap Unit :=
  do
    let _t1 ← identity
    let _t2 ← position_to_bytes _t1
    let z := _t2
    let _as4 ← SudoRt.sudoAssertEq (SudoRt.listLen z) digest_len 889
    let _fromV := (0 : Int)
    let _toV := (28 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init8 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init8 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t6 ← SudoRt.atL z i
  let _as7 ← SudoRt.sudoAssertEq _t6 (0 : Int) 891
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
      pure ()) (fun r => pure r))
    pure _out

def test_compose_inverse_round_trip : Except SudoRt.Trap Unit :=
  do
    let _t9 ← face_move (3 : Int)
    let _t10 ← face_move (7 : Int)
    let _t11 ← compose _t9 _t10
    let t := _t11
    let _t12 ← identity
    let idp := _t12
    let _t13 ← inverse t
    let _t14 ← compose t _t13
    let left := _t14
    let _t15 ← inverse t
    let _t16 ← compose _t15 t
    let right := _t16
    let _as17 ← SudoRt.sudoAssertEq (left).sudo_8Position_2cp (idp).sudo_8Position_2cp 898
    let _as18 ← SudoRt.sudoAssertEq (left).sudo_8Position_2co (idp).sudo_8Position_2co 899
    let _as19 ← SudoRt.sudoAssertEq (left).sudo_8Position_2ep (idp).sudo_8Position_2ep 900
    let _as20 ← SudoRt.sudoAssertEq (left).sudo_8Position_2eo (idp).sudo_8Position_2eo 901
    let _as21 ← SudoRt.sudoAssertEq (right).sudo_8Position_2cp (idp).sudo_8Position_2cp 902
    let _as22 ← SudoRt.sudoAssertEq (right).sudo_8Position_2co (idp).sudo_8Position_2co 903
    let _as23 ← SudoRt.sudoAssertEq (right).sudo_8Position_2ep (idp).sudo_8Position_2ep 904
    let _as24 ← SudoRt.sudoAssertEq (right).sudo_8Position_2eo (idp).sudo_8Position_2eo 905
    pure ()

def test_iv_cook12_digest : Except SudoRt.Trap Unit :=
  do
    let _t25 ← iv_cook12
    let _t26 ← position_to_bytes _t25
    let d := _t26
    let _t27 ← hex_iv
    let _as28 ← SudoRt.sudoAssertEq d _t27 909
    pure ()

def test_empty_pad_is_one_block : Except SudoRt.Trap Unit :=
  do
    let _t29 ← pad_message (#[] : Array (Int))
    let p := _t29
    let _as31 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 913
    let _t32 ← SudoRt.atL p (0 : Int)
    let _as33 ← SudoRt.sudoAssertEq _t32 (128 : Int) 914
    let _fromV := (1 : Int)
    let _toV := (27 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init37 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init37 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t35 ← SudoRt.atL p i
  let _as36 ← SudoRt.sudoAssertEq _t35 (0 : Int) 916
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
      pure ()) (fun r => pure r))
    pure _out

def test_kat_pad_lengths : Except SudoRt.Trap Unit :=
  do
    let _t43 ← pad_message (#[] : Array (Int))
    let _as45 ← SudoRt.sudoAssertEq (SudoRt.listLen _t43) (28 : Int) 919
    let _t46 ← pad_message (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let _as48 ← SudoRt.sudoAssertEq (SudoRt.listLen _t46) (28 : Int) 920
    let _t49 ← pad_message (#[(0 : Int)] : Array (Int))
    let _as51 ← SudoRt.sudoAssertEq (SudoRt.listLen _t49) (28 : Int) 921
    let m27 := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (26 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init93 := (_fromV, m27)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init93 fuel (fun σ =>
    let i := σ.1
    let m27 := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, m27))
      else
        match ← ((do
  let _mb53 := SudoRt.appendL m27 i
  let ⟨_nr54, _⟩ := _mb53
  let m27 := _nr54
  let _hm38 := ()
  let _u55 := _hm38
  pure (SudoRt.Flow.cont (ρ := Unit) m27)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let m27 := σ.2
    do
      let _t56 ← pad_message m27
      let _as58 ← SudoRt.sudoAssertEq (SudoRt.listLen _t56) (56 : Int) 925
      let m28 := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (27 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init92 := (_fromV, m28)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init92 fuel (fun σ =>
    let i := σ.1
    let m28 := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, m28))
      else
        match ← ((do
  let _mb60 := SudoRt.appendL m28 i
  let ⟨_nr61, _⟩ := _mb60
  let m28 := _nr61
  let _hm39 := ()
  let _u62 := _hm39
  pure (SudoRt.Flow.cont (ρ := Unit) m28)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let m28 := σ.2
    do
      let _t63 ← pad_message m28
      let _as65 ← SudoRt.sudoAssertEq (SudoRt.listLen _t63) (56 : Int) 929
      let m29 := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (28 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init91 := (_fromV, m29)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init91 fuel (fun σ =>
    let i := σ.1
    let m29 := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, m29))
      else
        match ← ((do
  let _mb67 := SudoRt.appendL m29 i
  let ⟨_nr68, _⟩ := _mb67
  let m29 := _nr68
  let _hm40 := ()
  let _u69 := _hm40
  pure (SudoRt.Flow.cont (ρ := Unit) m29)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let m29 := σ.2
    do
      let _t70 ← pad_message m29
      let _as72 ← SudoRt.sudoAssertEq (SudoRt.listLen _t70) (56 : Int) 933
      let m56 := (#[] : Array (Int))
      let _fromV := (1 : Int)
      let _toV := (56 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init90 := (_fromV, m56)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init90 fuel (fun σ =>
    let i := σ.1
    let m56 := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, m56))
      else
        match ← ((do
  let _mb74 := SudoRt.appendL m56 (109 : Int)
  let ⟨_nr75, _⟩ := _mb74
  let m56 := _nr75
  let _hm41 := ()
  let _u76 := _hm41
  pure (SudoRt.Flow.cont (ρ := Unit) m56)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let m56 := σ.2
    do
      let _t77 ← pad_message m56
      let _as79 ← SudoRt.sudoAssertEq (SudoRt.listLen _t77) (84 : Int) 937
      let m100 := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (99 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init89 := (_fromV, m100)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init89 fuel (fun σ =>
    let i := σ.1
    let m100 := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, m100))
      else
        match ← ((do
  let _t81 ← SudoRt.mulI i (17 : Int)
  let _t82 ← SudoRt.modI _t81 (256 : Int)
  let _mb83 := SudoRt.appendL m100 _t82
  let ⟨_nr84, _⟩ := _mb83
  let m100 := _nr84
  let _hm42 := ()
  let _u85 := _hm42
  pure (SudoRt.Flow.cont (ρ := Unit) m100)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let m100 := σ.2
    do
      let _t86 ← pad_message m100
      let _as88 ← SudoRt.sudoAssertEq (SudoRt.listLen _t86) (112 : Int) 941
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_abc_pad_recovers_the_24_bit_length : Except SudoRt.Trap Unit :=
  do
    let _t94 ← pad_message (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let p := _t94
    let _as96 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 945
    let _t97 ← SudoRt.atL p (0 : Int)
    let _as98 ← SudoRt.sudoAssertEq _t97 (97 : Int) 946
    let _t99 ← SudoRt.atL p (1 : Int)
    let _as100 ← SudoRt.sudoAssertEq _t99 (98 : Int) 947
    let _t101 ← SudoRt.atL p (2 : Int)
    let _as102 ← SudoRt.sudoAssertEq _t101 (99 : Int) 948
    let _t103 ← SudoRt.atL p (3 : Int)
    let _as104 ← SudoRt.sudoAssertEq _t103 (128 : Int) 949
    let _t105 ← SudoRt.atL p (27 : Int)
    let _as106 ← SudoRt.sudoAssertEq _t105 (24 : Int) 950
    pure ()

def test_phi_of_28_zero_bytes_is_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t107 ← SudoRt.filledL (28 : Int) (0 : Int)
    let z := _t107
    let _t108 ← phi_chunk z
    let deal := _t108
    let _as110 ← SudoRt.sudoAssertEq (SudoRt.listLen deal) (52 : Int) 955
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init118 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init118 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t112 ← SudoRt.atL deal i
  let _as113 ← SudoRt.sudoAssertEq _t112 i 957
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
      let _t114 ← require_permutation deal
      let _as115 ← SudoRt.sudoAssertEq _t114 deal 958
      let _t116 ← phi_inv deal
      let _as117 ← SudoRt.sudoAssertEq _t116 z 959
      pure ()) (fun r => pure r))
    pure _out

def test_hash_aliases_agree_on_the_empty_message : Except SudoRt.Trap Unit :=
  do
    let _t119 ← v_Hash (#[] : Array (Int))
    let d := _t119
    let _as121 ← SudoRt.sudoAssertEq (SudoRt.listLen d) digest_len 963
    let _t122 ← v_MegaDreifach (#[] : Array (Int))
    let _as123 ← SudoRt.sudoAssertEq _t122 d 964
    pure ()

def test_hashdeckbody_on_the_identity_deal_is_29_bytes : Except SudoRt.Trap Unit :=
  do
    let _t124 ← range_list (52 : Int)
    let deal := _t124
    let _t125 ← v_HashDeckBody deal
    let b := _t125
    let _as127 ← SudoRt.sudoAssertEq (SudoRt.listLen b) digest_len 969
    let _t128 ← v_MegaDreifachBody deal
    let _as129 ← SudoRt.sudoAssertEq _t128 b 970
    pure ()

def test_hashdeckbodyfrom_at_iv_matches_hashdeckbody : Except SudoRt.Trap Unit :=
  do
    let _t130 ← range_list (52 : Int)
    let deal := _t130
    let _t131 ← iv_cook12
    let iv := _t131
    let _t132 ← v_HashDeckBodyFrom deal iv
    let «from_iv» := _t132
    let _t133 ← v_HashDeckBody deal
    let _as134 ← SudoRt.sudoAssertEq «from_iv» _t133 976
    let _t135 ← v_MegaDreifachBodyFrom deal iv
    let _t136 ← v_MegaDreifachBody deal
    let _as137 ← SudoRt.sudoAssertEq _t135 _t136 977
    let _t138 ← identity
    let _t139 ← v_HashDeckBodyFrom deal _t138
    let «from_id» := _t139
    let _as141 ← SudoRt.sudoAssertEq (SudoRt.listLen «from_id») digest_len 979
    let _as143 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq «from_id» «from_iv»)) 980
    pure ()

def test_hashdecksbody_chains_hashdeckbody : Except SudoRt.Trap Unit :=
  do
    let _t145 ← range_list (52 : Int)
    let a := _t145
    let b := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init165 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init165 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, b))
      else
        match ← ((do
  let _t147 ← SudoRt.subI (51 : Int) i
  let _mb148 := SudoRt.appendL b _t147
  let ⟨_nr149, _⟩ := _mb148
  let b := _nr149
  let _hm144 := ()
  let _u150 := _hm144
  pure (SudoRt.Flow.cont (ρ := Unit) b)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let b := σ.2
    do
      let _t151 ← v_HashDecksBody (#[a] : Array (Array (Int)))
      let _t152 ← v_HashDeckBody a
      let _as153 ← SudoRt.sudoAssertEq _t151 _t152 987
      let _t154 ← iv_cook12
      let _t155 ← iv_cook12
      let _t156 ← em_block _t155 a
      let _t157 ← compose _t154 _t156
      let h1 := _t157
      let _t158 ← v_HashDecksBody (#[a, b] : Array (Array (Int)))
      let _t159 ← v_HashDeckBodyFrom b h1
      let _as160 ← SudoRt.sudoAssertEq _t158 _t159 989
      let _t161 ← v_HashDecksBody (#[a, b] : Array (Array (Int)))
      let _t162 ← v_HashDecksBody (#[b, a] : Array (Array (Int)))
      let _as164 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t161 _t162)) 990
      pure ()) (fun r => pure r))
    pure _out

def test_hashdecksbody_rejects_an_empty_list : Except SudoRt.Trap Unit :=
  do
    let «none» := (#[] : Array (Array (Int)))
    let _ex167 := (do
  let _t166 ← v_HashDecksBody «none»
  let d := _t166
  pure ()
  pure ())
    match _ex167 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 994: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 994: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_hashdecksbody_rejects_a_non_deck : Except SudoRt.Trap Unit :=
  do
    let _t168 ← range_list (52 : Int)
    let bad := _t168
    let _ix169 := (3 : Int)
    let _t170 ← SudoRt.putL bad _ix169 (4 : Int)
    let bad := _t170
    let _ex172 := (do
  let _t171 ← v_HashDecksBody (#[bad] : Array (Array (Int)))
  let e := _t171
  pure ()
  pure ())
    match _ex172 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 1000: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 1000: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_require_permutation_rejects_a_duplicate : Except SudoRt.Trap Unit :=
  do
    let _t173 ← SudoRt.filledL (52 : Int) (0 : Int)
    let bad := _t173
    let _ex176 := (do
  let _t174 ← require_permutation bad
  let _u175 := _t174
  pure ()
  pure ())
    match _ex176 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 1005: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 1005: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_v2_kat_digests_kats_megaminx_hash_kats_v2_json : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init182 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init182 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t178 ← kat_msg n
  let _t179 ← v_Hash _t178
  let _t180 ← kat_v2_digest n
  let _as181 ← SudoRt.sudoAssertEq _t179 _t180 1010
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) n)
        | .cont _fs => do
            if n == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) n)
            else do
              let i' ← SudoRt.addI n (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_v2_kat_hashdeck_of_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t183 ← range_list (52 : Int)
    let deal := _t183
    let _t184 ← v_HashDeck deal
    let _t185 ← kat_v2_digest (8 : Int)
    let _as186 ← SudoRt.sudoAssertEq _t184 _t185 1014
    let _t187 ← v_HashDeck deal
    let _t188 ← SudoRt.filledL (28 : Int) (0 : Int)
    let _t189 ← v_Hash _t188
    let _as190 ← SudoRt.sudoAssertEq _t187 _t189 1015
    pure ()

def test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init215 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init215 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t192 ← face_nbrs f
  let nb := _t192
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init207 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init207 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t194 ← SudoRt.atL nb i
  let _t195 ← edge_slot f _t194
  let s := _t195
  let _t196 ← edge_faces s
  let ⟨a, b⟩ := _t196
  let _t198 ← (if (SudoRt.SEq.beq a f) then (do
  let _t199 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq b _t199)) else pure false)
  let _t201 ← (if _t198 then pure true else (do
  let _t203 ← (if (SudoRt.SEq.beq b f) then (do
  let _t204 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq a _t204)) else pure false)
  pure _t203))
  let _as206 ← SudoRt.sudoAssert _t201 1023
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
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) f)
        | .cont _fs => do
            if f == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) f)
            else do
              let i' ← SudoRt.addI f (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init214 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init214 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t209 ← edge_faces s
  let ⟨a, b⟩ := _t209
  let _as211 ← SudoRt.sudoAssert (decide (a < b)) 1026
  let _t212 ← edge_slot a b
  let _as213 ← SudoRt.sudoAssertEq _t212 s 1027
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) s)
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) s)
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init227 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init227 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t217 ← face_move f
  let t := _t217
  let _fromV := (0 : Int)
  let _toV := (29 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init226 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init226 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t219 ← edge_faces s
  let ⟨a, b⟩ := _t219
  let _t220 ← SudoRt.atL (t).sudo_8Position_2ep s
  let moved := (!(SudoRt.SEq.beq _t220 s))
  let _t223 ← (if (SudoRt.SEq.beq f a) then pure true else (do
  pure (SudoRt.SEq.beq f b)))
  let _as225 ← SudoRt.sudoAssertEq moved _t223 1035
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) s)
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) s)
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) f)
        | .cont _fs => do
            if f == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) f)
            else do
              let i' ← SudoRt.addI f (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_edge_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_edges : Except SudoRt.Trap Unit :=
  do
    let _t228 ← identity
    let idp := _t228
    let _fromV := (0 : Int)
    let _toV := (29 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init250 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init250 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t230 ← edge_faces s
  let ⟨a, b⟩ := _t230
  let _t231 ← edge_colours_at idp a b
  let _as232 ← SudoRt.sudoAssertEq _t231 (a, b) 1041
  let _t233 ← edge_colours_at idp b a
  let _as234 ← SudoRt.sudoAssertEq _t233 (b, a) 1042
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) s)
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) s)
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _fromV := (0 : Int)
      let _toV := (11 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init249 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init249 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t236 ← identity
  let _t237 ← face_turn _t236 f (1 : Int)
  let g := _t237
  let _t238 ← face_nbrs f
  let nb := _t238
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init248 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init248 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t240 ← SudoRt.atL nb i
  let _t241 ← edge_colours_at g f _t240
  let ⟨c1, c2⟩ := _t241
  let _as242 ← SudoRt.sudoAssertEq c1 f 1048
  let _t243 ← SudoRt.atL nb i
  let _t244 ← SudoRt.atL nb i
  let _t245 ← corner_after_noon f _t244
  let _t246 ← colours_at g f _t243 _t245
  let ⟨d1, d2⟩ := _t246
  let _as247 ← SudoRt.sudoAssertEq d1 f 1050
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
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) f)
        | .cont _fs => do
            if f == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) f)
            else do
              let i' ← SudoRt.addI f (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_visual_noon_is_a_neighbour_of_the_held_face_in_all_60_grips : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (59 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init273 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init273 fuel (fun σ =>
    let r := σ
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) r)
      else
        match ← ((do
  let _t252 ← rot_at r
  let o := _t252
  let _t253 ← visual_noon held_up o
  let _t254 ← SudoRt.atL o held_front
  let _as255 ← SudoRt.sudoAssertEq _t253 _t254 1055
  let _t256 ← visual_noon held_front o
  let _t257 ← SudoRt.atL o held_up
  let _as258 ← SudoRt.sudoAssertEq _t256 _t257 1056
  let _t259 ← visual_noon held_down o
  let _t260 ← SudoRt.atL o down_noon_hold
  let _as261 ← SudoRt.sudoAssertEq _t259 _t260 1057
  let _fromV := (0 : Int)
  let _toV := (11 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init272 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init272 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t263 ← visual_noon h o
  let n := _t263
  let _t264 ← SudoRt.atL o h
  let _t265 ← face_nbrs _t264
  let nb := _t265
  let hit := (0 : Int)
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init271 := (_fromV, hit)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init271 fuel (fun σ =>
    let i := σ.1
    let hit := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, hit))
      else
        match ← ((do
  let _t267 ← SudoRt.atL nb i
  if (SudoRt.SEq.beq _t267 n) then
    do
      let _t269 ← SudoRt.addI hit (1 : Int)
      let hit := _t269
      pure (SudoRt.Flow.cont (ρ := Unit) hit)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) hit)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let hit := σ.2
    do
      let _as270 ← SudoRt.sudoAssertEq hit (1 : Int) 1065
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) h)
        | .cont _fs => do
            if h == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) h)
            else do
              let i' ← SudoRt.addI h (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) r)
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) r)
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_lower_ring_noon_is_the_upper_left_of_the_two_upper_ring_neighbours : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (59 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init292 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init292 fuel (fun σ =>
    let r := σ
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) r)
      else
        match ← ((do
  let _t275 ← rot_at r
  let o := _t275
  let _fromV := (6 : Int)
  let _toV := (10 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init291 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init291 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t277 ← visual_noon h o
  let n := _t277
  let _t278 ← hold_of n o
  let _t279 ← SudoRt.subI h (5 : Int)
  let _as280 ← SudoRt.sudoAssertEq _t278 _t279 1072
  let _t281 ← SudoRt.atL o h
  let _t282 ← corner_after_noon _t281 n
  let right := _t282
  let _t283 ← hold_of right o
  let _as285 ← SudoRt.sudoAssert (decide (_t283 ≥ (1 : Int))) 1074
  let _t286 ← hold_of right o
  let _as288 ← SudoRt.sudoAssert (decide (_t286 ≤ (5 : Int))) 1075
  let _as290 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq right n)) 1076
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) h)
        | .cont _fs => do
            if h == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) h)
            else do
              let i' ← SudoRt.addI h (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) r)
        | .cont _fs => do
            if r == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) r)
            else do
              let i' ← SudoRt.addI r (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_identity_rank_is_29_zero_bytes", fun _ => test_identity_rank_is_29_zero_bytes), ("test_compose_inverse_round_trip", fun _ => test_compose_inverse_round_trip), ("test_iv_cook12_digest", fun _ => test_iv_cook12_digest), ("test_empty_pad_is_one_block", fun _ => test_empty_pad_is_one_block), ("test_kat_pad_lengths", fun _ => test_kat_pad_lengths), ("test_abc_pad_recovers_the_24_bit_length", fun _ => test_abc_pad_recovers_the_24_bit_length), ("test_phi_of_28_zero_bytes_is_the_identity_deal", fun _ => test_phi_of_28_zero_bytes_is_the_identity_deal), ("test_hash_aliases_agree_on_the_empty_message", fun _ => test_hash_aliases_agree_on_the_empty_message), ("test_hashdeckbody_on_the_identity_deal_is_29_bytes", fun _ => test_hashdeckbody_on_the_identity_deal_is_29_bytes), ("test_hashdeckbodyfrom_at_iv_matches_hashdeckbody", fun _ => test_hashdeckbodyfrom_at_iv_matches_hashdeckbody), ("test_hashdecksbody_chains_hashdeckbody", fun _ => test_hashdecksbody_chains_hashdeckbody), ("test_hashdecksbody_rejects_an_empty_list", fun _ => test_hashdecksbody_rejects_an_empty_list), ("test_hashdecksbody_rejects_a_non_deck", fun _ => test_hashdecksbody_rejects_a_non_deck), ("test_require_permutation_rejects_a_duplicate", fun _ => test_require_permutation_rejects_a_duplicate), ("test_v2_kat_digests_kats_megaminx_hash_kats_v2_json", fun _ => test_v2_kat_digests_kats_megaminx_hash_kats_v2_json), ("test_v2_kat_hashdeck_of_the_identity_deal", fun _ => test_v2_kat_hashdeck_of_the_identity_deal), ("test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot", fun _ => test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot), ("test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot", fun _ => test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot), ("test_edge_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_edges", fun _ => test_edge_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_edges), ("test_visual_noon_is_a_neighbour_of_the_held_face_in_all_60_grips", fun _ => test_visual_noon_is_a_neighbour_of_the_held_face_in_all_60_grips), ("test_lower_ring_noon_is_the_upper_left_of_the_two_upper_ring_neighbours", fun _ => test_lower_ring_noon_is_the_upper_left_of_the_two_upper_ring_neighbours)]
