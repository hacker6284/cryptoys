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
    let _as4 ← SudoRt.sudoAssertEq (SudoRt.listLen z) digest_len 857
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
  let _as7 ← SudoRt.sudoAssertEq _t6 (0 : Int) 859
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
    let _as17 ← SudoRt.sudoAssertEq (left).sudo_8Position_2cp (idp).sudo_8Position_2cp 866
    let _as18 ← SudoRt.sudoAssertEq (left).sudo_8Position_2co (idp).sudo_8Position_2co 867
    let _as19 ← SudoRt.sudoAssertEq (left).sudo_8Position_2ep (idp).sudo_8Position_2ep 868
    let _as20 ← SudoRt.sudoAssertEq (left).sudo_8Position_2eo (idp).sudo_8Position_2eo 869
    let _as21 ← SudoRt.sudoAssertEq (right).sudo_8Position_2cp (idp).sudo_8Position_2cp 870
    let _as22 ← SudoRt.sudoAssertEq (right).sudo_8Position_2co (idp).sudo_8Position_2co 871
    let _as23 ← SudoRt.sudoAssertEq (right).sudo_8Position_2ep (idp).sudo_8Position_2ep 872
    let _as24 ← SudoRt.sudoAssertEq (right).sudo_8Position_2eo (idp).sudo_8Position_2eo 873
    pure ()

def test_iv_cook12_digest : Except SudoRt.Trap Unit :=
  do
    let _t25 ← iv_cook12
    let _t26 ← position_to_bytes _t25
    let d := _t26
    let _t27 ← hex_iv
    let _as28 ← SudoRt.sudoAssertEq d _t27 877
    pure ()

def test_empty_pad_is_one_block : Except SudoRt.Trap Unit :=
  do
    let _t29 ← pad_message (#[] : Array (Int))
    let p := _t29
    let _as31 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 881
    let _t32 ← SudoRt.atL p (0 : Int)
    let _as33 ← SudoRt.sudoAssertEq _t32 (128 : Int) 882
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
  let _as36 ← SudoRt.sudoAssertEq _t35 (0 : Int) 884
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
    let _as45 ← SudoRt.sudoAssertEq (SudoRt.listLen _t43) (28 : Int) 887
    let _t46 ← pad_message (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let _as48 ← SudoRt.sudoAssertEq (SudoRt.listLen _t46) (28 : Int) 888
    let _t49 ← pad_message (#[(0 : Int)] : Array (Int))
    let _as51 ← SudoRt.sudoAssertEq (SudoRt.listLen _t49) (28 : Int) 889
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
      let _as58 ← SudoRt.sudoAssertEq (SudoRt.listLen _t56) (56 : Int) 893
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
      let _as65 ← SudoRt.sudoAssertEq (SudoRt.listLen _t63) (56 : Int) 897
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
      let _as72 ← SudoRt.sudoAssertEq (SudoRt.listLen _t70) (56 : Int) 901
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
      let _as79 ← SudoRt.sudoAssertEq (SudoRt.listLen _t77) (84 : Int) 905
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
      let _as88 ← SudoRt.sudoAssertEq (SudoRt.listLen _t86) (112 : Int) 909
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
    let _as96 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 913
    let _t97 ← SudoRt.atL p (0 : Int)
    let _as98 ← SudoRt.sudoAssertEq _t97 (97 : Int) 914
    let _t99 ← SudoRt.atL p (1 : Int)
    let _as100 ← SudoRt.sudoAssertEq _t99 (98 : Int) 915
    let _t101 ← SudoRt.atL p (2 : Int)
    let _as102 ← SudoRt.sudoAssertEq _t101 (99 : Int) 916
    let _t103 ← SudoRt.atL p (3 : Int)
    let _as104 ← SudoRt.sudoAssertEq _t103 (128 : Int) 917
    let _t105 ← SudoRt.atL p (27 : Int)
    let _as106 ← SudoRt.sudoAssertEq _t105 (24 : Int) 918
    pure ()

def test_phi_of_28_zero_bytes_is_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t107 ← SudoRt.filledL (28 : Int) (0 : Int)
    let z := _t107
    let _t108 ← phi_chunk z
    let deal := _t108
    let _as110 ← SudoRt.sudoAssertEq (SudoRt.listLen deal) (52 : Int) 923
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
  let _as113 ← SudoRt.sudoAssertEq _t112 i 925
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
      let _as115 ← SudoRt.sudoAssertEq _t114 deal 926
      let _t116 ← phi_inv deal
      let _as117 ← SudoRt.sudoAssertEq _t116 z 927
      pure ()) (fun r => pure r))
    pure _out

def test_hash_aliases_agree_on_the_empty_message : Except SudoRt.Trap Unit :=
  do
    let _t119 ← v_Hash (#[] : Array (Int))
    let d := _t119
    let _as121 ← SudoRt.sudoAssertEq (SudoRt.listLen d) digest_len 931
    let _t122 ← v_MegaDreifach (#[] : Array (Int))
    let _as123 ← SudoRt.sudoAssertEq _t122 d 932
    pure ()

def test_hashdeckbody_on_the_identity_deal_is_29_bytes : Except SudoRt.Trap Unit :=
  do
    let _t124 ← range_list (52 : Int)
    let deal := _t124
    let _t125 ← v_HashDeckBody deal
    let b := _t125
    let _as127 ← SudoRt.sudoAssertEq (SudoRt.listLen b) digest_len 937
    let _t128 ← v_MegaDreifachBody deal
    let _as129 ← SudoRt.sudoAssertEq _t128 b 938
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
    let _as134 ← SudoRt.sudoAssertEq «from_iv» _t133 944
    let _t135 ← v_MegaDreifachBodyFrom deal iv
    let _t136 ← v_MegaDreifachBody deal
    let _as137 ← SudoRt.sudoAssertEq _t135 _t136 945
    let _t138 ← identity
    let _t139 ← v_HashDeckBodyFrom deal _t138
    let «from_id» := _t139
    let _as141 ← SudoRt.sudoAssertEq (SudoRt.listLen «from_id») digest_len 947
    let _as143 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq «from_id» «from_iv»)) 948
    pure ()

def test_hashdecksbody_chains_hashdeckbody : Except SudoRt.Trap Unit :=
  do
    let _t145 ← range_list (52 : Int)
    let a := _t145
    let b := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init163 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init163 fuel (fun σ =>
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
      let _as153 ← SudoRt.sudoAssertEq _t151 _t152 955
      let _t154 ← iv_cook12
      let _t155 ← dm_step _t154 a
      let h1 := _t155
      let _t156 ← v_HashDecksBody (#[a, b] : Array (Array (Int)))
      let _t157 ← v_HashDeckBodyFrom b h1
      let _as158 ← SudoRt.sudoAssertEq _t156 _t157 957
      let _t159 ← v_HashDecksBody (#[a, b] : Array (Array (Int)))
      let _t160 ← v_HashDecksBody (#[b, a] : Array (Array (Int)))
      let _as162 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t159 _t160)) 958
      pure ()) (fun r => pure r))
    pure _out

def test_hashdecksbody_rejects_an_empty_list : Except SudoRt.Trap Unit :=
  do
    let «none» := (#[] : Array (Array (Int)))
    let _ex165 := (do
  let _t164 ← v_HashDecksBody «none»
  let d := _t164
  pure ()
  pure ())
    match _ex165 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 962: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 962: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_hashdecksbody_rejects_a_non_deck : Except SudoRt.Trap Unit :=
  do
    let _t166 ← range_list (52 : Int)
    let bad := _t166
    let _ix167 := (3 : Int)
    let _t168 ← SudoRt.putL bad _ix167 (4 : Int)
    let bad := _t168
    let _ex170 := (do
  let _t169 ← v_HashDecksBody (#[bad] : Array (Array (Int)))
  let e := _t169
  pure ()
  pure ())
    match _ex170 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 968: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 968: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_require_permutation_rejects_a_duplicate : Except SudoRt.Trap Unit :=
  do
    let _t171 ← SudoRt.filledL (52 : Int) (0 : Int)
    let bad := _t171
    let _ex174 := (do
  let _t172 ← require_permutation bad
  let _u173 := _t172
  pure ()
  pure ())
    match _ex174 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 973: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 973: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_v3_kat_digests_kats_megaminx_hash_kats_v3_json : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init180 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init180 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t176 ← kat_msg n
  let _t177 ← v_Hash _t176
  let _t178 ← kat_v3_digest n
  let _as179 ← SudoRt.sudoAssertEq _t177 _t178 978
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

def test_v3_kat_hashdeck_of_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t181 ← range_list (52 : Int)
    let deal := _t181
    let _t182 ← v_HashDeck deal
    let _t183 ← kat_v3_digest (8 : Int)
    let _as184 ← SudoRt.sudoAssertEq _t182 _t183 982
    let _t185 ← v_HashDeck deal
    let _t186 ← SudoRt.filledL (28 : Int) (0 : Int)
    let _t187 ← v_Hash _t186
    let _as188 ← SudoRt.sudoAssertEq _t185 _t187 983
    pure ()

def test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init197 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init197 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t190 ← kat_v3_body_deal n
  let _t191 ← v_HashDeckBody _t190
  let _t192 ← kat_v3_body_digest n
  let _as193 ← SudoRt.sudoAssertEq _t191 _t192 987
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
      let _t194 ← kat_v3_body_deal (1 : Int)
      let _t195 ← SudoRt.atL _t194 (51 : Int)
      let _as196 ← SudoRt.sudoAssertEq _t195 (51 : Int) 988
      pure ()) (fun r => pure r))
    pure _out

def test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init222 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init222 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t199 ← face_nbrs f
  let nb := _t199
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init214 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init214 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t201 ← SudoRt.atL nb i
  let _t202 ← edge_slot f _t201
  let s := _t202
  let _t203 ← edge_faces s
  let ⟨a, b⟩ := _t203
  let _t205 ← (if (SudoRt.SEq.beq a f) then (do
  let _t206 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq b _t206)) else pure false)
  let _t208 ← (if _t205 then pure true else (do
  let _t210 ← (if (SudoRt.SEq.beq b f) then (do
  let _t211 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq a _t211)) else pure false)
  pure _t210))
  let _as213 ← SudoRt.sudoAssert _t208 996
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
      let _init221 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init221 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t216 ← edge_faces s
  let ⟨a, b⟩ := _t216
  let _as218 ← SudoRt.sudoAssert (decide (a < b)) 999
  let _t219 ← edge_slot a b
  let _as220 ← SudoRt.sudoAssertEq _t219 s 1000
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
    let _init234 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init234 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t224 ← face_move f
  let t := _t224
  let _fromV := (0 : Int)
  let _toV := (29 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init233 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init233 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t226 ← edge_faces s
  let ⟨a, b⟩ := _t226
  let _t227 ← SudoRt.atL (t).sudo_8Position_2ep s
  let moved := (!(SudoRt.SEq.beq _t227 s))
  let _t230 ← (if (SudoRt.SEq.beq f a) then pure true else (do
  pure (SudoRt.SEq.beq f b)))
  let _as232 ← SudoRt.sudoAssertEq moved _t230 1008
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

def test_edge_and_corner_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_pieces : Except SudoRt.Trap Unit :=
  do
    let _t235 ← identity
    let idp := _t235
    let _fromV := (0 : Int)
    let _toV := (29 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init255 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init255 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t237 ← edge_faces s
  let ⟨a, b⟩ := _t237
  let _t238 ← edge_colours_at idp a b
  let _as239 ← SudoRt.sudoAssertEq _t238 (a, b) 1014
  let _t240 ← edge_face_of idp a b a
  let _as241 ← SudoRt.sudoAssertEq _t240 a 1015
  let _t242 ← edge_face_of idp a b b
  let _as243 ← SudoRt.sudoAssertEq _t242 b 1016
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
      let _init254 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init254 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t245 ← identity
  let _t246 ← face_turn _t245 f (1 : Int)
  let g := _t246
  let _fromV := (1 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init253 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init253 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t248 ← suit_nbrs f k
  let ⟨n, n2⟩ := _t248
  let _t249 ← edge_face_of g f n f
  let _as250 ← SudoRt.sudoAssertEq _t249 f 1021
  let _t251 ← corner_face_of g f n n2 f
  let _as252 ← SudoRt.sudoAssertEq _t251 f 1022
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) k)
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) k)
            else do
              let i' ← SudoRt.addI k (1 : Int)
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

def test_suit_neighbours_four_different_neighbours_n2_follows_n_clockwise : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init287 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init287 fuel (fun σ =>
    let c := σ
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) c)
      else
        match ← ((do
  let _t257 ← face_nbrs c
  let nb := _t257
  let _t258 ← lowest_nbr_index c
  let _t259 ← SudoRt.atL nb _t258
  let lo := _t259
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init286 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init286 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t261 ← SudoRt.atL nb i
  let _as263 ← SudoRt.sudoAssert (decide (lo ≤ _t261)) 1029
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
      let _t264 ← suit_nbrs c (1 : Int)
      let ⟨n1, m1⟩ := _t264
      let _as265 ← SudoRt.sudoAssertEq n1 lo 1031
      let _fromV := (1 : Int)
      let _toV := (4 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init285 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init285 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t267 ← suit_nbrs c k
  let ⟨n, n2⟩ := _t267
  let hit := (0 : Int)
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init284 := (_fromV, hit)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init284 fuel (fun σ =>
    let i := σ.1
    let hit := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, hit))
      else
        match ← ((do
  let _t269 ← SudoRt.atL nb i
  let _t271 ← (if (SudoRt.SEq.beq _t269 n) then (do
  let _t272 ← SudoRt.addI i (1 : Int)
  let _t273 ← SudoRt.modI _t272 (5 : Int)
  let _t274 ← SudoRt.atL nb _t273
  pure (SudoRt.SEq.beq _t274 n2)) else pure false)
  if _t271 then
    do
      let _t276 ← SudoRt.addI hit (1 : Int)
      let hit := _t276
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
      let _as277 ← SudoRt.sudoAssertEq hit (1 : Int) 1038
      let _fromV := (1 : Int)
      let _toV := (4 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init283 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init283 fuel (fun σ =>
    let j := σ
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) j)
      else
        match ← ((do
  if (!(SudoRt.SEq.beq j k)) then
    do
      let _t280 ← suit_nbrs c j
      let ⟨m, m2⟩ := _t280
      let _as282 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq m n)) 1042
      pure (SudoRt.Flow.cont (ρ := Unit) ())
  else
    do
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
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
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
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) c)
        | .cont _fs => do
            if c == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) c)
            else do
              let i' ← SudoRt.addI c (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_coverage_the_48_non_king_cards_name_all_30_edges_and_all_20_corners : Except SudoRt.Trap Unit :=
  do
    let _t288 ← SudoRt.filledL (30 : Int) (0 : Int)
    let eseen := _t288
    let _t289 ← SudoRt.filledL (20 : Int) (0 : Int)
    let cseen := _t289
    let _fromV := (0 : Int)
    let _toV := (47 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init319 := (_fromV, (eseen, cseen))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init319 fuel (fun σ =>
    let card := σ.1
    let eseen := σ.2.1
    let _sp317 := σ.2.2
    let cseen := _sp317
    do
      if card > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (card, (eseen, cseen)))
      else
        match ← ((do
  let _t291 ← card_colour card
  let c := _t291
  let _t292 ← SudoRt.modI card (4 : Int)
  let _t293 ← SudoRt.addI _t292 (1 : Int)
  let _t294 ← suit_nbrs c _t293
  let ⟨n, n2⟩ := _t294
  let _t295 ← edge_slot c n
  let _ix296 := _t295
  let _t297 ← edge_slot c n
  let _t298 ← SudoRt.atL eseen _t297
  let _t299 ← SudoRt.addI _t298 (1 : Int)
  let _t300 ← SudoRt.putL eseen _ix296 _t299
  let eseen := _t300
  let _t301 ← corner_slot c n n2
  let _ix302 := _t301
  let _t303 ← corner_slot c n n2
  let _t304 ← SudoRt.atL cseen _t303
  let _t305 ← SudoRt.addI _t304 (1 : Int)
  let _t306 ← SudoRt.putL cseen _ix302 _t305
  let cseen := _t306
  pure (SudoRt.Flow.cont (ρ := Unit) (eseen, cseen))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (card, _fs))
        | .cont _fs => do
            if card == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (card, _fs))
            else do
              let i' ← SudoRt.addI card (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let eseen := σ.2.1
    let _sp318 := σ.2.2
    let cseen := _sp318
    do
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init316 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init316 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t308 ← SudoRt.atL eseen s
  let _as310 ← SudoRt.sudoAssert (decide (_t308 ≥ (1 : Int))) 1053
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
      let _toV := (19 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init315 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init315 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t312 ← SudoRt.atL cseen s
  let _as314 ← SudoRt.sudoAssert (decide (_t312 ≥ (1 : Int))) 1055
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
      pure _out) (fun r => pure r))
    pure _out

def test_card_pass_the_last_face_is_re_derivable_from_the_board_and_the_top_dealt_card : Except SudoRt.Trap Unit :=
  do
    let _t320 ← iv_cook12
    let _t321 ← start_run _t320
    let r := _t321
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init337 := (_fromV, r)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init337 fuel (fun σ =>
    let i := σ.1
    let r := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, r))
      else
        match ← ((do
  let _t323 ← SudoRt.mulI i (23 : Int)
  let _t324 ← SudoRt.addI _t323 (7 : Int)
  let _t325 ← SudoRt.modI _t324 (52 : Int)
  let card := _t325
  let _t326 ← SudoRt.divI card (4 : Int)
  let _t327 ← SudoRt.modI card (4 : Int)
  let _t328 ← SudoRt.addI _t327 (1 : Int)
  let _t329 ← card_colour card
  let _t330 ← card_step r (r).sudo_3Run_4last _t326 _t328 _t329
  let r := _t330
  let _t331 ← card_colour card
  let c := _t331
  let _t332 ← SudoRt.modI card (4 : Int)
  let _t333 ← SudoRt.addI _t332 (1 : Int)
  let _t334 ← suit_nbrs c _t333
  let ⟨n, n2⟩ := _t334
  let _t335 ← edge_face_of (r).sudo_3Run_1g c n n
  let _as336 ← SudoRt.sudoAssertEq _t335 (r).sudo_3Run_4last 1064
  pure (SudoRt.Flow.cont (ρ := Unit) r)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let r := σ.2
    do
      pure ()) (fun r => pure r))
    pure _out

def test_a_king_steps_as_the_rank_counting_up_to_its_opposite_face : Except SudoRt.Trap Unit :=
  do
    let _t338 ← iv_cook12
    let _t339 ← start_run _t338
    let r0 := _t339
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init354 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init354 fuel (fun σ =>
    let last := σ
    do
      if last > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) last)
      else
        match ← ((do
  let _t341 ← SudoRt.atL opposites last
  let _as343 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t341 last)) 1070
  let _t344 ← SudoRt.atL opposites last
  let _t345 ← SudoRt.subI _t344 last
  let _t346 ← SudoRt.addI _t345 (12 : Int)
  let _t347 ← SudoRt.modI _t346 (12 : Int)
  let rank := _t347
  let _fromV := (1 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init353 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init353 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t349 ← card_step r0 last (12 : Int) k (0 : Int)
  let king := _t349
  let _t350 ← card_step r0 last rank k (0 : Int)
  let same := _t350
  let _as351 ← SudoRt.sudoAssertEq (king).sudo_3Run_4last (same).sudo_3Run_4last 1075
  let _as352 ← SudoRt.sudoAssertEq (king).sudo_3Run_1g (same).sudo_3Run_1g 1076
  pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) k)
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) k)
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) last)
        | .cont _fs => do
            if last == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) last)
            else do
              let i' ← SudoRt.addI last (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_cost_per_block_spec_v3_5_6_468_turns_520_26k_clicks_156_finds_78_re_looks_52_register_looks : Except SudoRt.Trap Unit :=
  do
    let _t357 ← iv_cook12
    let g0 := _t357
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init378 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init378 fuel (fun σ =>
    let held := σ
    do
      if held > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) held)
      else
        match ← ((do
  let deal := (#[] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (51 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init377 := (_fromV, deal)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init377 fuel (fun σ =>
    let card := σ.1
    let deal := σ.2
    do
      if card > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (card, deal))
      else
        match ← ((do
  if (!(SudoRt.SEq.beq card held)) then
    do
      let _mb361 := SudoRt.appendL deal card
      let ⟨_nr362, _⟩ := _mb361
      let deal := _nr362
      let _hm355 := ()
      let _u363 := _hm355
      pure (SudoRt.Flow.cont (ρ := Unit) deal)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) deal)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (card, _fs))
        | .cont _fs => do
            if card == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (card, _fs))
            else do
              let i' ← SudoRt.addI card (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let deal := σ.2
    do
      let _mb364 := SudoRt.appendL deal held
      let ⟨_nr365, _⟩ := _mb364
      let deal := _nr365
      let _hm356 := ()
      let _u366 := _hm356
      let _t367 ← em_run g0 deal
      let r := _t367
      let _as368 ← SudoRt.sudoAssertEq (r).sudo_3Run_5turns (468 : Int) 1087
      let _t369 ← SudoRt.modI held (4 : Int)
      let _t370 ← SudoRt.addI _t369 (1 : Int)
      let _t371 ← SudoRt.mulI (26 : Int) _t370
      let _t372 ← SudoRt.addI (520 : Int) _t371
      let _as373 ← SudoRt.sudoAssertEq (r).sudo_3Run_6clicks _t372 1088
      let _as374 ← SudoRt.sudoAssertEq (r).sudo_3Run_5finds (156 : Int) 1089
      let _as375 ← SudoRt.sudoAssertEq (r).sudo_3Run_7relooks (78 : Int) 1090
      let _as376 ← SudoRt.sudoAssertEq (r).sudo_3Run_14register_looks (52 : Int) 1091
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) held)
        | .cont _fs => do
            if held == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) held)
            else do
              let i' ← SudoRt.addI held (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
    pure _out

def test_read_words_spec_v3_5_8_for_every_piece_and_ordered_pair_of_its_colours_its_60_states_give_60_distinct_two_turn_words : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (29 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init489 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init489 fuel (fun σ =>
    let p := σ
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) p)
      else
        match ← ((do
  let _t382 ← edge_faces p
  let ⟨a, b⟩ := _t382
  let _fromV := (0 : Int)
  let _toV := (1 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init447 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init447 fuel (fun σ =>
    let order := σ
    do
      if order > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) order)
      else
        match ← ((do
  let x := a
  let y := b
  if (SudoRt.SEq.beq order (1 : Int)) then
    do
      let x := b
      let y := a
      let words := (SudoRt.setNew : SudoRt.SSet (Position))
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init415 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init415 fuel (fun σ =>
    let s := σ.1
    let words := σ.2
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (s, words))
      else
        match ← ((do
  let _fromV := (0 : Int)
  let _toV := (1 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init412 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init412 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t388 ← identity
  let g := _t388
  let _ix389 := p
  let _t390 ← SudoRt.atL (g).sudo_8Position_2ep s
  let _t391 ← SudoRt.putL (g).sudo_8Position_2ep _ix389 _t390
  let _t392 := ({ g with sudo_8Position_2ep := _t391 } : Position)
  let g := _t392
  let _ix393 := p
  let _t394 ← SudoRt.putL (g).sudo_8Position_2eo _ix393 (0 : Int)
  let _t395 := ({ g with sudo_8Position_2eo := _t394 } : Position)
  let g := _t395
  let _ix396 := s
  let _t397 ← SudoRt.putL (g).sudo_8Position_2ep _ix396 p
  let _t398 := ({ g with sudo_8Position_2ep := _t397 } : Position)
  let g := _t398
  let _ix399 := s
  let _t400 ← SudoRt.putL (g).sudo_8Position_2eo _ix399 o
  let _t401 := ({ g with sudo_8Position_2eo := _t400 } : Position)
  let g := _t401
  let _t402 ← edge_face_of g a b x
  let f1 := _t402
  let _t403 ← face_turn g f1 (1 : Int)
  let _t404 ← edge_face_of _t403 a b y
  let f2 := _t404
  let _t405 ← identity
  let _t406 ← face_turn _t405 f1 (1 : Int)
  let _t407 ← face_turn _t406 f2 (1 : Int)
  let _mb408 := SudoRt.setAdd words _t407
  let ⟨_nr409, _mv410⟩ := _mb408
  let words := _nr409
  let _hm379 := _mv410
  let _u411 := _hm379
  pure (SudoRt.Flow.cont (ρ := Unit) words)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
        | .cont _fs => do
            if o == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
            else do
              let i' ← SudoRt.addI o (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Unit) words)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      let _as414 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1113
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out
  else
    do
      let words := (SudoRt.setNew : SudoRt.SSet (Position))
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init446 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init446 fuel (fun σ =>
    let s := σ.1
    let words := σ.2
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (s, words))
      else
        match ← ((do
  let _fromV := (0 : Int)
  let _toV := (1 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init443 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init443 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t419 ← identity
  let g := _t419
  let _ix420 := p
  let _t421 ← SudoRt.atL (g).sudo_8Position_2ep s
  let _t422 ← SudoRt.putL (g).sudo_8Position_2ep _ix420 _t421
  let _t423 := ({ g with sudo_8Position_2ep := _t422 } : Position)
  let g := _t423
  let _ix424 := p
  let _t425 ← SudoRt.putL (g).sudo_8Position_2eo _ix424 (0 : Int)
  let _t426 := ({ g with sudo_8Position_2eo := _t425 } : Position)
  let g := _t426
  let _ix427 := s
  let _t428 ← SudoRt.putL (g).sudo_8Position_2ep _ix427 p
  let _t429 := ({ g with sudo_8Position_2ep := _t428 } : Position)
  let g := _t429
  let _ix430 := s
  let _t431 ← SudoRt.putL (g).sudo_8Position_2eo _ix430 o
  let _t432 := ({ g with sudo_8Position_2eo := _t431 } : Position)
  let g := _t432
  let _t433 ← edge_face_of g a b x
  let f1 := _t433
  let _t434 ← face_turn g f1 (1 : Int)
  let _t435 ← edge_face_of _t434 a b y
  let f2 := _t435
  let _t436 ← identity
  let _t437 ← face_turn _t436 f1 (1 : Int)
  let _t438 ← face_turn _t437 f2 (1 : Int)
  let _mb439 := SudoRt.setAdd words _t438
  let ⟨_nr440, _mv441⟩ := _mb439
  let words := _nr440
  let _hm379 := _mv441
  let _u442 := _hm379
  pure (SudoRt.Flow.cont (ρ := Unit) words)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
        | .cont _fs => do
            if o == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
            else do
              let i' ← SudoRt.addI o (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Unit) words)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      let _as445 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1113
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) order)
        | .cont _fs => do
            if order == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) order)
            else do
              let i' ← SudoRt.addI order (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) p)
        | .cont _fs => do
            if p == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) p)
            else do
              let i' ← SudoRt.addI p (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      let _fromV := (0 : Int)
      let _toV := (19 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init488 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init488 fuel (fun σ =>
    let p := σ
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) p)
      else
        match ← ((do
  let _t449 ← corner_faces p
  let ⟨a, b, c⟩ := _t449
  let cols := (#[a, b, c] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init487 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init487 fuel (fun σ =>
    let i1 := σ
    do
      if i1 > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i1)
      else
        match ← ((do
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init486 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init486 fuel (fun σ =>
    let i2 := σ
    do
      if i2 > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i2)
      else
        match ← ((do
  if (!(SudoRt.SEq.beq i1 i2)) then
    do
      let words := (SudoRt.setNew : SudoRt.SSet (Position))
      let _fromV := (0 : Int)
      let _toV := (19 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init485 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init485 fuel (fun σ =>
    let s := σ.1
    let words := σ.2
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (s, words))
      else
        match ← ((do
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init482 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init482 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t456 ← identity
  let g := _t456
  let _ix457 := p
  let _t458 ← SudoRt.atL (g).sudo_8Position_2cp s
  let _t459 ← SudoRt.putL (g).sudo_8Position_2cp _ix457 _t458
  let _t460 := ({ g with sudo_8Position_2cp := _t459 } : Position)
  let g := _t460
  let _ix461 := p
  let _t462 ← SudoRt.putL (g).sudo_8Position_2co _ix461 (0 : Int)
  let _t463 := ({ g with sudo_8Position_2co := _t462 } : Position)
  let g := _t463
  let _ix464 := s
  let _t465 ← SudoRt.putL (g).sudo_8Position_2cp _ix464 p
  let _t466 := ({ g with sudo_8Position_2cp := _t465 } : Position)
  let g := _t466
  let _ix467 := s
  let _t468 ← SudoRt.putL (g).sudo_8Position_2co _ix467 o
  let _t469 := ({ g with sudo_8Position_2co := _t468 } : Position)
  let g := _t469
  let _t470 ← SudoRt.atL cols i1
  let _t471 ← corner_face_of g a b c _t470
  let f1 := _t471
  let _t472 ← face_turn g f1 (1 : Int)
  let _t473 ← SudoRt.atL cols i2
  let _t474 ← corner_face_of _t472 a b c _t473
  let f2 := _t474
  let _t475 ← identity
  let _t476 ← face_turn _t475 f1 (1 : Int)
  let _t477 ← face_turn _t476 f2 (1 : Int)
  let _mb478 := SudoRt.setAdd words _t477
  let ⟨_nr479, _mv480⟩ := _mb478
  let words := _nr479
  let _hm380 := _mv480
  let _u481 := _hm380
  pure (SudoRt.Flow.cont (ρ := Unit) words)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
        | .cont _fs => do
            if o == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (o, _fs))
            else do
              let i' ← SudoRt.addI o (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Unit) words)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let words := σ.2
    do
      let _as484 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1131
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out
  else
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) i2)
        | .cont _fs => do
            if i2 == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) i2)
            else do
              let i' ← SudoRt.addI i2 (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) i1)
        | .cont _fs => do
            if i1 == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) i1)
            else do
              let i' ← SudoRt.addI i1 (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) p)
        | .cont _fs => do
            if p == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) p)
            else do
              let i' ← SudoRt.addI p (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) i')) (fun σ =>
    do
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_trace_hash_matches_hash_em_block_dm_step_and_iv_cook12_on_every_kat : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init541 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init541 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t491 ← kat_msg n
  let msg := _t491
  let _t492 ← trace_hash msg
  let tr := _t492
  let _t493 ← kat_v3_digest n
  let _as494 ← SudoRt.sudoAssertEq (tr).sudo_5Trace_6digest _t493 1265
  let _t495 ← v_Hash msg
  let _as496 ← SudoRt.sudoAssertEq (tr).sudo_5Trace_6digest _t495 1266
  let _t497 ← identity
  let _t498 ← replay_turns _t497 (tr).sudo_5Trace_8iv_turns
  let _t499 ← iv_cook12
  let _as500 ← SudoRt.sudoAssertEq _t498 _t499 1267
  let _t501 ← pad_message msg
  let padded := _t501
  let _t503 ← SudoRt.mulI (SudoRt.listLen (tr).sudo_5Trace_6blocks) pad_block
  let _as505 ← SudoRt.sudoAssertEq _t503 (SudoRt.listLen padded) 1269
  let _t506 ← iv_cook12
  let h := _t506
  let _t539 ← SudoRt.subI (SudoRt.listLen (tr).sudo_5Trace_6blocks) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t539
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init540 := (_fromV, h)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init540 fuel (fun σ =>
    let b := σ.1
    let h := σ.2
    do
      if b > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (b, h))
      else
        match ← ((do
  let _t508 ← SudoRt.atL (tr).sudo_5Trace_6blocks b
  let blk := _t508
  let _as509 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_1h h 1273
  let _t510 ← phi_chunk (blk).sudo_10TraceBlock_5chunk
  let _as511 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_4deal _t510 1274
  let _t512 ← em_block h (blk).sudo_10TraceBlock_4deal
  let _as513 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_1e _t512 1275
  let _t515 ← SudoRt.addI body_len echo_count
  let _as516 ← SudoRt.sudoAssertEq (SudoRt.listLen (blk).sudo_10TraceBlock_5steps) _t515 1276
  let g := h
  let _t527 ← SudoRt.subI (SudoRt.listLen (blk).sudo_10TraceBlock_5steps) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t527
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init537 := (_fromV, g)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init537 fuel (fun σ =>
    let s := σ.1
    let g := σ.2
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (s, g))
      else
        match ← ((do
  let _t518 ← SudoRt.atL (blk).sudo_10TraceBlock_5steps s
  let st := _t518
  let _t519 ← SudoRt.addI s (1 : Int)
  let _as520 ← SudoRt.sudoAssertEq (st).sudo_9TraceStep_3pos _t519 1280
  let _as522 ← SudoRt.sudoAssertEq (SudoRt.listLen (st).sudo_9TraceStep_5turns) (12 : Int) 1281
  let _t523 ← replay_turns g (st).sudo_9TraceStep_5turns
  let g := _t523
  let _t524 ← SudoRt.atL (st).sudo_9TraceStep_5turns (10 : Int)
  let _as525 ← SudoRt.sudoAssertEq (st).sudo_9TraceStep_4last _t524 1283
  pure (SudoRt.Flow.cont (ρ := Unit) g)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
        | .cont _fs => do
            if s == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (s, _fs))
            else do
              let i' ← SudoRt.addI s (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let g := σ.2
    do
      let _as528 ← SudoRt.sudoAssertEq g (blk).sudo_10TraceBlock_1e 1284
      let _t529 ← dm_step h (blk).sudo_10TraceBlock_4deal
      let _as530 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_6h_next _t529 1285
      let _t531 ← compose (blk).sudo_10TraceBlock_1h (blk).sudo_10TraceBlock_5h_inv
      let _t532 ← identity
      let _as533 ← SudoRt.sudoAssertEq _t531 _t532 1286
      let _t534 ← compose (blk).sudo_10TraceBlock_6h_next (blk).sudo_10TraceBlock_10h_next_inv
      let _t535 ← identity
      let _as536 ← SudoRt.sudoAssertEq _t534 _t535 1287
      let h := (blk).sudo_10TraceBlock_6h_next
      pure (SudoRt.Flow.cont (ρ := Unit) h)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (b, _fs))
        | .cont _fs => do
            if b == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (b, _fs))
            else do
              let i' ← SudoRt.addI b (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let h := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
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

def test_trace_card_step_returns_card_step_s_run_at_every_step_of_the_kat_blocks : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init603 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init603 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t544 ← kat_msg n
  let _t545 ← pad_message _t544
  let padded := _t545
  let _t546 ← iv_cook12
  let h := _t546
  let _t600 ← SudoRt.divI (SudoRt.listLen padded) pad_block
  let _t601 ← SudoRt.subI _t600 (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t601
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init602 := (_fromV, h)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init602 fuel (fun σ =>
    let b := σ.1
    let h := σ.2
    do
      if b > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (b, h))
      else
        match ← ((do
  let chunk := (#[] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (27 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init598 := (_fromV, chunk)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init598 fuel (fun σ =>
    let j := σ.1
    let chunk := σ.2
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, chunk))
      else
        match ← ((do
  let _t549 ← SudoRt.mulI b pad_block
  let _t550 ← SudoRt.addI _t549 j
  let _t551 ← SudoRt.atL padded _t550
  let _mb552 := SudoRt.appendL chunk _t551
  let ⟨_nr553, _⟩ := _mb552
  let chunk := _nr553
  let _hm542 := ()
  let _u554 := _hm542
  pure (SudoRt.Flow.cont (ρ := Unit) chunk)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let chunk := σ.2
    do
      let _t555 ← phi_chunk chunk
      let deal := _t555
      let _t556 ← start_run h
      let r := _t556
      let _t557 ← start_run h
      let t := _t557
      let _fromV := (0 : Int)
      let _toV := (51 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init597 := (_fromV, (r, t))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init597 fuel (fun σ =>
    let i := σ.1
    let r := σ.2.1
    let _sp595 := σ.2.2
    let t := _sp595
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, (r, t)))
      else
        match ← ((do
  let _t559 ← SudoRt.atL deal i
  let card := _t559
  let turns := (#[] : Array (Int))
  let _t560 ← SudoRt.divI card (4 : Int)
  let _t561 ← SudoRt.modI card (4 : Int)
  let _t562 ← SudoRt.addI _t561 (1 : Int)
  let _t563 ← card_colour card
  let _t564 ← card_step r (r).sudo_3Run_4last _t560 _t562 _t563
  let r := _t564
  let _t565 ← SudoRt.divI card (4 : Int)
  let _t566 ← SudoRt.modI card (4 : Int)
  let _t567 ← SudoRt.addI _t566 (1 : Int)
  let _t568 ← card_colour card
  let _io569 ← trace_card_step t (t).sudo_3Run_4last _t565 _t567 _t568 turns
  let ⟨_ret570, _iw0571⟩ := _io569
  let turns := _iw0571
  let t := _ret570
  let _as572 ← SudoRt.sudoAssertEq t r 1306
  pure (SudoRt.Flow.cont (ρ := Unit) (r, t))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let r := σ.2.1
    let _sp596 := σ.2.2
    let t := _sp596
    do
      let _t573 ← SudoRt.atL deal (51 : Int)
      let held := _t573
      let _fromV := (1 : Int)
      let _toV := echo_count
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init594 := (_fromV, (r, t))
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init594 fuel (fun σ =>
    let j := σ.1
    let r := σ.2.1
    let _sp592 := σ.2.2
    let t := _sp592
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, (r, t)))
      else
        match ← ((do
  let _t575 ← echo_colour (r).sudo_3Run_1g held
  let p := _t575
  let _t576 ← count_register_looks r
  let r := _t576
  let _t577 ← count_register_looks t
  let t := _t577
  let turns := (#[] : Array (Int))
  let _t578 ← SudoRt.divI held (4 : Int)
  let _t579 ← SudoRt.modI held (4 : Int)
  let _t580 ← SudoRt.addI _t579 (1 : Int)
  let _t581 ← card_step r p _t578 _t580 p
  let r := _t581
  let _t582 ← SudoRt.divI held (4 : Int)
  let _t583 ← SudoRt.modI held (4 : Int)
  let _t584 ← SudoRt.addI _t583 (1 : Int)
  let _io585 ← trace_card_step t p _t582 _t584 p turns
  let ⟨_ret586, _iw0587⟩ := _io585
  let turns := _iw0587
  let t := _ret586
  let _as588 ← SudoRt.sudoAssertEq t r 1315
  pure (SudoRt.Flow.cont (ρ := Unit) (r, t))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let r := σ.2.1
    let _sp593 := σ.2.2
    let t := _sp593
    do
      let _t589 ← em_run h deal
      let _as590 ← SudoRt.sudoAssertEq r _t589 1316
      let _t591 ← dm_step h deal
      let h := _t591
      pure (SudoRt.Flow.cont (ρ := Unit) h)) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (b, _fs))
        | .cont _fs => do
            if b == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (b, _fs))
            else do
              let i' ← SudoRt.addI b (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let h := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
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

def test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved : Except SudoRt.Trap Unit :=
  do
    let _t604 ← identity
    let b := _t604
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init648 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init648 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, b))
      else
        match ← ((do
  let _t606 ← SudoRt.subI (11 : Int) i
  let _t607 ← face_turn b _t606 (4 : Int)
  let b := _t607
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
      let _t608 ← iv_cook12
      let _t609 ← inverse _t608
      let _as610 ← SudoRt.sudoAssertEq b _t609 1325
      let _fromV := (0 : Int)
      let _toV := (7 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init647 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init647 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t612 ← kat_msg n
  let _t613 ← trace_hash _t612
  let tr := _t613
  let _t614 ← iv_cook12
  let pa := _t614
  let pb := b
  let _t615 ← identity
  let pc := _t615
  let _t638 ← SudoRt.subI (SudoRt.listLen (tr).sudo_5Trace_6blocks) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t638
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init646 := (_fromV, (pa, pb, pc))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init646 fuel (fun σ =>
    let k := σ.1
    let pa := σ.2.1
    let _sp642 := σ.2.2
    let pb := _sp642.1
    let _sp643 := _sp642.2
    let pc := _sp643
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, (pa, pb, pc)))
      else
        match ← ((do
  let _t617 ← SudoRt.atL (tr).sudo_5Trace_6blocks k
  let blk := _t617
  let _as618 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_1h 1333
  let _t619 ← compose pa pb
  let _t620 ← identity
  let _as621 ← SudoRt.sudoAssertEq _t619 _t620 1334
  let _t622 ← identity
  let _as623 ← SudoRt.sudoAssertEq pc _t622 1335
  let pa := (blk).sudo_10TraceBlock_1e
  let _t624 ← inverse pb
  let _t625 ← compose _t624 pa
  let pa := _t625
  let _t626 ← identity
  let pb := _t626
  let _as627 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_6h_next 1339
  let _t628 ← inverse pa
  let s2 := _t628
  let _t629 ← identity
  let pa := _t629
  let _t630 ← compose s2 pb
  let pb := _t630
  let _t631 ← compose s2 pc
  let pc := _t631
  let _t632 ← inverse pc
  let _t633 ← compose _t632 pa
  let pa := _t633
  let _t634 ← identity
  let pc := _t634
  let _as635 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_6h_next 1346
  let _as636 ← SudoRt.sudoAssertEq pb (blk).sudo_10TraceBlock_10h_next_inv 1347
  pure (SudoRt.Flow.cont (ρ := Unit) (pa, pb, pc))) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
        | .cont _fs => do
            if k == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (k, _fs))
            else do
              let i' ← SudoRt.addI k (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let pa := σ.2.1
    let _sp644 := σ.2.2
    let pb := _sp644.1
    let _sp645 := _sp644.2
    let pc := _sp645
    do
      let _t639 ← position_to_bytes pa
      let _t640 ← kat_v3_digest n
      let _as641 ← SudoRt.sudoAssertEq _t639 _t640 1348
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
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
      pure _out) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_identity_rank_is_29_zero_bytes", fun _ => test_identity_rank_is_29_zero_bytes), ("test_compose_inverse_round_trip", fun _ => test_compose_inverse_round_trip), ("test_iv_cook12_digest", fun _ => test_iv_cook12_digest), ("test_empty_pad_is_one_block", fun _ => test_empty_pad_is_one_block), ("test_kat_pad_lengths", fun _ => test_kat_pad_lengths), ("test_abc_pad_recovers_the_24_bit_length", fun _ => test_abc_pad_recovers_the_24_bit_length), ("test_phi_of_28_zero_bytes_is_the_identity_deal", fun _ => test_phi_of_28_zero_bytes_is_the_identity_deal), ("test_hash_aliases_agree_on_the_empty_message", fun _ => test_hash_aliases_agree_on_the_empty_message), ("test_hashdeckbody_on_the_identity_deal_is_29_bytes", fun _ => test_hashdeckbody_on_the_identity_deal_is_29_bytes), ("test_hashdeckbodyfrom_at_iv_matches_hashdeckbody", fun _ => test_hashdeckbodyfrom_at_iv_matches_hashdeckbody), ("test_hashdecksbody_chains_hashdeckbody", fun _ => test_hashdecksbody_chains_hashdeckbody), ("test_hashdecksbody_rejects_an_empty_list", fun _ => test_hashdecksbody_rejects_an_empty_list), ("test_hashdecksbody_rejects_a_non_deck", fun _ => test_hashdecksbody_rejects_a_non_deck), ("test_require_permutation_rejects_a_duplicate", fun _ => test_require_permutation_rejects_a_duplicate), ("test_v3_kat_digests_kats_megaminx_hash_kats_v3_json", fun _ => test_v3_kat_digests_kats_megaminx_hash_kats_v3_json), ("test_v3_kat_hashdeck_of_the_identity_deal", fun _ => test_v3_kat_hashdeck_of_the_identity_deal), ("test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes", fun _ => test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes), ("test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot", fun _ => test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot), ("test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot", fun _ => test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot), ("test_edge_and_corner_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_pieces", fun _ => test_edge_and_corner_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_pieces), ("test_suit_neighbours_four_different_neighbours_n2_follows_n_clockwise", fun _ => test_suit_neighbours_four_different_neighbours_n2_follows_n_clockwise), ("test_coverage_the_48_non_king_cards_name_all_30_edges_and_all_20_corners", fun _ => test_coverage_the_48_non_king_cards_name_all_30_edges_and_all_20_corners), ("test_card_pass_the_last_face_is_re_derivable_from_the_board_and_the_top_dealt_card", fun _ => test_card_pass_the_last_face_is_re_derivable_from_the_board_and_the_top_dealt_card), ("test_a_king_steps_as_the_rank_counting_up_to_its_opposite_face", fun _ => test_a_king_steps_as_the_rank_counting_up_to_its_opposite_face), ("test_cost_per_block_spec_v3_5_6_468_turns_520_26k_clicks_156_finds_78_re_looks_52_register_looks", fun _ => test_cost_per_block_spec_v3_5_6_468_turns_520_26k_clicks_156_finds_78_re_looks_52_register_looks), ("test_read_words_spec_v3_5_8_for_every_piece_and_ordered_pair_of_its_colours_its_60_states_give_60_distinct_two_turn_words", fun _ => test_read_words_spec_v3_5_8_for_every_piece_and_ordered_pair_of_its_colours_its_60_states_give_60_distinct_two_turn_words), ("test_trace_hash_matches_hash_em_block_dm_step_and_iv_cook12_on_every_kat", fun _ => test_trace_hash_matches_hash_em_block_dm_step_and_iv_cook12_on_every_kat), ("test_trace_card_step_returns_card_step_s_run_at_every_step_of_the_kat_blocks", fun _ => test_trace_card_step_returns_card_step_s_run_at_every_step_of_the_kat_blocks), ("test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved", fun _ => test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved)]
