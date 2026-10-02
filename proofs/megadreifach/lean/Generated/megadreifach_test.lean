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
    let _as4 ← SudoRt.sudoAssertEq (SudoRt.listLen z) digest_len 878
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
  let _as7 ← SudoRt.sudoAssertEq _t6 (0 : Int) 880
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
    let _as17 ← SudoRt.sudoAssertEq (left).sudo_8Position_2cp (idp).sudo_8Position_2cp 887
    let _as18 ← SudoRt.sudoAssertEq (left).sudo_8Position_2co (idp).sudo_8Position_2co 888
    let _as19 ← SudoRt.sudoAssertEq (left).sudo_8Position_2ep (idp).sudo_8Position_2ep 889
    let _as20 ← SudoRt.sudoAssertEq (left).sudo_8Position_2eo (idp).sudo_8Position_2eo 890
    let _as21 ← SudoRt.sudoAssertEq (right).sudo_8Position_2cp (idp).sudo_8Position_2cp 891
    let _as22 ← SudoRt.sudoAssertEq (right).sudo_8Position_2co (idp).sudo_8Position_2co 892
    let _as23 ← SudoRt.sudoAssertEq (right).sudo_8Position_2ep (idp).sudo_8Position_2ep 893
    let _as24 ← SudoRt.sudoAssertEq (right).sudo_8Position_2eo (idp).sudo_8Position_2eo 894
    pure ()

def test_iv_cook12_digest : Except SudoRt.Trap Unit :=
  do
    let _t25 ← iv_cook12
    let _t26 ← position_to_bytes _t25
    let d := _t26
    let _t27 ← hex_iv
    let _as28 ← SudoRt.sudoAssertEq d _t27 898
    pure ()

def test_empty_pad_is_one_block : Except SudoRt.Trap Unit :=
  do
    let _t29 ← pad_message (#[] : Array (Int))
    let p := _t29
    let _as31 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 902
    let _t32 ← SudoRt.atL p (0 : Int)
    let _as33 ← SudoRt.sudoAssertEq _t32 (128 : Int) 903
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
  let _as36 ← SudoRt.sudoAssertEq _t35 (0 : Int) 905
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
    let _as45 ← SudoRt.sudoAssertEq (SudoRt.listLen _t43) (28 : Int) 908
    let _t46 ← pad_message (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let _as48 ← SudoRt.sudoAssertEq (SudoRt.listLen _t46) (28 : Int) 909
    let _t49 ← pad_message (#[(0 : Int)] : Array (Int))
    let _as51 ← SudoRt.sudoAssertEq (SudoRt.listLen _t49) (28 : Int) 910
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
      let _as58 ← SudoRt.sudoAssertEq (SudoRt.listLen _t56) (56 : Int) 914
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
      let _as65 ← SudoRt.sudoAssertEq (SudoRt.listLen _t63) (56 : Int) 918
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
      let _as72 ← SudoRt.sudoAssertEq (SudoRt.listLen _t70) (56 : Int) 922
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
      let _as79 ← SudoRt.sudoAssertEq (SudoRt.listLen _t77) (84 : Int) 926
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
      let _as88 ← SudoRt.sudoAssertEq (SudoRt.listLen _t86) (112 : Int) 930
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
    let _as96 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 934
    let _t97 ← SudoRt.atL p (0 : Int)
    let _as98 ← SudoRt.sudoAssertEq _t97 (97 : Int) 935
    let _t99 ← SudoRt.atL p (1 : Int)
    let _as100 ← SudoRt.sudoAssertEq _t99 (98 : Int) 936
    let _t101 ← SudoRt.atL p (2 : Int)
    let _as102 ← SudoRt.sudoAssertEq _t101 (99 : Int) 937
    let _t103 ← SudoRt.atL p (3 : Int)
    let _as104 ← SudoRt.sudoAssertEq _t103 (128 : Int) 938
    let _t105 ← SudoRt.atL p (27 : Int)
    let _as106 ← SudoRt.sudoAssertEq _t105 (24 : Int) 939
    pure ()

def test_phi_of_28_zero_bytes_is_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t107 ← SudoRt.filledL (28 : Int) (0 : Int)
    let z := _t107
    let _t108 ← phi_chunk z
    let deal := _t108
    let _as110 ← SudoRt.sudoAssertEq (SudoRt.listLen deal) (52 : Int) 944
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
  let _as113 ← SudoRt.sudoAssertEq _t112 i 946
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
      let _as115 ← SudoRt.sudoAssertEq _t114 deal 947
      let _t116 ← phi_inv deal
      let _as117 ← SudoRt.sudoAssertEq _t116 z 948
      pure ()) (fun r => pure r))
    pure _out

def test_hash_aliases_agree_on_the_empty_message : Except SudoRt.Trap Unit :=
  do
    let _t119 ← v_Hash (#[] : Array (Int))
    let d := _t119
    let _as121 ← SudoRt.sudoAssertEq (SudoRt.listLen d) digest_len 952
    let _t122 ← v_MegaDreifach (#[] : Array (Int))
    let _as123 ← SudoRt.sudoAssertEq _t122 d 953
    pure ()

def test_hashdeckbody_on_the_identity_deal_is_29_bytes : Except SudoRt.Trap Unit :=
  do
    let _t124 ← range_list (52 : Int)
    let deal := _t124
    let _t125 ← v_HashDeckBody deal
    let b := _t125
    let _as127 ← SudoRt.sudoAssertEq (SudoRt.listLen b) digest_len 958
    let _t128 ← v_MegaDreifachBody deal
    let _as129 ← SudoRt.sudoAssertEq _t128 b 959
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
    let _as134 ← SudoRt.sudoAssertEq «from_iv» _t133 965
    let _t135 ← v_MegaDreifachBodyFrom deal iv
    let _t136 ← v_MegaDreifachBody deal
    let _as137 ← SudoRt.sudoAssertEq _t135 _t136 966
    let _t138 ← identity
    let _t139 ← v_HashDeckBodyFrom deal _t138
    let «from_id» := _t139
    let _as141 ← SudoRt.sudoAssertEq (SudoRt.listLen «from_id») digest_len 968
    let _as143 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq «from_id» «from_iv»)) 969
    pure ()

def test_require_permutation_rejects_a_duplicate : Except SudoRt.Trap Unit :=
  do
    let _t144 ← SudoRt.filledL (52 : Int) (0 : Int)
    let bad := _t144
    let _ex147 := (do
  let _t145 ← require_permutation bad
  let _u146 := _t145
  pure ()
  pure ())
    match _ex147 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 973: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 973: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_v2_kat_digests_kats_megaminx_hash_kats_v2_json : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init153 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init153 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t149 ← kat_msg n
  let _t150 ← v_Hash _t149
  let _t151 ← kat_v2_digest n
  let _as152 ← SudoRt.sudoAssertEq _t150 _t151 978
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
    let _t154 ← range_list (52 : Int)
    let deal := _t154
    let _t155 ← v_HashDeck deal
    let _t156 ← kat_v2_digest (8 : Int)
    let _as157 ← SudoRt.sudoAssertEq _t155 _t156 982
    let _t158 ← v_HashDeck deal
    let _t159 ← SudoRt.filledL (28 : Int) (0 : Int)
    let _t160 ← v_Hash _t159
    let _as161 ← SudoRt.sudoAssertEq _t158 _t160 983
    pure ()

def test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init186 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init186 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t163 ← face_nbrs f
  let nb := _t163
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init178 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init178 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t165 ← SudoRt.atL nb i
  let _t166 ← edge_slot f _t165
  let s := _t166
  let _t167 ← edge_faces s
  let ⟨a, b⟩ := _t167
  let _t169 ← (if (SudoRt.SEq.beq a f) then (do
  let _t170 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq b _t170)) else pure false)
  let _t172 ← (if _t169 then pure true else (do
  let _t174 ← (if (SudoRt.SEq.beq b f) then (do
  let _t175 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq a _t175)) else pure false)
  pure _t174))
  let _as177 ← SudoRt.sudoAssert _t172 991
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
      let _init185 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init185 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t180 ← edge_faces s
  let ⟨a, b⟩ := _t180
  let _as182 ← SudoRt.sudoAssert (decide (a < b)) 994
  let _t183 ← edge_slot a b
  let _as184 ← SudoRt.sudoAssertEq _t183 s 995
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
    let _init198 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init198 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t188 ← face_move f
  let t := _t188
  let _fromV := (0 : Int)
  let _toV := (29 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init197 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init197 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t190 ← edge_faces s
  let ⟨a, b⟩ := _t190
  let _t191 ← SudoRt.atL (t).sudo_8Position_2ep s
  let moved := (!(SudoRt.SEq.beq _t191 s))
  let _t194 ← (if (SudoRt.SEq.beq f a) then pure true else (do
  pure (SudoRt.SEq.beq f b)))
  let _as196 ← SudoRt.sudoAssertEq moved _t194 1003
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
    let _t199 ← identity
    let idp := _t199
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
  let _t201 ← edge_faces s
  let ⟨a, b⟩ := _t201
  let _t202 ← edge_colours_at idp a b
  let _as203 ← SudoRt.sudoAssertEq _t202 (a, b) 1009
  let _t204 ← edge_colours_at idp b a
  let _as205 ← SudoRt.sudoAssertEq _t204 (b, a) 1010
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
      let _init220 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init220 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t207 ← identity
  let _t208 ← face_turn _t207 f (1 : Int)
  let g := _t208
  let _t209 ← face_nbrs f
  let nb := _t209
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init219 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init219 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t211 ← SudoRt.atL nb i
  let _t212 ← edge_colours_at g f _t211
  let ⟨c1, c2⟩ := _t212
  let _as213 ← SudoRt.sudoAssertEq c1 f 1016
  let _t214 ← SudoRt.atL nb i
  let _t215 ← SudoRt.atL nb i
  let _t216 ← corner_after_noon f _t215
  let _t217 ← colours_at g f _t214 _t216
  let ⟨d1, d2⟩ := _t217
  let _as218 ← SudoRt.sudoAssertEq d1 f 1018
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
    let _init244 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init244 fuel (fun σ =>
    let r := σ
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) r)
      else
        match ← ((do
  let _t223 ← rot_at r
  let o := _t223
  let _t224 ← visual_noon held_up o
  let _t225 ← SudoRt.atL o held_front
  let _as226 ← SudoRt.sudoAssertEq _t224 _t225 1023
  let _t227 ← visual_noon held_front o
  let _t228 ← SudoRt.atL o held_up
  let _as229 ← SudoRt.sudoAssertEq _t227 _t228 1024
  let _t230 ← visual_noon held_down o
  let _t231 ← SudoRt.atL o down_noon_hold
  let _as232 ← SudoRt.sudoAssertEq _t230 _t231 1025
  let _fromV := (0 : Int)
  let _toV := (11 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init243 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init243 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t234 ← visual_noon h o
  let n := _t234
  let _t235 ← SudoRt.atL o h
  let _t236 ← face_nbrs _t235
  let nb := _t236
  let hit := (0 : Int)
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init242 := (_fromV, hit)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init242 fuel (fun σ =>
    let i := σ.1
    let hit := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, hit))
      else
        match ← ((do
  let _t238 ← SudoRt.atL nb i
  if (SudoRt.SEq.beq _t238 n) then
    do
      let _t240 ← SudoRt.addI hit (1 : Int)
      let hit := _t240
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
      let _as241 ← SudoRt.sudoAssertEq hit (1 : Int) 1033
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
    let _init263 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init263 fuel (fun σ =>
    let r := σ
    do
      if r > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) r)
      else
        match ← ((do
  let _t246 ← rot_at r
  let o := _t246
  let _fromV := (6 : Int)
  let _toV := (10 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init262 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init262 fuel (fun σ =>
    let h := σ
    do
      if h > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) h)
      else
        match ← ((do
  let _t248 ← visual_noon h o
  let n := _t248
  let _t249 ← hold_of n o
  let _t250 ← SudoRt.subI h (5 : Int)
  let _as251 ← SudoRt.sudoAssertEq _t249 _t250 1040
  let _t252 ← SudoRt.atL o h
  let _t253 ← corner_after_noon _t252 n
  let right := _t253
  let _t254 ← hold_of right o
  let _as256 ← SudoRt.sudoAssert (decide (_t254 ≥ (1 : Int))) 1042
  let _t257 ← hold_of right o
  let _as259 ← SudoRt.sudoAssert (decide (_t257 ≤ (5 : Int))) 1043
  let _as261 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq right n)) 1044
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

def test_trace_hash_matches_hash_em_block_and_iv_cook12_on_every_kat : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (7 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init311 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init311 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t265 ← kat_msg n
  let msg := _t265
  let _t266 ← trace_hash msg
  let tr := _t266
  let _t267 ← kat_v2_digest n
  let _as268 ← SudoRt.sudoAssertEq (tr).sudo_5Trace_6digest _t267 1180
  let _t269 ← v_Hash msg
  let _as270 ← SudoRt.sudoAssertEq (tr).sudo_5Trace_6digest _t269 1181
  let _t271 ← identity
  let _t272 ← replay_turns _t271 (tr).sudo_5Trace_8iv_turns
  let _t273 ← iv_cook12
  let _as274 ← SudoRt.sudoAssertEq _t272 _t273 1182
  let _t275 ← pad_message msg
  let padded := _t275
  let _t277 ← SudoRt.mulI (SudoRt.listLen (tr).sudo_5Trace_6blocks) pad_block
  let _as279 ← SudoRt.sudoAssertEq _t277 (SudoRt.listLen padded) 1184
  let _t280 ← iv_cook12
  let h := _t280
  let _t309 ← SudoRt.subI (SudoRt.listLen (tr).sudo_5Trace_6blocks) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t309
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init310 := (_fromV, h)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init310 fuel (fun σ =>
    let b := σ.1
    let h := σ.2
    do
      if b > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (b, h))
      else
        match ← ((do
  let _t282 ← SudoRt.atL (tr).sudo_5Trace_6blocks b
  let blk := _t282
  let _as283 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_1h h 1188
  let _t284 ← phi_chunk (blk).sudo_10TraceBlock_5chunk
  let _as285 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_4deal _t284 1189
  let _t286 ← em_block h (blk).sudo_10TraceBlock_4deal
  let _as287 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_1e _t286 1190
  let _t289 ← SudoRt.addI body_len f3_t
  let _as290 ← SudoRt.sudoAssertEq (SudoRt.listLen (blk).sudo_10TraceBlock_5steps) _t289 1191
  let g := h
  let _t297 ← SudoRt.subI (SudoRt.listLen (blk).sudo_10TraceBlock_5steps) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t297
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init307 := (_fromV, g)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init307 fuel (fun σ =>
    let s := σ.1
    let g := σ.2
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (s, g))
      else
        match ← ((do
  let _t292 ← SudoRt.atL (blk).sudo_10TraceBlock_5steps s
  let st := _t292
  let _t293 ← SudoRt.addI s (1 : Int)
  let _as294 ← SudoRt.sudoAssertEq (st).sudo_9TraceStep_3pos _t293 1195
  let _t295 ← replay_turns g (st).sudo_9TraceStep_5turns
  let g := _t295
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
      let _as298 ← SudoRt.sudoAssertEq g (blk).sudo_10TraceBlock_1e 1197
      let _t299 ← compose h (blk).sudo_10TraceBlock_1e
      let _as300 ← SudoRt.sudoAssertEq (blk).sudo_10TraceBlock_6h_next _t299 1198
      let _t301 ← compose (blk).sudo_10TraceBlock_1h (blk).sudo_10TraceBlock_5h_inv
      let _t302 ← identity
      let _as303 ← SudoRt.sudoAssertEq _t301 _t302 1199
      let _t304 ← compose (blk).sudo_10TraceBlock_6h_next (blk).sudo_10TraceBlock_10h_next_inv
      let _t305 ← identity
      let _as306 ← SudoRt.sudoAssertEq _t304 _t305 1200
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

def test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved : Except SudoRt.Trap Unit :=
  do
    let _t312 ← identity
    let b := _t312
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init356 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init356 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, b))
      else
        match ← ((do
  let _t314 ← SudoRt.subI (11 : Int) i
  let _t315 ← face_turn b _t314 (4 : Int)
  let b := _t315
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
      let _t316 ← iv_cook12
      let _t317 ← inverse _t316
      let _as318 ← SudoRt.sudoAssertEq b _t317 1210
      let _fromV := (0 : Int)
      let _toV := (7 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init355 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init355 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t320 ← kat_msg n
  let _t321 ← trace_hash _t320
  let tr := _t321
  let _t322 ← iv_cook12
  let pa := _t322
  let pb := b
  let _t323 ← identity
  let pc := _t323
  let _t346 ← SudoRt.subI (SudoRt.listLen (tr).sudo_5Trace_6blocks) (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t346
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init354 := (_fromV, (pa, pb, pc))
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init354 fuel (fun σ =>
    let k := σ.1
    let pa := σ.2.1
    let _sp350 := σ.2.2
    let pb := _sp350.1
    let _sp351 := _sp350.2
    let pc := _sp351
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (k, (pa, pb, pc)))
      else
        match ← ((do
  let _t325 ← SudoRt.atL (tr).sudo_5Trace_6blocks k
  let blk := _t325
  let _as326 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_1h 1218
  let _t327 ← compose pa pb
  let _t328 ← identity
  let _as329 ← SudoRt.sudoAssertEq _t327 _t328 1219
  let _t330 ← identity
  let _as331 ← SudoRt.sudoAssertEq pc _t330 1220
  let pa := (blk).sudo_10TraceBlock_1e
  let _t332 ← inverse pb
  let _t333 ← compose _t332 pa
  let pa := _t333
  let _t334 ← identity
  let pb := _t334
  let _as335 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_6h_next 1224
  let _t336 ← inverse pa
  let s2 := _t336
  let _t337 ← identity
  let pa := _t337
  let _t338 ← compose s2 pb
  let pb := _t338
  let _t339 ← compose s2 pc
  let pc := _t339
  let _t340 ← inverse pc
  let _t341 ← compose _t340 pa
  let pa := _t341
  let _t342 ← identity
  let pc := _t342
  let _as343 ← SudoRt.sudoAssertEq pa (blk).sudo_10TraceBlock_6h_next 1231
  let _as344 ← SudoRt.sudoAssertEq pb (blk).sudo_10TraceBlock_10h_next_inv 1232
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
    let _sp352 := σ.2.2
    let pb := _sp352.1
    let _sp353 := _sp352.2
    let pc := _sp353
    do
      let _t347 ← position_to_bytes pa
      let _t348 ← kat_v2_digest n
      let _as349 ← SudoRt.sudoAssertEq _t347 _t348 1233
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
  SudoRt.runTests [("test_identity_rank_is_29_zero_bytes", fun _ => test_identity_rank_is_29_zero_bytes), ("test_compose_inverse_round_trip", fun _ => test_compose_inverse_round_trip), ("test_iv_cook12_digest", fun _ => test_iv_cook12_digest), ("test_empty_pad_is_one_block", fun _ => test_empty_pad_is_one_block), ("test_kat_pad_lengths", fun _ => test_kat_pad_lengths), ("test_abc_pad_recovers_the_24_bit_length", fun _ => test_abc_pad_recovers_the_24_bit_length), ("test_phi_of_28_zero_bytes_is_the_identity_deal", fun _ => test_phi_of_28_zero_bytes_is_the_identity_deal), ("test_hash_aliases_agree_on_the_empty_message", fun _ => test_hash_aliases_agree_on_the_empty_message), ("test_hashdeckbody_on_the_identity_deal_is_29_bytes", fun _ => test_hashdeckbody_on_the_identity_deal_is_29_bytes), ("test_hashdeckbodyfrom_at_iv_matches_hashdeckbody", fun _ => test_hashdeckbodyfrom_at_iv_matches_hashdeckbody), ("test_require_permutation_rejects_a_duplicate", fun _ => test_require_permutation_rejects_a_duplicate), ("test_v2_kat_digests_kats_megaminx_hash_kats_v2_json", fun _ => test_v2_kat_digests_kats_megaminx_hash_kats_v2_json), ("test_v2_kat_hashdeck_of_the_identity_deal", fun _ => test_v2_kat_hashdeck_of_the_identity_deal), ("test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot", fun _ => test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot), ("test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot", fun _ => test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot), ("test_edge_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_edges", fun _ => test_edge_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_edges), ("test_visual_noon_is_a_neighbour_of_the_held_face_in_all_60_grips", fun _ => test_visual_noon_is_a_neighbour_of_the_held_face_in_all_60_grips), ("test_lower_ring_noon_is_the_upper_left_of_the_two_upper_ring_neighbours", fun _ => test_lower_ring_noon_is_the_upper_left_of_the_two_upper_ring_neighbours), ("test_trace_hash_matches_hash_em_block_and_iv_cook12_on_every_kat", fun _ => test_trace_hash_matches_hash_em_block_and_iv_cook12_on_every_kat), ("test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved", fun _ => test_cook_b_backwards_is_iv_cook12_inverse_and_the_3_solve_leaves_h_h_1_solved)]
