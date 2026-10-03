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
    let _as4 ← SudoRt.sudoAssertEq (SudoRt.listLen z) digest_len 845
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
  let _as7 ← SudoRt.sudoAssertEq _t6 (0 : Int) 847
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
    let _as17 ← SudoRt.sudoAssertEq (left).sudo_8Position_2cp (idp).sudo_8Position_2cp 854
    let _as18 ← SudoRt.sudoAssertEq (left).sudo_8Position_2co (idp).sudo_8Position_2co 855
    let _as19 ← SudoRt.sudoAssertEq (left).sudo_8Position_2ep (idp).sudo_8Position_2ep 856
    let _as20 ← SudoRt.sudoAssertEq (left).sudo_8Position_2eo (idp).sudo_8Position_2eo 857
    let _as21 ← SudoRt.sudoAssertEq (right).sudo_8Position_2cp (idp).sudo_8Position_2cp 858
    let _as22 ← SudoRt.sudoAssertEq (right).sudo_8Position_2co (idp).sudo_8Position_2co 859
    let _as23 ← SudoRt.sudoAssertEq (right).sudo_8Position_2ep (idp).sudo_8Position_2ep 860
    let _as24 ← SudoRt.sudoAssertEq (right).sudo_8Position_2eo (idp).sudo_8Position_2eo 861
    pure ()

def test_iv_cook12_digest : Except SudoRt.Trap Unit :=
  do
    let _t25 ← iv_cook12
    let _t26 ← position_to_bytes _t25
    let d := _t26
    let _t27 ← hex_iv
    let _as28 ← SudoRt.sudoAssertEq d _t27 865
    pure ()

def test_empty_pad_is_one_block : Except SudoRt.Trap Unit :=
  do
    let _t29 ← pad_message (#[] : Array (Int))
    let p := _t29
    let _as31 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 869
    let _t32 ← SudoRt.atL p (0 : Int)
    let _as33 ← SudoRt.sudoAssertEq _t32 (128 : Int) 870
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
  let _as36 ← SudoRt.sudoAssertEq _t35 (0 : Int) 872
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
    let _as45 ← SudoRt.sudoAssertEq (SudoRt.listLen _t43) (28 : Int) 875
    let _t46 ← pad_message (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let _as48 ← SudoRt.sudoAssertEq (SudoRt.listLen _t46) (28 : Int) 876
    let _t49 ← pad_message (#[(0 : Int)] : Array (Int))
    let _as51 ← SudoRt.sudoAssertEq (SudoRt.listLen _t49) (28 : Int) 877
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
      let _as58 ← SudoRt.sudoAssertEq (SudoRt.listLen _t56) (56 : Int) 881
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
      let _as65 ← SudoRt.sudoAssertEq (SudoRt.listLen _t63) (56 : Int) 885
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
      let _as72 ← SudoRt.sudoAssertEq (SudoRt.listLen _t70) (56 : Int) 889
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
      let _as79 ← SudoRt.sudoAssertEq (SudoRt.listLen _t77) (84 : Int) 893
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
      let _as88 ← SudoRt.sudoAssertEq (SudoRt.listLen _t86) (112 : Int) 897
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
    let _as96 ← SudoRt.sudoAssertEq (SudoRt.listLen p) (28 : Int) 901
    let _t97 ← SudoRt.atL p (0 : Int)
    let _as98 ← SudoRt.sudoAssertEq _t97 (97 : Int) 902
    let _t99 ← SudoRt.atL p (1 : Int)
    let _as100 ← SudoRt.sudoAssertEq _t99 (98 : Int) 903
    let _t101 ← SudoRt.atL p (2 : Int)
    let _as102 ← SudoRt.sudoAssertEq _t101 (99 : Int) 904
    let _t103 ← SudoRt.atL p (3 : Int)
    let _as104 ← SudoRt.sudoAssertEq _t103 (128 : Int) 905
    let _t105 ← SudoRt.atL p (27 : Int)
    let _as106 ← SudoRt.sudoAssertEq _t105 (24 : Int) 906
    pure ()

def test_phi_of_28_zero_bytes_is_the_identity_deal : Except SudoRt.Trap Unit :=
  do
    let _t107 ← SudoRt.filledL (28 : Int) (0 : Int)
    let z := _t107
    let _t108 ← phi_chunk z
    let deal := _t108
    let _as110 ← SudoRt.sudoAssertEq (SudoRt.listLen deal) (52 : Int) 911
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
  let _as113 ← SudoRt.sudoAssertEq _t112 i 913
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
      let _as115 ← SudoRt.sudoAssertEq _t114 deal 914
      let _t116 ← phi_inv deal
      let _as117 ← SudoRt.sudoAssertEq _t116 z 915
      pure ()) (fun r => pure r))
    pure _out

def test_hash_aliases_agree_on_the_empty_message : Except SudoRt.Trap Unit :=
  do
    let _t119 ← v_Hash (#[] : Array (Int))
    let d := _t119
    let _as121 ← SudoRt.sudoAssertEq (SudoRt.listLen d) digest_len 919
    let _t122 ← v_MegaDreifach (#[] : Array (Int))
    let _as123 ← SudoRt.sudoAssertEq _t122 d 920
    pure ()

def test_hashdeckbody_on_the_identity_deal_is_29_bytes : Except SudoRt.Trap Unit :=
  do
    let _t124 ← range_list (52 : Int)
    let deal := _t124
    let _t125 ← v_HashDeckBody deal
    let b := _t125
    let _as127 ← SudoRt.sudoAssertEq (SudoRt.listLen b) digest_len 925
    let _t128 ← v_MegaDreifachBody deal
    let _as129 ← SudoRt.sudoAssertEq _t128 b 926
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
    let _as134 ← SudoRt.sudoAssertEq «from_iv» _t133 932
    let _t135 ← v_MegaDreifachBodyFrom deal iv
    let _t136 ← v_MegaDreifachBody deal
    let _as137 ← SudoRt.sudoAssertEq _t135 _t136 933
    let _t138 ← identity
    let _t139 ← v_HashDeckBodyFrom deal _t138
    let «from_id» := _t139
    let _as141 ← SudoRt.sudoAssertEq (SudoRt.listLen «from_id») digest_len 935
    let _as143 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq «from_id» «from_iv»)) 936
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
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 940: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 940: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_v3_kat_digests_kats_megaminx_hash_kats_v3_json : Except SudoRt.Trap Unit :=
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
  let _t151 ← kat_v3_digest n
  let _as152 ← SudoRt.sudoAssertEq _t150 _t151 945
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
    let _t154 ← range_list (52 : Int)
    let deal := _t154
    let _t155 ← v_HashDeck deal
    let _t156 ← kat_v3_digest (8 : Int)
    let _as157 ← SudoRt.sudoAssertEq _t155 _t156 949
    let _t158 ← v_HashDeck deal
    let _t159 ← SudoRt.filledL (28 : Int) (0 : Int)
    let _t160 ← v_Hash _t159
    let _as161 ← SudoRt.sudoAssertEq _t158 _t160 950
    pure ()

def test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init170 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init170 fuel (fun σ =>
    let n := σ
    do
      if n > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) n)
      else
        match ← ((do
  let _t163 ← kat_v3_body_deal n
  let _t164 ← v_HashDeckBody _t163
  let _t165 ← kat_v3_body_digest n
  let _as166 ← SudoRt.sudoAssertEq _t164 _t165 954
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
      let _t167 ← kat_v3_body_deal (1 : Int)
      let _t168 ← SudoRt.atL _t167 (51 : Int)
      let _as169 ← SudoRt.sudoAssertEq _t168 (51 : Int) 955
      pure ()) (fun r => pure r))
    pure _out

def test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot : Except SudoRt.Trap Unit :=
  do
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init195 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init195 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t172 ← face_nbrs f
  let nb := _t172
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init187 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init187 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t174 ← SudoRt.atL nb i
  let _t175 ← edge_slot f _t174
  let s := _t175
  let _t176 ← edge_faces s
  let ⟨a, b⟩ := _t176
  let _t178 ← (if (SudoRt.SEq.beq a f) then (do
  let _t179 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq b _t179)) else pure false)
  let _t181 ← (if _t178 then pure true else (do
  let _t183 ← (if (SudoRt.SEq.beq b f) then (do
  let _t184 ← SudoRt.atL nb i
  pure (SudoRt.SEq.beq a _t184)) else pure false)
  pure _t183))
  let _as186 ← SudoRt.sudoAssert _t181 963
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
      let _init194 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init194 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t189 ← edge_faces s
  let ⟨a, b⟩ := _t189
  let _as191 ← SudoRt.sudoAssert (decide (a < b)) 966
  let _t192 ← edge_slot a b
  let _as193 ← SudoRt.sudoAssertEq _t192 s 967
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
    let _init207 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init207 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t197 ← face_move f
  let t := _t197
  let _fromV := (0 : Int)
  let _toV := (29 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init206 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init206 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t199 ← edge_faces s
  let ⟨a, b⟩ := _t199
  let _t200 ← SudoRt.atL (t).sudo_8Position_2ep s
  let moved := (!(SudoRt.SEq.beq _t200 s))
  let _t203 ← (if (SudoRt.SEq.beq f a) then pure true else (do
  pure (SudoRt.SEq.beq f b)))
  let _as205 ← SudoRt.sudoAssertEq moved _t203 975
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
    let _t208 ← identity
    let idp := _t208
    let _fromV := (0 : Int)
    let _toV := (29 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init228 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init228 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t210 ← edge_faces s
  let ⟨a, b⟩ := _t210
  let _t211 ← edge_colours_at idp a b
  let _as212 ← SudoRt.sudoAssertEq _t211 (a, b) 981
  let _t213 ← edge_face_of idp a b a
  let _as214 ← SudoRt.sudoAssertEq _t213 a 982
  let _t215 ← edge_face_of idp a b b
  let _as216 ← SudoRt.sudoAssertEq _t215 b 983
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
      let _init227 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init227 fuel (fun σ =>
    let f := σ
    do
      if f > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) f)
      else
        match ← ((do
  let _t218 ← identity
  let _t219 ← face_turn _t218 f (1 : Int)
  let g := _t219
  let _fromV := (1 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init226 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init226 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t221 ← suit_nbrs f k
  let ⟨n, n2⟩ := _t221
  let _t222 ← edge_face_of g f n f
  let _as223 ← SudoRt.sudoAssertEq _t222 f 988
  let _t224 ← corner_face_of g f n n2 f
  let _as225 ← SudoRt.sudoAssertEq _t224 f 989
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
    let _init260 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init260 fuel (fun σ =>
    let c := σ
    do
      if c > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) c)
      else
        match ← ((do
  let _t230 ← face_nbrs c
  let nb := _t230
  let _t231 ← lowest_nbr_index c
  let _t232 ← SudoRt.atL nb _t231
  let lo := _t232
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init259 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init259 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t234 ← SudoRt.atL nb i
  let _as236 ← SudoRt.sudoAssert (decide (lo ≤ _t234)) 996
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
      let _t237 ← suit_nbrs c (1 : Int)
      let ⟨n1, m1⟩ := _t237
      let _as238 ← SudoRt.sudoAssertEq n1 lo 998
      let _fromV := (1 : Int)
      let _toV := (4 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init258 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init258 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t240 ← suit_nbrs c k
  let ⟨n, n2⟩ := _t240
  let hit := (0 : Int)
  let _fromV := (0 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init257 := (_fromV, hit)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init257 fuel (fun σ =>
    let i := σ.1
    let hit := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, hit))
      else
        match ← ((do
  let _t242 ← SudoRt.atL nb i
  let _t244 ← (if (SudoRt.SEq.beq _t242 n) then (do
  let _t245 ← SudoRt.addI i (1 : Int)
  let _t246 ← SudoRt.modI _t245 (5 : Int)
  let _t247 ← SudoRt.atL nb _t246
  pure (SudoRt.SEq.beq _t247 n2)) else pure false)
  if _t244 then
    do
      let _t249 ← SudoRt.addI hit (1 : Int)
      let hit := _t249
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
      let _as250 ← SudoRt.sudoAssertEq hit (1 : Int) 1005
      let _fromV := (1 : Int)
      let _toV := (4 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init256 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init256 fuel (fun σ =>
    let j := σ
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) j)
      else
        match ← ((do
  if (!(SudoRt.SEq.beq j k)) then
    do
      let _t253 ← suit_nbrs c j
      let ⟨m, m2⟩ := _t253
      let _as255 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq m n)) 1009
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
    let _t261 ← SudoRt.filledL (30 : Int) (0 : Int)
    let eseen := _t261
    let _t262 ← SudoRt.filledL (20 : Int) (0 : Int)
    let cseen := _t262
    let _fromV := (0 : Int)
    let _toV := (47 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init292 := (_fromV, (eseen, cseen))
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init292 fuel (fun σ =>
    let card := σ.1
    let eseen := σ.2.1
    let _sp290 := σ.2.2
    let cseen := _sp290
    do
      if card > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (card, (eseen, cseen)))
      else
        match ← ((do
  let _t264 ← card_colour card
  let c := _t264
  let _t265 ← SudoRt.modI card (4 : Int)
  let _t266 ← SudoRt.addI _t265 (1 : Int)
  let _t267 ← suit_nbrs c _t266
  let ⟨n, n2⟩ := _t267
  let _t268 ← edge_slot c n
  let _ix269 := _t268
  let _t270 ← edge_slot c n
  let _t271 ← SudoRt.atL eseen _t270
  let _t272 ← SudoRt.addI _t271 (1 : Int)
  let _t273 ← SudoRt.putL eseen _ix269 _t272
  let eseen := _t273
  let _t274 ← corner_slot c n n2
  let _ix275 := _t274
  let _t276 ← corner_slot c n n2
  let _t277 ← SudoRt.atL cseen _t276
  let _t278 ← SudoRt.addI _t277 (1 : Int)
  let _t279 ← SudoRt.putL cseen _ix275 _t278
  let cseen := _t279
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
    let _sp291 := σ.2.2
    let cseen := _sp291
    do
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init289 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init289 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t281 ← SudoRt.atL eseen s
  let _as283 ← SudoRt.sudoAssert (decide (_t281 ≥ (1 : Int))) 1020
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
      let _init288 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init288 fuel (fun σ =>
    let s := σ
    do
      if s > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) s)
      else
        match ← ((do
  let _t285 ← SudoRt.atL cseen s
  let _as287 ← SudoRt.sudoAssert (decide (_t285 ≥ (1 : Int))) 1022
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
    let _t293 ← iv_cook12
    let _t294 ← start_run _t293
    let r := _t294
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init310 := (_fromV, r)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init310 fuel (fun σ =>
    let i := σ.1
    let r := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, r))
      else
        match ← ((do
  let _t296 ← SudoRt.mulI i (23 : Int)
  let _t297 ← SudoRt.addI _t296 (7 : Int)
  let _t298 ← SudoRt.modI _t297 (52 : Int)
  let card := _t298
  let _t299 ← SudoRt.divI card (4 : Int)
  let _t300 ← SudoRt.modI card (4 : Int)
  let _t301 ← SudoRt.addI _t300 (1 : Int)
  let _t302 ← card_colour card
  let _t303 ← card_step r (r).sudo_3Run_4last _t299 _t301 _t302
  let r := _t303
  let _t304 ← card_colour card
  let c := _t304
  let _t305 ← SudoRt.modI card (4 : Int)
  let _t306 ← SudoRt.addI _t305 (1 : Int)
  let _t307 ← suit_nbrs c _t306
  let ⟨n, n2⟩ := _t307
  let _t308 ← edge_face_of (r).sudo_3Run_1g c n n
  let _as309 ← SudoRt.sudoAssertEq _t308 (r).sudo_3Run_4last 1031
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

def test_a_king_step_equals_the_step_of_the_rank_that_counts_up_to_the_opposite_face_opposites_last_last : Except SudoRt.Trap Unit :=
  do
    let _t311 ← iv_cook12
    let _t312 ← start_run _t311
    let r0 := _t312
    let _fromV := (0 : Int)
    let _toV := (11 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init327 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init327 fuel (fun σ =>
    let last := σ
    do
      if last > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) last)
      else
        match ← ((do
  let _t314 ← SudoRt.atL opposites last
  let _as316 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t314 last)) 1036
  let _t317 ← SudoRt.atL opposites last
  let _t318 ← SudoRt.subI _t317 last
  let _t319 ← SudoRt.addI _t318 (12 : Int)
  let _t320 ← SudoRt.modI _t319 (12 : Int)
  let rank := _t320
  let _fromV := (1 : Int)
  let _toV := (4 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init326 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init326 fuel (fun σ =>
    let k := σ
    do
      if k > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) k)
      else
        match ← ((do
  let _t322 ← card_step r0 last (12 : Int) k (0 : Int)
  let king := _t322
  let _t323 ← card_step r0 last rank k (0 : Int)
  let same := _t323
  let _as324 ← SudoRt.sudoAssertEq (king).sudo_3Run_4last (same).sudo_3Run_4last 1041
  let _as325 ← SudoRt.sudoAssertEq (king).sudo_3Run_1g (same).sudo_3Run_1g 1042
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
    let _t330 ← iv_cook12
    let g0 := _t330
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init351 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init351 fuel (fun σ =>
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
  let _init350 := (_fromV, deal)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init350 fuel (fun σ =>
    let card := σ.1
    let deal := σ.2
    do
      if card > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (card, deal))
      else
        match ← ((do
  if (!(SudoRt.SEq.beq card held)) then
    do
      let _mb334 := SudoRt.appendL deal card
      let ⟨_nr335, _⟩ := _mb334
      let deal := _nr335
      let _hm328 := ()
      let _u336 := _hm328
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
      let _mb337 := SudoRt.appendL deal held
      let ⟨_nr338, _⟩ := _mb337
      let deal := _nr338
      let _hm329 := ()
      let _u339 := _hm329
      let _t340 ← em_run g0 deal
      let r := _t340
      let _as341 ← SudoRt.sudoAssertEq (r).sudo_3Run_5turns (468 : Int) 1053
      let _t342 ← SudoRt.modI held (4 : Int)
      let _t343 ← SudoRt.addI _t342 (1 : Int)
      let _t344 ← SudoRt.mulI (26 : Int) _t343
      let _t345 ← SudoRt.addI (520 : Int) _t344
      let _as346 ← SudoRt.sudoAssertEq (r).sudo_3Run_6clicks _t345 1054
      let _as347 ← SudoRt.sudoAssertEq (r).sudo_3Run_5finds (156 : Int) 1055
      let _as348 ← SudoRt.sudoAssertEq (r).sudo_3Run_7relooks (78 : Int) 1056
      let _as349 ← SudoRt.sudoAssertEq (r).sudo_3Run_14register_looks (52 : Int) 1057
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
    let _init462 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init462 fuel (fun σ =>
    let p := σ
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) p)
      else
        match ← ((do
  let _t355 ← edge_faces p
  let ⟨a, b⟩ := _t355
  let _fromV := (0 : Int)
  let _toV := (1 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init420 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init420 fuel (fun σ =>
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
      let _init388 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init388 fuel (fun σ =>
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
  let _init385 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init385 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t361 ← identity
  let g := _t361
  let _ix362 := p
  let _t363 ← SudoRt.atL (g).sudo_8Position_2ep s
  let _t364 ← SudoRt.putL (g).sudo_8Position_2ep _ix362 _t363
  let _t365 := { g with sudo_8Position_2ep := _t364 }
  let g := _t365
  let _ix366 := p
  let _t367 ← SudoRt.putL (g).sudo_8Position_2eo _ix366 (0 : Int)
  let _t368 := { g with sudo_8Position_2eo := _t367 }
  let g := _t368
  let _ix369 := s
  let _t370 ← SudoRt.putL (g).sudo_8Position_2ep _ix369 p
  let _t371 := { g with sudo_8Position_2ep := _t370 }
  let g := _t371
  let _ix372 := s
  let _t373 ← SudoRt.putL (g).sudo_8Position_2eo _ix372 o
  let _t374 := { g with sudo_8Position_2eo := _t373 }
  let g := _t374
  let _t375 ← edge_face_of g a b x
  let f1 := _t375
  let _t376 ← face_turn g f1 (1 : Int)
  let _t377 ← edge_face_of _t376 a b y
  let f2 := _t377
  let _t378 ← identity
  let _t379 ← face_turn _t378 f1 (1 : Int)
  let _t380 ← face_turn _t379 f2 (1 : Int)
  let _mb381 := SudoRt.setAdd words _t380
  let ⟨_nr382, _mv383⟩ := _mb381
  let words := _nr382
  let _hm352 := _mv383
  let _u384 := _hm352
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
      let _as387 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1079
      pure (SudoRt.Flow.cont (ρ := Unit) ())) (fun r => pure (SudoRt.Flow.ret (ρ := Unit) r)))
      pure _out
  else
    do
      let words := (SudoRt.setNew : SudoRt.SSet (Position))
      let _fromV := (0 : Int)
      let _toV := (29 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init419 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init419 fuel (fun σ =>
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
  let _init416 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init416 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t392 ← identity
  let g := _t392
  let _ix393 := p
  let _t394 ← SudoRt.atL (g).sudo_8Position_2ep s
  let _t395 ← SudoRt.putL (g).sudo_8Position_2ep _ix393 _t394
  let _t396 := { g with sudo_8Position_2ep := _t395 }
  let g := _t396
  let _ix397 := p
  let _t398 ← SudoRt.putL (g).sudo_8Position_2eo _ix397 (0 : Int)
  let _t399 := { g with sudo_8Position_2eo := _t398 }
  let g := _t399
  let _ix400 := s
  let _t401 ← SudoRt.putL (g).sudo_8Position_2ep _ix400 p
  let _t402 := { g with sudo_8Position_2ep := _t401 }
  let g := _t402
  let _ix403 := s
  let _t404 ← SudoRt.putL (g).sudo_8Position_2eo _ix403 o
  let _t405 := { g with sudo_8Position_2eo := _t404 }
  let g := _t405
  let _t406 ← edge_face_of g a b x
  let f1 := _t406
  let _t407 ← face_turn g f1 (1 : Int)
  let _t408 ← edge_face_of _t407 a b y
  let f2 := _t408
  let _t409 ← identity
  let _t410 ← face_turn _t409 f1 (1 : Int)
  let _t411 ← face_turn _t410 f2 (1 : Int)
  let _mb412 := SudoRt.setAdd words _t411
  let ⟨_nr413, _mv414⟩ := _mb412
  let words := _nr413
  let _hm352 := _mv414
  let _u415 := _hm352
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
      let _as418 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1079
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
      let _init461 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init461 fuel (fun σ =>
    let p := σ
    do
      if p > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) p)
      else
        match ← ((do
  let _t422 ← corner_faces p
  let ⟨a, b, c⟩ := _t422
  let cols := (#[a, b, c] : Array (Int))
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init460 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init460 fuel (fun σ =>
    let i1 := σ
    do
      if i1 > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i1)
      else
        match ← ((do
  let _fromV := (0 : Int)
  let _toV := (2 : Int)
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init459 := _fromV
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init459 fuel (fun σ =>
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
      let _init458 := (_fromV, words)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init458 fuel (fun σ =>
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
  let _init455 := (_fromV, words)
  let _out ← (SudoRt.runLoopOn (ρ := Unit) _init455 fuel (fun σ =>
    let o := σ.1
    let words := σ.2
    do
      if o > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (o, words))
      else
        match ← ((do
  let _t429 ← identity
  let g := _t429
  let _ix430 := p
  let _t431 ← SudoRt.atL (g).sudo_8Position_2cp s
  let _t432 ← SudoRt.putL (g).sudo_8Position_2cp _ix430 _t431
  let _t433 := { g with sudo_8Position_2cp := _t432 }
  let g := _t433
  let _ix434 := p
  let _t435 ← SudoRt.putL (g).sudo_8Position_2co _ix434 (0 : Int)
  let _t436 := { g with sudo_8Position_2co := _t435 }
  let g := _t436
  let _ix437 := s
  let _t438 ← SudoRt.putL (g).sudo_8Position_2cp _ix437 p
  let _t439 := { g with sudo_8Position_2cp := _t438 }
  let g := _t439
  let _ix440 := s
  let _t441 ← SudoRt.putL (g).sudo_8Position_2co _ix440 o
  let _t442 := { g with sudo_8Position_2co := _t441 }
  let g := _t442
  let _t443 ← SudoRt.atL cols i1
  let _t444 ← corner_face_of g a b c _t443
  let f1 := _t444
  let _t445 ← face_turn g f1 (1 : Int)
  let _t446 ← SudoRt.atL cols i2
  let _t447 ← corner_face_of _t445 a b c _t446
  let f2 := _t447
  let _t448 ← identity
  let _t449 ← face_turn _t448 f1 (1 : Int)
  let _t450 ← face_turn _t449 f2 (1 : Int)
  let _mb451 := SudoRt.setAdd words _t450
  let ⟨_nr452, _mv453⟩ := _mb451
  let words := _nr452
  let _hm353 := _mv453
  let _u454 := _hm353
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
      let _as457 ← SudoRt.sudoAssertEq (SudoRt.setSize words) (60 : Int) 1097
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

def main : IO UInt32 :=
  SudoRt.runTests [("test_identity_rank_is_29_zero_bytes", fun _ => test_identity_rank_is_29_zero_bytes), ("test_compose_inverse_round_trip", fun _ => test_compose_inverse_round_trip), ("test_iv_cook12_digest", fun _ => test_iv_cook12_digest), ("test_empty_pad_is_one_block", fun _ => test_empty_pad_is_one_block), ("test_kat_pad_lengths", fun _ => test_kat_pad_lengths), ("test_abc_pad_recovers_the_24_bit_length", fun _ => test_abc_pad_recovers_the_24_bit_length), ("test_phi_of_28_zero_bytes_is_the_identity_deal", fun _ => test_phi_of_28_zero_bytes_is_the_identity_deal), ("test_hash_aliases_agree_on_the_empty_message", fun _ => test_hash_aliases_agree_on_the_empty_message), ("test_hashdeckbody_on_the_identity_deal_is_29_bytes", fun _ => test_hashdeckbody_on_the_identity_deal_is_29_bytes), ("test_hashdeckbodyfrom_at_iv_matches_hashdeckbody", fun _ => test_hashdeckbodyfrom_at_iv_matches_hashdeckbody), ("test_require_permutation_rejects_a_duplicate", fun _ => test_require_permutation_rejects_a_duplicate), ("test_v3_kat_digests_kats_megaminx_hash_kats_v3_json", fun _ => test_v3_kat_digests_kats_megaminx_hash_kats_v3_json), ("test_v3_kat_hashdeck_of_the_identity_deal", fun _ => test_v3_kat_hashdeck_of_the_identity_deal), ("test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes", fun _ => test_v3_kat_hashdeckbody_vectors_one_with_a_king_held_for_the_echoes), ("test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot", fun _ => test_edge_slot_table_every_adjacent_face_pair_owns_exactly_one_slot), ("test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot", fun _ => test_edge_slot_table_exactly_the_two_owning_faces_move_each_slot), ("test_edge_and_corner_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_pieces", fun _ => test_edge_and_corner_read_solved_shows_own_colours_a_turn_keeps_its_colour_on_its_pieces), ("test_suit_neighbours_four_different_neighbours_n2_follows_n_clockwise", fun _ => test_suit_neighbours_four_different_neighbours_n2_follows_n_clockwise), ("test_coverage_the_48_non_king_cards_name_all_30_edges_and_all_20_corners", fun _ => test_coverage_the_48_non_king_cards_name_all_30_edges_and_all_20_corners), ("test_card_pass_the_last_face_is_re_derivable_from_the_board_and_the_top_dealt_card", fun _ => test_card_pass_the_last_face_is_re_derivable_from_the_board_and_the_top_dealt_card), ("test_a_king_step_equals_the_step_of_the_rank_that_counts_up_to_the_opposite_face_opposites_last_last", fun _ => test_a_king_step_equals_the_step_of_the_rank_that_counts_up_to_the_opposite_face_opposites_last_last), ("test_cost_per_block_spec_v3_5_6_468_turns_520_26k_clicks_156_finds_78_re_looks_52_register_looks", fun _ => test_cost_per_block_spec_v3_5_6_468_turns_520_26k_clicks_156_finds_78_re_looks_52_register_looks), ("test_read_words_spec_v3_5_8_for_every_piece_and_ordered_pair_of_its_colours_its_60_states_give_60_distinct_two_turn_words", fun _ => test_read_words_spec_v3_5_8_for_every_piece_and_ordered_pair_of_its_colours_its_60_states_give_60_distinct_two_turn_words)]
