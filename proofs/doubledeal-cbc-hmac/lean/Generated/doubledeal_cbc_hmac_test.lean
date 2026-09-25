-- DO NOT EDIT. Generated from doubledeal_cbc_hmac.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for doubledeal_cbc_hmac.sudo
import SudoRt
import Doubledeal_cbc_hmac
import Megadreifach
set_option linter.unusedVariables false
open Doubledeal_cbc_hmac

def test_xor_is_bitwise_and_involutive : Except SudoRt.Trap Unit :=
  do
    let _t1 ← xor_byte (0 : Int) (0 : Int)
    let _as2 ← SudoRt.sudoAssertEq _t1 (0 : Int) 177
    let _t3 ← xor_byte (255 : Int) (0 : Int)
    let _as4 ← SudoRt.sudoAssertEq _t3 (255 : Int) 178
    let _t5 ← xor_byte (54 : Int) (54 : Int)
    let _as6 ← SudoRt.sudoAssertEq _t5 (0 : Int) 179
    let _t7 ← xor_byte (92 : Int) (255 : Int)
    let _as8 ← SudoRt.sudoAssertEq _t7 (163 : Int) 180
    let a := (#[(1 : Int), (2 : Int), (3 : Int), (4 : Int)] : Array (Int))
    let b := (#[(255 : Int), (0 : Int), (1 : Int), (128 : Int)] : Array (Int))
    let _t9 ← xor_bytes a b
    let x := _t9
    let _t10 ← xor_bytes x b
    let _as11 ← SudoRt.sudoAssertEq _t10 a 184
    let _t12 ← xor_bytes a a
    let _as13 ← SudoRt.sudoAssertEq _t12 (#[(0 : Int), (0 : Int), (0 : Int), (0 : Int)] : Array (Int)) 185
    pure ()

def test_iso7816_pad_matches_doubledeal_ecb : Except SudoRt.Trap Unit :=
  do
    let _t15 ← pad_iso7816 (#[] : Array (Int))
    let empty := _t15
    let _as17 ← SudoRt.sudoAssertEq (SudoRt.listLen empty) (28 : Int) 189
    let _t18 ← SudoRt.atL empty (0 : Int)
    let _as19 ← SudoRt.sudoAssertEq _t18 (128 : Int) 190
    let _fromV := (1 : Int)
    let _toV := (27 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init38 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init38 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t21 ← SudoRt.atL empty i
  let _as22 ← SudoRt.sudoAssertEq _t21 (0 : Int) 192
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
      let _t23 ← unpad_iso7816 empty
      let _as24 ← SudoRt.sudoAssertEq _t23 (#[] : Array (Int)) 193
      let «exact» := (#[] : Array (Int))
      let _fromV := (0 : Int)
      let _toV := (27 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init37 := (_fromV, «exact»)
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init37 fuel (fun σ =>
    let i := σ.1
    let «exact» := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, «exact»))
      else
        match ← ((do
  let _mb26 := SudoRt.appendL «exact» i
  let ⟨_nr27, _⟩ := _mb26
  let «exact» := _nr27
  let _hm14 := ()
  let _u28 := _hm14
  pure (SudoRt.Flow.cont (ρ := Unit) «exact»)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let «exact» := σ.2
    do
      let _t29 ← pad_iso7816 «exact»
      let twice := _t29
      let _as31 ← SudoRt.sudoAssertEq (SudoRt.listLen twice) (56 : Int) 198
      let _t32 ← unpad_iso7816 twice
      let _as33 ← SudoRt.sudoAssertEq _t32 «exact» 199
      let mid := (#[(1 : Int), (2 : Int), (128 : Int)] : Array (Int))
      let _t34 ← pad_iso7816 mid
      let _t35 ← unpad_iso7816 _t34
      let _as36 ← SudoRt.sudoAssertEq _t35 mid 201
      pure ()) (fun r => pure r))
      pure _out) (fun r => pure r))
    pure _out

def test_hmac_key_shorter_than_b_is_zero_padded : Except SudoRt.Trap Unit :=
  do
    let _t39 ← hmac_normalize_key (#[(1 : Int), (2 : Int), (3 : Int)] : Array (Int))
    let k := _t39
    let _as41 ← SudoRt.sudoAssertEq (SudoRt.listLen k) (28 : Int) 205
    let _t42 ← SudoRt.atL k (0 : Int)
    let _as43 ← SudoRt.sudoAssertEq _t42 (1 : Int) 206
    let _t44 ← SudoRt.atL k (1 : Int)
    let _as45 ← SudoRt.sudoAssertEq _t44 (2 : Int) 207
    let _t46 ← SudoRt.atL k (2 : Int)
    let _as47 ← SudoRt.sudoAssertEq _t46 (3 : Int) 208
    let _fromV := (3 : Int)
    let _toV := (27 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init54 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init54 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t49 ← SudoRt.atL k i
  let _as50 ← SudoRt.sudoAssertEq _t49 (0 : Int) 210
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
      let _t51 ← hmac_normalize_key (#[] : Array (Int))
      let z := _t51
      let _t52 ← SudoRt.filledL (28 : Int) (0 : Int)
      let _as53 ← SudoRt.sudoAssertEq z _t52 212
      pure ()) (fun r => pure r))
    pure _out

def test_cbc_chain_drops_the_most_significant_rank_byte : Except SudoRt.Trap Unit :=
  do
    let block := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (28 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init68 := (_fromV, block)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init68 fuel (fun σ =>
    let i := σ.1
    let block := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, block))
      else
        match ← ((do
  let _mb57 := SudoRt.appendL block i
  let ⟨_nr58, _⟩ := _mb57
  let block := _nr58
  let _hm55 := ()
  let _u59 := _hm55
  pure (SudoRt.Flow.cont (ρ := Unit) block)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let block := σ.2
    do
      let _t60 ← cbc_chain_from_cipher_block block
      let chain := _t60
      let _as62 ← SudoRt.sudoAssertEq (SudoRt.listLen chain) (28 : Int) 219
      let _fromV := (0 : Int)
      let _toV := (27 : Int)
      let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
      let _init67 := _fromV
      let _out ← (SudoRt.runLoopOn (ρ := Unit) _init67 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t64 ← SudoRt.atL chain i
  let _t65 ← SudoRt.addI i (1 : Int)
  let _as66 ← SudoRt.sudoAssertEq _t64 _t65 221
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
      pure _out) (fun r => pure r))
    pure _out

def test_mac_input_is_length_delimited : Except SudoRt.Trap Unit :=
  do
    let aad := (#[(1 : Int), (2 : Int)] : Array (Int))
    let _t69 ← SudoRt.filledL (28 : Int) (7 : Int)
    let iv := _t69
    let _t70 ← SudoRt.filledL (29 : Int) (9 : Int)
    let c := _t70
    let _t71 ← mac_input aad iv c
    let m := _t71
    let _t72 ← SudoRt.atL m (0 : Int)
    let _as73 ← SudoRt.sudoAssertEq _t72 (0 : Int) 228
    let _t74 ← SudoRt.atL m (1 : Int)
    let _as76 ← SudoRt.sudoAssertEq _t74 (SudoRt.listLen version_label) 229
    let _t78 ← SudoRt.addI (2 : Int) (SudoRt.listLen version_label)
    let _t79 ← take_prefix m _t78
    let _t81 ← u16be (SudoRt.listLen version_label)
    let _as83 ← SudoRt.sudoAssertEq _t79 (SudoRt.concatL _t81 version_label) 230
    pure ()

def test_hmac_aliases_agree_and_returns_29_bytes : Except SudoRt.Trap Unit :=
  do
    let _t84 ← v_HMAC (#[(99 : Int), (114 : Int), (121 : Int), (112 : Int), (116 : Int), (111 : Int), (121 : Int)] : Array (Int)) (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let tag := _t84
    let _as86 ← SudoRt.sudoAssertEq (SudoRt.listLen tag) (29 : Int) 234
    let _t87 ← v_HMAC_MegaDreifach (#[(99 : Int), (114 : Int), (121 : Int), (112 : Int), (116 : Int), (111 : Int), (121 : Int)] : Array (Int)) (#[(97 : Int), (98 : Int), (99 : Int)] : Array (Int))
    let _as88 ← SudoRt.sudoAssertEq _t87 tag 235
    let published := (#[(1 : Int), (105 : Int), (39 : Int), (111 : Int), (136 : Int), (146 : Int), (139 : Int), (218 : Int), (84 : Int), (110 : Int), (16 : Int), (142 : Int), (181 : Int), (159 : Int), (241 : Int), (182 : Int), (136 : Int), (174 : Int), (139 : Int), (125 : Int), (230 : Int), (82 : Int), (40 : Int), (242 : Int), (28 : Int), (47 : Int), (4 : Int), (157 : Int), (114 : Int)] : Array (Int))
    let _as89 ← SudoRt.sudoAssertEq tag published 237
    pure ()

def test_hmac_depends_on_the_key_and_the_message : Except SudoRt.Trap Unit :=
  do
    let k1 := (#[(1 : Int), (2 : Int), (3 : Int)] : Array (Int))
    let k2 := (#[(1 : Int), (2 : Int), (4 : Int)] : Array (Int))
    let m1 := (#[(97 : Int)] : Array (Int))
    let m2 := (#[(98 : Int)] : Array (Int))
    let _t90 ← v_HMAC k1 m1
    let a := _t90
    let _t91 ← v_HMAC k1 m1
    let _as92 ← SudoRt.sudoAssertEq _t91 a 245
    let _t93 ← v_HMAC k1 m2
    let _as95 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t93 a)) 246
    let _t96 ← v_HMAC k2 m1
    let _as98 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t96 a)) 247
    pure ()

def test_a_long_hmac_key_is_hashed_then_truncated_to_b : Except SudoRt.Trap Unit :=
  do
    let long := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (39 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init116 := (_fromV, long)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init116 fuel (fun σ =>
    let i := σ.1
    let long := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, long))
      else
        match ← ((do
  let _t101 ← SudoRt.mulI i (17 : Int)
  let _t102 ← SudoRt.modI _t101 (256 : Int)
  let _mb103 := SudoRt.appendL long _t102
  let ⟨_nr104, _⟩ := _mb103
  let long := _nr104
  let _hm99 := ()
  let _u105 := _hm99
  pure (SudoRt.Flow.cont (ρ := Unit) long)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let long := σ.2
    do
      let _t106 ← Megadreifach.v_Hash long
      let hashed := _t106
      let _t107 ← take_prefix hashed (28 : Int)
      let _t108 ← hmac_normalize_key _t107
      let expected := _t108
      let _t109 ← hmac_normalize_key long
      let _as110 ← SudoRt.sudoAssertEq _t109 expected 255
      let _t111 ← v_HMAC long (#[(1 : Int)] : Array (Int))
      let _t112 ← take_prefix long (28 : Int)
      let _t113 ← v_HMAC _t112 (#[(1 : Int)] : Array (Int))
      let _as115 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t111 _t113)) 256
      pure ()) (fun r => pure r))
    pure _out

def test_derive_keys_splits_the_master_secret : Except SudoRt.Trap Unit :=
  do
    let master := (#[(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)] : Array (Int))
    let _t117 ← derive_keys master
    let ⟨enc_a, mac_a⟩ := _t117
    let _t118 ← derive_keys master
    let ⟨enc_b, mac_b⟩ := _t118
    let _as119 ← SudoRt.sudoAssertEq enc_a enc_b 262
    let _as120 ← SudoRt.sudoAssertEq mac_a mac_b 263
    let _as122 ← SudoRt.sudoAssertEq (SudoRt.listLen enc_a) (28 : Int) 264
    let _as124 ← SudoRt.sudoAssertEq (SudoRt.listLen mac_a) (29 : Int) 265
    let _t125 ← take_prefix mac_a (28 : Int)
    let _as127 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq enc_a _t125)) 266
    let _t128 ← derive_keys (#[(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (9 : Int)] : Array (Int))
    let ⟨other, other_mac⟩ := _t128
    let _as130 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq other enc_a)) 268
    let _as132 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq other_mac mac_a)) 269
    pure ()

def test_empty_master_key_is_rejected : Except SudoRt.Trap Unit :=
  do
    let _ex134 := (do
  let _t133 ← derive_keys (#[] : Array (Int))
  let ⟨enc, mac⟩ := _t133
  pure ()
  pure ())
    match _ex134 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 272: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 272: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_tag_compare_is_full_length : Except SudoRt.Trap Unit :=
  do
    let _t135 ← SudoRt.filledL (29 : Int) (1 : Int)
    let a := _t135
    let _t136 ← SudoRt.filledL (29 : Int) (1 : Int)
    let b := _t136
    let _t137 ← SudoRt.filledL (29 : Int) (1 : Int)
    let c := _t137
    let _ix138 := (28 : Int)
    let _t139 ← SudoRt.putL c _ix138 (2 : Int)
    let c := _t139
    let _t140 ← tags_equal a b
    let _as141 ← SudoRt.sudoAssert _t140 280
    let _t142 ← tags_equal a c
    let _as143 ← SudoRt.sudoAssert (!( _t142 )) 281
    let _t144 ← SudoRt.filledL (28 : Int) (1 : Int)
    let _t145 ← tags_equal a _t144
    let _as146 ← SudoRt.sudoAssert (!( _t145 )) 282
    pure ()

def main : IO UInt32 :=
  SudoRt.runTests [("test_xor_is_bitwise_and_involutive", fun _ => test_xor_is_bitwise_and_involutive), ("test_iso7816_pad_matches_doubledeal_ecb", fun _ => test_iso7816_pad_matches_doubledeal_ecb), ("test_hmac_key_shorter_than_b_is_zero_padded", fun _ => test_hmac_key_shorter_than_b_is_zero_padded), ("test_cbc_chain_drops_the_most_significant_rank_byte", fun _ => test_cbc_chain_drops_the_most_significant_rank_byte), ("test_mac_input_is_length_delimited", fun _ => test_mac_input_is_length_delimited), ("test_hmac_aliases_agree_and_returns_29_bytes", fun _ => test_hmac_aliases_agree_and_returns_29_bytes), ("test_hmac_depends_on_the_key_and_the_message", fun _ => test_hmac_depends_on_the_key_and_the_message), ("test_a_long_hmac_key_is_hashed_then_truncated_to_b", fun _ => test_a_long_hmac_key_is_hashed_then_truncated_to_b), ("test_derive_keys_splits_the_master_secret", fun _ => test_derive_keys_splits_the_master_secret), ("test_empty_master_key_is_rejected", fun _ => test_empty_master_key_is_rejected), ("test_tag_compare_is_full_length", fun _ => test_tag_compare_is_full_length)]
