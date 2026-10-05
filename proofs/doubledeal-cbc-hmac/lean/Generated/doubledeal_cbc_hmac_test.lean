-- DO NOT EDIT. Generated from doubledeal_cbc_hmac.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
-- Generated tests for doubledeal_cbc_hmac.sudo
import SudoRt
import Doubledeal_cbc_hmac
import Megadreifach
import Doubledeal
set_option linter.unusedVariables false
open Doubledeal_cbc_hmac

def test_place_through_a_sorted_deck_keeps_a_deck_through_a_turned_over_deck_reverses_it : Except SudoRt.Trap Unit :=
  do
    let _t1 ← «some_deck» (7 : Int)
    let k := _t1
    let _t2 ← sorted_deck
    let _t3 ← compose k _t2
    let _as4 ← SudoRt.sudoAssertEq _t3 k 459
    let _t5 ← sorted_deck
    let _t6 ← turned_over _t5
    let _t7 ← compose k _t6
    let _t8 ← turned_over k
    let _as9 ← SudoRt.sudoAssertEq _t7 _t8 460
    let _t10 ← «some_deck» (11 : Int)
    let c := _t10
    let _t11 ← compose k c
    let _t12 ← inverse_compose _t11 c
    let _as13 ← SudoRt.sudoAssertEq _t12 k 462
    let _t14 ← inverse_compose k c
    let _t15 ← compose _t14 c
    let _as16 ← SudoRt.sudoAssertEq _t15 k 463
    pure ()

def test_turning_the_key_over_moves_every_card_to_a_new_seat : Except SudoRt.Trap Unit :=
  do
    let _t17 ← «some_deck» (7 : Int)
    let k := _t17
    let _t18 ← turned_over k
    let t := _t18
    let _fromV := (0 : Int)
    let _toV := (51 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init26 := _fromV
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init26 fuel (fun σ =>
    let i := σ
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) i)
      else
        match ← ((do
  let _t20 ← SudoRt.atL t i
  let _t21 ← SudoRt.atL k i
  let _as23 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t20 _t21)) 469
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
      let _t24 ← turned_over t
      let _as25 ← SudoRt.sudoAssertEq _t24 k 470
      pure ()) (fun r => pure r))
    pure _out

def test_wire_ranks_sorted_is_0_turned_over_sorted_is_52_1_52_is_not_a_deck : Except SudoRt.Trap Unit :=
  do
    let _t27 ← sorted_deck
    let _t28 ← rank29 _t27
    let z := _t28
    let _t29 ← bn_is_zero z
    let _as30 ← SudoRt.sudoAssert _t29 474
    let _t31 ← sorted_deck
    let _t32 ← turned_over _t31
    let _t33 ← rank29 _t32
    let top := _t33
    let _t34 ← wire_to_deck top
    let ⟨ok, d⟩ := _t34
    let _as35 ← SudoRt.sudoAssert ok 477
    let _t36 ← sorted_deck
    let _t37 ← turned_over _t36
    let _as38 ← SudoRt.sudoAssertEq d _t37 478
    let _t39 ← SudoRt.filledL wire_block (0 : Int)
    let one := _t39
    let _t40 ← SudoRt.subI wire_block (1 : Int)
    let _ix41 := _t40
    let _t42 ← SudoRt.putL one _ix41 (1 : Int)
    let one := _t42
    let _t43 ← bn_add top one
    let _t44 ← wire_to_deck _t43
    let ⟨ok2, d2⟩ := _t44
    let _as45 ← SudoRt.sudoAssert (!( ok2 )) 482
    let _t46 ← «some_deck» (7 : Int)
    let k := _t46
    let _t47 ← rank29 k
    let _t48 ← wire_to_deck _t47
    let ⟨ok3, d3⟩ := _t48
    let _as49 ← SudoRt.sudoAssert ok3 485
    let _as50 ← SudoRt.sudoAssertEq d3 k 486
    pure ()

def test_28_byte_blocks_round_trip_a_deck_of_rank_at_least_2_224_is_not_a_message_block : Except SudoRt.Trap Unit :=
  do
    let _t51 ← SudoRt.filledL msg_block (255 : Int)
    let b := _t51
    let _t52 ← block_to_deck b
    let _t53 ← deck_to_block _t52
    let ⟨ok, back⟩ := _t53
    let _as54 ← SudoRt.sudoAssert ok 491
    let _as55 ← SudoRt.sudoAssertEq back b 492
    let _t56 ← sorted_deck
    let _t57 ← turned_over _t56
    let _t58 ← deck_to_block _t57
    let ⟨okr, r⟩ := _t58
    let _as59 ← SudoRt.sudoAssert (!( okr )) 494
    pure ()

def test_group_order_is_29_bytes_with_top_byte_3 : Except SudoRt.Trap Unit :=
  do
    let _t60 ← group_order
    let g := _t60
    let _as62 ← SudoRt.sudoAssertEq (SudoRt.listLen g) wire_block 498
    let _t63 ← SudoRt.atL g (0 : Int)
    let _as64 ← SudoRt.sudoAssertEq _t63 (3 : Int) 499
    pure ()

def test_pad_and_checked_unpad : Except SudoRt.Trap Unit :=
  do
    let _t66 ← pad_iso7816 (#[] : Array (Int))
    let e := _t66
    let _as68 ← SudoRt.sudoAssertEq (SudoRt.listLen e) (28 : Int) 503
    let _t69 ← unpad_checked e
    let ⟨ok, m⟩ := _t69
    let _as70 ← SudoRt.sudoAssert ok 505
    let _as72 ← SudoRt.sudoAssertEq (SudoRt.listLen m) (0 : Int) 506
    let x := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (27 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init91 := (_fromV, x)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init91 fuel (fun σ =>
    let i := σ.1
    let x := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, x))
      else
        match ← ((do
  let _t74 ← SudoRt.addI i (1 : Int)
  let _mb75 := SudoRt.appendL x _t74
  let ⟨_nr76, _⟩ := _mb75
  let x := _nr76
  let _hm65 := ()
  let _u77 := _hm65
  pure (SudoRt.Flow.cont (ρ := Unit) x)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let x := σ.2
    do
      let _t78 ← pad_iso7816 x
      let _t79 ← unpad_checked _t78
      let ⟨ok2, m2⟩ := _t79
      let _as80 ← SudoRt.sudoAssert ok2 511
      let _as81 ← SudoRt.sudoAssertEq m2 x 512
      let _t82 ← pad_iso7816 (#[(1 : Int), (2 : Int), (3 : Int)] : Array (Int))
      let bad := _t82
      let _ix83 := (3 : Int)
      let _t84 ← SudoRt.putL bad _ix83 (0 : Int)
      let bad := _t84
      let _t85 ← unpad_checked bad
      let ⟨ok3, m3⟩ := _t85
      let _as86 ← SudoRt.sudoAssert (!( ok3 )) 516
      let _t87 ← SudoRt.filledL (55 : Int) (0 : Int)
      let late := (SudoRt.concatL (#[(128 : Int)] : Array (Int)) _t87)
      let _t89 ← unpad_checked late
      let ⟨ok4, m4⟩ := _t89
      let _as90 ← SudoRt.sudoAssert (!( ok4 )) 519
      pure ()) (fun r => pure r))
    pure _out

def test_the_mac_input_version_deck_first_length_deck_last_zero_filled_aad_kept_apart : Except SudoRt.Trap Unit :=
  do
    let _t92 ← «some_deck» (7 : Int)
    let iv := _t92
    let _t93 ← «some_deck» (11 : Int)
    let c := (#[_t93] : Array (Array (Int)))
    let _t94 ← mac_decks (#[] : Array (Int)) iv c
    let s0 := _t94
    let _as96 ← SudoRt.sudoAssertEq (SudoRt.listLen s0) (4 : Int) 525
    let _t97 ← SudoRt.atL s0 (0 : Int)
    let _t98 ← version_deck
    let _as99 ← SudoRt.sudoAssertEq _t97 _t98 526
    let _t100 ← SudoRt.atL s0 (0 : Int)
    let _t101 ← sorted_deck
    let _as103 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t100 _t101)) 527
    let _t104 ← SudoRt.atL s0 (1 : Int)
    let _as105 ← SudoRt.sudoAssertEq _t104 iv 528
    let _t106 ← SudoRt.atL s0 (3 : Int)
    let _t107 ← sorted_deck
    let _as108 ← SudoRt.sudoAssertEq _t106 _t107 529
    let _t109 ← mac_decks (#[(0 : Int)] : Array (Int)) iv c
    let s1 := _t109
    let _t110 ← SudoRt.filledL (27 : Int) (0 : Int)
    let _t111 ← mac_decks _t110 iv c
    let s27 := _t111
    let _t112 ← SudoRt.filledL (28 : Int) (0 : Int)
    let _t113 ← mac_decks _t112 iv c
    let s28 := _t113
    let _t114 ← SudoRt.filledL (29 : Int) (0 : Int)
    let _t115 ← mac_decks _t114 iv c
    let s29 := _t115
    let _as117 ← SudoRt.sudoAssertEq (SudoRt.listLen s1) (5 : Int) 534
    let _t118 ← SudoRt.atL s1 (1 : Int)
    let _t119 ← SudoRt.atL s27 (1 : Int)
    let _as120 ← SudoRt.sudoAssertEq _t118 _t119 535
    let _t121 ← SudoRt.atL s1 (4 : Int)
    let _t122 ← SudoRt.atL s27 (4 : Int)
    let _as124 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t121 _t122)) 536
    let _t125 ← SudoRt.atL s27 (4 : Int)
    let _t126 ← SudoRt.atL s28 (4 : Int)
    let _as128 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t125 _t126)) 537
    let _as130 ← SudoRt.sudoAssertEq (SudoRt.listLen s29) (6 : Int) 538
    pure ()

def test_the_sandwich_tag_is_one_megaminx_through_key_message_decks_key_turned_over : Except SudoRt.Trap Unit :=
  do
    let _t134 ← «some_deck» (7 : Int)
    let k := _t134
    let _t135 ← «some_deck» (11 : Int)
    let _t136 ← «some_deck» (15 : Int)
    let _t137 ← mac_decks (#[(1 : Int), (2 : Int)] : Array (Int)) _t135 (#[_t136] : Array (Array (Int)))
    let s := _t137
    let seq := (#[] : Array (Array (Int)))
    let _t138 ← md_ids k
    let _mb139 := SudoRt.appendL seq _t138
    let ⟨_nr140, _⟩ := _mb139
    let seq := _nr140
    let _hm131 := ()
    let _u141 := _hm131
    let _t149 ← SudoRt.subI (SudoRt.listLen s) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t149
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init166 := (_fromV, seq)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init166 fuel (fun σ =>
    let i := σ.1
    let seq := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, seq))
      else
        match ← ((do
  let _t143 ← SudoRt.atL s i
  let _t144 ← md_ids _t143
  let _mb145 := SudoRt.appendL seq _t144
  let ⟨_nr146, _⟩ := _mb145
  let seq := _nr146
  let _hm132 := ()
  let _u147 := _hm132
  pure (SudoRt.Flow.cont (ρ := Unit) seq)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let seq := σ.2
    do
      let _t150 ← turned_over k
      let _t151 ← md_ids _t150
      let _mb152 := SudoRt.appendL seq _t151
      let ⟨_nr153, _⟩ := _mb152
      let seq := _nr153
      let _hm133 := ()
      let _u154 := _hm133
      let _t155 ← mac_tag k s
      let _t156 ← Megadreifach.v_HashDecksBody seq
      let _as157 ← SudoRt.sudoAssertEq _t155 _t156 548
      let _t158 ← mac_tag k s
      let _t159 ← turned_over k
      let _t160 ← mac_tag _t159 s
      let _as162 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq _t158 _t160)) 549
      let _t163 ← mac_tag k s
      let _as165 ← SudoRt.sudoAssertEq (SudoRt.listLen _t163) tag_len 550
      pure ()) (fun r => pure r))
    pure _out

def test_card_ids_the_same_physical_card_in_megadreifach_numbering : Except SudoRt.Trap Unit :=
  do
    let _t167 ← sorted_deck
    let _t168 ← md_ids _t167
    let ids := _t168
    let _t169 ← SudoRt.atL ids (0 : Int)
    let _as170 ← SudoRt.sudoAssertEq _t169 (0 : Int) 554
    let _t171 ← SudoRt.atL ids (1 : Int)
    let _as172 ← SudoRt.sudoAssertEq _t171 (4 : Int) 555
    let _t173 ← SudoRt.atL ids (13 : Int)
    let _as174 ← SudoRt.sudoAssertEq _t173 (1 : Int) 556
    let _t175 ← SudoRt.atL ids (51 : Int)
    let _as176 ← SudoRt.sudoAssertEq _t175 (51 : Int) 557
    pure ()

def test_optional_key_derivation_gives_two_distinct_decks : Except SudoRt.Trap Unit :=
  do
    let _t177 ← derive_key_decks (#[(1 : Int), (2 : Int), (3 : Int)] : Array (Int))
    let ⟨a, b⟩ := _t177
    let _t178 ← is_deck a
    let _as179 ← SudoRt.sudoAssert _t178 561
    let _t180 ← is_deck b
    let _as181 ← SudoRt.sudoAssert _t180 562
    let _as183 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq a b)) 563
    let _t184 ← derive_key_decks (#[(1 : Int), (2 : Int), (4 : Int)] : Array (Int))
    let ⟨c, d⟩ := _t184
    let _as186 ← SudoRt.sudoAssert (!(SudoRt.SEq.beq c a)) 565
    pure ()

def test_optional_key_derivation_rejects_an_empty_master : Except SudoRt.Trap Unit :=
  do
    let _ex188 := (do
  let _t187 ← derive_key_decks (#[] : Array (Int))
  let ⟨a, b⟩ := _t187
  pure ()
  pure ())
    match _ex188 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 568: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 568: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_published_mac_version_only_kats_doubledeal_cbc_hmac_kats_json : Except SudoRt.Trap Unit :=
  do
    let k := (#[(11 : Int), (30 : Int), (26 : Int), (38 : Int), (13 : Int), (44 : Int), (15 : Int), (6 : Int), (24 : Int), (35 : Int), (37 : Int), (27 : Int), (33 : Int), (32 : Int), (21 : Int), (10 : Int), (43 : Int), (4 : Int), (49 : Int), (18 : Int), (42 : Int), (19 : Int), (51 : Int), (3 : Int), (23 : Int), (41 : Int), (5 : Int), (45 : Int), (0 : Int), (50 : Int), (47 : Int), (36 : Int), (39 : Int), (31 : Int), (8 : Int), (46 : Int), (1 : Int), (22 : Int), (20 : Int), (48 : Int), (34 : Int), (17 : Int), (14 : Int), (29 : Int), (12 : Int), (9 : Int), (28 : Int), (7 : Int), (25 : Int), (2 : Int), (16 : Int), (40 : Int)] : Array (Int))
    let _t189 ← version_deck
    let _t190 ← mac_tag k (#[_t189] : Array (Array (Int)))
    let _as191 ← SudoRt.sudoAssertEq _t190 (#[(1 : Int), (244 : Int), (194 : Int), (178 : Int), (105 : Int), (103 : Int), (90 : Int), (186 : Int), (53 : Int), (202 : Int), (56 : Int), (17 : Int), (144 : Int), (72 : Int), (162 : Int), (174 : Int), (96 : Int), (106 : Int), (207 : Int), (14 : Int), (5 : Int), (177 : Int), (184 : Int), (5 : Int), (255 : Int), (18 : Int), (168 : Int), (54 : Int), (66 : Int)] : Array (Int)) 573
    pure ()

def test_aead_seal_then_aead_open_round_trips_and_every_tamper_rejects : Except SudoRt.Trap Unit :=
  do
    let _t193 ← «some_deck» (7 : Int)
    let ke := _t193
    let _t194 ← «some_deck» (11 : Int)
    let km := _t194
    let _t195 ← «some_deck» (15 : Int)
    let iv := _t195
    let pt := (#[(104 : Int), (105 : Int)] : Array (Int))
    let _t196 ← aead_seal pt ke km (#[(9 : Int)] : Array (Int)) iv
    let blob := _t196
    let _t198 ← SudoRt.mulI (3 : Int) wire_block
    let _as199 ← SudoRt.sudoAssertEq (SudoRt.listLen blob) _t198 581
    let _t200 ← aead_open blob ke km (#[(9 : Int)] : Array (Int))
    let ⟨ok, back⟩ := _t200
    let _as201 ← SudoRt.sudoAssert ok 583
    let _as202 ← SudoRt.sudoAssertEq back pt 584
    let t := blob
    let _t204 ← SudoRt.subI (SudoRt.listLen blob) (1 : Int)
    let _ix205 := _t204
    let _t207 ← SudoRt.subI (SudoRt.listLen blob) (1 : Int)
    let _t208 ← SudoRt.atL t _t207
    let _t209 ← SudoRt.addI _t208 (1 : Int)
    let _t210 ← SudoRt.modI _t209 (256 : Int)
    let _t211 ← SudoRt.putL t _ix205 _t210
    let t := _t211
    let _t212 ← aead_open t ke km (#[(9 : Int)] : Array (Int))
    let ⟨okt, bt⟩ := _t212
    let _as213 ← SudoRt.sudoAssert (!( okt )) 588
    let _as215 ← SudoRt.sudoAssertEq (SudoRt.listLen bt) (0 : Int) 589
    let c := blob
    let _ix216 := (40 : Int)
    let _t217 ← SudoRt.atL c (40 : Int)
    let _t218 ← SudoRt.addI _t217 (1 : Int)
    let _t219 ← SudoRt.modI _t218 (256 : Int)
    let _t220 ← SudoRt.putL c _ix216 _t219
    let c := _t220
    let _t221 ← aead_open c ke km (#[(9 : Int)] : Array (Int))
    let ⟨okc, bc⟩ := _t221
    let _as222 ← SudoRt.sudoAssert (!( okc )) 593
    let _t223 ← aead_open blob ke km (#[(8 : Int)] : Array (Int))
    let ⟨oka, ba⟩ := _t223
    let _as224 ← SudoRt.sudoAssert (!( oka )) 595
    let _t225 ← aead_open blob km ke (#[(9 : Int)] : Array (Int))
    let ⟨okk, bk⟩ := _t225
    let _as226 ← SudoRt.sudoAssert (!( okk )) 597
    let short := (#[] : Array (Int))
    let _t233 ← SudoRt.subI (SudoRt.listLen blob) wire_block
    let _t234 ← SudoRt.subI _t233 (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t234
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init237 := (_fromV, short)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init237 fuel (fun σ =>
    let i := σ.1
    let short := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, short))
      else
        match ← ((do
  let _t228 ← SudoRt.atL blob i
  let _mb229 := SudoRt.appendL short _t228
  let ⟨_nr230, _⟩ := _mb229
  let short := _nr230
  let _hm192 := ()
  let _u231 := _hm192
  pure (SudoRt.Flow.cont (ρ := Unit) short)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let short := σ.2
    do
      let _t235 ← aead_open short ke km (#[(9 : Int)] : Array (Int))
      let ⟨oks, bs⟩ := _t235
      let _as236 ← SudoRt.sudoAssert (!( oks )) 602
      pure ()) (fun r => pure r))
    pure _out

def test_a_blob_number_that_is_not_a_deck_is_rejected_by_the_public_parse : Except SudoRt.Trap Unit :=
  do
    let _t238 ← «some_deck» (7 : Int)
    let ke := _t238
    let _t239 ← «some_deck» (11 : Int)
    let km := _t239
    let _t240 ← «some_deck» (15 : Int)
    let _t241 ← aead_seal (#[] : Array (Int)) ke km (#[] : Array (Int)) _t240
    let blob := _t241
    let _t245 ← SudoRt.subI wire_block (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t245
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init248 := (_fromV, blob)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init248 fuel (fun σ =>
    let j := σ.1
    let blob := σ.2
    do
      if j > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (j, blob))
      else
        match ← ((do
  let _ix243 := j
  let _t244 ← SudoRt.putL blob _ix243 (255 : Int)
  let blob := _t244
  pure (SudoRt.Flow.cont (ρ := Unit) blob)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
        | .cont _fs => do
            if j == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let blob := σ.2
    do
      let _t246 ← aead_open blob ke km (#[] : Array (Int))
      let ⟨ok, m⟩ := _t246
      let _as247 ← SudoRt.sudoAssert (!( ok )) 611
      pure ()) (fun r => pure r))
    pure _out

def test_the_two_key_decks_must_differ : Except SudoRt.Trap Unit :=
  do
    let _t249 ← «some_deck» (7 : Int)
    let k := _t249
    let _ex252 := (do
  let _t250 ← «some_deck» (11 : Int)
  let _t251 ← aead_seal (#[(1 : Int)] : Array (Int)) k k (#[] : Array (Int)) _t250
  let b := _t251
  pure ()
  pure ())
    match _ex252 with
    | .error t => if t.kind == "AssertFailed" then pure () else SudoRt.fail "AssertFailed" s!"line 615: expected trap AssertFailed, got {t.kind}"
    | .ok _ => SudoRt.fail "AssertFailed" "line 615: expected trap AssertFailed, but nothing trapped"
    pure ()

def test_longer_messages_chain_through_the_previous_ciphertext_deck : Except SudoRt.Trap Unit :=
  do
    let _t254 ← «some_deck» (7 : Int)
    let ke := _t254
    let _t255 ← «some_deck» (11 : Int)
    let km := _t255
    let pt := (#[] : Array (Int))
    let _fromV := (0 : Int)
    let _toV := (59 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init270 := (_fromV, pt)
    let _out ← (SudoRt.runLoopOn (ρ := Unit) _init270 fuel (fun σ =>
    let i := σ.1
    let pt := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Unit) (i, pt))
      else
        match ← ((do
  let _t257 ← SudoRt.mulI i (37 : Int)
  let _t258 ← SudoRt.modI _t257 (256 : Int)
  let _mb259 := SudoRt.appendL pt _t258
  let ⟨_nr260, _⟩ := _mb259
  let pt := _nr260
  let _hm253 := ()
  let _u261 := _hm253
  pure (SudoRt.Flow.cont (ρ := Unit) pt)) : Except SudoRt.Trap (SudoRt.Flow _ (Unit))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Unit) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Unit) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Unit) (i', _fs))) (fun σ =>
    let pt := σ.2
    do
      let _t262 ← «some_deck» (15 : Int)
      let _t263 ← aead_seal pt ke km (#[] : Array (Int)) _t262
      let blob := _t263
      let _t265 ← SudoRt.mulI (5 : Int) wire_block
      let _as266 ← SudoRt.sudoAssertEq (SudoRt.listLen blob) _t265 625
      let _t267 ← aead_open blob ke km (#[] : Array (Int))
      let ⟨ok, back⟩ := _t267
      let _as268 ← SudoRt.sudoAssert ok 627
      let _as269 ← SudoRt.sudoAssertEq back pt 628
      pure ()) (fun r => pure r))
    pure _out

def main : IO UInt32 :=
  SudoRt.runTests [("test_place_through_a_sorted_deck_keeps_a_deck_through_a_turned_over_deck_reverses_it", fun _ => test_place_through_a_sorted_deck_keeps_a_deck_through_a_turned_over_deck_reverses_it), ("test_turning_the_key_over_moves_every_card_to_a_new_seat", fun _ => test_turning_the_key_over_moves_every_card_to_a_new_seat), ("test_wire_ranks_sorted_is_0_turned_over_sorted_is_52_1_52_is_not_a_deck", fun _ => test_wire_ranks_sorted_is_0_turned_over_sorted_is_52_1_52_is_not_a_deck), ("test_28_byte_blocks_round_trip_a_deck_of_rank_at_least_2_224_is_not_a_message_block", fun _ => test_28_byte_blocks_round_trip_a_deck_of_rank_at_least_2_224_is_not_a_message_block), ("test_group_order_is_29_bytes_with_top_byte_3", fun _ => test_group_order_is_29_bytes_with_top_byte_3), ("test_pad_and_checked_unpad", fun _ => test_pad_and_checked_unpad), ("test_the_mac_input_version_deck_first_length_deck_last_zero_filled_aad_kept_apart", fun _ => test_the_mac_input_version_deck_first_length_deck_last_zero_filled_aad_kept_apart), ("test_the_sandwich_tag_is_one_megaminx_through_key_message_decks_key_turned_over", fun _ => test_the_sandwich_tag_is_one_megaminx_through_key_message_decks_key_turned_over), ("test_card_ids_the_same_physical_card_in_megadreifach_numbering", fun _ => test_card_ids_the_same_physical_card_in_megadreifach_numbering), ("test_optional_key_derivation_gives_two_distinct_decks", fun _ => test_optional_key_derivation_gives_two_distinct_decks), ("test_optional_key_derivation_rejects_an_empty_master", fun _ => test_optional_key_derivation_rejects_an_empty_master), ("test_published_mac_version_only_kats_doubledeal_cbc_hmac_kats_json", fun _ => test_published_mac_version_only_kats_doubledeal_cbc_hmac_kats_json), ("test_aead_seal_then_aead_open_round_trips_and_every_tamper_rejects", fun _ => test_aead_seal_then_aead_open_round_trips_and_every_tamper_rejects), ("test_a_blob_number_that_is_not_a_deck_is_rejected_by_the_public_parse", fun _ => test_a_blob_number_that_is_not_a_deck_is_rejected_by_the_public_parse), ("test_the_two_key_decks_must_differ", fun _ => test_the_two_key_decks_must_differ), ("test_longer_messages_chain_through_the_previous_ciphertext_deck", fun _ => test_longer_messages_chain_through_the_previous_ciphertext_deck)]
