import DoubleDealCbcHmac.Link2.Bytes
import MegaDreifach.Link2.VHash
import MegaDreifach.Link2.PosBytesGen

/-!
  LINK 2 for `v_HMAC`, `derive_keys` and `mac_input` (SPEC §4–§6.1): the emitted
  functions equal the hand-written model in `DoubleDealCbcHmac.Spec`, instantiated at
  `H := vhashAlg`, the model MegaDreifach's `v_Hash_refines` proves the emitted
  `Megadreifach.v_Hash` equal to. Refinement holds on byte lists whose lengths fit the
  i64 bounds the emitted runtime checks (`FitsLen` / `FitsBitlen`). Not emitter soundness.
-/

namespace DoubleDealCbcHmac.Link2
open MegaDreifach.Link2

theorem concatL_embed (a b : List Nat) : SudoRt.concatL (embed a) (embed b) = embed (a ++ b) := by
  apply Array.ext'
  simp [SudoRt.concatL, embed, Array.toList_append]

theorem enc_label_eq : Doubledeal_cbc_hmac.enc_label = embed encLabel := by decide
theorem mac_label_eq : Doubledeal_cbc_hmac.mac_label = embed macLabel := by decide
theorem version_label_eq : Doubledeal_cbc_hmac.version_label = embed versionLabel := by decide
theorem encLabel_length : encLabel.length = 26 := by decide
theorem macLabel_length : macLabel.length = 26 := by decide
theorem versionLabel_length : versionLabel.length = 22 := by decide

theorem vhashAlg_bytes (msg : List Nat) : Bytes (vhashAlg msg) := by
  intro b hb
  unfold vhashAlg MegaDreifach.positionToBytes at hb
  have := toBE_mem_lt _ _ (rankPosition_lt_digest _ (injPos_chainPre _ _)) b hb
  omega

theorem hmacBlock_int : Doubledeal_cbc_hmac.hmac_block = Int.ofNat hmacBlock := rfl

theorem fits28 : FitsLen hmacBlock := by unfold FitsLen i64MaxNat hmacBlock; decide

theorem v_Hash_bytes (m : List Nat) (hb : Bytes m) (hfit : FitsBitlen m.length) :
    Megadreifach.v_Hash (embed m) = .ok (embed (vhashAlg m)) :=
  v_Hash_refines m ⟨hb, hfit⟩

theorem decide_ofNat_gt (a b : Nat) :
    decide (Int.ofNat a > Int.ofNat b) = decide (b < a) :=
  decide_eq_decide.mpr Int.ofNat_lt

theorem normalizeKey_long (key : List Nat) (h : hmacBlock < key.length) :
    normalizeKey vhashAlg key = (vhashAlg key).take hmacBlock := by
  have hl := vhashAlg_length key
  unfold normalizeKey
  simp only [if_pos h, hl, show hmacBlock < 29 from by decide, if_true, List.length_take,
    show min hmacBlock 29 = hmacBlock from rfl, Nat.sub_self, List.replicate_zero,
    List.append_nil]

theorem normalizeKey_short (key : List Nat) (h : ¬ hmacBlock < key.length) :
    normalizeKey vhashAlg key = key ++ List.replicate (hmacBlock - key.length) 0 := by
  simp [normalizeKey, h]

theorem normalizeKey_length (key : List Nat) : (normalizeKey vhashAlg key).length = hmacBlock := by
  by_cases h : hmacBlock < key.length
  · rw [normalizeKey_long key h, List.length_take, vhashAlg_length]; rfl
  · rw [normalizeKey_short key h, List.length_append, List.length_replicate]; omega

theorem normalizeKey_bytes (key : List Nat) (hb : Bytes key) : Bytes (normalizeKey vhashAlg key) := by
  by_cases h : hmacBlock < key.length
  · rw [normalizeKey_long key h]
    exact fun b hb' => vhashAlg_bytes key b (List.mem_of_mem_take hb')
  · rw [normalizeKey_short key h]
    intro b hb'
    rcases List.mem_append.mp hb' with h1 | h1
    · exact hb b h1
    · rw [List.eq_of_mem_replicate h1]; decide

theorem hmac_normalize_key_refines (key : List Nat) (hb : Bytes key)
    (hfit : FitsBitlen key.length) :
    Doubledeal_cbc_hmac.hmac_normalize_key (embed key) = .ok (embed (normalizeKey vhashAlg key)) := by
  have hfl : FitsLen key.length := hfit.fitsLen
  unfold Doubledeal_cbc_hmac.hmac_normalize_key
  simp only [require_bytes_refines key hb hfl, ok_bind, listLen_embed, hmacBlock_int,
    decide_ofNat_gt]
  by_cases h : hmacBlock < key.length
  · simp only [h, decide_True, if_true, v_Hash_bytes key hb hfit, ok_bind, listLen_embed,
      decide_ofNat_gt, vhashAlg_length, show hmacBlock < 29 from by decide, pure_eq_ok,
      bind_ok_right]
    rw [take_prefix_refines _ _ (by rw [vhashAlg_length]; decide)
      (by rw [vhashAlg_length]; unfold FitsLen i64MaxNat; decide), ok_bind,
      pad_zeros_refines _ _ (by rw [List.length_take]; omega) fits28, normalizeKey_long key h]
    have : ((vhashAlg key).take hmacBlock).length = hmacBlock := by
      rw [List.length_take, vhashAlg_length]; rfl
    rw [this, Nat.sub_self, List.replicate_zero, List.append_nil]
  · simp only [h, decide_False, Bool.false_eq_true, if_false, pure_eq_ok, bind_ok_right]
    rw [pad_zeros_refines _ _ (by omega) fits28, normalizeKey_short key h]

theorem xorBytes_length (a b : List Nat) : (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

theorem xorBytes_bytes (a b : List Nat) (ha : Bytes a) (hb : Bytes b) : Bytes (xorBytes a b) := by
  intro x hx
  unfold xorBytes at hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.getElem_zipWith]
  have h1 : i < a.length := by simp at hi; omega
  have h2 : i < b.length := by simp at hi; omega
  exact xor_lt_256 (ha.get i h1) (hb.get i h2)

theorem Bytes.append {a b : List Nat} (ha : Bytes a) (hb : Bytes b) : Bytes (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem Bytes.replicate {n p : Nat} (hp : p ≤ 255) : Bytes (List.replicate n p) := by
  intro x hx; rw [List.eq_of_mem_replicate hx]; exact hp

/-- The key block `K' ⊕ pad`, as the generated `xor_pad` computes it. -/
theorem xor_pad_key (key : List Nat) (hb : Bytes key) (p : Nat) (hp : p ≤ 255) :
    Doubledeal_cbc_hmac.xor_pad (embed (normalizeKey vhashAlg key)) (Int.ofNat p) =
      .ok (embed (xorBytes (normalizeKey vhashAlg key) (List.replicate hmacBlock p))) :=
  xor_pad_refines _ p (normalizeKey_length key) (normalizeKey_bytes key hb) hp

theorem xorPad_length (key : List Nat) (p : Nat) :
    (xorBytes (normalizeKey vhashAlg key) (List.replicate hmacBlock p)).length = hmacBlock := by
  rw [xorBytes_length, normalizeKey_length, List.length_replicate, Nat.min_self]

theorem xorPad_bytes (key : List Nat) (hb : Bytes key) (p : Nat) (hp : p ≤ 255) :
    Bytes (xorBytes (normalizeKey vhashAlg key) (List.replicate hmacBlock p)) :=
  xorBytes_bytes _ _ (normalizeKey_bytes key hb) (Bytes.replicate hp)

/-- HMAC-MegaDreifach: the generated `HMAC` is the model's `hmac` over the algebraic
    MegaDreifach hash, on byte keys and messages whose hash inputs fit the pad's i64
    bit length. -/
theorem v_HMAC_refines (key msg : List Nat) (hk : Bytes key) (hkfit : FitsBitlen key.length)
    (hm : Bytes msg) (hmfit : FitsBitlen (hmacBlock + msg.length)) :
    Doubledeal_cbc_hmac.v_HMAC (embed key) (embed msg) = .ok (embed (hmac vhashAlg key msg)) := by
  have hmfl : FitsLen msg.length :=
    FitsLen.of_le hmfit.fitsLen (Nat.le_add_left _ _)
  unfold Doubledeal_cbc_hmac.v_HMAC
  simp only [require_bytes_refines msg hm hmfl, ok_bind, hmac_normalize_key_refines key hk hkfit,
    show Doubledeal_cbc_hmac.ipad_byte = Int.ofNat ipadByte from rfl,
    show Doubledeal_cbc_hmac.opad_byte = Int.ofNat opadByte from rfl,
    xor_pad_key key hk _ (by decide : ipadByte ≤ 255), xor_pad_key key hk _ (by decide : opadByte ≤ 255),
    concatL_embed]
  rw [v_Hash_bytes _ ((xorPad_bytes key hk ipadByte (by decide)).append hm)
    (by rw [List.length_append, xorPad_length]; exact hmfit), ok_bind, concatL_embed,
    v_Hash_bytes _ ((xorPad_bytes key hk opadByte (by decide)).append (vhashAlg_bytes _))
    (by rw [List.length_append, xorPad_length, vhashAlg_length]; unfold FitsBitlen i64MaxNat hmacBlock; decide),
    ok_bind, listLen_embed, vhashAlg_length]
  rfl

theorem v_HMAC_MegaDreifach_refines (key msg : List Nat) (hk : Bytes key)
    (hkfit : FitsBitlen key.length) (hm : Bytes msg)
    (hmfit : FitsBitlen (hmacBlock + msg.length)) :
    Doubledeal_cbc_hmac.v_HMAC_MegaDreifach (embed key) (embed msg) =
      .ok (embed (hmac vhashAlg key msg)) := by
  unfold Doubledeal_cbc_hmac.v_HMAC_MegaDreifach
  rw [v_HMAC_refines key msg hk hkfit hm hmfit]
  rfl

theorem u16be_bytes (n : Nat) : Bytes (u16be n) := by
  intro b hb
  simp only [u16be, beBytes, List.mem_map] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have := Nat.mod_lt (n / 256 ^ i) (by decide : 0 < 256)
  omega

theorem u64be_bytes (n : Nat) : Bytes (u64be n) := by
  intro b hb
  simp only [u64be, beBytes, List.mem_map] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have := Nat.mod_lt (n / 256 ^ i) (by decide : 0 < 256)
  omega

theorem u16be_length (n : Nat) : (u16be n).length = 2 := by simp [u16be, beBytes]
theorem u64be_length (n : Nat) : (u64be n).length = 8 := by simp [u64be, beBytes]

theorem label_bytes_enc : Bytes encLabel := by unfold Bytes; decide
theorem label_bytes_mac : Bytes macLabel := by unfold Bytes; decide
theorem label_bytes_version : Bytes versionLabel := by unfold Bytes; decide

/-- SPEC §5 key schedule: on a nonempty byte master secret whose hash inputs fit the
    pad's i64 bit length. -/
theorem derive_keys_refines (mk : List Nat) (hb : Bytes mk) (hne : mk ≠ [])
    (hfit : FitsBitlen (36 + mk.length)) :
    Doubledeal_cbc_hmac.derive_keys (embed mk) =
      .ok (embed (deriveKeys vhashAlg mk).1, embed (deriveKeys vhashAlg mk).2) := by
  have hfl : FitsLen mk.length := FitsLen.of_le hfit.fitsLen (Nat.le_add_left _ _)
  have hpos : 0 < mk.length := List.length_pos.mpr hne
  have hin : ∀ lab : List Nat, Bytes lab → lab.length = 26 →
      Bytes (u16be lab.length ++ lab ++ u64be mk.length ++ mk) ∧
      FitsBitlen (u16be lab.length ++ lab ++ u64be mk.length ++ mk).length := by
    intro lab hl hlen
    refine ⟨(((u16be_bytes _).append hl).append (u64be_bytes _)).append hb, ?_⟩
    simp only [List.length_append, u16be_length, u64be_length, hlen]
    unfold FitsBitlen at *; omega
  obtain ⟨he1, he2⟩ := hin encLabel label_bytes_enc encLabel_length
  obtain ⟨hm1, hm2⟩ := hin macLabel label_bytes_mac macLabel_length
  unfold Doubledeal_cbc_hmac.derive_keys
  simp only [require_bytes_refines mk hb hfl, ok_bind, listLen_embed, decide_ofNat_pos,
    decide_eq_true hpos, sudoAssert_true, enc_label_eq, mac_label_eq]
  rw [u16be_refines _ (by rw [encLabel_length]; decide), ok_bind, u64be_refines _ hfl, ok_bind,
    concatL_embed, concatL_embed, concatL_embed, v_Hash_bytes _ he1 he2, ok_bind,
    u16be_refines _ (by rw [macLabel_length]; decide), ok_bind, ok_bind,
    concatL_embed, concatL_embed, concatL_embed, v_Hash_bytes _ hm1 hm2, ok_bind]
  simp only [listLen_embed, vhashAlg_length, SudoRt.sudoAssertEq, sEq_int,
    show Doubledeal_cbc_hmac.digest_len = Int.ofNat 29 from rfl, decide_True, if_true, ok_bind,
    hmacBlock_int]
  rw [take_prefix_refines _ _ (by rw [vhashAlg_length]; decide)
    (by rw [vhashAlg_length]; unfold FitsLen i64MaxNat; decide), ok_bind]
  rfl

/-- The empty master secret is rejected (SPEC §5), by the assert on line 152. -/
theorem derive_keys_empty :
    Doubledeal_cbc_hmac.derive_keys (embed []) = SudoRt.fail "AssertFailed" "line 152" := by
  rfl

/-- SPEC §6.1: the MAC input, on byte strings whose lengths fit an i64. -/
theorem mac_input_refines (aad iv c : List Nat) (ha : Bytes aad) (hi : Bytes iv) (hc : Bytes c)
    (hfa : FitsLen aad.length) (hfi : FitsLen iv.length) (hfc : FitsLen c.length) :
    Doubledeal_cbc_hmac.mac_input (embed aad) (embed iv) (embed c) =
      .ok (embed (macInput aad iv c)) := by
  unfold Doubledeal_cbc_hmac.mac_input
  simp only [require_bytes_refines aad ha hfa, require_bytes_refines iv hi hfi,
    require_bytes_refines c hc hfc, ok_bind, version_label_eq, listLen_embed]
  rw [u16be_refines _ (by rw [versionLabel_length]; decide), ok_bind, u64be_refines _ hfa, ok_bind,
    u64be_refines _ hfi, ok_bind, u64be_refines _ hfc, ok_bind]
  simp only [concatL_embed, pure_eq_ok, macInput]

end DoubleDealCbcHmac.Link2
