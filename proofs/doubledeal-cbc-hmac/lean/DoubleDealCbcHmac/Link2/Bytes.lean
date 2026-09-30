/-
  LINK 2. The emitted byte helpers of doubledeal_cbc_hmac.sudo refine the model in
  `DoubleDealCbcHmac.Spec`: `require_bytes`, `xor_byte`, `xor_bytes`, `take_prefix`,
  `pad_zeros`, `xor_pad`, `cbc_chain_from_cipher_block`, `tags_equal`. Proof-only.
  Domain: `embed` of `List Nat` (so every cell is nonnegative), bytes `≤ 255` where the
  sudo asserts it, lengths that fit an i64 (`FitsLen`). Not emitter soundness.
-/
import DoubleDealCbcHmac.Spec
import DoubleDealCbcHmac.Link2.Loop
import MegaDreifach.Link2.Bytes
import MegaDreifach.Link2.MulGenMath
import Doubledeal_cbc_hmac

namespace DoubleDealCbcHmac.Link2
open MegaDreifach.Link2

/-- Every cell is a byte (the sudo `require_bytes` range): MegaDreifach's `Byte` on
    each cell, i.e. `PadWf.bytes` without the length bound. -/
def Bytes (xs : List Nat) : Prop := ∀ b ∈ xs, Byte b

/-- The CBC message block and the HMAC block are both 28 bytes (SPEC §2); the sudo uses
    `hmac_block` for the pad. The one bridge between the two model parameters. -/
theorem msgBlock_eq_hmacBlock : msgBlock = hmacBlock := rfl

theorem Bytes.get {xs : List Nat} (h : Bytes xs) (i : Nat) (hi : i < xs.length) :
    xs[i] ≤ 255 := h _ (List.getElem_mem hi)

/-! ## require_bytes -/

theorem require_bytes_refines (xs : List Nat) (hb : Bytes xs) (hfit : FitsLen xs.length) :
    Doubledeal_cbc_hmac.require_bytes (embed xs) = .ok () := by
  unfold Doubledeal_cbc_hmac.require_bytes
  simp only [listLen_embed, pure_eq_ok, fuelRange_eq, bind_ok_right]
  rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
  · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    rw [idx_break _ _ _ _ _ (by decide) (by simp)]
  · rw [subI_ofNat_one _ hpos hfit, ok_bind]
    refine chain_idx _ _ _ 0 (xs.length - 1) (Nat.zero_le _) ?_ _ rfl
    intro i _ hi
    have hix : i < xs.length := by omega
    rw [if_neg (ofNat_not_gt hi), atL_embed xs i hix, ok_bind]
    simp only [ge_iff_le, decide_zero_le_ofNat, if_true, ok_bind, pure_eq_ok,
      show (255 : Int) = Int.ofNat 255 from rfl, decide_ofNat_le_of (hb.get i hix),
      sudoAssert_true]
    exact asc_tail_idx _ i (FitsLen.succ_le hix hfit)

/-! ## xor_byte -/

theorem xor_div_pow (a b j : Nat) : (a ^^^ b) / 2 ^ j = (a / 2 ^ j) ^^^ (b / 2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih, Nat.xor_div_two,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

theorem xor_mod_two (x y : Nat) : (x ^^^ y) % 2 = if x % 2 = y % 2 then 0 else 1 := by
  have h := Nat.xor_mod_two_eq_one (a := x) (b := y)
  have hx := Nat.mod_two_eq_zero_or_one x
  have hy := Nat.mod_two_eq_zero_or_one y
  have hxy := Nat.mod_two_eq_zero_or_one (x ^^^ y)
  split <;> omega

theorem xor_mod_pow_succ (a b j : Nat) :
    (a ^^^ b) % 2 ^ (j + 1) = (a ^^^ b) % 2 ^ j +
      (if a / 2 ^ j % 2 = b / 2 ^ j % 2 then 0 else 2 ^ j) := by
  rw [Nat.mod_pow_succ, xor_div_pow, xor_mod_two]
  split <;> simp

/-- State of the emitted `xor_byte` loop on entry to bit `j`: `(out, left, right, place)`. -/
def xorState (a b j : Nat) : Int × Int × Int × Int :=
  (Int.ofNat ((a ^^^ b) % 2 ^ j), Int.ofNat (a / 2 ^ j), Int.ofNat (b / 2 ^ j),
    Int.ofNat (2 ^ j))

/-- The 8-step bit loop is XOR on bytes. -/
theorem xor_byte_refines (a b : Nat) (ha : a ≤ 255) (hb : b ≤ 255) :
    Doubledeal_cbc_hmac.xor_byte (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a ^^^ b)) := by
  unfold Doubledeal_cbc_hmac.xor_byte
  simp only [ge_iff_le, decide_zero_le_ofNat, show (255 : Int) = Int.ofNat 255 from rfl,
    decide_ofNat_le_of ha, decide_ofNat_le_of hb, ite_true, pure_eq_ok, ok_bind,
    sudoAssert_true, fuelRange_eq, bind_ok_right]
  have h0 : ((0 : Int), (0 : Int), Int.ofNat a, Int.ofNat b, (1 : Int)) =
      (Int.ofNat 0, xorState a b 0) := by simp [xorState]
  rw [h0]
  refine chain_loop (f := xorState a b) (fromN := 0) (toN := 7) _ _ _ (Nat.zero_le _) ?_ _ ?_
  · intro i _ hi
    have hfit : FitsLen (i + 1) := by unfold FitsLen i64MaxNat; omega
    have hpow : 2 ^ i ≤ 128 := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hi
      simpa using this
    dsimp only [xorState]
    rw [show (7 : Int) = Int.ofNat 7 from rfl, show (2 : Int) = Int.ofNat 2 from rfl,
      if_neg (ofNat_not_gt hi), modI_ofNat _ (by decide), modI_ofNat _ (by decide), ok_bind,
      ok_bind, sEq_int]
    have h2 : FitsLen (2 ^ i * 2) := by unfold FitsLen i64MaxNat; omega
    have h3 : FitsLen ((a ^^^ b) % 2 ^ i + 2 ^ i) := by
      have := Nat.mod_lt (a ^^^ b) (Nat.pos_pow_of_pos i (by decide : 0 < 2))
      unfold FitsLen i64MaxNat; omega
    rw [divI_ofNat _ (by decide), divI_ofNat _ (by decide), mulI_ofNat _ _ h2,
      addI_ofNat _ _ h3]
    simp only [ok_bind, Nat.div_div_eq_div_mul, show 2 ^ i * 2 = 2 ^ (i + 1) from rfl,
      xor_mod_pow_succ]
    by_cases hc : a / 2 ^ i % 2 = b / 2 ^ i % 2
    · simp only [hc, decide_True, Bool.not_true, Bool.false_eq_true, if_true, if_false,
        ok_bind, Nat.add_zero]
      rw [asc_tail 7 i hfit]
    · simp only [Int.ofNat.injEq, hc, decide_False, Bool.not_false, if_true, if_false, ok_bind]
      rw [asc_tail 7 i hfit]
  · dsimp only [xorState]
    have : a ^^^ b < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
    rw [Nat.mod_eq_of_lt this]

theorem xor_lt_256 {a b : Nat} (ha : a ≤ 255) (hb : b ≤ 255) : a ^^^ b ≤ 255 := by
  have : a ^^^ b < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  omega

/-! ## xor_bytes -/

theorem xorBytes_prefix (a b : List Nat) (n : Nat) (hn : n ≤ a.length) (hab : a.length = b.length) :
    (List.range' 0 n).map (fun i => a.getD i 0 ^^^ b.getD i 0) = xorBytes (a.take n) (b.take n) := by
  induction n with
  | zero => simp [xorBytes]
  | succ n ih =>
    rw [List.range'_1_concat, List.map_append, ih (by omega)]
    simp only [xorBytes, Nat.zero_add, List.map_cons, List.map_nil]
    rw [List.take_succ, List.take_succ, List.getElem?_eq_getElem (by omega : n < a.length),
      List.getElem?_eq_getElem (by omega : n < b.length), getD_eq_getElem' a n (by omega),
      getD_eq_getElem' b n (by omega)]
    simp [List.zipWith_append, List.length_take, Nat.min_eq_left (by omega : n ≤ a.length),
      Nat.min_eq_left (by omega : n ≤ b.length)]

/-- `xor_bytes` is the model's `xorBytes` on two byte strings of the same length. -/
theorem xor_bytes_refines (a b : List Nat) (hab : a.length = b.length) (ha : Bytes a)
    (hb : Bytes b) (hfit : FitsLen a.length) :
    Doubledeal_cbc_hmac.xor_bytes (embed a) (embed b) = .ok (embed (xorBytes a b)) := by
  unfold Doubledeal_cbc_hmac.xor_bytes
  simp only [listLen_embed, hab, SudoRt.sudoAssertEq, sEq_int, decide_True, if_true, ok_bind,
    require_bytes_refines a ha hfit, require_bytes_refines b hb (hab ▸ hfit), pure_eq_ok,
    fuelRange_eq, bind_ok_right]
  rcases Nat.eq_zero_or_pos b.length with h0 | hpos
  · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    rw [asc_break _ _ _ _ _ _ (by decide) (by simp)]
    have ha0 : a = [] := List.eq_nil_of_length_eq_zero (hab.trans h0)
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero h0
    subst ha0; subst hb0; rfl
  · rw [subI_ofNat_one _ hpos (hab ▸ hfit), ok_bind]
    rw [show ((0 : Int), (#[] : Array Int)) = (Int.ofNat 0, embed []) from rfl]
    refine (push_loop 0 (b.length - 1) (Nat.zero_le _)
      (fun i => a.getD i 0 ^^^ b.getD i 0) [] _ _ _ ?_).trans ?_
    · intro i l _ hi
      have hia : i < a.length := by omega
      have hib : i < b.length := by omega
      dsimp only
      rw [if_neg (ofNat_not_gt hi), atL_embed a i hia, ok_bind, atL_embed b i hib, ok_bind,
        xor_byte_refines _ _ (ha.get i hia) (hb.get i hib), ok_bind]
      simp only [SudoRt.appendL, ok_bind, push_embed]
      rw [asc_tail _ i (FitsLen.succ_le hia hfit), getD_eq_getElem' a i hia, getD_eq_getElem' b i hib]
    · simp only [List.nil_append, Nat.sub_zero, Nat.sub_add_cancel hpos]
      rw [xorBytes_prefix a b _ (by omega) hab, ← hab, List.take_length, hab, List.take_length]

/-! ## take_prefix / pad_zeros -/

theorem take_prefix_refines (xs : List Nat) (n : Nat) (hn : n ≤ xs.length)
    (hfit : FitsLen xs.length) :
    Doubledeal_cbc_hmac.take_prefix (embed xs) (Int.ofNat n) = .ok (embed (xs.take n)) := by
  unfold Doubledeal_cbc_hmac.take_prefix
  simp only [ge_iff_le, listLen_embed, pure_eq_ok, decide_zero_le_ofNat, decide_ofNat_le,
    decide_eq_true hn, sudoAssert_true, ok_bind, fuelRange_eq, bind_ok_right]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    rw [asc_break _ _ _ _ _ _ (by decide) (by simp)]
    rfl
  · rw [subI_ofNat_one n hpos (FitsLen.of_le hfit hn), ok_bind]
    rw [show ((0 : Int), (#[] : Array Int)) = (Int.ofNat 0, embed []) from rfl]
    refine (push_loop 0 (n - 1) (Nat.zero_le _) (fun i => xs.getD i 0) [] _ _ _ ?_).trans ?_
    · intro i l _ hi
      have hix : i < xs.length := by omega
      rw [if_neg (ofNat_not_gt hi), atL_embed xs i hix, ok_bind]
      simp only [SudoRt.appendL, ok_bind, push_embed]
      rw [asc_tail (n - 1) i (FitsLen.of_le hfit (by omega)), getD_eq_getElem' xs i hix]
    · simp only [List.nil_append, Nat.sub_zero, Nat.sub_add_cancel hpos]
      rw [range'_map_getD xs 0 n (by omega), List.drop_zero]

theorem range'_map_pad (xs : List Nat) (n : Nat) (hn : xs.length ≤ n) :
    (List.range' 0 n).map (fun i => if i < xs.length then xs.getD i 0 else 0) =
      xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range'] at h1
    rw [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    by_cases hi : i < xs.length
    · rw [if_pos hi, List.getElem_append_left hi, getD_eq_getElem' xs i hi]
    · rw [if_neg hi, List.getElem_append_right (by omega)]
      simp

theorem pad_zeros_refines (xs : List Nat) (n : Nat) (hn : xs.length ≤ n) (hfit : FitsLen n) :
    Doubledeal_cbc_hmac.pad_zeros (embed xs) (Int.ofNat n) =
      .ok (embed (xs ++ List.replicate (n - xs.length) 0)) := by
  unfold Doubledeal_cbc_hmac.pad_zeros
  simp only [ge_iff_le, listLen_embed, pure_eq_ok, decide_ofNat_le, decide_eq_true hn,
    sudoAssert_true, ok_bind, fuelRange_eq, bind_ok_right]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    rw [asc_break _ _ _ _ _ _ (by decide) (by simp)]
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  · rw [subI_ofNat_one n hpos hfit, ok_bind]
    rw [show ((0 : Int), (#[] : Array Int)) = (Int.ofNat 0, embed []) from rfl]
    refine (push_loop 0 (n - 1) (Nat.zero_le _)
      (fun i => if i < xs.length then xs.getD i 0 else 0) [] _ _ _ ?_).trans ?_
    · intro i l _ hi
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      by_cases hix : i < xs.length
      · have hd : decide (Int.ofNat i < Int.ofNat xs.length) = true :=
          decide_eq_true (Int.ofNat_lt.mpr hix)
        rw [if_neg (ofNat_not_gt hi)]
        simp only [hd, if_true, atL_embed xs i hix, ok_bind, SudoRt.appendL, push_embed]
        rw [asc_tail (n - 1) i hfi, if_pos hix, getD_eq_getElem' xs i hix]
      · have hd : decide (Int.ofNat i < Int.ofNat xs.length) = false :=
          decide_eq_false (fun h => hix (Int.ofNat_lt.mp h))
        rw [if_neg (ofNat_not_gt hi)]
        simp only [hd, Bool.false_eq_true, if_false, ok_bind, SudoRt.appendL,
          show (0 : Int) = Int.ofNat 0 from rfl, push_embed]
        rw [asc_tail (n - 1) i hfi, if_neg hix]
    · simp only [List.nil_append, Nat.sub_zero, Nat.sub_add_cancel hpos]
      rw [range'_map_pad xs n hn]

/-! ## xor_pad -/

theorem range'_map_xor_rep (k : List Nat) (p : Nat) :
    (List.range' 0 k.length).map (fun i => k.getD i 0 ^^^ p) =
      xorBytes k (List.replicate k.length p) := by
  apply List.ext_getElem
  · simp [xorBytes]
  · intro i h1 h2
    simp only [List.length_map, List.length_range'] at h1
    unfold xorBytes
    rw [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul,
      List.getElem_zipWith, getD_eq_getElem' k i h1, List.getElem_replicate]

theorem xor_pad_refines (k : List Nat) (p : Nat) (hk : k.length = hmacBlock) (hb : Bytes k)
    (hp : p ≤ 255) :
    Doubledeal_cbc_hmac.xor_pad (embed k) (Int.ofNat p) =
      .ok (embed (xorBytes k (List.replicate hmacBlock p))) := by
  unfold Doubledeal_cbc_hmac.xor_pad
  simp only [listLen_embed, hk, SudoRt.sudoAssertEq, sEq_int, hmacBlock,
    Doubledeal_cbc_hmac.hmac_block, pure_eq_ok, fuelRange_eq, bind_ok_right]
  simp only [show (28 : Int) = Int.ofNat 28 from rfl, decide_True, if_true, ok_bind,
    subI_ofNat_one 28 (by decide) (by unfold FitsLen i64MaxNat; decide)]
  rw [show ((0 : Int), (#[] : Array Int)) = (Int.ofNat 0, embed []) from rfl]
  refine (push_loop 0 (28 - 1) (Nat.zero_le _) (fun i => k.getD i 0 ^^^ p) [] _ _ _ ?_).trans ?_
  · intro i l _ hi
    have hik : i < k.length := by rw [hk]; unfold hmacBlock; omega
    rw [if_neg (ofNat_not_gt hi), atL_embed k i hik, ok_bind,
      xor_byte_refines _ _ (hb.get i hik) hp, ok_bind]
    simp only [SudoRt.appendL, ok_bind, push_embed]
    rw [asc_tail _ i (by unfold FitsLen i64MaxNat; omega), getD_eq_getElem' k i hik]
  · simp only [List.nil_append]
    rw [show (28 - 1 + 1 - 0) = k.length by rw [hk]; rfl, range'_map_xor_rep, hk]
    rfl

/-! ## cbc_chain_from_cipher_block / tags_equal -/

theorem cbc_chain_from_cipher_block_refines (block : List Nat) (hlen : block.length = cipherBlock)
    (hb : Bytes block) :
    Doubledeal_cbc_hmac.cbc_chain_from_cipher_block (embed block) =
      .ok (embed (cbcChain block)) := by
  have hfit : FitsLen block.length := by rw [hlen]; unfold FitsLen i64MaxNat cipherBlock; decide
  unfold Doubledeal_cbc_hmac.cbc_chain_from_cipher_block
  simp only [listLen_embed, hlen, SudoRt.sudoAssertEq, sEq_int, cipherBlock,
    Doubledeal_cbc_hmac.cipher_block, Doubledeal_cbc_hmac.hmac_block, pure_eq_ok,
    fuelRange_eq, bind_ok_right]
  simp only [show (29 : Int) = Int.ofNat 29 from rfl, decide_True, if_true, ok_bind,
    require_bytes_refines block hb hfit]
  rw [show ((1 : Int), (#[] : Array Int)) = (Int.ofNat 1, embed []) from rfl,
    show (28 : Int) = Int.ofNat 28 from rfl]
  refine (push_loop 1 28 (by decide) (fun i => block.getD i 0) [] _ _ _ ?_).trans ?_
  · intro i l h1 hi
    have hib : i < block.length := by rw [hlen]; unfold cipherBlock; omega
    rw [if_neg (ofNat_not_gt hi), atL_embed block i hib, ok_bind]
    simp only [SudoRt.appendL, ok_bind, push_embed]
    rw [asc_tail _ i (by unfold FitsLen i64MaxNat; omega), getD_eq_getElem' block i hib]
  · simp only [List.nil_append]
    rw [range'_map_getD block 1 28 (by rw [hlen]; decide), cbcChain,
      List.take_of_length_le (by rw [List.length_drop, hlen]; decide)]

/-! ## u16be / u64be -/

theorem u16be_refines (n : Nat) (hn : n ≤ 65535) :
    Doubledeal_cbc_hmac.u16be (Int.ofNat n) = .ok (embed (u16be n)) := by
  unfold Doubledeal_cbc_hmac.u16be
  simp only [ge_iff_le, decide_zero_le_ofNat, show (65535 : Int) = Int.ofNat 65535 from rfl,
    decide_ofNat_le_of hn, if_true, pure_eq_ok, ok_bind, sudoAssert_true,
    show (256 : Int) = Int.ofNat 256 from rfl, divI_ofNat n (by decide : 256 ≠ 0),
    modI_ofNat n (by decide : 256 ≠ 0), SudoRt.appendL]
  have : n / 256 % 256 = n / 256 := Nat.mod_eq_of_lt (by omega)
  simp [u16be, beBytes, embed, this, List.range_succ]

theorem u64be_refines (n : Nat) (hn : FitsLen n) :
    Doubledeal_cbc_hmac.u64be (Int.ofNat n) = .ok (embed (u64be n)) := by
  unfold Doubledeal_cbc_hmac.u64be
  simp only [ge_iff_le, decide_zero_le_ofNat, if_true, pure_eq_ok, ok_bind, sudoAssert_true,
    fuelRange_eq, bind_ok_right]
  -- loop 1: parts = the little-endian bytes, rest = n / 256^(i-1)
  let g : Nat → Nat := fun j => n / 256 ^ (j - 1) % 256
  have h0 : ((1 : Int), (#[] : Array Int), Int.ofNat n) =
      (Int.ofNat 1, embed ((List.range' 1 (1 - 1)).map g), Int.ofNat (n / 256 ^ (1 - 1))) := by
    simp; rfl
  rw [h0]
  refine chain_loop (f := fun i => (embed ((List.range' 1 (i - 1)).map g),
    Int.ofNat (n / 256 ^ (i - 1)))) (fromN := 1) (toN := 8) _ _ _ (by decide) ?_ _ ?_
  · intro i h1 hi
    dsimp only
    rw [show (8 : Int) = Int.ofNat 8 from rfl, show (256 : Int) = Int.ofNat 256 from rfl,
      if_neg (ofNat_not_gt hi), modI_ofNat _ (by decide), ok_bind, divI_ofNat _ (by decide),
      ok_bind]
    simp only [SudoRt.appendL, ok_bind, push_embed]
    rw [asc_tail 8 i (by unfold FitsLen i64MaxNat; omega)]
    have hr : (List.range' 1 (i - 1)).map g ++ [n / 256 ^ (i - 1) % 256] =
        (List.range' 1 (i + 1 - 1)).map g := by
      rw [show i + 1 - 1 = (i - 1) + 1 by omega, List.range'_1_concat, List.map_append]
      simp [g, show 1 + (i - 1) - 1 = i - 1 by omega]
    have hq : n / 256 ^ (i - 1) / 256 = n / 256 ^ (i + 1 - 1) := by
      rw [Nat.div_div_eq_div_mul, show i + 1 - 1 = (i - 1) + 1 by omega, Nat.pow_succ]
    rw [hr, hq]
  · dsimp only
    have hz : n / 256 ^ (8 + 1 - 1) = 0 := Nat.div_eq_of_lt (fitsLen_lt_be hn)
    rw [hz, SudoRt.sudoAssertEq, sEq_int, show Int.ofNat 0 = (0 : Int) from rfl,
      if_pos (decide_eq_true rfl), ok_bind]
    let p : Nat → Nat := fun j => n / 256 ^ j % 256
    have hP : ∀ i, i < 8 → (List.map g (List.range' 1 (8 + 1 - 1)))[i]? = some (p i) := by
      intro i hi
      simp [g, p, List.getElem?_range', hi, show 1 + i - 1 = i by omega]
    rw [show fuelRange 0 7 = fuelDown (Int.ofNat 7) 0 from rfl,
      show ((7 : Int), (#[] : Array Int)) =
        (Int.ofNat 7, embed ((List.range' (7 + 1) (7 - 7)).reverse.map p)) from rfl]
    refine chain_down _ _ _ (fun i => embed ((List.range' (i + 1) (7 - i)).reverse.map p))
      (fun i => embed ((List.range' i (8 - i)).reverse.map p)) 7 ?_ ?_ _ ?_
    · intro i hi
      have hlen : i < (List.map g (List.range' 1 (8 + 1 - 1))).length := by simp; omega
      dsimp only
      rw [if_neg (show ¬ (Int.ofNat i < 0) from Int.not_lt.mpr (Int.ofNat_zero_le i)), atL_ofNat _ i (by rw [size_embed]; exact hlen),
        get_embed, ok_bind]
      simp only [SudoRt.appendL, ok_bind, push_embed]
      rw [show (0 : Int) = Int.ofNat 0 from rfl, desc_tail i (by unfold FitsLen i64MaxNat; omega)]
      have hg : (List.map g (List.range' 1 (8 + 1 - 1)))[i] = p i := by
        have := hP i (by omega)
        rw [List.getElem?_eq_getElem hlen] at this
        exact Option.some.inj this
      rw [hg, show 8 - i = (7 - i) + 1 by omega, List.range'_succ, List.reverse_cons,
        List.map_append]
      rfl
    · intro i hp hi
      dsimp only
      rw [show i - 1 + 1 = i by omega, show 7 - (i - 1) = 8 - i by omega]
    · dsimp only
      rfl

/-! ## tags_equal -/

/-- The emitted `ok` flag after the first `i` indices. -/
def allEq (a b : List Nat) (i : Nat) : Bool := (List.range i).all fun j => a.getD j 0 == b.getD j 0

theorem allEq_succ (a b : List Nat) (i : Nat) (hia : i < a.length) (hib : i < b.length) :
    allEq a b (i + 1) = if a[i] = b[i] then allEq a b i else false := by
  unfold allEq
  rw [List.range_succ, List.all_append]
  simp only [List.all_cons, List.all_nil, Bool.and_true, getD_eq_getElem' a i hia,
    getD_eq_getElem' b i hib]
  by_cases h : a[i] = b[i] <;> simp [h]

theorem allEq_iff (a b : List Nat) (hab : a.length = b.length) :
    allEq a b a.length = decide (a = b) := by
  unfold allEq
  by_cases h : a = b
  · subst h; simp
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro H
    apply h
    apply List.ext_getElem hab
    intro j h1 h2
    have := (List.all_eq_true.mp H) j (List.mem_range.mpr h1)
    simp only [beq_iff_eq] at this
    rwa [getD_eq_getElem' a j h1, getD_eq_getElem' b j h2] at this

theorem tags_equal_refines (a b : List Nat) (hfa : FitsLen a.length) :
    Doubledeal_cbc_hmac.tags_equal (embed a) (embed b) = .ok (tagsEqual a b) := by
  unfold Doubledeal_cbc_hmac.tags_equal
  simp only [listLen_embed, sEq_int, pure_eq_ok, fuelRange_eq, bind_ok_right]
  by_cases hab : a.length = b.length
  · simp only [Int.ofNat.injEq, hab, decide_True, Bool.not_true, Bool.false_eq_true, if_false]
    have hfb : FitsLen b.length := hab ▸ hfa
    rcases Nat.eq_zero_or_pos b.length with h0 | hpos
    · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
      rw [asc_break _ _ _ _ _ _ (by decide) (by simp)]
      have ha0 : a = [] := List.eq_nil_of_length_eq_zero (hab.trans h0)
      have hb0 : b = [] := List.eq_nil_of_length_eq_zero h0
      subst ha0; subst hb0; rfl
    · rw [subI_ofNat_one _ hpos hfb, ok_bind]
      have h0 : ((0 : Int), true) = (Int.ofNat 0, allEq a b 0) := rfl
      rw [h0]
      refine chain_loop (f := allEq a b) (fromN := 0)
        (toN := b.length - 1) _ _ _ (Nat.zero_le _) ?_ _ ?_
      · intro i _ hi
        have hia : i < a.length := by omega
        have hib : i < b.length := by omega
        dsimp only
        rw [if_neg (ofNat_not_gt hi), atL_embed a i hia, ok_bind, atL_embed b i hib, ok_bind]
        rw [allEq_succ a b i hia hib]
        by_cases hc : a[i] = b[i]
        · simp only [Int.ofNat.injEq, hc, decide_True, Bool.not_true, Bool.false_eq_true,
            if_false, if_true, ok_bind]
          rw [asc_tail _ i (FitsLen.succ_le hib hfb)]
        · simp only [Int.ofNat.injEq, hc, decide_False, Bool.not_false, if_false, if_true,
            ok_bind]
          rw [asc_tail _ i (FitsLen.succ_le hib hfb)]
      · dsimp only
        rw [Nat.sub_add_cancel hpos, tagsEqual, ← hab, allEq_iff a b hab]
  · have hne : ¬ (Int.ofNat a.length = Int.ofNat b.length) := fun e => hab (Int.ofNat.inj e)
    simp only [hne, decide_False, Bool.not_false, if_true, tagsEqual]
    congr 1
    exact (decide_eq_false (fun e => hab (congrArg List.length e))).symm

end DoubleDealCbcHmac.Link2

