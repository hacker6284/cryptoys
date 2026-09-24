/-
  M5 — SHA-2-style pad, B=28: injectivity and length recovery.
  `padded = M ‖ 0x80 ‖ 0x00^z ‖ bitlen(M) as 8-byte BE`.
  Zero sorry. No native_decide.
-/
import MegaDreifach.Basic
import MegaDreifach.NatUtil

namespace MegaDreifach

/-- Big-endian encode: `width` bytes. -/
def toBE (width val : Nat) : List Nat :=
  mixDecode (List.replicate width 256) val

/-- Big-endian decode. -/
def fromBE (bs : List Nat) : Nat :=
  mixEncode (List.replicate bs.length 256) bs

theorem toBE_length (width val : Nat) : (toBE width val).length = width := by
  simp [toBE, mixDecode_length, List.length_replicate]

theorem replicate_256_pos (k : Nat) : ∀ r ∈ List.replicate k 256, 0 < r := by
  intro r hr
  have : r = 256 := List.eq_of_mem_replicate hr
  subst this; exact Nat.succ_pos 255

theorem product_replicate_256 (k : Nat) : product (List.replicate k 256) = 256 ^ k :=
  product_replicate 256 k

theorem fromBE_toBE (width val : Nat) (h : val < 256 ^ width) :
    fromBE (toBE width val) = val := by
  have hlen : (mixDecode (List.replicate width 256) val).length = width := by
    simp [mixDecode_length, List.length_replicate]
  unfold fromBE toBE
  rw [hlen]
  have hval : val < product (List.replicate width 256) := by
    simpa [product_replicate_256] using h
  exact mixEncode_decode _ val hval (replicate_256_pos width)

theorem toBE_inj (width v1 v2 : Nat)
    (h1 : v1 < 256 ^ width) (h2 : v2 < 256 ^ width)
    (heq : toBE width v1 = toBE width v2) : v1 = v2 := by
  have e1 := fromBE_toBE width v1 h1
  have e2 := fromBE_toBE width v2 h2
  rw [← e1, ← e2, heq]

/-- Zero-fill count so that `|M| + 1 + 8 + z` is a multiple of 28. -/
def padZ (msgLen : Nat) : Nat :=
  (padBlock - (msgLen + 1 + lenField) % padBlock) % padBlock

/-- SHA-2-style pad, B=28, 8-byte BE bit length. -/
def pad (msg : List Nat) : List Nat :=
  msg ++ [0x80] ++ List.replicate (padZ msg.length) 0 ++ toBE 8 (8 * msg.length)

/-- `n + (m - n % m) % m` is a multiple of `m`. -/
theorem pad_round (n m : Nat) (hm : 0 < m) :
    (n + (m - n % m) % m) % m = 0 := by
  rw [Nat.add_mod, Nat.mod_mod]
  by_cases hk : n % m = 0
  · simp [hk, Nat.sub_zero, Nat.mod_self]
  · have hpos : 0 < n % m := Nat.pos_of_ne_zero hk
    have hlt : m - n % m < m := Nat.sub_lt hm hpos
    have hsub : (m - n % m) % m = m - n % m := Nat.mod_eq_of_lt hlt
    rw [hsub]
    have : n % m + (m - n % m) = m := Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt n hm))
    rw [this, Nat.mod_self]

theorem pad_length (msg : List Nat) :
    (pad msg).length = msg.length + 1 + padZ msg.length + 8 := by
  simp [pad, List.length_append, List.length_replicate, toBE_length]
  omega

/-- M5: padded length is a positive multiple of B=28. -/
theorem pad_length_mod (msg : List Nat) : (pad msg).length % padBlock = 0 := by
  have hm : 0 < padBlock := by decide
  have : (pad msg).length = (msg.length + 9) + padZ msg.length := by
    rw [pad_length]; omega
  rw [this]
  simp only [padZ, padBlock, lenField] at *
  -- padZ = (28 - (len+9) % 28) % 28
  change
    (msg.length + 9 + (28 - (msg.length + 1 + 8) % 28) % 28) % 28 = 0
  have : msg.length + 1 + 8 = msg.length + 9 := by omega
  rw [this]
  exact pad_round (msg.length + 9) 28 (by decide)

theorem pad_length_pos (msg : List Nat) : 0 < (pad msg).length := by
  have hmod := pad_length_mod msg
  have hge : 9 ≤ (pad msg).length := by
    rw [pad_length]; omega
  omega

theorem pad_suffix (msg : List Nat) :
    (pad msg).drop ((pad msg).length - 8) = toBE 8 (8 * msg.length) := by
  let pref := msg ++ [0x80] ++ List.replicate (padZ msg.length) 0
  have hpad : pad msg = pref ++ toBE 8 (8 * msg.length) := rfl
  have hplen : pref.length = (pad msg).length - 8 := by
    simp [pref, pad, List.length_append, List.length_replicate, toBE_length]
    omega
  have hdrop : (pad msg).length - 8 = pref.length := hplen.symm
  rw [hdrop, hpad, List.drop_left]

/-- M5: the length field recovers the bit length (when it fits in 8 bytes). -/
theorem pad_recovers_bitlen (msg : List Nat) (hfit : 8 * msg.length < 256 ^ 8) :
    fromBE ((pad msg).drop ((pad msg).length - 8)) = 8 * msg.length := by
  rw [pad_suffix, fromBE_toBE _ _ hfit]

/-- Recover the message from a well-formed pad. -/
def unpad (p : List Nat) : Option (List Nat) :=
  if _h : p.length = 0 ∨ p.length % padBlock ≠ 0 ∨ p.length < 9 then
    none
  else
    let bitlen := fromBE (p.drop (p.length - 8))
    if bitlen % 8 ≠ 0 then
      none
    else
      let n := bitlen / 8
      if p.length < n + 9 then
        none
      else if p[n]?.getD 0 ≠ 0x80 then
        none
      else
        let fill := (p.drop (n + 1)).take (p.length - 8 - (n + 1))
        if fill.any (fun b => !decide (b = 0)) then
          none
        else if fill.length ≠ padZ n then
          none
        else
          some (p.take n)

private theorem pad_prefix_take (msg : List Nat) :
    (pad msg).take msg.length = msg := by
  simp [pad, List.take_left]

private theorem pad_at_len (msg : List Nat) :
    (pad msg)[msg.length]?.getD 0 = 0x80 := by
  have hrest : pad msg = msg ++ (0x80 ::
      (List.replicate (padZ msg.length) 0 ++ toBE 8 (8 * msg.length))) := by
    simp [pad]
  rw [hrest, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp

private theorem pad_fill (msg : List Nat) :
    ((pad msg).drop (msg.length + 1)).take (padZ msg.length) =
      List.replicate (padZ msg.length) 0 := by
  have hmid : pad msg = (msg ++ [0x80]) ++
      (List.replicate (padZ msg.length) 0 ++ toBE 8 (8 * msg.length)) := by
    simp [pad]
  have hlen : (msg ++ [0x80]).length = msg.length + 1 := by simp
  rw [hmid, ← hlen, List.drop_left]
  induction (padZ msg.length) with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.take, ih]

/-- M5: unpad recovers the message (bit length fits in 8 bytes). -/
theorem unpad_pad (msg : List Nat) (hfit : 8 * msg.length < 256 ^ 8) :
    unpad (pad msg) = some msg := by
  have hlenpos : (pad msg).length ≠ 0 := Nat.ne_of_gt (pad_length_pos msg)
  have hmod : (pad msg).length % padBlock = 0 := pad_length_mod msg
  have hge : 9 ≤ (pad msg).length := by rw [pad_length]; omega
  have hge' : ¬ (pad msg).length < 9 := Nat.not_lt.mpr hge
  unfold unpad
  have hcond : ¬ ((pad msg).length = 0 ∨ (pad msg).length % padBlock ≠ 0 ∨
      (pad msg).length < 9) := by
    intro h
    rcases h with h | h | h
    · exact hlenpos h
    · exact h (by exact hmod)
    · exact hge' h
  simp only [hcond, ↓reduceDIte]
  have hbit : fromBE ((pad msg).drop ((pad msg).length - 8)) = 8 * msg.length :=
    pad_recovers_bitlen msg hfit
  simp only [hbit]
  have h8 : (8 * msg.length) % 8 = 0 := Nat.mul_mod_right 8 _
  simp only [h8, ↓reduceIte, Nat.ne_of_beq_eq_false]
  -- Lean may not fire `≠ 0` the way we want; rewrite explicitly
  have : ¬ ((8 * msg.length) % 8 ≠ 0) := by simp [h8]
  -- after simp of bitlen
  -- n = (8 * |M|) / 8 = |M|
  have hn : 8 * msg.length / 8 = msg.length := Nat.mul_div_right msg.length (by decide)
  -- Continue by rewriting n
  -- Use a calc-style unfold of the remaining ifs
  simp only [hn]
  have hroom : ¬ (pad msg).length < msg.length + 9 := by
    rw [pad_length]; omega
  simp only [hroom, ↓reduceIte]
  have hat := pad_at_len msg
  simp only [hat, ↓reduceIte]
  have hfill := pad_fill msg
  -- fill = take (len-8-(n+1)) (drop (n+1))
  -- len - 8 - (n+1) = padZ n   because len = n + 1 + padZ n + 8
  have htake : (pad msg).length - 8 - (msg.length + 1) = padZ msg.length := by
    rw [pad_length]; omega
  have hfill' :
      ((pad msg).drop (msg.length + 1)).take ((pad msg).length - 8 - (msg.length + 1)) =
        List.replicate (padZ msg.length) 0 := by
    rw [htake, hfill]
  simp only [hfill']
  have hany : ¬ (List.replicate (padZ msg.length) 0).any (fun b => !decide (b = 0)) := by
    simp
  simp only [hany, ↓reduceIte]
  have hflen : (List.replicate (padZ msg.length) 0).length = padZ msg.length :=
    List.length_replicate _ _
  simp only [hflen, ↓reduceIte]
  simp [pad_prefix_take]

/-- M5: pad is injective on messages whose bit length fits in 8 bytes. -/
theorem pad_injective (m1 m2 : List Nat)
    (h1 : 8 * m1.length < 256 ^ 8) (h2 : 8 * m2.length < 256 ^ 8)
    (heq : pad m1 = pad m2) : m1 = m2 := by
  have u1 := unpad_pad m1 h1
  have u2 := unpad_pad m2 h2
  rw [heq] at u1
  have : some m1 = some m2 := by
    rw [← u1, ← u2]
  exact Option.some.inj this

end MegaDreifach
