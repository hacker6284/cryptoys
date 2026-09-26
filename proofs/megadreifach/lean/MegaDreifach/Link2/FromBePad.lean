/-
  LINK 2. `big_from_be` ≃ algebraic `fromBE` on byte strings of length ≤ 28
  (the pad block).

  Domain `BePadWf` / `WellFormedBePad`: length ≤ 28 and every byte ≤ 255.
  Then `256^28 < 10^72 = limbBase^8`, so every Horner prefix is at most
  eight base-10^9 limbs and the value is `< 256^28 < 10^72`. Each step
  `acc * 256 + b` is `big_mul_nat` (wide accumulator times the one-limb
  factor 256) followed by `big_add_nat`.

  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.FromBeLimb2
import MegaDreifach.Link2.MulWide
import MegaDreifach.Link2.MagAdd

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

/-! ## Bounds -/

private theorem pow256_le {a b : Nat} (h : a ≤ b) : 256 ^ a ≤ 256 ^ b :=
  Nat.pow_le_pow_of_le_right (by decide : 256 > 0) h

/-- `256^28 = 2^224 < 10^72 = limbBase^8`, so a 28-byte Horner stays in eight limbs. -/
theorem pow256_28_lt_limb8 : 256 ^ 28 < limbBase ^ 8 := by
  have h28 : (256 : Nat) ^ 28 = (256 ^ 4) ^ 7 := by
    rw [show (28 : Nat) = 4 * 7 from rfl, Nat.pow_mul]
  have hle : ((256 : Nat) ^ 4) ^ 7 ≤ ((10 : Nat) ^ 10) ^ 7 :=
    Nat.pow_le_pow_left (by decide : (256 : Nat) ^ 4 ≤ (10 : Nat) ^ 10) 7
  have h4 : ((10 : Nat) ^ 10) ^ 7 = (10 : Nat) ^ 70 := by
    rw [← Nat.pow_mul 10 10 7]
  have h5 : (10 : Nat) ^ 70 < (10 : Nat) ^ 72 :=
    Nat.pow_lt_pow_of_lt (by decide : (1 : Nat) < 10) (by decide : (70 : Nat) < 72)
  have h6 : (10 : Nat) ^ 72 = limbBase ^ 8 := by
    have hb : limbBase = (10 : Nat) ^ 9 := by unfold limbBase; decide
    rw [hb, ← Nat.pow_mul 10 9 8]
  calc (256 : Nat) ^ 28 = ((256 : Nat) ^ 4) ^ 7 := h28
    _ ≤ ((10 : Nat) ^ 10) ^ 7 := hle
    _ = (10 : Nat) ^ 70 := h4
    _ < (10 : Nat) ^ 72 := h5
    _ = limbBase ^ 8 := h6

/-! ## Domain -/

/-- Trap-free domain for a pad-block `big_from_be`.

    Length `≤ 28` keeps every prefix of the base-256 Horner below
    `256^28 < 10^72`, hence in at most eight limbs. Bytes `≤ 255` are the
    digits `fromBE` expects. -/
structure BePadWf (bs : List Nat) : Prop where
  len : bs.length ≤ 28
  byte : ∀ b ∈ bs, b ≤ 255

/-- Array-side pad-block big-endian domain. -/
structure WellFormedBePad (a : Array Int) : Prop where
  len : a.size ≤ 28
  nn : Nonneg a
  byte : ∀ x ∈ decode a, x ≤ 255

theorem bePad_decode (a : Array Int) (h : WellFormedBePad a) :
    BePadWf (decode a) where
  len := by
    have : (decode a).length = a.size := by simp [decode]
    rw [this]
    exact h.len
  byte := h.byte

private theorem byte_lt (bs : List Nat) (h : BePadWf bs) :
    ∀ b ∈ bs, b < 256 := by
  intro b hb
  exact Nat.lt_of_le_of_lt (h.byte b hb) (by decide : 255 < 256)

private theorem byte_lt_base {b : Nat} (hb : b ≤ 255) : b < limbBase := by
  have h255 : (255 : Nat) < limbBase := by unfold limbBase; decide
  exact Nat.lt_of_le_of_lt hb h255

private theorem lt_limb8_of_lt_limb {x : Nat} (hx : x < limbBase) : x < limbBase ^ 8 := by
  have hle : limbBase ^ 1 ≤ limbBase ^ 8 :=
    Nat.pow_le_pow_right limbBase_pos (by decide : (1 : Nat) ≤ 8)
  rw [Nat.pow_one] at hle
  exact Nat.lt_of_lt_of_le hx hle

private theorem fits255 : FitsLen 255 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits28 : FitsLen 28 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_byte {b : Nat} (hb : b ≤ 255) : FitsLen b :=
  FitsLen.of_le fits255 hb

private theorem two56_lt_limb : 256 < limbBase := by
  unfold limbBase
  decide

/-- Below the limb base `limbsOfNat` and `natLimbs` agree: `[]` or `[b]`. -/
private theorem limbsOfNat_eq_natLimbs {b : Nat} (hb : b < limbBase) :
    limbsOfNat b = natLimbs b := by
  rw [natLimbs_of_lt b hb]
  unfold limbsOfNat
  by_cases h0 : b = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rw [Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]
    simp

private theorem fromBE_nil : fromBE [] = 0 := by
  simp [fromBE, mixEncode]

private theorem fromBE_eq_acc (bs : List Nat) :
    fromBE bs = oriAcc 256 bs bs.length := by
  rw [oriAcc, List.take_length]
  unfold fromBE
  exact (hornerAcc_mix 256 bs).symm

private theorem ori_pad_lt (bs : List Nat) (hb : ∀ b ∈ bs, b < 256)
    (i : Nat) (hi28 : i ≤ 28) (hlen : i ≤ bs.length) :
    oriAcc 256 bs i < limbBase ^ 8 := by
  have h1 := oriAcc_lt (r := 256) bs hb i hlen
  have h2 : 256 ^ i ≤ 256 ^ 28 := pow256_le hi28
  exact Nat.lt_trans (Nat.lt_of_lt_of_le h1 h2) pow256_28_lt_limb8

theorem fromBE_pad_lt_limb8 (bs : List Nat) (h : BePadWf bs) :
    fromBE bs < limbBase ^ 8 := by
  rw [fromBE_eq_acc]
  exact ori_pad_lt bs (byte_lt bs h) bs.length h.len (Nat.le_refl _)

/-! ## Horner step -/

private theorem beFromStep_gt (bs : Array Int) (two56 : Megadreifach.BigInt)
    (toV i : Int) (n : Megadreifach.BigInt) (h : i > toV) :
    beFromStep bs two56 toV (i, n) = .ok (SudoRt.Flow.brk (i, n)) := by
  unfold beFromStep
  rw [if_pos h]
  rfl

/-- One Horner step `acc * 256 + byte` while the value stays below `10^72`. -/
private theorem bePadStep (bs : List Nat) (h : BePadWf bs) (i : Nat)
    (hi : i < bs.length) :
    beFromStep (embed bs) (bigOf [256]) (Int.ofNat (bs.length - 1))
        (Int.ofNat i, bigOf (natLimbs (oriAcc 256 bs i))) =
      if i = bs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigOf (natLimbs (oriAcc 256 bs (i + 1)))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigOf (natLimbs (oriAcc 256 bs (i + 1))))) := by
  unfold beFromStep
  dsimp
  have hle : i ≤ bs.length - 1 := Nat.le_sub_one_of_lt hi
  have hngt : ¬ (i : Int) > ((bs.length - 1 : Nat) : Int) := ofNat_not_gt hle
  rw [if_neg hngt]
  have hb := byte_lt bs h
  have hi28 : i ≤ 28 := Nat.le_of_lt (Nat.lt_of_lt_of_le hi h.len)
  have hacc : oriAcc 256 bs i < limbBase ^ 8 := ori_pad_lt bs hb i hi28 (Nat.le_of_lt hi)
  have hmem : bs[i] ∈ bs := List.getElem_mem hi
  have hble : bs[i] ≤ 255 := h.byte _ hmem
  have hblimb : bs[i] < limbBase := byte_lt_base hble
  have hsum_eq : oriAcc 256 bs i * 256 + bs[i] = oriAcc 256 bs (i + 1) :=
    (oriAcc_succ 256 bs i hi).symm
  have hi1 : i + 1 ≤ 28 := Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hi h.len)
  have hnext : oriAcc 256 bs (i + 1) < limbBase ^ 8 :=
    ori_pad_lt bs hb (i + 1) hi1 (Nat.succ_le_of_lt hi)
  have hprod : 256 * oriAcc 256 bs i < limbBase ^ 8 := by
    have hleP : 256 * oriAcc 256 bs i ≤ oriAcc 256 bs i * 256 + bs[i] := by
      rw [Nat.mul_comm]
      exact Nat.le_add_right _ _
    rw [hsum_eq] at hleP
    exact Nat.lt_of_le_of_lt hleP hnext
  have hfitsMul : FitsLen ((natLimbs (oriAcc 256 bs i)).length + 1) := by
    have hlen := natLimbs_length_le (oriAcc 256 bs i) 8 hacc
    exact fits_le9 (Nat.succ_le_succ hlen)
  have hfitsAdd : FitsLen
      (max (natLimbs (256 * oriAcc 256 bs i)).length (natLimbs (bs[i])).length + 1) := by
    have h1 := natLimbs_length_le (256 * oriAcc 256 bs i) 8 hprod
    have h2 := natLimbs_length_le (bs[i]) 8 (lt_limb8_of_lt_limb hblimb)
    have hmax := (Nat.max_le).mpr ⟨h1, h2⟩
    exact fits_le9 (Nat.succ_le_succ hmax)
  rw [show bigOf [256] = bigOf (natLimbs 256) from by
    rw [natLimbs_of_pos_lt 256 (by decide) two56_lt_limb]]
  rw [big_mul_nat 256 (oriAcc 256 bs i) two56_lt_limb hfitsMul, ok_bind]
  have hat := atL_embed bs i hi
  rw [ofNat_eq_natCast i] at hat
  rw [hat, ok_bind]
  rw [big_from_int_refines (bs[i]) (fits_byte hble), ok_bind]
  rw [show bigOf (limbsOfNat (bs[i])) = bigOf (natLimbs (bs[i])) from by
    rw [limbsOfNat_eq_natLimbs hblimb]]
  rw [big_add_nat (256 * oriAcc 256 bs i) (bs[i]) hfitsAdd, ok_bind]
  rw [show 256 * oriAcc 256 bs i + bs[i] = oriAcc 256 bs (i + 1) from by
    rw [Nat.mul_comm, hsum_eq]]
  rw [pure_eq_ok]
  simp only [ok_bind]
  by_cases heq : i = bs.length - 1
  · have hbeq : ((i : Int) == ((bs.length - 1 : Nat) : Int)) = true := by
      simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (i : Int) ≠ ((bs.length - 1 : Nat) : Int) :=
      fun hq => heq (Int.ofNat.inj hq)
    have hbeq : ((i : Int) == ((bs.length - 1 : Nat) : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((i : Int) == ((bs.length - 1 : Nat) : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one i (FitsLen.of_le fits28 hi1)
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- `big_from_be` agrees with `fromBE` on `BePadWf` (length `≤ 28`). -/
theorem big_from_be_pad (bs : List Nat) (h : BePadWf bs) :
    Megadreifach.big_from_be (embed bs) = .ok (bigOf (natLimbs (fromBE bs))) := by
  unfold Megadreifach.big_from_be
  rw [big_zero_spec, ok_bind, two56_refines, ok_bind, listLen_embed]
  cases hlen : bs.length with
  | zero =>
    have hempty : bs = [] := List.length_eq_zero.mp hlen
    subst hempty
    rw [show SudoRt.subI (Int.ofNat 0) (1 : Int) = .ok (-1) from subI_zero_one,
      ok_bind]
    dsimp
    rw [except_bind_pure]
    have hgt : (0 : Int) > (-1) := by decide
    rw [show (1 : Nat) = fuelRange (0 : Int) (-1) from (fuelRange_gt hgt).symm]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed ([] : List Nat)) (bigOf [256]) (-1))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · rw [asc_break (0 : Int) (-1) (bigOf []) _ _ _ hgt
          (beFromStep_gt (embed ([] : List Nat)) (bigOf [256]) (-1) 0 (bigOf []) hgt),
        pure_eq_ok, fromBE_nil, natLimbs_zero]
  | succ k =>
    have hpos : 0 < k + 1 := Nat.succ_pos k
    have hfits : FitsLen (k + 1) :=
      FitsLen.of_le fits28 (by rw [← hlen]; exact h.len)
    rw [subI_ofNat_one (k + 1) hpos hfits, ok_bind]
    dsimp
    rw [fuelRange_eq (0 : Int) (k : Int), except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed bs) (bigOf [256]) (k : Int))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · have hstate :
          ((0 : Int), bigOf []) =
            (Int.ofNat 0, bigOf (natLimbs (oriAcc 256 bs 0))) := by
        rw [oriAcc_zero, natLimbs_zero]
        rfl
      rw [hstate]
      apply chain_loop
        (f := fun j => bigOf (natLimbs (oriAcc 256 bs j)))
        (fromN := 0) (toN := k)
        (hle := Nat.zero_le _)
        (goal := .ok (bigOf (natLimbs (fromBE bs))))
      · intro i _hlo hhi
        have hi : i < bs.length := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        have hs := bePadStep bs h i hi
        have hto : bs.length - 1 = k := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        rw [hto] at hs
        exact hs
      · have hk : k + 1 = bs.length := hlen.symm
        rw [hk, fromBE_eq_acc, pure_eq_ok]

/-- Same refinement on a nonnegative `Array Int` in `WellFormedBePad`. -/
theorem big_from_be_pad_array (a : Array Int) (h : WellFormedBePad a) :
    Megadreifach.big_from_be a = .ok (bigOf (natLimbs (fromBE (decode a)))) := by
  have hr := big_from_be_pad (decode a) (bePad_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2
