/-
  LINK 2. `big_from_be` ≃ algebraic `fromBE` on short byte strings.

  Domain `BeShortWf`: length `≤ 3` and every byte `≤ 255`. Then
  `fromBE < 256^3 < 10^9`, so the value is one base-10^9 limb (the empty
  limb list when the value is zero). Each Horner step `acc * 256 + b`
  stays inside the proved one-limb multiply (`big_mul_acc`) and one-limb
  add (`big_add_small`).

  Length 4 is out: `256^4 > 10^9`. The 28-byte pad block is out. Not
  `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.FromBe

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

/-- `256^3 = 16_777_216` still fits in one limb. -/
theorem pow256_three_lt_limb : 256 ^ 3 < limbBase := by
  unfold limbBase
  decide

/-- `256^4` does not. Length 4 is outside this slice. -/
theorem pow256_four_ge_limb : limbBase ≤ 256 ^ 4 := by
  unfold limbBase
  decide

private theorem pow256_le {a b : Nat} (h : a ≤ b) : 256 ^ a ≤ 256 ^ b :=
  Nat.pow_le_pow_of_le_right (by decide : 256 > 0) h

private theorem fits3 : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits255 : FitsLen 255 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_byte {b : Nat} (hb : b ≤ 255) : FitsLen b :=
  FitsLen.of_le fits255 hb

private theorem two56_lt_limb : 256 < limbBase := by
  unfold limbBase
  decide

private theorem two56_nat : bigNat 256 = bigOf [256] :=
  bigNat_limb 256 two56_lt_limb (by decide)

/-- Trap-free domain for a one-limb `big_from_be`.

    Length `≤ 3` keeps every prefix of the base-256 Horner below `256^3`,
    hence below one limb. Bytes `≤ 255` are the digits `fromBE` expects. -/
structure BeShortWf (bs : List Nat) : Prop where
  len : bs.length ≤ 3
  byte : ∀ b ∈ bs, b ≤ 255

/-- Array-side short big-endian domain. -/
structure WellFormedBeShort (a : Array Int) : Prop where
  len : a.size ≤ 3
  nn : Nonneg a
  byte : ∀ x ∈ decode a, x ≤ 255

theorem beShort_decode (a : Array Int) (h : WellFormedBeShort a) :
    BeShortWf (decode a) where
  len := by
    have : (decode a).length = a.size := by simp [decode]
    rw [this]
    exact h.len
  byte := h.byte

private theorem byte_lt (bs : List Nat) (h : BeShortWf bs) :
    ∀ b ∈ bs, b < 256 := by
  intro b hb
  exact Nat.lt_of_le_of_lt (h.byte b hb) (by decide : 255 < 256)

private theorem fromBE_nil : fromBE [] = 0 := by
  simp [fromBE, mixEncode]

private theorem fromBE_eq_acc (bs : List Nat) :
    fromBE bs = oriAcc 256 bs bs.length := by
  rw [oriAcc, List.take_length]
  unfold fromBE
  exact (hornerAcc_mix 256 bs).symm

/-- A prefix of a short byte string is still one limb. -/
private theorem ori_short_lt (bs : List Nat) (hb : ∀ b ∈ bs, b < 256)
    (i : Nat) (hi3 : i ≤ 3) (hlen : i ≤ bs.length) :
    oriAcc 256 bs i < limbBase := by
  have h1 := oriAcc_lt (r := 256) bs hb i hlen
  have h2 : 256 ^ i ≤ 256 ^ 3 := pow256_le hi3
  exact Nat.lt_trans (Nat.lt_of_lt_of_le h1 h2) pow256_three_lt_limb

theorem fromBE_short_lt_limb (bs : List Nat) (h : BeShortWf bs) :
    fromBE bs < limbBase := by
  rw [fromBE_eq_acc]
  exact ori_short_lt bs (byte_lt bs h) bs.length h.len (Nat.le_refl _)

private theorem beFromStep_gt (bs : Array Int) (two56 : Megadreifach.BigInt)
    (toV i : Int) (n : Megadreifach.BigInt) (h : i > toV) :
    beFromStep bs two56 toV (i, n) = .ok (SudoRt.Flow.brk (i, n)) := by
  unfold beFromStep
  rw [if_pos h]
  rfl

/-- One Horner step `acc * 256 + byte` on a short string. -/
private theorem beShortStep (bs : List Nat) (h : BeShortWf bs) (i : Nat)
    (hi : i < bs.length) :
    beFromStep (embed bs) (bigOf [256]) (Int.ofNat (bs.length - 1))
        (Int.ofNat i, bigNat (oriAcc 256 bs i)) =
      if i = bs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (oriAcc 256 bs (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (oriAcc 256 bs (i + 1)))) := by
  unfold beFromStep
  dsimp
  have hlen3 : bs.length ≤ 3 := h.len
  have hle : i ≤ bs.length - 1 := by omega
  have hngt : ¬ (i : Int) > ((bs.length - 1 : Nat) : Int) := ofNat_not_gt hle
  rw [if_neg hngt]
  have hb := byte_lt bs h
  have hi3 : i ≤ 3 := by omega
  have hacc : oriAcc 256 bs i < limbBase :=
    ori_short_lt bs hb i hi3 (Nat.le_of_lt hi)
  have hmem : bs[i] ∈ bs := List.getElem_mem hi
  have hble : bs[i] ≤ 255 := h.byte _ hmem
  have h255 : 255 < limbBase := by unfold limbBase; decide
  have hblimb : bs[i] < limbBase := Nat.lt_of_le_of_lt hble h255
  have hsum_eq : oriAcc 256 bs i * 256 + bs[i] = oriAcc 256 bs (i + 1) :=
    (oriAcc_succ 256 bs i hi).symm
  have hi1 : i + 1 ≤ 3 := by omega
  have hsum : oriAcc 256 bs i * 256 + bs[i] < limbBase := by
    rw [hsum_eq]
    exact ori_short_lt bs hb (i + 1) hi1 (Nat.succ_le_of_lt hi)
  have hmul : oriAcc 256 bs i * 256 < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ (bs[i])) hsum
  rw [← two56_nat]
  rw [big_mul_acc (oriAcc 256 bs i) 256 (by decide) two56_lt_limb hacc, ok_bind]
  have hat := atL_embed bs i hi
  rw [ofNat_eq_natCast i] at hat
  rw [hat, ok_bind]
  rw [big_from_int_refines (bs[i]) (fits_byte hble), ok_bind]
  rw [show bigOf (limbsOfNat (bs[i])) = bigNat (bs[i]) from rfl]
  rw [big_add_small (oriAcc 256 bs i * 256) (bs[i]) hmul hblimb hsum, ok_bind,
    hsum_eq, pure_eq_ok]
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
    have hadd := addI_ofNat_one i (FitsLen.of_le fits3 hi1)
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- `big_from_be` agrees with `fromBE` on `BeShortWf`. -/
theorem big_from_be_short (bs : List Nat) (h : BeShortWf bs) :
    Megadreifach.big_from_be (embed bs) = .ok (bigNat (fromBE bs)) := by
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
        pure_eq_ok, fromBE_nil, bigNat_zero]
  | succ k =>
    have hpos : 0 < k + 1 := Nat.succ_pos k
    have hfits : FitsLen (k + 1) :=
      FitsLen.of_le fits3 (by rw [← hlen]; exact h.len)
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
            (Int.ofNat 0, bigNat (oriAcc 256 bs 0)) := by
        rw [oriAcc_zero, bigNat_zero]
        rfl
      rw [hstate]
      apply chain_loop
        (f := fun j => bigNat (oriAcc 256 bs j))
        (fromN := 0) (toN := k)
        (hle := Nat.zero_le _)
        (goal := .ok (bigNat (fromBE bs)))
      · intro i _hlo hhi
        have hi : i < bs.length := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        have hs := beShortStep bs h i hi
        have hto : bs.length - 1 = k := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        rw [hto] at hs
        exact hs
      · have hk : k + 1 = bs.length := hlen.symm
        rw [hk, fromBE_eq_acc, pure_eq_ok]

/-- Same refinement on a nonnegative `Array Int` in `WellFormedBeShort`. -/
theorem big_from_be_short_array (a : Array Int) (h : WellFormedBeShort a) :
    Megadreifach.big_from_be a = .ok (bigNat (fromBE (decode a))) := by
  have hr := big_from_be_short (decode a) (beShort_decode a h)
  simpa [embed_decode a h.nn] using hr

/-- One byte `≤ 255` is the nonzero (or zero) one-limb case. `fromBE [b] = b`. -/
theorem big_from_be_byte (b : Nat) (hb : b ≤ 255) :
    Megadreifach.big_from_be (embed [b]) = .ok (bigNat b) := by
  have hwf : BeShortWf [b] :=
    ⟨by simp, fun x hx => by
      simp at hx
      simpa [hx] using hb⟩
  have hr := big_from_be_short [b] hwf
  have hbe : fromBE [b] = b := by
    simp [fromBE, List.replicate, mixEncode, product]
  simpa [hbe] using hr

end MegaDreifach.Link2
