/-
  LINK 2. `peel_leading` of a rank in `[d!, 2·d!)` for `d ≤ 19`.

  The factoradic digit is `n / d! = 1` and the remainder is `n - d!`
  (`n % d!`). `d!` itself is the old digit-1 corner (remainder 0). Every
  larger rank in the half-open interval has a positive remainder. For
  `13 ≤ d ≤ 19` both the rank and `d!` are two limbs (`2·19! < 10^18`).
  The division loop is `divmod_cube`. The closing product is the digit
  `1` times `d!`. `mag_sub` may borrow across the low limb.

  Not `d ≥ 20` (three-limb `d!`). Not a digit `q ≥ 2`. Not `n ≥ 2·d!`.
  Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.PeelCube
import MegaDreifach.Link2.PeelBelow

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  rfl

private theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

private theorem not_neg (k : Nat) : decide (Int.ofNat k < 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

private theorem neg_lt_zero (k : Nat) (hk : 0 < k) :
    decide (-(k : Int) < 0) = true := by
  rw [decide_eq_true_iff]
  have : (0 : Int) < (k : Int) := (ofNat_pos_iff k).mpr hk
  omega

private theorem append_dig (out : List Nat) (k : Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat k)).1 = embed (out ++ [k]) := by
  rw [appendL_spec]
  exact push_embed out k

private theorem narrowI_neg (k : Nat) (hk : k ≤ limbBase) :
    SudoRt.narrowI (-(k : Int)) = .ok (-(k : Int)) := by
  unfold SudoRt.narrowI
  have hB : SudoRt.i64Min ≤ -(limbBase : Int) := by
    unfold SudoRt.i64Min limbBase
    decide
  have hlo : SudoRt.i64Min ≤ -(k : Int) := by
    have hkI : (k : Int) ≤ (limbBase : Int) := Int.ofNat_le.mpr hk
    exact Int.le_trans hB (Int.neg_le_neg hkI)
  have hhi : -(k : Int) ≤ SudoRt.i64Max := by
    have h0 : -(k : Int) ≤ 0 := Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg k)
    have hmax : (0 : Int) ≤ SudoRt.i64Max := by decide
    exact Int.le_trans h0 hmax
  split
  · next ht =>
    simp only [Bool.or_eq_true, decide_eq_true_iff] at ht
    cases ht with
    | inl h => exact absurd h (Int.not_lt.mpr hlo)
    | inr h => exact absurd h (Int.not_lt.mpr hhi)
  · rfl

private theorem subI_under (a b : Nat) (hlt : a < b) (hb : b ≤ limbBase) :
    SudoRt.subI (Int.ofNat a) (Int.ofNat b) = .ok (-((b - a : Nat) : Int)) := by
  unfold SudoRt.subI
  have hle : a ≤ b := Nat.le_of_lt hlt
  have hsub : Int.ofNat a - Int.ofNat b = -Int.ofNat (b - a) := by
    rw [ofNat_eq_natCast a, ofNat_eq_natCast b, ofNat_eq_natCast (b - a)]
    have hb : (b : Int) - (a : Int) = ((b - a : Nat) : Int) := (Int.ofNat_sub hle).symm
    rw [← hb]
    omega
  rw [hsub]
  exact narrowI_neg (b - a) (Nat.le_trans (Nat.sub_le b a) hb)

private theorem subI_neg_ofNat (k b : Nat) (hsum : k + b ≤ limbBase) :
    SudoRt.subI (-(k : Int)) (Int.ofNat b) = .ok (-Int.ofNat (k + b)) := by
  unfold SudoRt.subI
  have hsub : -(k : Int) - Int.ofNat b = -Int.ofNat (k + b) := by
    rw [ofNat_eq_natCast b, ofNat_eq_natCast (k + b), Int.ofNat_add]
    omega
  rw [hsub]
  exact narrowI_neg (k + b) hsum

private theorem addI_neg_base (k : Nat) (hk0 : 0 < k) (hk : k ≤ limbBase) :
    SudoRt.addI (-(k : Int)) Megadreifach.limb_base =
      .ok (Int.ofNat (limbBase - k)) := by
  unfold SudoRt.addI
  rw [limb_base_eq]
  have hsum : -(k : Int) + (limbBase : Int) = Int.ofNat (limbBase - k) := by
    have : (limbBase : Int) - (k : Int) = Int.ofNat (limbBase - k) :=
      (Int.ofNat_sub hk).symm
    omega
  rw [hsum]
  exact narrowI_ofNat (limbBase - k) (fits_of_lt_limb (Nat.sub_lt limbBase_pos hk0))

/-! ## One schoolbook limb -/

/-- Subtract limb `b` and incoming borrow `br ∈ {0,1}` from limb `a`.
    The pair is `(digit, borrowOut)`. -/
def subDigit (a b br : Nat) : Nat × Nat :=
  if b + br ≤ a then (a - (b + br), 0) else (a + limbBase - (b + br), 1)

private theorem subDigit_spec (a b br : Nat)
    (ha : a < limbBase) (hb : b < limbBase) (hbr : br ≤ 1) :
    (subDigit a b br).1 < limbBase ∧ (subDigit a b br).2 ≤ 1 ∧
      a + (subDigit a b br).2 * limbBase = (subDigit a b br).1 + b + br := by
  unfold subDigit
  by_cases hle : b + br ≤ a
  · simp only [hle, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
    refine ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha, Nat.zero_le _, ?_⟩
    have : a - (b + br) + (b + br) = a := Nat.sub_add_cancel hle
    omega
  · simp only [hle, ↓reduceIte]
    have hbrB : b + br ≤ limbBase := by omega
    have hsum : b + br ≤ a + limbBase := by omega
    have hlt : a < b + br := Nat.lt_of_not_le hle
    have hd : a + limbBase - (b + br) < limbBase := by omega
    refine ⟨hd, Nat.le_refl _, ?_⟩
    have : a + limbBase - (b + br) + (b + br) = a + limbBase := Nat.sub_add_cancel hsum
    omega

private theorem mod_add_mul (d q : Nat) (hd : d < limbBase) :
    (d + limbBase * q) % limbBase = d := by
  have hmul : (limbBase * q) % limbBase = 0 := Nat.mul_mod_right limbBase q
  rw [Nat.add_mod, hmul, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hd]

private theorem div_add_mul (d q : Nat) (hd : d < limbBase) :
    (d + limbBase * q) / limbBase = q := by
  rw [Nat.add_comm, Nat.mul_add_div limbBase_pos q d, Nat.div_eq_of_lt hd, Nat.add_zero]

private theorem limbs_raw2 (v d0 d1 : Nat) (hv : v < limbBase ^ 2)
    (hd0 : d0 < limbBase) (_hd1 : d1 < limbBase)
    (hval : d0 + limbBase * d1 = v) :
    dropTrail [d0, d1] = limbsOfNat v := by
  have hmod : v % limbBase = d0 := by rw [← hval, mod_add_mul d0 d1 hd0]
  have hdiv : v / limbBase = d1 := by rw [← hval, div_add_mul d0 d1 hd0]
  rw [dropTrail_two, ← hmod, ← hdiv]
  unfold limbsOfNat
  by_cases hv0 : v = 0
  · simp [hv0]
  · simp only [hv0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq
      simp [hq, Nat.mod_eq_of_lt hlt, Nat.ne_of_gt (Nat.pos_of_ne_zero hv0)]
    · have hq2 : (v / limbBase) / limbBase = 0 := by
        rw [limbBase_pow2] at hv
        exact Nat.div_eq_of_lt (div_lt_of_lt_mul limbBase_pos hv)
      have hmid : (v / limbBase) % limbBase = v / limbBase :=
        Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq2)
      simp [hq, hq2, hmid, Nat.ne_of_gt (Nat.pos_of_ne_zero hq)]

private theorem limbs_raw3 (v d0 d1 d2 : Nat) (_hv : v < limbBase ^ 3)
    (hd0 : d0 < limbBase) (hd1 : d1 < limbBase) (_hd2 : d2 < limbBase)
    (hval : d0 + limbBase * (d1 + limbBase * d2) = v) :
    dropTrail [d0, d1, d2] = limbsOfNat v := by
  have hmod : v % limbBase = d0 := by
    rw [← hval, mod_add_mul d0 (d1 + limbBase * d2) hd0]
  have hdiv : v / limbBase = d1 + limbBase * d2 := by
    rw [← hval, div_add_mul d0 (d1 + limbBase * d2) hd0]
  have hmod1 : (v / limbBase) % limbBase = d1 := by
    rw [hdiv, mod_add_mul d1 d2 hd1]
  have hdiv1 : (v / limbBase) / limbBase = d2 := by
    rw [hdiv, div_add_mul d1 d2 hd1]
  have hdrop : dropTrail [d0, d1, d2] =
      dropTrail [v % limbBase, (v / limbBase) % limbBase, (v / limbBase) / limbBase] := by
    rw [hmod, hmod1, hdiv1]
  rw [hdrop]
  unfold limbsOfNat
  by_cases hv0 : v = 0
  · simp [hv0, dropTrail]
  · simp only [hv0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq
      have hnn : v % limbBase ≠ 0 := by
        rw [Nat.mod_eq_of_lt hlt]
        exact hv0
      simp [hq, dropTrail, hnn, Nat.zero_div]
    · simp only [hq, ↓reduceIte]
      by_cases hq2 : (v / limbBase) / limbBase = 0
      · have hnn : (v / limbBase) % limbBase ≠ 0 := by
          rw [Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq2)]
          exact hq
        simp [hq2, dropTrail, hnn]
      · have hnn : (v / limbBase) / limbBase ≠ 0 := hq2
        simp [hq2, dropTrail, hnn]

/-! ## `magSubStep` with a possible borrow -/

private theorem decide_len (i len : Nat) (h : i < len) :
    decide (Int.ofNat i < Int.ofNat len) = true := by
  rw [decide_eq_true_iff]
  exact (ofNat_lt_iff i len).mpr h

/-- One limb of `mag_sub`, both arrays long enough to contain index `i`.
    Incoming borrow is `0` or `1`. The outgoing digit is `subDigit`. -/
private theorem magSub_at
    (xs ys out : List Nat) (i toV ai bi br : Nat)
    (hi : i < xs.length) (hy : i < ys.length)
    (hxi : xs[i]'(hi) = ai) (hyi : ys[i]'(hy) = bi)
    (hai : ai < limbBase) (hbi : bi < limbBase) (hbr : br ≤ 1)
    (hiLe : i ≤ toV) (hfits : FitsLen (i + 1)) :
    magSubStep (embed xs) (embed ys) (Int.ofNat toV)
        (Int.ofNat i, (Int.ofNat br, embed out)) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          ((Int.ofNat i), ((Int.ofNat (subDigit ai bi br).2),
            embed (out ++ [(subDigit ai bi br).1]))))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          ((Int.ofNat (i + 1)), ((Int.ofNat (subDigit ai bi br).2),
            embed (out ++ [(subDigit ai bi br).1]))))) := by
  unfold magSubStep
  dsimp
  rw [show (i : Int) = Int.ofNat i from rfl, show (toV : Int) = Int.ofNat toV from rfl,
    show (br : Int) = Int.ofNat br from rfl]
  have hngt : ¬ Int.ofNat i > Int.ofNat toV := ofNat_not_gt hiLe
  rw [if_neg hngt]
  rw [atL_embed xs i hi, ok_bind, hxi]
  -- The five borrow shapes. Each ends at `pure (Flow.cont (digitBorrow, out'))`.
  by_cases hbr0 : br = 0
  · subst hbr0
    rw [subI_ofNat ai 0 (fits_of_lt_limb hai) (Nat.zero_le _), ok_bind, Nat.sub_zero]
    rw [listLen_embed, decide_len i ys.length hy]
    simp only [ite_true, ok_bind]
    rw [atL_embed ys i hy, ok_bind, hyi]
    by_cases hle : bi ≤ ai
    · rw [subI_ofNat ai bi (fits_of_lt_limb hai) hle, ok_bind, not_neg (ai - bi)]
      simp only [Bool.false_eq_true, ite_false]
      rw [append_dig out (ai - bi), bind_pure_flow]
      dsimp
      have hfits' : FitsLen (i + 1) := hfits
      by_cases heq : i = toV
      · subst heq
        have hbeq : ((i : Int) == (i : Int)) = true := by simp [beq_int_iff]
        rw [if_pos hbeq, pure_eq_ok]
        unfold subDigit
        simp [hle, Nat.zero_add]
      · have hneI : (i : Int) ≠ (toV : Int) := fun h => heq (Int.ofNat.inj h)
        have hbeq : ((i : Int) == (toV : Int)) = false := by
          simpa [beq_int_iff] using hneI
        have hneB : ¬ ((i : Int) == (toV : Int)) = true := by rw [hbeq]; decide
        erw [addI_ofNat_one i hfits']
        rw [if_neg hneB, ok_bind, pure_eq_ok]
        unfold subDigit
        simp [hle, heq, Nat.zero_add]
    · have hlt : ai < bi := Nat.lt_of_not_le hle
      rw [subI_under ai bi hlt (Nat.le_of_lt hbi), ok_bind,
        neg_lt_zero (bi - ai) (Nat.sub_pos_of_lt hlt)]
      simp only [ite_true]
      have hk : bi - ai ≤ limbBase := Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt hbi)
      have hk0 : 0 < bi - ai := Nat.sub_pos_of_lt hlt
      rw [addI_neg_base (bi - ai) hk0 hk, ok_bind]
      have hdig : limbBase - (bi - ai) = ai + limbBase - bi := by omega
      rw [hdig, append_dig out (ai + limbBase - bi), bind_pure_flow]
      dsimp
      by_cases heq : i = toV
      · subst heq
        have hbeq : ((i : Int) == (i : Int)) = true := by simp [beq_int_iff]
        rw [if_pos hbeq, pure_eq_ok]
        unfold subDigit
        simp [hle, Nat.not_le.mpr hlt, Nat.zero_add]
      · have hneI : (i : Int) ≠ (toV : Int) := fun h => heq (Int.ofNat.inj h)
        have hbeq : ((i : Int) == (toV : Int)) = false := by
          simpa [beq_int_iff] using hneI
        have hneB : ¬ ((i : Int) == (toV : Int)) = true := by rw [hbeq]; decide
        erw [addI_ofNat_one i hfits]
        rw [if_neg hneB, ok_bind, pure_eq_ok]
        unfold subDigit
        simp [hle, heq, Nat.not_le.mpr hlt, Nat.zero_add]
  · have hbr1 : br = 1 := by omega
    subst hbr1
    by_cases hai0 : ai = 0
    · subst hai0
      erw [subI_zero_one]
      rw [ok_bind]
      rw [listLen_embed, decide_len i ys.length hy]
      simp only [ite_true, ok_bind]
      rw [atL_embed ys i hy, ok_bind, hyi]
      have hsum : 1 + bi ≤ limbBase := by omega
      erw [subI_neg_ofNat 1 bi hsum]
      rw [ok_bind]
      erw [neg_lt_zero (1 + bi) (by omega)]
      simp only [ite_true]
      have hk0 : 0 < 1 + bi := by omega
      erw [addI_neg_base (1 + bi) hk0 hsum]
      rw [ok_bind]
      have hdig : limbBase - (1 + bi) = limbBase - (bi + 1) := by omega
      rw [hdig, append_dig out (limbBase - (bi + 1)), bind_pure_flow]
      dsimp
      by_cases heq : i = toV
      · subst heq
        have hbeq : ((i : Int) == (i : Int)) = true := by simp [beq_int_iff]
        rw [if_pos hbeq, pure_eq_ok]
        unfold subDigit
        simp [Nat.not_le.mpr (show 0 < bi + 1 by omega)]
      · have hneI : (i : Int) ≠ (toV : Int) := fun h => heq (Int.ofNat.inj h)
        have hbeq : ((i : Int) == (toV : Int)) = false := by
          simpa [beq_int_iff] using hneI
        have hneB : ¬ ((i : Int) == (toV : Int)) = true := by rw [hbeq]; decide
        erw [addI_ofNat_one i hfits]
        rw [if_neg hneB, ok_bind, pure_eq_ok]
        unfold subDigit
        simp [heq, Nat.not_le.mpr (show 0 < bi + 1 by omega)]
    · have hai1 : 1 ≤ ai := by omega
      rw [subI_ofNat ai 1 (fits_of_lt_limb hai) hai1, ok_bind]
      rw [listLen_embed, decide_len i ys.length hy]
      simp only [ite_true, ok_bind]
      rw [atL_embed ys i hy, ok_bind, hyi]
      have hai' : ai - 1 < limbBase := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hai
      by_cases hle : bi ≤ ai - 1
      · rw [subI_ofNat (ai - 1) bi (fits_of_lt_limb hai') hle, ok_bind,
          not_neg (ai - 1 - bi)]
        simp only [Bool.false_eq_true, ite_false]
        have hdig : ai - 1 - bi = ai - (bi + 1) := by omega
        rw [hdig, append_dig out (ai - (bi + 1)), bind_pure_flow]
        dsimp
        by_cases heq : i = toV
        · subst heq
          have hbeq : ((i : Int) == (i : Int)) = true := by simp [beq_int_iff]
          rw [if_pos hbeq, pure_eq_ok]
          unfold subDigit
          have hle' : bi + 1 ≤ ai := by omega
          simp [hle']
        · have hneI : (i : Int) ≠ (toV : Int) := fun h => heq (Int.ofNat.inj h)
          have hbeq : ((i : Int) == (toV : Int)) = false := by
            simpa [beq_int_iff] using hneI
          have hneB : ¬ ((i : Int) == (toV : Int)) = true := by rw [hbeq]; decide
          erw [addI_ofNat_one i hfits]
          rw [if_neg hneB, ok_bind, pure_eq_ok]
          unfold subDigit
          have hle' : bi + 1 ≤ ai := by omega
          simp [hle', heq]
      · have hlt : ai - 1 < bi := Nat.lt_of_not_le hle
        rw [subI_under (ai - 1) bi hlt (Nat.le_of_lt hbi), ok_bind,
          neg_lt_zero (bi - (ai - 1)) (Nat.sub_pos_of_lt hlt)]
        simp only [ite_true]
        have hk0 : 0 < bi - (ai - 1) := Nat.sub_pos_of_lt hlt
        have hk : bi - (ai - 1) ≤ limbBase :=
          Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt hbi)
        rw [addI_neg_base (bi - (ai - 1)) hk0 hk, ok_bind]
        have hdig : limbBase - (bi - (ai - 1)) = ai + limbBase - (bi + 1) := by omega
        rw [hdig, append_dig out (ai + limbBase - (bi + 1)), bind_pure_flow]
        dsimp
        by_cases heq : i = toV
        · subst heq
          have hbeq : ((i : Int) == (i : Int)) = true := by simp [beq_int_iff]
          rw [if_pos hbeq, pure_eq_ok]
          unfold subDigit
          have hlt' : ¬ bi + 1 ≤ ai := by omega
          simp [hlt']
        · have hneI : (i : Int) ≠ (toV : Int) := fun h => heq (Int.ofNat.inj h)
          have hbeq : ((i : Int) == (toV : Int)) = false := by
            simpa [beq_int_iff] using hneI
          have hneB : ¬ ((i : Int) == (toV : Int)) = true := by rw [hbeq]; decide
          erw [addI_ofNat_one i hfits]
          rw [if_neg hneB, ok_bind, pure_eq_ok]
          unfold subDigit
          have hlt' : ¬ bi + 1 ≤ ai := by omega
          simp [hlt', heq]

/-! ## Two-limb subtraction, borrow allowed -/

private theorem sub_add_reassoc (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  omega

private theorem sub_no_borrow2 (a0 a1 b0 b1 : Nat) (h0 : b0 ≤ a0) (h1 : b1 ≤ a1) :
    (a0 + limbBase * a1) - (b0 + limbBase * b1) =
      (a0 - b0) + limbBase * (a1 - b1) := by
  have hsum : a0 + limbBase * a1 =
      ((a0 - b0) + limbBase * (a1 - b1)) + (b0 + limbBase * b1) := by
    have hc0 := Nat.sub_add_cancel h0
    have hc1 := Nat.sub_add_cancel h1
    calc
      a0 + limbBase * a1
          = (a0 - b0 + b0) + limbBase * (a1 - b1 + b1) := by rw [hc0, hc1]
      _ = (a0 - b0 + b0) + (limbBase * (a1 - b1) + limbBase * b1) := by rw [Nat.mul_add]
      _ = ((a0 - b0) + limbBase * (a1 - b1)) + (b0 + limbBase * b1) := by
          omega
  rw [hsum, Nat.add_sub_cancel_right]

private theorem sub_borrow2 (a0 a1 b0 b1 : Nat)
    (_h0 : a0 < b0) (h1 : b1 + 1 ≤ a1) (hb0 : b0 ≤ limbBase) :
    (a0 + limbBase * a1) - (b0 + limbBase * b1) =
      (a0 + limbBase - b0) + limbBase * (a1 - (b1 + 1)) := by
  have ha1 : 1 ≤ a1 := Nat.le_trans (Nat.le_add_left 1 b1) h1
  have h1' : b1 ≤ a1 - 1 := by
    have : b1 + 1 ≤ a1 := h1
    omega
  have h0' : b0 ≤ a0 + limbBase := by omega
  have hid : a0 + limbBase * a1 = (a0 + limbBase) + limbBase * (a1 - 1) := by
    have hc := Nat.sub_add_cancel ha1
    calc
      a0 + limbBase * a1
          = a0 + limbBase * ((a1 - 1) + 1) := by rw [hc]
      _ = a0 + (limbBase * (a1 - 1) + limbBase * 1) := by rw [Nat.mul_add]
      _ = (a0 + limbBase) + limbBase * (a1 - 1) := by
          rw [Nat.mul_one]
          omega
  have htail : (a1 - 1) - b1 = a1 - (b1 + 1) := by omega
  have hsub := sub_no_borrow2 (a0 + limbBase) (a1 - 1) b0 b1 h0' h1'
  rw [← hid, htail] at hsub
  exact hsub


private theorem sub2_val (n0 n1 m0 m1 : Nat)
    (hn0 : n0 < limbBase) (_hn1 : n1 < limbBase)
    (hm0 : m0 < limbBase) (_hm1 : m1 < limbBase)
    (hle : m0 + limbBase * m1 ≤ n0 + limbBase * n1) :
    (subDigit n1 m1 (subDigit n0 m0 0).2).2 = 0 ∧
      (subDigit n0 m0 0).1 +
          limbBase * (subDigit n1 m1 (subDigit n0 m0 0).2).1 =
        (n0 + limbBase * n1) - (m0 + limbBase * m1) := by
  unfold subDigit
  by_cases hlo0 : m0 + 0 ≤ n0
  · simp only [hlo0, ↓reduceIte, Nat.zero_add]
    by_cases hlo1 : m1 ≤ n1
    · simp only [hlo1, ↓reduceIte, Nat.add_zero]
      refine ⟨trivial, ?_⟩
      exact (sub_no_borrow2 n0 n1 m0 m1 hlo0 hlo1).symm
    · have hlt1 : n1 < m1 := Nat.lt_of_not_le hlo1
      have : n0 + limbBase * n1 < m0 + limbBase * m1 := by
        have h1 : n1 + 1 ≤ m1 := Nat.succ_le_of_lt hlt1
        have hmul : limbBase * n1 + limbBase ≤ limbBase * m1 := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left _ h1
        have : n0 + limbBase * n1 < limbBase + limbBase * n1 := Nat.add_lt_add_right hn0 _
        omega
      exact absurd hle (Nat.not_le.mpr this)
  · have hlt0 : n0 < m0 := Nat.lt_of_not_le hlo0
    simp only [hlo0, ↓reduceIte, Nat.zero_add]
    by_cases hlo1 : m1 + 1 ≤ n1
    · simp only [hlo1, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      exact (sub_borrow2 n0 n1 m0 m1 hlt0 hlo1 (Nat.le_of_lt hm0)).symm
    · have hlt1 : n1 < m1 + 1 := Nat.lt_of_not_le hlo1
      have : n0 + limbBase * n1 < m0 + limbBase * m1 := by
        have h1 : n1 ≤ m1 := Nat.lt_succ_iff.mp hlt1
        have hmul : limbBase * n1 ≤ limbBase * m1 := Nat.mul_le_mul_left _ h1
        have : n0 + limbBase * n1 < m0 + limbBase * n1 := Nat.add_lt_add_right hlt0 _
        omega
      exact absurd hle (Nat.not_le.mpr this)

private theorem fits1 : FitsLen 1 := FitsLen.one

private theorem fits2 : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits3 : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

private theorem mag_sub_limbs2 (n0 n1 m0 m1 : Nat)
    (hn0 : n0 < limbBase) (hn1 : n1 < limbBase)
    (hm0 : m0 < limbBase) (hm1 : m1 < limbBase)
    (hle : m0 + limbBase * m1 ≤ n0 + limbBase * n1) :
    Megadreifach.mag_sub (embed [n0, n1]) (embed [m0, m1]) =
      .ok (embed (limbsOfNat ((n0 + limbBase * n1) - (m0 + limbBase * m1)))) := by
  have hsub := sub2_val n0 n1 m0 m1 hn0 hn1 hm0 hm1 hle
  have hbr1 : (subDigit n0 m0 0).2 ≤ 1 :=
    (subDigit_spec n0 m0 0 hn0 hm0 (by decide)).2.1
  let d0 := (subDigit n0 m0 0).1
  let br1 := (subDigit n0 m0 0).2
  let d1 := (subDigit n1 m1 br1).1
  have hz : (subDigit n1 m1 br1).2 = 0 := by simpa [d1, br1] using hsub.1
  have hdigits : d0 + limbBase * d1 =
      (n0 + limbBase * n1) - (m0 + limbBase * m1) := by
    simpa [d0, d1, br1] using hsub.2
  have hd0 : d0 < limbBase := (subDigit_spec n0 m0 0 hn0 hm0 (by decide)).1
  have hd1 : d1 < limbBase :=
    (subDigit_spec n1 m1 br1 hn1 hm1 hbr1).1
  have hv : (n0 + limbBase * n1) - (m0 + limbBase * m1) < limbBase ^ 2 := by
    have h0le : n0 ≤ limbBase - 1 := by
      have := Nat.succ_le_of_lt hn0
      omega
    have h1le : n1 ≤ limbBase - 1 := by
      have := Nat.succ_le_of_lt hn1
      omega
    have hle' : n0 + limbBase * n1 ≤ (limbBase - 1) + limbBase * (limbBase - 1) :=
      Nat.add_le_add h0le (Nat.mul_le_mul_left _ h1le)
    have hmax : (limbBase - 1) + limbBase * (limbBase - 1) < limbBase ^ 2 := by
      unfold limbBase
      decide
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) hle') hmax
  unfold Megadreifach.mag_sub
  rw [show SudoRt.listLen (embed [n0, n1]) = (2 : Int) by rw [listLen_embed]; rfl,
    subI_two_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := magSubStep (embed [n0, n1]) (embed [m0, m1]) (1 : Int))
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  have h0 := magSub_at [n0, n1] [m0, m1] [] 0 1 n0 m0 0
    (by simp) (by simp) (by simp) (by simp) hn0 hm0 (by decide) (by decide) fits1
  have hinit : ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      (Int.ofNat 0, (Int.ofNat 0, embed ([] : List Nat))) := by
    simp [embed_nil]
  rw [hinit]
  erw [h0]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  have h1 := magSub_at [n0, n1] [m0, m1] [d0] 1 1 n1 m1 br1
    (by simp) (by simp) (by simp) (by simp) hn1 hm1 hbr1 (Nat.le_refl _) fits2
  have hst1 : ((1 : Int), ((subDigit n0 m0 0).2 : Int), embed [(subDigit n0 m0 0).1]) =
      (Int.ofNat 1, (Int.ofNat br1), embed [d0]) := by
    dsimp [d0, br1]
  erw [hst1, h1]
  dsimp
  have hlist : embed [d0, (subDigit n1 m1 br1).1] = embed [d0, d1] := by
    dsimp [d1]
  rw [hlist, trim_embed [d0, d1] (fits_le3 (by simp)), ok_bind]
  have hraw := limbs_raw2 ((n0 + limbBase * n1) - (m0 + limbBase * m1)) d0 d1 hv
    hd0 hd1 (by simpa [Nat.mul_comm] using hdigits)
  rw [hraw, pure_eq_ok]

/-- `mag_sub` of two two-limb values. The subtrahend is at most the minuend.
    A borrow may cross the low limb. The trimmed limbs are `n - m`. -/
theorem mag_sub_two_le (n m : Nat)
    (hnLo : limbBase ≤ n) (hnHi : n < limbBase ^ 2)
    (hmLo : limbBase ≤ m) (hmHi : m < limbBase ^ 2)
    (hle : m ≤ n) :
    Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        (bigNat m).sudo_6BigInt_5limbs =
      .ok (embed (limbsOfNat (n - m))) := by
  have hn0 : n % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hn1 : n / limbBase < limbBase := by
    rw [limbBase_pow2] at hnHi
    exact div_lt_of_lt_mul limbBase_pos hnHi
  have hm0 : m % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hm1 : m / limbBase < limbBase := by
    rw [limbBase_pow2] at hmHi
    exact div_lt_of_lt_mul limbBase_pos hmHi
  have hnval : n % limbBase + limbBase * (n / limbBase) = n := Nat.mod_add_div n limbBase
  have hmval : m % limbBase + limbBase * (m / limbBase) = m := Nat.mod_add_div m limbBase
  rw [bigNat_two n hnLo hnHi, bigNat_two m hmLo hmHi]
  dsimp [bigOf]
  have h := mag_sub_limbs2 (n % limbBase) (n / limbBase) (m % limbBase) (m / limbBase)
    hn0 hn1 hm0 hm1 (by simpa [hnval, hmval] using hle)
  simpa [hnval, hmval] using h

/-! ## `peel_leading` on `[d!, 2·d!)` -/

private theorem fits27 : FitsLen 27 := by
  unfold FitsLen i64MaxNat
  decide

private theorem twentySix_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

private theorem fact12_lt_limb : factorial 12 < limbBase := by
  unfold factorial limbBase
  decide

private theorem two_fact12_lt_limb : 2 * factorial 12 < limbBase := by
  unfold factorial limbBase
  decide

private theorem fact13_ge_limb : limbBase ≤ factorial 13 := by
  unfold factorial limbBase
  decide

private theorem fact19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem two_fact19_lt_sq : 2 * factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem factorial_le_succ (b : Nat) : factorial b ≤ factorial (b + 1) := by
  have hmul : factorial b ≤ factorial b * (b + 1) :=
    Nat.le_mul_of_pos_right (factorial b) (Nat.succ_pos b)
  rw [factorial_succ, Nat.mul_comm]
  exact hmul

private theorem factorial_mono (a b : Nat) (h : a ≤ b) : factorial a ≤ factorial b := by
  induction b generalizing a with
  | zero =>
    have : a = 0 := Nat.eq_zero_of_le_zero h
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hle : a ≤ b
    · exact Nat.le_trans (ih a hle) (factorial_le_succ b)
    · have heq : a = b + 1 := by omega
      subst heq
      exact Nat.le_refl _

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem div_fact_step (n f : Nat) (hf0 : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf0]

private theorem div_one_of_half (n d : Nat) (hpos : 0 < d)
    (hlo : d ≤ n) (hhi : n < 2 * d) : n / d = 1 := by
  have hmod : n % d < d := Nat.mod_lt _ hpos
  have hsum := Nat.div_add_mod n d
  by_cases hlt : n / d < 2
  · by_cases hgt : 0 < n / d
    · omega
    · have hzero : n / d = 0 := Nat.eq_zero_of_not_pos hgt
      have hmod_eq : n % d = n := by
        have hs := hsum
        rw [hzero, Nat.mul_zero, Nat.zero_add] at hs
        exact hs
      have hnlt : n < d := by
        rw [← hmod_eq]
        exact hmod
      omega
  · have h2 : 2 ≤ n / d := Nat.le_of_not_lt hlt
    have hmul : d * 2 ≤ d * (n / d) := Nat.mul_le_mul_left d h2
    have hle' : d * (n / d) ≤ n := by
      have := Nat.le_add_right (d * (n / d)) (n % d)
      simpa [hsum] using this
    have : 2 * d ≤ n := by
      rw [Nat.mul_comm] at hmul
      exact Nat.le_trans hmul hle'
    omega

private theorem mod_eq_sub_one (n d : Nat) (_hpos : 0 < d) (hdiv : n / d = 1) :
    n % d = n - d := by
  have hsum := Nat.div_add_mod n d
  rw [hdiv] at hsum
  have : d + n % d = n := by simpa [Nat.mul_one] using hsum
  omega

private theorem peelDivStep_one (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 26) (hn : n < limbBase ^ 3) :
    peelDivStep (Int.ofNat d)
        (Int.ofNat f, bigNat (n / factorial (f - 1))) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigNat (n / factorial f)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigNat (n / factorial f))) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) twentySix_lt_limb
  have hq : n / factorial (f - 1) < limbBase ^ 3 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [show (f : Int) = Int.ofNat f from rfl,
    divmod_cube (n / factorial (f - 1)) f hq hf0 hflt, ok_bind]
  rw [show ((bigNat ((n / factorial (f - 1)) / f),
        ((((n / factorial (f - 1)) % f : Nat) : Int))).1) =
      bigNat ((n / factorial (f - 1)) / f) from rfl,
    div_fact_step n f hf0, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : f = d
  · have hbeq : ((f : Int) == (d : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (f : Int) ≠ (d : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((f : Int) == (d : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((f : Int) == (d : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one f (FitsLen.of_le fits27 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_finish_one_two (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < 2 * factorial d) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat 1)
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat (n - factorial d), (1 : Int)) := by
  have h1 : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hfLo : limbBase ≤ factorial d :=
    Nat.le_trans fact13_ge_limb (factorial_mono 13 d hdLo)
  have hfHi : factorial d < limbBase ^ 2 :=
    Nat.lt_of_le_of_lt (factorial_mono d 19 hd) fact19_lt_sq
  have hnLo : limbBase ≤ n := Nat.le_trans hfLo hlo
  have hnHi : n < limbBase ^ 2 :=
    Nat.lt_trans hhi (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 (factorial_mono d 19 hd)) two_fact19_lt_sq)
  have hdiff : n - factorial d < limbBase ^ 3 := by
    have hpow : limbBase ^ 2 < limbBase ^ 3 := by
      unfold limbBase
      decide
    exact Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnHi) hpow
  rw [limb_to_small_limb 1 h1, ok_bind, big_factorial_two d hd, ok_bind]
  rw [show ((1 : Nat) : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one,
    ok_bind]
  have hlimbs : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1
    simp [limbsOfNat, hq, Nat.mod_eq_of_lt h1]
  rw [hlimbs, show bigOf [1] = bigNat 1 from by rw [bigNat_limb 1 h1 (by decide)],
    big_mul_one (factorial d) hfLo hfHi, ok_bind,
    mag_sub_two_le n (factorial d) hnLo hnHi hfLo hfHi hlo, ok_bind,
    make_big_false (limbsOfNat (n - factorial d)) (fits_le3 (limbsOfNat_len _)),
    ok_bind, limbsOfNat_trimmed (n - factorial d) hdiff, pure_eq_ok]
  rfl

private theorem peel_leading_one_wide (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < 2 * factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n - factorial d), (1 : Int)) := by
  have hn3 : n < limbBase ^ 3 := by
    have hsq : n < limbBase ^ 2 :=
      Nat.lt_trans hhi (Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_left 2 (factorial_mono d 19 hd)) two_fact19_lt_sq)
    have hpow : limbBase ^ 2 < limbBase ^ 3 := by
      unfold limbBase
      decide
    exact Nat.lt_trans hsq hpow
  unfold Megadreifach.peel_leading
  dsimp
  rw [fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := peelDivStep (d : Int))
    intro σ
    unfold peelDivStep
    dsimp
    rfl
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  have hdiv1 : n / factorial (2 - 1) = n := by
    have : factorial (2 - 1) = 1 := by simp [factorial]
    rw [this, Nat.div_one]
  have hpair :
      ((Int.ofNat 2, bigNat n) : Int × Megadreifach.BigInt) =
        (Int.ofNat 2, bigNat (n / factorial (2 - 1))) := by
    rw [hdiv1]
  rw [hpair]
  apply chain_loop
    (f := fun i => bigNat (n / factorial (i - 1)))
    (fromN := 2) (toN := d)
    (hle := by omega)
    (goal := .ok (bigNat (n - factorial d), (1 : Int)))
  · intro i hlo' hhi'
    have hd26 : d ≤ 26 := Nat.le_trans hd (by decide)
    have hs := peelDivStep_one n d i hlo' hhi' hd26 hn3
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · simp only [Prod.snd]
    rw [show (d + 1) - 1 = d from by omega,
      div_one_of_half n (factorial d) (factorial_pos d) hlo hhi]
    exact peel_finish_one_two n d hdLo hd hlo hhi

/--
  `peel_leading (bigNat n) d = (n - d!, 1)` when `d! ≤ n < 2·d!` and `d ≤ 19`.

  The factoradic digit is `1` and the remainder is `n % d! = n - d!`.
  For `d ≤ 12` the rank is still one limb (`2·12! < 10^9`). For
  `13 ≤ d ≤ 19` the rank and `d!` are two limbs (`2·19! < 10^18`), and
  the remainder may be positive. The closing product is the digit `1`.
  Not `d ≥ 20`. Not a digit `q ≥ 2`. Not `n ≥ 2·d!`. Not `27!`. Not `51!`.
  Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_one (n d : Nat) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < 2 * factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n - factorial d), (1 : Int)) := by
  by_cases hd12 : d ≤ 12
  · have hn : n < limbBase :=
      Nat.lt_trans hhi (Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_left 2 (factorial_mono d 12 hd12)) two_fact12_lt_limb)
    have h := peel_leading_limb n d hd12 hn
    have hdiv : n / factorial d = 1 :=
      div_one_of_half n (factorial d) (factorial_pos d) hlo hhi
    have hmod : n % factorial d = n - factorial d :=
      mod_eq_sub_one n (factorial d) (factorial_pos d) hdiv
    simpa [hdiv, hmod] using h
  · exact peel_leading_one_wide n d (by omega) hd hlo hhi

/-- Same peel, as the factoradic pair `(n % d!, n / d!)`. -/
theorem peel_leading_one_digit (n d : Nat) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < 2 * factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  have hdiv : n / factorial d = 1 :=
    div_one_of_half n (factorial d) (factorial_pos d) hlo hhi
  have hmod : n % factorial d = n - factorial d :=
    mod_eq_sub_one n (factorial d) (factorial_pos d) hdiv
  rw [hdiv, hmod]
  exact peel_leading_one n d hd hlo hhi

end MegaDreifach.Link2

