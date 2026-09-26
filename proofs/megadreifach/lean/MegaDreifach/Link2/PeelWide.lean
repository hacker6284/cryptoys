/-
  LINK 2. `peel_leading` of every rank that fits in the limb cap of `d!`.

  For `d ≤ 12` the cap is one limb (`n < 10^9`), already
  `peel_leading_limb`. For `13 ≤ d ≤ 19` the cap is two limbs
  (`n < 10^18`). For `20 ≤ d ≤ 26` the cap is three limbs
  (`n < 10^27`). On each cap the factoradic digit `n / d!` is one
  limb, so this is every digit, including `q ≥ 2`.

  The new multiply is one limb times the factorial (the emitted order
  is digit × `d!`). The product stays inside the same limb cap, and
  `mag_sub` may borrow.

  Not `d ≥ 27`. Not `27!`. Not `51!`. Not a 28-byte `big_from_be`.
  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.PeelOneThree

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

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

private theorem addI_zero_zero : SudoRt.addI (0 : Int) (0 : Int) = .ok (0 : Int) := by
  erw [addI_ofNat 0 0 FitsLen.zero]
  simp

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem addI_one_two : SudoRt.addI (1 : Int) (2 : Int) = .ok (3 : Int) := by
  have h : FitsLen (1 + 2) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 2 h]
  rfl

private theorem addI_one_three : SudoRt.addI (1 : Int) (3 : Int) = .ok (4 : Int) := by
  have h : FitsLen (1 + 3) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 3 h]
  rfl

private theorem addI_nat_zero (n : Nat) (h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

private theorem addI_zero_nat (n : Nat) (h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  rfl

private theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

private theorem subI_four_one : SudoRt.subI (4 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen 4 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 4 1 h (by decide)]
  rfl

private theorem filledL_three :
    SudoRt.filledL (3 : Int) (0 : Int) = .ok (Array.mkArray 3 (0 : Int)) := by
  erw [filledL_ofNat 3 (0 : Int)]

private theorem filledL_four :
    SudoRt.filledL (4 : Int) (0 : Int) = .ok (Array.mkArray 4 (0 : Int)) := by
  erw [filledL_ofNat 4 (0 : Int)]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem fits2 : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits3 : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits4 : FitsLen 4 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits27 : FitsLen 27 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_lt_sq {n : Nat} (h : n < limbBase ^ 2) : FitsLen n :=
  FitsLen.of_le (by unfold FitsLen; exact limb_sq_fits) (Nat.le_of_lt h)

private theorem mul_limb_lt (q x : Nat) (hq : q < limbBase) (hx : x < limbBase) :
    q * x < limbBase ^ 2 := by
  have hq' : q ≤ limbBase - 1 := by omega
  have hx' : x ≤ limbBase - 1 := by omega
  have hmul : q * x ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul hq' hx'
  have hconst : (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hmul hconst

private theorem sum_lt_sq (q x c : Nat) (hq : q < limbBase) (hx : x < limbBase)
    (hc : c < limbBase) : q * x + c < limbBase ^ 2 := by
  have hq' : q ≤ limbBase - 1 := by omega
  have hx' : x ≤ limbBase - 1 := by omega
  have hc' : c ≤ limbBase - 1 := by omega
  have hmul : q * x ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul hq' hx'
  have hsum : q * x + c ≤ (limbBase - 1) * (limbBase - 1) + (limbBase - 1) :=
    Nat.add_le_add hmul hc'
  have hconst : (limbBase - 1) * (limbBase - 1) + (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hsum hconst

private theorem pack3_re (a b c : Nat) :
    a + limbBase * b + limbBase ^ 2 * c = a + limbBase * (b + limbBase * c) := by
  calc
    a + limbBase * b + limbBase ^ 2 * c
        = a + (limbBase * b + limbBase ^ 2 * c) := Nat.add_assoc _ _ _
    _ = a + (limbBase * b + limbBase * (limbBase * c)) := by
          rw [limbBase_pow2, Nat.mul_assoc]
    _ = a + limbBase * (b + limbBase * c) := by
          rw [← Nat.mul_add]

private theorem mod_add_mul (d q : Nat) (hd : d < limbBase) :
    (d + limbBase * q) % limbBase = d := by
  have hmul : (limbBase * q) % limbBase = 0 := Nat.mul_mod_right limbBase q
  rw [Nat.add_mod, hmul, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hd]

private theorem div_add_mul (d q : Nat) (hd : d < limbBase) :
    (d + limbBase * q) / limbBase = q := by
  rw [Nat.add_comm, Nat.mul_add_div limbBase_pos q d, Nat.div_eq_of_lt hd, Nat.add_zero]

private theorem two_lt_sq (lo hi : Nat) (hlo : lo < limbBase) (hhi : hi < limbBase) :
    lo + limbBase * hi < limbBase ^ 2 := by
  rw [limbBase_pow2]
  calc
    lo + limbBase * hi < limbBase + limbBase * hi := Nat.add_lt_add_right hlo _
    _ = limbBase * (hi + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ limbBase * limbBase := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhi)

private theorem mul_horner3 (q lo mid hi : Nat) :
    q * (lo + limbBase * mid + limbBase ^ 2 * hi) =
      q * lo + limbBase * (q * mid) + limbBase ^ 2 * (q * hi) := by
  calc
    q * (lo + limbBase * mid + limbBase ^ 2 * hi)
        = q * (lo + limbBase * mid) + q * (limbBase ^ 2 * hi) := by rw [Nat.mul_add]
    _ = q * lo + q * (limbBase * mid) + q * (limbBase ^ 2 * hi) := by
          rw [Nat.mul_add, Nat.add_assoc]
    _ = q * lo + limbBase * (q * mid) + limbBase ^ 2 * (q * hi) := by
          rw [Nat.mul_left_comm q limbBase mid, Nat.mul_left_comm q (limbBase ^ 2) hi]

private theorem schoolbook3 (q lo mid hi : Nat) :
    q * lo + limbBase * (q * mid) + limbBase ^ 2 * (q * hi) =
      (q * lo) % limbBase +
        limbBase * ((q * mid + (q * lo) / limbBase) % limbBase) +
        limbBase ^ 2 *
          ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase) +
        limbBase ^ 3 *
          ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) / limbBase) := by
  let c0 := (q * lo) / limbBase
  let d0 := (q * lo) % limbBase
  let c1 := (q * mid + c0) / limbBase
  let d1 := (q * mid + c0) % limbBase
  let c2 := (q * hi + c1) / limbBase
  let d2 := (q * hi + c1) % limbBase
  have e0 : q * lo = d0 + limbBase * c0 := (Nat.mod_add_div (q * lo) limbBase).symm
  have e1 : q * mid + c0 = d1 + limbBase * c1 :=
    (Nat.mod_add_div (q * mid + c0) limbBase).symm
  have e2 : q * hi + c1 = d2 + limbBase * c2 :=
    (Nat.mod_add_div (q * hi + c1) limbBase).symm
  have hpow : limbBase ^ 2 * limbBase = limbBase ^ 3 := (Nat.pow_succ limbBase 2).symm
  have p2 : d0 + limbBase * c0 + limbBase * (q * mid) =
      d0 + limbBase * (c0 + q * mid) := by
    rw [Nat.add_assoc, ← Nat.mul_add]
  have p3 : d0 + limbBase * (c0 + q * mid) = d0 + limbBase * (q * mid + c0) := by
    rw [Nat.add_comm c0]
  have p5 : d0 + limbBase * (d1 + limbBase * c1) =
      d0 + (limbBase * d1 + limbBase * (limbBase * c1)) := by
    rw [Nat.mul_add]
  have p6 : limbBase * (limbBase * c1) = limbBase ^ 2 * c1 := by
    rw [← Nat.mul_assoc, limbBase_pow2]
  have p8 : d0 + limbBase * d1 + limbBase ^ 2 * c1 + limbBase ^ 2 * (q * hi) =
      d0 + limbBase * d1 + limbBase ^ 2 * (c1 + q * hi) := by
    rw [Nat.add_assoc (d0 + limbBase * d1) (limbBase ^ 2 * c1) (limbBase ^ 2 * (q * hi)),
      ← Nat.mul_add (limbBase ^ 2) c1 (q * hi)]
  have p9 : c1 + q * hi = q * hi + c1 := Nat.add_comm _ _
  have p11 : limbBase ^ 2 * (d2 + limbBase * c2) =
      limbBase ^ 2 * d2 + limbBase ^ 2 * (limbBase * c2) := Nat.mul_add _ _ _
  have p12 : limbBase ^ 2 * (limbBase * c2) = limbBase ^ 3 * c2 := by
    rw [← Nat.mul_assoc, hpow]
  calc
    q * lo + limbBase * (q * mid) + limbBase ^ 2 * (q * hi)
        = d0 + limbBase * c0 + limbBase * (q * mid) + limbBase ^ 2 * (q * hi) := by
          rw [e0]
    _ = d0 + limbBase * (c0 + q * mid) + limbBase ^ 2 * (q * hi) :=
          congrArg (fun t => t + limbBase ^ 2 * (q * hi)) p2
    _ = d0 + limbBase * (q * mid + c0) + limbBase ^ 2 * (q * hi) :=
          congrArg (fun t => t + limbBase ^ 2 * (q * hi)) p3
    _ = d0 + limbBase * (d1 + limbBase * c1) + limbBase ^ 2 * (q * hi) := by
          rw [e1]
    _ = d0 + (limbBase * d1 + limbBase * (limbBase * c1)) + limbBase ^ 2 * (q * hi) :=
          congrArg (fun t => t + limbBase ^ 2 * (q * hi)) p5
    _ = d0 + (limbBase * d1 + limbBase ^ 2 * c1) + limbBase ^ 2 * (q * hi) := by
          rw [p6]
    _ = d0 + limbBase * d1 + limbBase ^ 2 * c1 + limbBase ^ 2 * (q * hi) := by
          rw [← Nat.add_assoc d0 (limbBase * d1) (limbBase ^ 2 * c1)]
    _ = d0 + limbBase * d1 + limbBase ^ 2 * (c1 + q * hi) := p8
    _ = d0 + limbBase * d1 + limbBase ^ 2 * (q * hi + c1) := by rw [p9]
    _ = d0 + limbBase * d1 + limbBase ^ 2 * (d2 + limbBase * c2) := by rw [e2]
    _ = d0 + limbBase * d1 + (limbBase ^ 2 * d2 + limbBase ^ 2 * (limbBase * c2)) := by
          rw [p11]
    _ = d0 + limbBase * d1 + (limbBase ^ 2 * d2 + limbBase ^ 3 * c2) := by rw [p12]
    _ = d0 + limbBase * d1 + limbBase ^ 2 * d2 + limbBase ^ 3 * c2 := by
          rw [← Nat.add_assoc]

private theorem mul_horner2 (q lo hi : Nat) :
    q * (lo + limbBase * hi) = q * lo + limbBase * (q * hi) := by
  rw [Nat.mul_add, Nat.mul_left_comm q limbBase hi]

private theorem schoolbook2 (q lo hi : Nat) :
    q * lo + limbBase * (q * hi) =
      (q * lo) % limbBase +
        limbBase * ((q * hi + (q * lo) / limbBase) % limbBase) +
        limbBase ^ 2 * ((q * hi + (q * lo) / limbBase) / limbBase) := by
  let c0 := (q * lo) / limbBase
  let d0 := (q * lo) % limbBase
  let c1 := (q * hi + c0) / limbBase
  let d1 := (q * hi + c0) % limbBase
  have e0 : q * lo = d0 + limbBase * c0 := (Nat.mod_add_div (q * lo) limbBase).symm
  have e1 : q * hi + c0 = d1 + limbBase * c1 :=
    (Nat.mod_add_div (q * hi + c0) limbBase).symm
  have p2 : d0 + limbBase * c0 + limbBase * (q * hi) =
      d0 + limbBase * (c0 + q * hi) := by
    rw [Nat.add_assoc, ← Nat.mul_add]
  have p3 : c0 + q * hi = q * hi + c0 := Nat.add_comm _ _
  have p5 : limbBase * (limbBase * c1) = limbBase ^ 2 * c1 := by
    rw [← Nat.mul_assoc, limbBase_pow2]
  calc
    q * lo + limbBase * (q * hi)
        = d0 + limbBase * c0 + limbBase * (q * hi) := by rw [e0]
    _ = d0 + limbBase * (c0 + q * hi) := p2
    _ = d0 + limbBase * (q * hi + c0) := by rw [p3]
    _ = d0 + limbBase * (d1 + limbBase * c1) := by rw [e1]
    _ = d0 + (limbBase * d1 + limbBase * (limbBase * c1)) := by rw [Nat.mul_add]
    _ = d0 + (limbBase * d1 + limbBase ^ 2 * c1) := by rw [p5]
    _ = d0 + limbBase * d1 + limbBase ^ 2 * c1 := by rw [← Nat.add_assoc]

private theorem zeros4_size0 : 0 < (Array.mkArray 4 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros4_set0 (x : Nat) :
    (Array.mkArray 4 (0 : Int)).set ⟨0, zeros4_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

private theorem embed4_set1 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, v, y, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem embed4_set2 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨2, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem zeros3_size0 : 0 < (Array.mkArray 3 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros3_set0 (x : Nat) :
    (Array.mkArray 3 (0 : Int)).set ⟨0, zeros3_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

private theorem embed3_set1 (x y z v : Nat) :
    (embed [x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem dropTrail_pad0_3 (a b c : Nat) (hc : c ≠ 0) :
    dropTrail [a, b, c, 0] = [a, b, c] := by
  simp [dropTrail, hc]

private theorem dropTrail_pad0_2 (a b : Nat) (hb : b ≠ 0) :
    dropTrail [a, b, 0] = [a, b] := by
  simp [dropTrail, hb]

private theorem mulK_idle (out : Array Int) (k : Nat) :
    mulKStep (Int.ofNat k) (Int.ofNat k, out, (0 : Int)) =
      .ok (SudoRt.Flow.brk (Int.ofNat k, out, (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hngt : ¬ (k : Int) > (k : Int) := Int.lt_irrefl _
  rw [if_neg hngt]
  simp only [show decide ((0 : Int) > 0) = false from by decide, decide_False,
    Bool.false_eq_true, ite_false, bind_pure_flow]
  have hbeq : ((k : Int) == (k : Int)) = true := by simp [beq_int_iff]
  rw [if_pos hbeq]
  exact pure_eq_ok _

private theorem runLoopOn_two {σ ρ α} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 2 step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s 1 step after onRet := by
  rw [show (2 : Nat) = 1 + 1 from rfl]
  exact runLoopOn_succ s0 1 step after onRet

private theorem runLoopOn_one {σ ρ α} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 1 step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s 0 step after onRet := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  exact runLoopOn_succ s0 0 step after onRet

set_option maxHeartbeats 8000000 in
private theorem mulStep_q3 (q lo mid hi : Nat)
    (hq : q < limbBase) (hlo : lo < limbBase) (hmid : mid < limbBase) (hhi : hi < limbBase)
    (hcarry :
      (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) / limbBase = 0) :
    mulIStep (bigOf [q]) (bigOf [lo, mid, hi]) (0 : Int)
        ((0 : Int), Array.mkArray 4 (0 : Int)) =
      .ok (SudoRt.Flow.brk ((0 : Int),
        embed [(q * lo) % limbBase,
          (q * mid + (q * lo) / limbBase) % limbBase,
          (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase,
          0])) := by
  have hc0 : (q * lo) / limbBase < limbBase :=
    div_lt_of_lt_mul limbBase_pos (mul_limb_lt q lo hq hlo)
  have hfitLo : FitsLen (q * lo) := fits_lt_sq (mul_limb_lt q lo hq hlo)
  have hfitMid0 : FitsLen (q * mid) := fits_lt_sq (mul_limb_lt q mid hq hmid)
  have hfitHi0 : FitsLen (q * hi) := fits_lt_sq (mul_limb_lt q hi hq hhi)
  have hsum1 : q * mid + (q * lo) / limbBase < limbBase ^ 2 :=
    sum_lt_sq q mid ((q * lo) / limbBase) hq hmid hc0
  have hfitSum1 : FitsLen (q * mid + (q * lo) / limbBase) := fits_lt_sq hsum1
  have hc1 : (q * mid + (q * lo) / limbBase) / limbBase < limbBase :=
    div_lt_of_lt_mul limbBase_pos hsum1
  have hsum2 :
      q * hi + (q * mid + (q * lo) / limbBase) / limbBase < limbBase ^ 2 :=
    sum_lt_sq q hi ((q * mid + (q * lo) / limbBase) / limbBase) hq hhi hc1
  have hfitSum2 :
      FitsLen (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) :=
    fits_lt_sq hsum2
  have hlenb : SudoRt.listLen (embed [lo, mid, hi]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_three_one, ok_bind]
  dsimp
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 4 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 4 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [q] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, mid, hi] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_zero]
  erw [mulI_ofNat q lo hfitLo]
  rw [ok_bind]
  erw [addI_zero_nat (q * lo) hfitLo]
  rw [ok_bind]
  erw [addI_nat_zero (q * lo) hfitLo]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (q * lo)]
  rw [ok_bind]
  erw [putL_ofNat (Array.mkArray 4 (0 : Int)) 0
    (Int.ofNat ((q * lo) % limbBase)) zeros4_size0]
  rw [ok_bind]
  erw [divI_nat_base (q * lo)]
  rw [ok_bind, zeros4_set0 ((q * lo) % limbBase), bind_pure_flow, addI_zero_one]
  simp only [ok_bind, pure_eq_ok]
  rw [runLoopOn_two]
  dsimp
  have hat1 : SudoRt.atL (embed [(q * lo) % limbBase, 0, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [(q * lo) % limbBase, 0, 0, 0] 1 (by simp)]
    simp
  rw [addI_zero_one, ok_bind, hat1, ok_bind]
  erw [atL_embed [lo, mid, hi] 1 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat q mid hfitMid0]
  rw [ok_bind]
  erw [addI_zero_nat (q * mid) hfitMid0]
  rw [ok_bind]
  erw [addI_ofNat (q * mid) ((q * lo) / limbBase) hfitSum1]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (q * mid + (q * lo) / limbBase)]
  rw [ok_bind]
  have hsz1 : 1 < (embed [(q * lo) % limbBase, 0, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [(q * lo) % limbBase, 0, 0, 0]) 1
    (Int.ofNat ((q * mid + (q * lo) / limbBase) % limbBase)) hsz1]
  rw [ok_bind]
  erw [divI_nat_base (q * mid + (q * lo) / limbBase)]
  rw [ok_bind,
    embed4_set1 ((q * lo) % limbBase) 0 0 0
      ((q * mid + (q * lo) / limbBase) % limbBase),
    ok_bind, addI_one_one]
  simp only [ok_bind, pure_eq_ok]
  rw [runLoopOn_one]
  dsimp
  have hat2 : SudoRt.atL
      (embed [(q * lo) % limbBase, (q * mid + (q * lo) / limbBase) % limbBase, 0, 0])
      (2 : Int) = .ok (0 : Int) := by
    erw [atL_embed [(q * lo) % limbBase, (q * mid + (q * lo) / limbBase) % limbBase, 0, 0]
      2 (by simp)]
    simp
  erw [addI_zero_nat 2 fits2]
  rw [ok_bind]
  erw [hat2]
  rw [ok_bind]
  erw [atL_embed [lo, mid, hi] 2 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat q hi hfitHi0]
  rw [ok_bind]
  erw [addI_zero_nat (q * hi) hfitHi0]
  rw [ok_bind]
  erw [addI_ofNat (q * hi) ((q * mid + (q * lo) / limbBase) / limbBase) hfitSum2]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (q * hi + (q * mid + (q * lo) / limbBase) / limbBase)]
  rw [ok_bind]
  have hsz2 : 2 < (embed [(q * lo) % limbBase,
      (q * mid + (q * lo) / limbBase) % limbBase, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [(q * lo) % limbBase,
      (q * mid + (q * lo) / limbBase) % limbBase, 0, 0]) 2
    (Int.ofNat ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase)) hsz2]
  rw [ok_bind]
  erw [divI_nat_base (q * hi + (q * mid + (q * lo) / limbBase) / limbBase)]
  rw [ok_bind, hcarry,
    embed4_set2 ((q * lo) % limbBase)
      ((q * mid + (q * lo) / limbBase) % limbBase) 0 0
      ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase)]
  simp only [ok_bind]
  have hlenOut : SudoRt.listLen (embed [(q * lo) % limbBase,
      (q * mid + (q * lo) / limbBase) % limbBase,
      (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase, 0]) = (4 : Int) := by
    rw [listLen_embed]; rfl
  erw [addI_zero_nat 3 fits3]
  rw [ok_bind, hlenOut, subI_four_one, ok_bind]
  dsimp
  rw [runLoopOn_one]
  erw [mulK_idle (embed [(q * lo) % limbBase,
      (q * mid + (q * lo) / limbBase) % limbBase,
      (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase, 0]) 3]
  simp only [match_ok_brk, pure_eq_ok, toPure_eq_ok, ok_bind]

/-- One-limb × three-limb product that stays below `10^27`. The fourth scratch limb is zero. -/
private theorem big_mul_q3_limbs (q lo mid hi : Nat)
    (hq0 : 0 < q) (hq : q < limbBase)
    (hlo : lo < limbBase) (hmid : mid < limbBase) (hhi0 : 0 < hi) (hhi : hi < limbBase)
    (hp : q * (lo + limbBase * mid + limbBase ^ 2 * hi) < limbBase ^ 3) :
    Megadreifach.big_mul (bigOf [q]) (bigOf [lo, mid, hi]) =
      .ok (bigNat (q * (lo + limbBase * mid + limbBase ^ 2 * hi))) := by
  have hpow : limbBase ^ 2 * hi ≤ lo + limbBase * mid + limbBase ^ 2 * hi :=
    Nat.le_add_left _ _
  have hhi1 : limbBase ^ 2 ≤ limbBase ^ 2 * hi := by
    simpa using Nat.mul_le_mul_left (limbBase ^ 2) (Nat.succ_le_of_lt hhi0)
  have hvge : limbBase ^ 2 ≤ lo + limbBase * mid + limbBase ^ 2 * hi :=
    Nat.le_trans hhi1 hpow
  have hpge : limbBase ^ 2 ≤ q * (lo + limbBase * mid + limbBase ^ 2 * hi) := by
    have hv : lo + limbBase * mid + limbBase ^ 2 * hi ≤
        (lo + limbBase * mid + limbBase ^ 2 * hi) * q :=
      Nat.le_mul_of_pos_right (lo + limbBase * mid + limbBase ^ 2 * hi) hq0
    have hv' : lo + limbBase * mid + limbBase ^ 2 * hi ≤
        q * (lo + limbBase * mid + limbBase ^ 2 * hi) := by
      rwa [← Nat.mul_comm q (lo + limbBase * mid + limbBase ^ 2 * hi)] at hv
    exact Nat.le_trans hvge hv'
  have hbook := schoolbook3 q lo mid hi
  have hexpand := mul_horner3 q lo mid hi
  have hval :
      q * (lo + limbBase * mid + limbBase ^ 2 * hi) =
        (q * lo) % limbBase +
          limbBase * ((q * mid + (q * lo) / limbBase) % limbBase) +
          limbBase ^ 2 *
            ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase) +
          limbBase ^ 3 *
            ((q * hi + (q * mid + (q * lo) / limbBase) / limbBase) / limbBase) :=
    hexpand.trans hbook
  let c2 := (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) / limbBase
  let d0 := (q * lo) % limbBase
  let d1 := (q * mid + (q * lo) / limbBase) % limbBase
  let d2 := (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) % limbBase
  have hd0 : d0 < limbBase := Nat.mod_lt _ limbBase_pos
  have hd1 : d1 < limbBase := Nat.mod_lt _ limbBase_pos
  have hd2 : d2 < limbBase := Nat.mod_lt _ limbBase_pos
  have hnamed : q * (lo + limbBase * mid + limbBase ^ 2 * hi) =
      d0 + limbBase * d1 + limbBase ^ 2 * d2 + limbBase ^ 3 * c2 := hval
  have hc2 : c2 = 0 := by
    by_cases hz : c2 = 0
    · exact hz
    · have hcpos : 0 < c2 := Nat.pos_of_ne_zero hz
      have hmul : limbBase ^ 3 ≤ limbBase ^ 3 * c2 :=
        Nat.le_mul_of_pos_right (limbBase ^ 3) hcpos
      have hge : limbBase ^ 3 ≤
          d0 + limbBase * d1 + limbBase ^ 2 * d2 + limbBase ^ 3 * c2 :=
        Nat.le_trans hmul
          (Nat.le_add_left (limbBase ^ 3 * c2)
            (d0 + limbBase * d1 + limbBase ^ 2 * d2))
      have hlt := hp
      rw [hnamed] at hlt
      exact absurd hge (Nat.not_le_of_lt hlt)
  have hd2ne : d2 ≠ 0 := by
    by_cases hz : d2 = 0
    · have hpack : q * (lo + limbBase * mid + limbBase ^ 2 * hi) = d0 + limbBase * d1 := by
        have h := hnamed
        rw [hc2, hz] at h
        simpa [Nat.mul_zero, Nat.add_zero] using h
      have hlt : d0 + limbBase * d1 < limbBase ^ 2 := two_lt_sq d0 d1 hd0 hd1
      have hge := hpge
      rw [hpack] at hge
      exact absurd hge (Nat.not_le_of_lt hlt)
    · exact hz
  have hcarry : (q * hi + (q * mid + (q * lo) / limbBase) / limbBase) / limbBase = 0 := hc2
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [lo, mid, hi]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq3 : SudoRt.SEq.beq (3 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq1]
  dsimp
  rw [hlenb, hbeq3]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_one_three, ok_bind, filledL_four, ok_bind, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [q]) (bigOf [lo, mid, hi]) (0 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rw [runLoopOn_one, mulStep_q3 q lo mid hi hq hlo hmid hhi hcarry]
  simp only [match_ok_brk]
  rw [make_big_false [d0, d1, d2, 0] fits4, ok_bind, dropTrail_pad0_3 d0 d1 d2 hd2ne,
    pure_eq_ok]
  have hpack : q * (lo + limbBase * mid + limbBase ^ 2 * hi) =
      d0 + limbBase * (d1 + limbBase * d2) := by
    have h := hnamed
    rw [hc2] at h
    simp only [Nat.mul_zero, Nat.add_zero] at h
    rwa [pack3_re d0 d1 d2] at h
  have hmod : (q * (lo + limbBase * mid + limbBase ^ 2 * hi)) % limbBase = d0 := by
    rw [hpack, mod_add_mul d0 (d1 + limbBase * d2) hd0]
  have hdiv1 : (q * (lo + limbBase * mid + limbBase ^ 2 * hi)) / limbBase =
      d1 + limbBase * d2 := by
    rw [hpack, div_add_mul d0 (d1 + limbBase * d2) hd0]
  have hmod2 : ((q * (lo + limbBase * mid + limbBase ^ 2 * hi)) / limbBase) % limbBase = d1 := by
    rw [hdiv1, mod_add_mul d1 d2 hd1]
  have hdiv2 : ((q * (lo + limbBase * mid + limbBase ^ 2 * hi)) / limbBase) / limbBase = d2 := by
    rw [hdiv1, div_add_mul d1 d2 hd1]
  rw [bigNat_three (q * (lo + limbBase * mid + limbBase ^ 2 * hi)) hpge hp, hmod, hmod2, hdiv2]

/--
  `big_mul (bigNat q) (bigNat a) = bigNat (q * a)` when `q` is one limb,
  `a` is three limbs, and the product stays below `10^27`.
-/
theorem big_mul_small_three (q a : Nat) (hq0 : 0 < q) (hq : q < limbBase)
    (hge : limbBase ^ 2 ≤ a) (hlt : a < limbBase ^ 3) (hp : q * a < limbBase ^ 3) :
    Megadreifach.big_mul (bigNat q) (bigNat a) = .ok (bigNat (q * a)) := by
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hmid : (a / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : (a / limbBase) / limbBase < limbBase := by
    have hdiv : a / limbBase < limbBase ^ 2 := by
      rw [limbBase_pow3] at hlt
      exact div_lt_of_lt_mul limbBase_pos hlt
    rw [limbBase_pow2] at hdiv
    exact div_lt_of_lt_mul limbBase_pos hdiv
  have hhi0 : 0 < (a / limbBase) / limbBase := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_pos_of_le (Nat.pow_pos limbBase_pos) hge
  have hrepr :
      a % limbBase + limbBase * ((a / limbBase) % limbBase) +
        limbBase ^ 2 * ((a / limbBase) / limbBase) = a := by
    have hmidv : (a / limbBase) % limbBase + limbBase * ((a / limbBase) / limbBase) =
        a / limbBase := Nat.mod_add_div (a / limbBase) limbBase
    calc
      a % limbBase + limbBase * ((a / limbBase) % limbBase) +
          limbBase ^ 2 * ((a / limbBase) / limbBase)
        = a % limbBase + (limbBase * ((a / limbBase) % limbBase) +
            limbBase * (limbBase * ((a / limbBase) / limbBase))) := by
          rw [← Nat.mul_assoc, ← limbBase_pow2, Nat.add_assoc]
      _ = a % limbBase + limbBase * ((a / limbBase) % limbBase +
            limbBase * ((a / limbBase) / limbBase)) := by rw [← Nat.mul_add]
      _ = a % limbBase + limbBase * (a / limbBase) := by rw [hmidv]
      _ = a := Nat.mod_add_div a limbBase
  rw [bigNat_limb q hq (Nat.ne_of_gt hq0), bigNat_three a hge hlt]
  have hp' : q * (a % limbBase + limbBase * ((a / limbBase) % limbBase) +
      limbBase ^ 2 * ((a / limbBase) / limbBase)) < limbBase ^ 3 := by
    simpa [hrepr] using hp
  have hmul := big_mul_q3_limbs q (a % limbBase) ((a / limbBase) % limbBase)
    ((a / limbBase) / limbBase) hq0 hq hlo hmid hhi0 hhi hp'
  simpa [hrepr] using hmul

set_option maxHeartbeats 8000000 in
private theorem mulStep_q2 (q lo hi : Nat)
    (hq : q < limbBase) (hlo : lo < limbBase) (hhi : hi < limbBase)
    (hcarry : (q * hi + (q * lo) / limbBase) / limbBase = 0) :
    mulIStep (bigOf [q]) (bigOf [lo, hi]) (0 : Int)
        ((0 : Int), Array.mkArray 3 (0 : Int)) =
      .ok (SudoRt.Flow.brk ((0 : Int),
        embed [(q * lo) % limbBase, (q * hi + (q * lo) / limbBase) % limbBase, 0])) := by
  have hc0 : (q * lo) / limbBase < limbBase :=
    div_lt_of_lt_mul limbBase_pos (mul_limb_lt q lo hq hlo)
  have hfitLo : FitsLen (q * lo) := fits_lt_sq (mul_limb_lt q lo hq hlo)
  have hfitHi0 : FitsLen (q * hi) := fits_lt_sq (mul_limb_lt q hi hq hhi)
  have hsum1 : q * hi + (q * lo) / limbBase < limbBase ^ 2 :=
    sum_lt_sq q hi ((q * lo) / limbBase) hq hhi hc0
  have hfitSum1 : FitsLen (q * hi + (q * lo) / limbBase) := fits_lt_sq hsum1
  have hlenb : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by
    rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_two_one, ok_bind]
  dsimp
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 3 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 3 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [q] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, hi] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_zero]
  erw [mulI_ofNat q lo hfitLo]
  rw [ok_bind]
  erw [addI_zero_nat (q * lo) hfitLo]
  rw [ok_bind]
  erw [addI_nat_zero (q * lo) hfitLo]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (q * lo)]
  rw [ok_bind]
  erw [putL_ofNat (Array.mkArray 3 (0 : Int)) 0
    (Int.ofNat ((q * lo) % limbBase)) zeros3_size0]
  rw [ok_bind]
  erw [divI_nat_base (q * lo)]
  rw [ok_bind, zeros3_set0 ((q * lo) % limbBase), bind_pure_flow, addI_zero_one]
  simp only [ok_bind, pure_eq_ok]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat1 : SudoRt.atL (embed [(q * lo) % limbBase, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [(q * lo) % limbBase, 0, 0] 1 (by simp)]
    simp
  rw [addI_zero_one, ok_bind, hat1, ok_bind]
  erw [atL_embed [lo, hi] 1 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat q hi hfitHi0]
  rw [ok_bind]
  erw [addI_zero_nat (q * hi) hfitHi0]
  rw [ok_bind]
  erw [addI_ofNat (q * hi) ((q * lo) / limbBase) hfitSum1]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (q * hi + (q * lo) / limbBase)]
  rw [ok_bind]
  have hsz1 : 1 < (embed [(q * lo) % limbBase, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [(q * lo) % limbBase, 0, 0]) 1
    (Int.ofNat ((q * hi + (q * lo) / limbBase) % limbBase)) hsz1]
  rw [ok_bind]
  erw [divI_nat_base (q * hi + (q * lo) / limbBase)]
  rw [ok_bind, hcarry, embed3_set1 ((q * lo) % limbBase) 0 0
      ((q * hi + (q * lo) / limbBase) % limbBase)]
  simp only [ok_bind]
  have hlenOut : SudoRt.listLen
      (embed [(q * lo) % limbBase, (q * hi + (q * lo) / limbBase) % limbBase, 0]) =
      (3 : Int) := by
    rw [listLen_embed]; rfl
  erw [addI_zero_nat 2 fits2]
  rw [ok_bind, hlenOut, subI_three_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  erw [mulK_idle (embed [(q * lo) % limbBase, (q * hi + (q * lo) / limbBase) % limbBase, 0]) 2]
  simp only [match_ok_brk, pure_eq_ok, toPure_eq_ok, ok_bind]

/-- One-limb × two-limb product that stays below `10^18`. The third scratch limb is zero. -/
private theorem big_mul_q2_limbs (q lo hi : Nat)
    (hq0 : 0 < q) (hq : q < limbBase)
    (hlo : lo < limbBase) (hhi0 : 0 < hi) (hhi : hi < limbBase)
    (hp : q * (lo + limbBase * hi) < limbBase ^ 2) :
    Megadreifach.big_mul (bigOf [q]) (bigOf [lo, hi]) =
      .ok (bigNat (q * (lo + limbBase * hi))) := by
  have hvge : limbBase ≤ lo + limbBase * hi := by
    have hhi1 : limbBase ≤ limbBase * hi := by
      simpa using Nat.mul_le_mul_left limbBase (Nat.succ_le_of_lt hhi0)
    exact Nat.le_trans hhi1 (Nat.le_add_left _ _)
  have hpge : limbBase ≤ q * (lo + limbBase * hi) := by
    have hv : lo + limbBase * hi ≤ (lo + limbBase * hi) * q :=
      Nat.le_mul_of_pos_right (lo + limbBase * hi) hq0
    have hv' : lo + limbBase * hi ≤ q * (lo + limbBase * hi) := by
      rwa [← Nat.mul_comm q (lo + limbBase * hi)] at hv
    exact Nat.le_trans hvge hv'
  have hbook := schoolbook2 q lo hi
  have hexpand := mul_horner2 q lo hi
  have hval : q * (lo + limbBase * hi) =
      (q * lo) % limbBase +
        limbBase * ((q * hi + (q * lo) / limbBase) % limbBase) +
        limbBase ^ 2 * ((q * hi + (q * lo) / limbBase) / limbBase) :=
    hexpand.trans hbook
  let c1 := (q * hi + (q * lo) / limbBase) / limbBase
  let d0 := (q * lo) % limbBase
  let d1 := (q * hi + (q * lo) / limbBase) % limbBase
  have hd0 : d0 < limbBase := Nat.mod_lt _ limbBase_pos
  have hd1 : d1 < limbBase := Nat.mod_lt _ limbBase_pos
  have hnamed : q * (lo + limbBase * hi) =
      d0 + limbBase * d1 + limbBase ^ 2 * c1 := hval
  have hc1 : c1 = 0 := by
    by_cases hz : c1 = 0
    · exact hz
    · have hcpos : 0 < c1 := Nat.pos_of_ne_zero hz
      have hmul : limbBase ^ 2 ≤ limbBase ^ 2 * c1 :=
        Nat.le_mul_of_pos_right (limbBase ^ 2) hcpos
      have hge : limbBase ^ 2 ≤ d0 + limbBase * d1 + limbBase ^ 2 * c1 :=
        Nat.le_trans hmul (Nat.le_add_left (limbBase ^ 2 * c1) (d0 + limbBase * d1))
      rw [hnamed] at hp
      exact absurd hge (Nat.not_le_of_lt hp)
  have hd1ne : d1 ≠ 0 := by
    by_cases hz : d1 = 0
    · have hpack : q * (lo + limbBase * hi) = d0 := by
        have h := hnamed
        rw [hc1, hz] at h
        simpa [Nat.mul_zero, Nat.add_zero] using h
      have hlt : d0 < limbBase := hd0
      have hge := hpge
      rw [hpack] at hge
      exact absurd hge (Nat.not_le_of_lt hlt)
    · exact hz
  have hcarry : (q * hi + (q * lo) / limbBase) / limbBase = 0 := hc1
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq2 : SudoRt.SEq.beq (2 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq1]
  dsimp
  rw [hlenb, hbeq2]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_one_two, ok_bind, filledL_three, ok_bind, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [q]) (bigOf [lo, hi]) (0 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
    mulStep_q2 q lo hi hq hlo hhi hcarry]
  simp only [match_ok_brk]
  rw [make_big_false [d0, d1, 0] (fits_le3 (by simp [List.length_cons, List.length_nil])),
    ok_bind, dropTrail_pad0_2 d0 d1 hd1ne, pure_eq_ok]
  have hpack : q * (lo + limbBase * hi) = d0 + limbBase * d1 := by
    have h := hnamed
    rw [hc1] at h
    simpa [Nat.mul_zero, Nat.add_zero] using h
  have hmod : (q * (lo + limbBase * hi)) % limbBase = d0 := by
    rw [hpack, mod_add_mul d0 d1 hd0]
  have hdiv : (q * (lo + limbBase * hi)) / limbBase = d1 := by
    rw [hpack, div_add_mul d0 d1 hd0]
  rw [bigNat_two (q * (lo + limbBase * hi)) hpge hp, hmod, hdiv]

/--
  `big_mul (bigNat q) (bigNat a) = bigNat (q * a)` when `q` is one limb,
  `a` is two limbs, and the product stays below `10^18`.
-/
theorem big_mul_small_two (q a : Nat) (hq0 : 0 < q) (hq : q < limbBase)
    (hge : limbBase ≤ a) (hlt : a < limbBase ^ 2) (hp : q * a < limbBase ^ 2) :
    Megadreifach.big_mul (bigNat q) (bigNat a) = .ok (bigNat (q * a)) := by
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : a / limbBase < limbBase := by
    rw [limbBase_pow2] at hlt
    exact div_lt_of_lt_mul limbBase_pos hlt
  have hhi0 : 0 < a / limbBase := div_pos_of_le limbBase_pos hge
  have hrepr : a % limbBase + limbBase * (a / limbBase) = a := Nat.mod_add_div a limbBase
  rw [bigNat_limb q hq (Nat.ne_of_gt hq0), bigNat_two a hge hlt]
  have hp' : q * (a % limbBase + limbBase * (a / limbBase)) < limbBase ^ 2 := by
    simpa [hrepr] using hp
  have hmul := big_mul_q2_limbs q (a % limbBase) (a / limbBase) hq0 hq hlo hhi0 hhi hp'
  simpa [hrepr] using hmul

/-! ## Every digit on the proved limb cap -/

private theorem twentySix_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

private theorem factorial_13_ge : limbBase ≤ factorial 13 := by
  unfold factorial limbBase
  decide

private theorem factorial_19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_ge_sq : limbBase ^ 2 ≤ factorial 20 := by
  unfold factorial limbBase
  decide

private theorem factorial_26_lt_cube : factorial 26 < limbBase ^ 3 := by
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

private theorem factorial_lt_sq (n : Nat) (hn : n ≤ 19) : factorial n < limbBase ^ 2 :=
  Nat.lt_of_le_of_lt (factorial_mono n 19 hn) factorial_19_lt_sq

private theorem factorial_ge_limb (n : Nat) (hn : 13 ≤ n) : limbBase ≤ factorial n :=
  Nat.le_trans factorial_13_ge (factorial_mono 13 n hn)

private theorem factorial_lt_cube (n : Nat) (hn : n ≤ 26) : factorial n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt (factorial_mono n 26 hn) factorial_26_lt_cube

private theorem factorial_ge_sq (n : Nat) (hn : 20 ≤ n) : limbBase ^ 2 ≤ factorial n :=
  Nat.le_trans factorial_20_ge_sq (factorial_mono 20 n hn)

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem div_fact_step (n f : Nat) (hf0 : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf0]

private theorem div_anti (n a b : Nat) (ha : 0 < a) (hab : a ≤ b) : n / b ≤ n / a := by
  have hself : (n / b) * b ≤ n := Nat.div_mul_le_self n b
  have hmul : (n / b) * a ≤ (n / b) * b := Nat.mul_le_mul_left (n / b) hab
  have h : (n / b) * a ≤ n := Nat.le_trans hmul hself
  exact (Nat.le_div_iff_mul_le ha).mpr h

private theorem quot_sq_lt (n d : Nat) (hd : 13 ≤ d) (hn : n < limbBase ^ 2) :
    n / factorial d < limbBase := by
  have hf : limbBase ≤ factorial d := factorial_ge_limb d hd
  have hdiv : n / factorial d ≤ n / limbBase :=
    div_anti n limbBase (factorial d) limbBase_pos hf
  have hlt : n / limbBase < limbBase := by
    rw [limbBase_pow2] at hn
    exact div_lt_of_lt_mul limbBase_pos hn
  exact Nat.lt_of_le_of_lt hdiv hlt

private theorem quot_cube_lt (n d : Nat) (hd : 20 ≤ d) (hn : n < limbBase ^ 3) :
    n / factorial d < limbBase := by
  have hf : limbBase ^ 2 ≤ factorial d := factorial_ge_sq d hd
  have hdiv : n / factorial d ≤ n / limbBase ^ 2 :=
    div_anti n (limbBase ^ 2) (factorial d) (Nat.pow_pos limbBase_pos) hf
  have hlt : n / limbBase ^ 2 < limbBase := by
    rw [limbBase_pow3] at hn
    exact div_lt_of_lt_mul (Nat.pow_pos limbBase_pos) hn
  exact Nat.lt_of_le_of_lt hdiv hlt

private theorem prod_le_self (n d : Nat) :
    (n / d) * d ≤ n := Nat.div_mul_le_self n d

private theorem mod_eq_sub_mul (n d : Nat) (_hd : 0 < d) :
    n % d = n - (n / d) * d := by
  have hsum : (n / d) * d + n % d = n := by
    rw [Nat.mul_comm (n / d) d]
    exact Nat.div_add_mod n d
  have hle : (n / d) * d ≤ n := Nat.div_mul_le_self n d
  have hcancel : (n / d) * d + n % d = (n / d) * d + (n - (n / d) * d) := by
    rw [hsum, Nat.add_sub_of_le hle]
  exact Nat.add_left_cancel hcancel

private theorem peelDivStep_cube (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
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

private theorem peelDivStep_sq (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 19) (hn : n < limbBase ^ 2) :
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
    Nat.lt_of_le_of_lt
      (Nat.le_trans hhi (Nat.le_trans hd (by decide : (19 : Nat) ≤ 26)))
      twentySix_lt_limb
  have hq : n / factorial (f - 1) < limbBase ^ 2 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [show (f : Int) = Int.ofNat f from rfl,
    divmod_sq (n / factorial (f - 1)) f hq hf0 hflt, ok_bind]
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

private theorem peel_finish_cube (n d : Nat) (hdLo : 20 ≤ d) (hd : d ≤ 26)
    (hlo : factorial d ≤ n) (hhi : n < limbBase ^ 3) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat (n / factorial d))
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  let q := n / factorial d
  have hq0 : 0 < q := div_pos_of_le (factorial_pos d) hlo
  have hq : q < limbBase := quot_cube_lt n d hdLo hhi
  have hfLo : limbBase ^ 2 ≤ factorial d := factorial_ge_sq d hdLo
  have hfHi : factorial d < limbBase ^ 3 := factorial_lt_cube d hd
  have hnLo : limbBase ^ 2 ≤ n := Nat.le_trans hfLo hlo
  have hple : q * factorial d ≤ n := prod_le_self n (factorial d)
  have hp : q * factorial d < limbBase ^ 3 := Nat.lt_of_le_of_lt hple hhi
  have hpLo : limbBase ^ 2 ≤ q * factorial d := by
    have hfact : factorial d ≤ factorial d * q :=
      Nat.le_mul_of_pos_right (factorial d) hq0
    have hfact' : factorial d ≤ q * factorial d := by
      rwa [← Nat.mul_comm q (factorial d)] at hfact
    exact Nat.le_trans hfLo hfact'
  have hdiff : n - q * factorial d < limbBase ^ 3 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hhi
  have hmod : n % factorial d = n - q * factorial d :=
    mod_eq_sub_mul n (factorial d) (factorial_pos d)
  rw [limb_to_small_limb q hq, ok_bind, big_factorial_acc3 d hd, ok_bind]
  rw [show (q : Int) = Int.ofNat q from rfl, big_from_int_refines q (fits_of_lt_limb hq),
    ok_bind]
  have hlimbs : limbsOfNat q = [q] := by
    have hdiv : q / limbBase = 0 := Nat.div_eq_of_lt hq
    simp [limbsOfNat, Nat.ne_of_gt hq0, hdiv, Nat.mod_eq_of_lt hq]
  rw [hlimbs, show bigOf [q] = bigNat q from by rw [bigNat_limb q hq (Nat.ne_of_gt hq0)],
    big_mul_small_three q (factorial d) hq0 hq hfLo hfHi hp, ok_bind,
    mag_sub_three_le n (q * factorial d) hnLo hhi hpLo hp hple, ok_bind,
    make_big_false (limbsOfNat (n - q * factorial d)) (fits_le3 (limbsOfNat_len _)),
    ok_bind, limbsOfNat_trimmed (n - q * factorial d) hdiff, hmod, pure_eq_ok]
  rfl

private theorem peel_leading_cube_pos (n d : Nat) (hdLo : 20 ≤ d) (hd : d ≤ 26)
    (hlo : factorial d ≤ n) (hhi : n < limbBase ^ 3) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
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
    (goal := .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)))
  · intro i hlo' hhi'
    have hs := peelDivStep_cube n d i hlo' hhi' hd hhi
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · simp only [Prod.snd]
    rw [show (d + 1) - 1 = d from by omega]
    exact peel_finish_cube n d hdLo hd hlo hhi

private theorem peel_finish_sq (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < limbBase ^ 2) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat (n / factorial d))
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  let q := n / factorial d
  have hq0 : 0 < q := div_pos_of_le (factorial_pos d) hlo
  have hq : q < limbBase := quot_sq_lt n d hdLo hhi
  have hfLo : limbBase ≤ factorial d := factorial_ge_limb d hdLo
  have hfHi : factorial d < limbBase ^ 2 := factorial_lt_sq d hd
  have hnLo : limbBase ≤ n := Nat.le_trans hfLo hlo
  have hple : q * factorial d ≤ n := prod_le_self n (factorial d)
  have hp : q * factorial d < limbBase ^ 2 := Nat.lt_of_le_of_lt hple hhi
  have hpLo : limbBase ≤ q * factorial d := by
    have hfact : factorial d ≤ factorial d * q :=
      Nat.le_mul_of_pos_right (factorial d) hq0
    have hfact' : factorial d ≤ q * factorial d := by
      rwa [← Nat.mul_comm q (factorial d)] at hfact
    exact Nat.le_trans hfLo hfact'
  have hdiff : n - q * factorial d < limbBase ^ 3 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_trans hhi (by unfold limbBase; decide))
  have hmod : n % factorial d = n - q * factorial d :=
    mod_eq_sub_mul n (factorial d) (factorial_pos d)
  rw [limb_to_small_limb q hq, ok_bind, big_factorial_acc3 d (Nat.le_trans hd (by decide)),
    ok_bind]
  rw [show (q : Int) = Int.ofNat q from rfl, big_from_int_refines q (fits_of_lt_limb hq),
    ok_bind]
  have hlimbs : limbsOfNat q = [q] := by
    have hdiv : q / limbBase = 0 := Nat.div_eq_of_lt hq
    simp [limbsOfNat, Nat.ne_of_gt hq0, hdiv, Nat.mod_eq_of_lt hq]
  rw [hlimbs, show bigOf [q] = bigNat q from by rw [bigNat_limb q hq (Nat.ne_of_gt hq0)],
    big_mul_small_two q (factorial d) hq0 hq hfLo hfHi hp, ok_bind,
    mag_sub_two_le n (q * factorial d) hnLo hhi hpLo hp hple, ok_bind,
    make_big_false (limbsOfNat (n - q * factorial d)) (fits_le3 (limbsOfNat_len _)),
    ok_bind, limbsOfNat_trimmed (n - q * factorial d) hdiff, hmod, pure_eq_ok]
  rfl

private theorem peel_leading_sq_pos (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19)
    (hlo : factorial d ≤ n) (hhi : n < limbBase ^ 2) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
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
    (goal := .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)))
  · intro i hlo' hhi'
    have hs := peelDivStep_sq n d i hlo' hhi' hd hhi
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · simp only [Prod.snd]
    rw [show (d + 1) - 1 = d from by omega]
    exact peel_finish_sq n d hdLo hd hlo hhi

/--
  `peel_leading (bigNat n) d = (n % d!, n / d!)` for `20 ≤ d ≤ 26` and
  `n < 10^27`.

  `d! ≥ 10^18`, so the digit `n / d!` is one limb for every such rank.
  Digit `0` is the strict-below peel. Every positive digit, including
  `q ≥ 2`, multiplies that digit by the three-limb factorial and subtracts.
  Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_cube (n d : Nat) (hdLo : 20 ≤ d) (hd : d ≤ 26)
    (hn : n < limbBase ^ 3) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  by_cases hlt : n < factorial d
  · exact peel_leading_below_digit n d hd hlt
  · exact peel_leading_cube_pos n d hdLo hd (Nat.le_of_not_lt hlt) hn

/--
  `peel_leading (bigNat n) d = (n % d!, n / d!)` for `13 ≤ d ≤ 19` and
  `n < 10^18`.

  `d! ≥ 10^9`, so the digit is one limb. Every positive digit, including
  `q ≥ 2`, stays inside two limbs. Not `d ≥ 20`. Not `27!`. Not `51!`.
  Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_sq (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19)
    (hn : n < limbBase ^ 2) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  by_cases hlt : n < factorial d
  · exact peel_leading_below_digit n d (Nat.le_trans hd (by decide)) hlt
  · exact peel_leading_sq_pos n d hdLo hd (Nat.le_of_not_lt hlt) hn

/-- Limb cap of a factorial that this file can peel: `10^9`, `10^18`, or `10^27`. -/
def limbCap (d : Nat) : Nat :=
  if d ≤ 12 then limbBase else if d ≤ 19 then limbBase ^ 2 else limbBase ^ 3

/--
  `peel_leading (bigNat n) d = (n % d!, n / d!)` for every `d ≤ 26` and
  every rank below `limbCap d`.

  That is the whole factoradic digit, including `q ≥ 2`, on one limb
  (`d ≤ 12`), two limbs (`13 ≤ d ≤ 19`), and three limbs (`20 ≤ d ≤ 26`).
  Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_cap (n d : Nat) (hd : d ≤ 26) (hn : n < limbCap d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  by_cases h12 : d ≤ 12
  · have hn1 : n < limbBase := by
      rw [limbCap, if_pos h12] at hn
      exact hn
    exact peel_leading_limb n d h12 hn1
  · by_cases h19 : d ≤ 19
    · have hn2 : n < limbBase ^ 2 := by
        rw [limbCap, if_neg h12, if_pos h19] at hn
        exact hn
      exact peel_leading_sq n d (by omega) h19 hn2
    · have hn3 : n < limbBase ^ 3 := by
        rw [limbCap, if_neg h12, if_neg h19] at hn
        exact hn
      exact peel_leading_cube n d (by omega) hd hn3

end MegaDreifach.Link2
