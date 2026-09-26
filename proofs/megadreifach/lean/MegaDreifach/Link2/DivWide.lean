/-
  LINK 2. `big_divmod_small` on a canonical limb list, divisor one limb.

  The dividend may have any number of base-`10^9` limbs. Each step's
  `rem * 10^9 + digit` stays below `10^18`, so it fits in an i64.
  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.NatLimbs
import MegaDreifach.Link2.Be
import MegaDreifach.Link2.Factorial

namespace MegaDreifach.Link2

private theorem limb_sq_le : limbBase ^ 2 ≤ i64MaxNat := by
  unfold i64MaxNat limbBase
  decide

private theorem rem_wide_fits (r : Nat) (hr : r < limbBase) : FitsLen (r * limbBase) := by
  have hle : r * limbBase ≤ (limbBase - 1) * limbBase :=
    Nat.mul_le_mul_right _ (by omega : r ≤ limbBase - 1)
  have hlt : (limbBase - 1) * limbBase < limbBase ^ 2 := by
    rw [limbBase_pow2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) limbBase_pos
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt)) limb_sq_le

private theorem cur_wide_fits (r x dv : Nat) (hr : r < dv) (hx : x < limbBase)
    (hd : dv < limbBase) : FitsLen (r * limbBase + x) := by
  have hrB : r < limbBase := Nat.lt_trans hr hd
  have hmul : FitsLen (r * limbBase) := rem_wide_fits r hrB
  have hle : r * limbBase + x ≤ (dv - 1) * limbBase + (limbBase - 1) := by
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
  have hconst : (dv - 1) * limbBase + limbBase = dv * limbBase := by
    cases dv with
    | zero => omega
    | succ dv =>
      rw [Nat.succ_sub_one]
      exact (Nat.succ_mul dv limbBase).symm
  have hlt : r * limbBase + x < dv * limbBase := by omega
  have hdv : dv * limbBase ≤ (limbBase - 1) * limbBase :=
    Nat.mul_le_mul_right _ (by omega)
  have hbase : (limbBase - 1) * limbBase < limbBase ^ 2 := by
    rw [limbBase_pow2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) limbBase_pos
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hdv (Nat.le_of_lt hbase))))
    limb_sq_le

/-- One descending step of `big_divmod_small` by a one-limb divisor. -/
def divGenStep (dv : Int) (limbs : Array Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Array Int × Int)) (Megadreifach.BigInt × Int)) :=
  if σ.1 < 0 then
    pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, σ.2.1, σ.2.2))
  else do
    let lift ←
      ((do
        let x ← SudoRt.mulI σ.2.2 Megadreifach.limb_base
        let d ← SudoRt.atL limbs σ.1
        let cur ← SudoRt.addI x d
        let qv ← SudoRt.divI cur dv
        let q ← SudoRt.putL σ.2.1 σ.1 qv
        let r ← SudoRt.modI cur dv
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (q, r))) :
        Except SudoRt.Trap
          (SudoRt.Flow (Array Int × Int) (Megadreifach.BigInt × Int)))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt × Int) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == 0) = true then
        pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
      else do
        let i' ← SudoRt.subI σ.1 1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (i', fs))

theorem divGenStep_at (dv : Nat) (xs : List Nat) (qArr : Array Int) (i r : Nat)
    (hd0 : 0 < dv) (hd : dv < limbBase)
    (hi : i < xs.length) (hr : r < dv) (hx : xs[i] < limbBase)
    (hsz : i < qArr.size) (hfiti : FitsLen i) :
    divGenStep (Int.ofNat dv) (embed xs) (Int.ofNat i, qArr, Int.ofNat r) =
      (let cur := r * limbBase + xs[i]
      let q' := qArr.set ⟨i, hsz⟩ (Int.ofNat (cur / dv))
      let r' := Int.ofNat (cur % dv)
      if i = 0 then
        .ok (SudoRt.Flow.brk (Int.ofNat 0, q', r'))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), q', r'))) := by
  unfold divGenStep
  dsimp
  rw [if_neg (Int.not_lt.mpr (Int.ofNat_zero_le i))]
  rw [limb_base_eq, ← ofNat_eq_natCast limbBase, ← ofNat_eq_natCast r,
    mulI_ofNat r limbBase (rem_wide_fits r (Nat.lt_trans hr hd)), ok_bind,
    ← ofNat_eq_natCast i, atL_embed xs i hi, ok_bind]
  have hcur : FitsLen (r * limbBase + xs[i]) := cur_wide_fits r (xs[i]) dv hr hx hd
  rw [addI_ofNat (r * limbBase) (xs[i]) hcur, ok_bind]
  erw [divI_ofNat (r * limbBase + xs[i]) (Nat.ne_of_gt hd0)]
  simp only [ok_bind]
  erw [putL_ofNat qArr i (Int.ofNat ((r * limbBase + xs[i]) / dv)) hsz]
  simp only [ok_bind]
  erw [modI_ofNat (r * limbBase + xs[i]) (Nat.ne_of_gt hd0)]
  simp only [ok_bind]
  by_cases hi0 : i = 0
  · simp [hi0]
    rfl
  · simp only [pure_bind]
    have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0) hfiti
    have hbeq : ((Int.ofNat i) == 0) = false := by
      simpa [beq_int_iff] using fun h : (i : Int) = 0 => hi0 (Int.ofNat.inj h)
    rw [hbeq, if_neg (by decide : ¬ ((false : Bool) = true))]
    erw [hsub, ok_bind]
    rw [if_neg hi0]
    simp only [pure]
    rfl

theorem big_divmod_empty (d : Nat) (hd0 : 0 < d) (hd : d < limbBase) :
    Megadreifach.big_divmod_small (bigOf []) (Int.ofNat d) =
      .ok (bigOf (natLimbs 0), (0 : Int)) := by
  simpa [natLimbs_zero] using divmod_zero d hd0 hd

end MegaDreifach.Link2
