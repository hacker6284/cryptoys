/-
  LINK 2. Emitted bigint helpers on the pad domain (values that fit in an
  i64, at most three base-10^9 limbs) refine the algebraic limb model.
  Proof-only. Not collision resistance. Not `v_Hash`.
-/
import Megadreifach
import MegaDreifach.Link2.Bytes
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

def bigOf (xs : List Nat) : Megadreifach.BigInt where
  sudo_6BigInt_8negative := false
  sudo_6BigInt_5limbs := embed xs

theorem big_zero_spec :
    Megadreifach.big_zero = .ok (bigOf []) := by
  unfold Megadreifach.big_zero bigOf
  rfl

theorem push_embed (xs : List Nat) (b : Nat) :
    (embed xs).push (Int.ofNat b) = embed (xs ++ [b]) := by
  apply Array.ext'
  simp [embed, toList_push]

theorem limb_base_eq : Megadreifach.limb_base = (limbBase : Int) := rfl

/-- One peel of `big_from_int`'s `for peel = 1 to 3` body. -/
def fromIntStep (toV : Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt) :=
  let peel := σ.1
  let limbs := σ.2.1
  let m := σ.2.2
  do
    if peel > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (peel, (limbs, m)))
    else
      match ← ((do
        if decide (m > (0 : Int)) then
          do
            let r ← SudoRt.modI m Megadreifach.limb_base
            let limbs := (SudoRt.appendL limbs r).1
            let m ← SudoRt.divI m Megadreifach.limb_base
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (limbs, m))
        else
          pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (limbs, m))
      ) : Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (peel, fs))
      | .cont fs => do
          if peel == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (peel, fs))
          else do
            let i' ← SudoRt.addI peel (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

theorem fromIntStep_hit (peel : Nat) (limbs : List Nat) (m : Nat)
    (hlo : 1 ≤ peel) (hhi : peel ≤ 3) (_hm : FitsLen m) (hnext : FitsLen (peel + 1)) :
    fromIntStep 3 (Int.ofNat peel, (embed limbs, Int.ofNat m)) =
      let limbs' := if m = 0 then limbs else limbs ++ [m % limbBase]
      let m' := if m = 0 then 0 else m / limbBase
      if peel = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat peel, (embed limbs', Int.ofNat m')))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (peel + 1), (embed limbs', Int.ofNat m'))) := by
  unfold fromIntStep
  dsimp
  have hngt : ¬ (peel : Int) > (3 : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  by_cases hm0 : m = 0
  · have hdec : decide ((m : Int) > (0 : Int)) = false := by
      rw [hm0]
      decide
    rw [hdec, if_neg (by decide : ¬ (false = true))]
    erw [ok_bind]
    by_cases hp : peel = 3
    · subst hp
      simp [beq_int_iff, hm0]
      rfl
    · have hne : ¬ (peel : Int) = (3 : Int) := fun h => hp (Int.ofNat.inj h)
      have hadd := addI_ofNat_one peel hnext
      rw [ofNat_eq_natCast peel] at hadd
      dsimp
      rw [ite_int_beq, if_neg hne, hadd, ok_bind, if_neg hp]
      simp [hm0]
      rfl
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hdec : decide ((m : Int) > (0 : Int)) = true := by
      rw [decide_eq_true_eq]
      exact (ofNat_pos_iff m).mpr hpos
    rw [hdec, if_pos (rfl : true = true)]
    rw [limb_base_eq, modI_cast m (Nat.ne_of_gt limbBase_pos), ok_bind,
      divI_cast m (Nat.ne_of_gt limbBase_pos)]
    simp only [ok_bind, appendL_spec, push_embed]
    by_cases hp : peel = 3
    · subst hp
      simp [beq_int_iff, hm0]
      rfl
    · have hne : ¬ (peel : Int) = (3 : Int) := fun h => hp (Int.ofNat.inj h)
      have hadd := addI_ofNat_one peel hnext
      rw [ofNat_eq_natCast peel] at hadd
      erw [ok_bind]
      dsimp
      rw [ite_int_beq, if_neg hne, hadd, ok_bind, if_neg hp]
      simp [hm0]
      rfl

/-- Three peels of a value below `limbBase ^ 3` are `limbsOfNat`. -/
def peeled (v : Nat) : List Nat :=
  let a0 := v % limbBase
  let q0 := v / limbBase
  let a1 := q0 % limbBase
  let q1 := q0 / limbBase
  let a2 := q1 % limbBase
  if v = 0 then []
  else if q0 = 0 then [a0]
  else if q1 = 0 then [a0, a1]
  else [a0, a1, a2]

theorem peeled_eq_limbs (v : Nat) (hv : v < limbBase ^ 3) : peeled v = limbsOfNat v := by
  unfold peeled limbsOfNat
  by_cases h0 : v = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      by_cases hq1 : (v / limbBase) / limbBase = 0
      · simp [hq1]
      · have hq2 : (v / limbBase) / limbBase < limbBase := by
          have hqlt : v / limbBase < limbBase ^ 2 := by
            rw [limbBase_pow3] at hv
            exact div_lt_of_lt_mul limbBase_pos hv
          rw [limbBase_pow2] at hqlt
          exact div_lt_of_lt_mul limbBase_pos hqlt
        simp [hq1, Nat.mod_eq_of_lt hq2]

private theorem fits_quot {v : Nat} (hv : FitsLen v) : FitsLen (v / limbBase) :=
  FitsLen.of_le hv (Nat.div_le_self _ _)

private theorem fits_small (n : Nat) (h : n ≤ 3) : FitsLen (n + 1) := by
  have : n + 1 ≤ 4 := Nat.succ_le_succ h
  exact FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) this

theorem big_from_int_refines (v : Nat) (hv : FitsLen v) :
    Megadreifach.big_from_int (Int.ofNat v) = .ok (bigOf (limbsOfNat v)) := by
  have hv3 : v < limbBase ^ 3 := fitsLen_lt_limb3 hv
  unfold Megadreifach.big_from_int
  by_cases h0 : v = 0
  · subst h0
    have hb : SudoRt.SEq.beq (Int.ofNat 0) (0 : Int) = true := by
      rw [sEq_ofNat_zero]
      decide
    rw [hb, if_pos (rfl : true = true), big_zero_spec]
    simp [limbsOfNat, bigOf]
  · rw [sEq_ofNat_zero, decide_eq_false_iff_not.mpr h0,
      if_neg (by decide : ¬ (false = true))]
    have hnn : decide (Int.ofNat v ≥ (0 : Int)) = true := by
      rw [decide_eq_true_eq]
      exact Int.ofNat_zero_le _
    rw [hnn, sudoAssert_true, ok_bind]
    dsimp
    rw [show (1 : Int) = Int.ofNat 1 from rfl, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := fromIntStep 3)
      intro σ
      unfold fromIntStep
      dsimp
      rfl
    rw [show 3 = 2 + 1 from rfl, runLoopOn_succ]
    have h1 := fromIntStep_hit 1 [] v (by decide) (by decide) hv (fits_small 1 (by decide))
    rw [embed_nil.symm, show (v : Int) = Int.ofNat v from rfl, h1]
    simp only [h0, (by decide : (1 = 3) = False), if_false]
    simp
    rw [runLoopOn_succ]
    have hq0fits := fits_quot hv
    have h2 := fromIntStep_hit 2 [v % limbBase] (v / limbBase)
      (by decide) (by decide) hq0fits (fits_small 2 (by decide))
    rw [show (2 : Int) = Int.ofNat 2 from rfl,
      show ((v : Int) / (limbBase : Int)) = Int.ofNat (v / limbBase) from
        (Int.ofNat_ediv v limbBase).symm,
      h2]
    simp only [(by decide : (2 = 3) = False), if_false]
    simp
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    by_cases hq0 : v / limbBase = 0
    · have h3 := fromIntStep_hit 3 [v % limbBase] 0 (by decide) (by decide)
        FitsLen.zero (fits_small 3 (by decide))
      simp only [hq0, if_true]
      erw [h3]
      simp only [(by decide : (3 = 3) = True), if_true]
      have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq0
      have hmod : v % limbBase = v := Nat.mod_eq_of_lt hlt
      have hlist : limbsOfNat v = [v] := by simp [limbsOfNat, h0, hq0, hmod]
      rw [hmod, ← hlist]
      rfl
    · have hq1fits := fits_quot hq0fits
      have h3 := fromIntStep_hit 3 [v % limbBase, (v / limbBase) % limbBase]
        ((v / limbBase) / limbBase) (by decide) (by decide) hq1fits (fits_small 3 (by decide))
      simp only [hq0, if_false]
      erw [h3]
      simp only [(by decide : (3 = 3) = True), if_true]
      by_cases hq1 : (v / limbBase) / limbBase = 0
      · have hmod1 : (v / limbBase) % limbBase = v / limbBase :=
          Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq1)
        have hlist : limbsOfNat v =
            [v % limbBase, v / limbBase] := by
          simp [limbsOfNat, h0, hq0, hq1, hmod1]
        simp only [hq1, if_true]
        rw [hmod1, ← hlist]
        rfl
      · simp only [hq1, if_false]
        have hq2lt : (v / limbBase) / limbBase < limbBase := by
          have hqlt : v / limbBase < limbBase ^ 2 := by
            rw [limbBase_pow3] at hv3
            exact div_lt_of_lt_mul limbBase_pos hv3
          rw [limbBase_pow2] at hqlt
          exact div_lt_of_lt_mul limbBase_pos hqlt
        have hmod2 : ((v / limbBase) / limbBase) % limbBase = (v / limbBase) / limbBase :=
          Nat.mod_eq_of_lt hq2lt
        have hlist : limbsOfNat v =
            [v % limbBase, (v / limbBase) % limbBase, (v / limbBase) / limbBase] := by
          simp [limbsOfNat, h0, hq0, hq1, hmod2]
        have happ :
            [v % limbBase, (v / limbBase) % limbBase] ++ [(v / limbBase) / limbBase] =
              limbsOfNat v := by
          simp [hlist]
        simp [hmod2, happ, bigOf]
        rfl

end MegaDreifach.Link2
