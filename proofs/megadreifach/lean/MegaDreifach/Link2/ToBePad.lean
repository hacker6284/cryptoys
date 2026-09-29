/-
  LINK 2. Multi-limb `big_to_be` ≃ base-256 `toBE` on the 28-byte pad value.

  `big_to_be_8` / `big_to_be_width` only cover i64-scale values (at most three
  base-`10^9` limbs). A Lehmer rank below `2^224` needs up to eight limbs.

  Domain: `v < 256 ^ w` and `FitsLen (natLimbs v).length`, i.e. the canonical
  limb count is i64-safe. For `w = 28` this is `v < 2^224`.

  Algebraic Link 2 only. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.Be
import MegaDreifach.Link2.DivInd
import MegaDreifach.Link2.MagSub
import MegaDreifach.Link2.FromBePad

namespace MegaDreifach.Link2

/-- Loop state after `i` emitted `big_to_be` steps, on canonical limbs. -/
def beAccNat (v i : Nat) : Megadreifach.BigInt × Array Int :=
  (bigOf (natLimbs (v / 256 ^ (i - 1))), embed (leBytes (i - 1) v))

theorem beAccNat_one (v : Nat) :
    beAccNat v 1 = (bigOf (natLimbs v), embed []) := by
  simp [beAccNat, leBytes, Nat.pow_zero, Nat.div_one]

/-- One step of `big_to_be` on canonical limbs, at any width. -/
theorem beStep_hit_nat (v w i : Nat) (hlimb : FitsLen (natLimbs v).length)
    (hwf : FitsLen w) (hi1 : 1 ≤ i) (hiw : i ≤ w) :
    beStep (Int.ofNat w) (Int.ofNat i, beAccNat v i) =
      (if i = w then
        .ok (SudoRt.Flow.brk (Int.ofNat i, beAccNat v (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), beAccNat v (i + 1)))) := by
  unfold beStep beAccNat
  dsimp
  rw [← ofNat_eq_natCast i, ← ofNat_eq_natCast w,
    if_neg (ofNat_not_gt hiw)]
  have hlenle : (natLimbs (v / 256 ^ (i - 1))).length ≤ (natLimbs v).length :=
    natLimbs_len_mono _ _ (Nat.div_le_self _ _)
  have hfits : FitsLen (natLimbs (v / 256 ^ (i - 1))).length :=
    FitsLen.of_le hlimb hlenle
  rw [show (256 : Int) = Int.ofNat 256 from rfl,
    big_divmod_nat 256 (v / 256 ^ (i - 1)) (by decide) (by decide) hfits,
    ok_bind, appendL_spec]
  dsimp only
  have hdiv : (v / 256 ^ (i - 1)) / 256 = v / 256 ^ i := by
    have hi : (i - 1) + 1 = i := by omega
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow256_succ, hi]
  rw [hdiv, push_embed (leBytes (i - 1) v) ((v / 256 ^ (i - 1)) % 256)]
  have hle :
      leBytes (i - 1) v ++ [(v / 256 ^ (i - 1)) % 256] = leBytes ((i - 1) + 1) v :=
    (leBytes_succ_append (i - 1) v).symm
  have hidx : (i - 1) + 1 = i := by omega
  rw [hle, hidx]
  have hnext : (i + 1) - 1 = i := by omega
  by_cases hi : i = w
  · subst hi
    simp [beq_int_iff]
    rfl
  · have hne : ¬ (i : Int) = (w : Int) := fun h => hi (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (FitsLen.of_le hwf (by omega))
    rw [ofNat_eq_natCast i] at hadd
    simp [hi, hnext, ite_int_beq, hne, hadd, ok_bind]

/-- The emitted downto copy of `leBytes w v` is `toBE w v`. -/
theorem be_down_nat (v w : Nat) (hw : 0 < w) (hwf : FitsLen w)
    (hv : v < 256 ^ w) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat (w - 1), embed ((leBytes w v).drop ((w - 1) + 1)).reverse)
        (fuelDown (Int.ofNat (w - 1)) 0)
        (downCopyStep (embed (leBytes w v)))
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r) =
      .ok (embed (toBE w v)) := by
  apply chain_down (downCopyStep (embed (leBytes w v)))
    (f := fun i => embed ((leBytes w v).drop (i + 1)).reverse)
    (g := fun i => embed ((leBytes w v).drop i).reverse)
    (fromN := w - 1)
    (hstep := by
      intro i hi
      have hlt : i < (leBytes w v).length := by
        rw [leBytes_length]
        omega
      exact down_hit (leBytes w v) i hlt (FitsLen.of_le hwf (by omega)))
    (hlink := by
      intro i hp _
      dsimp
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)])
    (goal := .ok (embed (toBE w v)))
    (hafter := by
      simp only [List.drop_zero]
      rw [← toBE_eq_leRev w v hv]
      rfl)

/-- `big_to_be` at any width on canonical limbs, once the limb count fits. -/
theorem big_to_be_nat (v w : Nat) (hw : 0 < w) (hwf : FitsLen w)
    (hlimb : FitsLen (natLimbs v).length) (hv : v < 256 ^ w) :
    Megadreifach.big_to_be (bigOf (natLimbs v)) (Int.ofNat w) =
      .ok (embed (toBE w v)) := by
  unfold Megadreifach.big_to_be
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := beStep (Int.ofNat w))
    intro σ
    unfold beStep
    rfl
  rw [fuelRange_eq, show (1 : Int) = Int.ofNat 1 from rfl,
    show ((w : Int)) = Int.ofNat w from rfl]
  rw [embed_nil.symm, ← beAccNat_one v]
  apply chain_loop (beStep (Int.ofNat w))
    (f := beAccNat v) (fromN := 1) (toN := w) (hle := by omega)
    (hstep := fun i hi1 hiw => beStep_hit_nat v w i hlimb hwf hi1 hiw)
    (goal := .ok (embed (toBE w v)))
    (hafter := by
      dsimp [beAccNat]
      rw [listLen_embed, leBytes_length,
        subI_ofNat_one w hw hwf, ok_bind]
      rw [fuelDown_eq]
      have hdrop : (leBytes w v).drop w = [] := by
        have h := List.drop_length (leBytes w v)
        rwa [leBytes_length w v] at h
      rw [show (embed [] : Array Int) =
          embed ((leBytes w v).drop ((w - 1) + 1)).reverse by
        rw [show (w - 1) + 1 = w from by omega, hdrop]; rfl]
      rw [except_bind_pure]
      apply Eq.trans
      · apply runLoopOn_step_pointwise (step' := downCopyStep (embed (leBytes w v)))
        intro σ
        unfold downCopyStep
        rfl
      exact be_down_nat v w hw hwf hv)

/-- The 28-byte pad block: `v < 2^224` uses at most eight base-`10^9` limbs. -/
theorem big_to_be_pad (v : Nat) (hv : v < phiMax) :
    Megadreifach.big_to_be (bigOf (natLimbs v)) (28 : Int) =
      .ok (embed (toBE 28 v)) := by
  have hp : (256 : Nat) ^ 28 = phiMax := by
    have h256 : (256 : Nat) = 2 ^ 8 := by decide
    unfold phiMax
    rw [h256, ← Nat.pow_mul]
  have hv' : v < 256 ^ 28 := by rw [hp]; exact hv
  have hlt8 : v < limbBase ^ 8 := Nat.lt_trans hv' pow256_28_lt_limb8
  have hfit8 : FitsLen 8 := by unfold FitsLen i64MaxNat; decide
  have hlimb : FitsLen (natLimbs v).length :=
    FitsLen.of_le hfit8 (natLimbs_length_le v 8 hlt8)
  exact big_to_be_nat v 28 (by decide) (by unfold FitsLen i64MaxNat; decide) hlimb hv'

end MegaDreifach.Link2
