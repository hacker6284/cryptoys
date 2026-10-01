/-
  BS Link 2 headline theorems: the emitted `tier`, `multiply` and `tidy` against the model
  `BsLink2.Spec`. Proof-only; correctness of the emitted code, not a security claim.
-/
import BsLink2.Link2.Bridge
import BsLink2.Link2.Tidy

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- B5 refines the model: on a well-formed field and a register of `n` trits, the emitted
    `tidy` returns exactly the model's tidy answer `toReg n (value x mod p)`. -/
theorem tidy_refines (F : Spec.Field) (hF : F.Wf) (hfit : FitsLen (F.n + 1))
    (x : List Nat) (hx : Spec.IsReg F.n x) :
    Bs.tidy (emb F) (embed x) = .ok (embed (Spec.tidy F x)) := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  obtain ⟨y, hy, hsz, htr, hv⟩ := tidy_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn hfit
    (embed x) (trits_embed hx.2) (by rw [size_embed]; exact hx.1)
  rw [hy]
  congr 1
  apply eq_embed_toReg htr hsz
  rw [hv, val_embed, ← p_cast F hF]
  rfl

/-- B3 refines the model: on a well-formed field, registers `a`, `b` of `n` trits and a
    nudge of 0, 1 or 2, the emitted `multiply` returns (the embedding of) a register that
    satisfies the model's `MulResult`: `n` trits, below `3^n`, and congruent to
    `A · B · 3^nudge` mod `p`. -/
theorem multiply_refines (F : Spec.Field) (hF : F.Wf) (a b : List Nat)
    (ha : Spec.IsReg F.n a) (hb : Spec.IsReg F.n b) (nudge : Nat) (hnu : nudge ≤ 2)
    (hfit : FitsLen (2 * F.n + nudge)) :
    ∃ out, Bs.multiply (emb F) (embed a) (embed b) (Int.ofNat nudge) = .ok (embed out) ∧
      Spec.MulResult F a b nudge out := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  obtain ⟨o, ho, hsz, htr, hlt, K, hK⟩ := multiply_spec (emb F) F.n (embed F.toll) rfl rfl
    htt hts htn (embed a) (embed b) (trits_embed ha.2) (trits_embed hb.2)
    (by rw [size_embed]; exact ha.1) (by rw [size_embed]; exact hb.1) nudge hnu hfit
  have hne := embed_decode o (nonneg_of_trits htr)
  refine ⟨decode o, by rw [ho, hne], ?_, ?_, ?_⟩
  · exact ⟨by simp [decode, hsz], decode_trits htr⟩
  · have := val_embed (decode o)
    rw [hne, pw_natCast] at *
    have h2 : (Spec.value (decode o) : Int) < ((3 ^ F.n : Nat) : Int) := by omega
    exact Int.ofNat_lt.mp h2
  · have hv := val_embed (decode o)
    rw [hne] at hv
    rw [val_embed, val_embed, ← p_cast F hF, pw_natCast] at hK
    rw [hv] at hK
    apply Int.ofNat.inj
    show ((Spec.value (decode o) % F.p : Nat) : Int) =
      ((Spec.value a * Spec.value b * 3 ^ nudge % F.p : Nat) : Int)
    rw [Int.ofNat_emod, Int.ofNat_emod, hK, Int.sub_eq_add_neg, ← Int.neg_mul,
      Int.add_mul_emod_self]
    simp [Int.ofNat_mul]

-- Tier names as the emitted code sees them (ASCII): `#[84, 49]` is "T1", `#[84, 50]` is
-- "T2", `#[84, 54]` is "T6".
private theorem beq_T1 : SudoRt.SEq.beq (#[84, 49] : Array Int) #[84, 49] = true := by decide!
private theorem beq_T2_T1 : SudoRt.SEq.beq (#[84, 50] : Array Int) #[84, 49] = false := by decide!
private theorem beq_T2 : SudoRt.SEq.beq (#[84, 50] : Array Int) #[84, 50] = true := by decide!
private theorem beq_T6_T1 : SudoRt.SEq.beq (#[84, 54] : Array Int) #[84, 49] = false := by decide!
private theorem beq_T6_T2 : SudoRt.SEq.beq (#[84, 54] : Array Int) #[84, 50] = false := by decide!

/-- §2.3: the emitted `tier "T1"` (`#[84, 49]` = "T1") is the model's T1
    (`p = 3^18 − 3^2 − 1`, `Spec.T1_p`). -/
theorem tier_T1_refines : Bs.tier #[84, 49] = .ok (emb Spec.T1) := by
  unfold Bs.tier; rw [beq_T1]; rfl

/-- §2.3: the emitted `tier "T2"` (`#[84, 50]` = "T2") is the model's T2
    (`p = 3^35 − 3^29 − 1`, `Spec.T2_p`). -/
theorem tier_T2_refines : Bs.tier #[84, 50] = .ok (emb Spec.T2) := by
  unfold Bs.tier; rw [beq_T2_T1]; simp only [Bool.false_eq_true, if_false]; rw [beq_T2]; rfl

/-- §2.3: the emitted `tier "T6"` (`#[84, 54]` = "T6") is `Spec.T6`, a well-formed field
    with `n = 100` and a 50-trit toll. Its toll digits are the sudo's (cross-checked against
    `params.json` by `vectors/check_oracle.py`); this theorem does not check them against π
    (`BsLink2.TollPi` does, against a cited rational bracket). -/
theorem tier_T6_wf : Bs.tier #[84, 54] = .ok (emb Spec.T6) ∧ Spec.T6.Wf ∧ Spec.T6.n = 100 ∧
    Spec.T6.toll.length = 50 := by
  refine ⟨?_, Spec.T6_wf, rfl, rfl⟩
  unfold Bs.tier; rw [beq_T6_T1]; simp only [Bool.false_eq_true, if_false]; rw [beq_T6_T2]
  simp only [Bool.false_eq_true, if_false]
  rw [sudoAssertEq_of_beq (a := (#[84, 54] : Array Int)) (b := #[84, 54]) (by decide!)]
  rfl

end BsLink2.Link2
