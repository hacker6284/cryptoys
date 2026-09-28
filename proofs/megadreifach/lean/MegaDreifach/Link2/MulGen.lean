/-
  LINK 2 (private copy). `Generated.big_mul` on two arbitrary canonical
  multi-limb factors is `natLimbs` of the product.

  CLOSED: `big_mul_gen_refines`, `big_mul_nat_gen`. Needs only
  `FitsLen (|xs| + |ys|)` (the scratch buffer length) and digits `< 10^9`.
  Every cell `out[i+j] + x*y + carry < 10^18` fits in an i64.
-/
import MegaDreifach.Link2.MulGenMath

namespace MegaDreifach.Link2

set_option maxHeartbeats 4000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem limbBase_ne : limbBase ≠ 0 := Nat.ne_of_gt limbBase_pos

private theorem fitsB2 (a : Nat) (h : a < limbBase * limbBase) : FitsLen a := by
  have : limbBase * limbBase ≤ i64MaxNat := by unfold limbBase i64MaxNat; decide
  unfold FitsLen; omega

/-- Carry tail after the inner row, generalised to row `i`. -/
def kAfterG (nlen : Int) (i : Int) (σ1 : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt) :=
  do
    let k0 ← SudoRt.addI i nlen
    let toK ← SudoRt.subI (SudoRt.listLen σ1.snd.fst) 1
    let kLoop ←
      SudoRt.runLoopOn (k0, σ1.snd.fst, σ1.snd.snd)
        (if k0 > toK then 1 else (toK - k0).natAbs + 1)
        (kCarryStep toK)
        (fun σk => pure (SudoRt.Flow.cont σk.snd.fst))
        (fun r => pure (SudoRt.Flow.ret r))
    pure kLoop

private theorem set_eq_self (xs : List Nat) (i : Nat) (hi : i < xs.length)
    (h : xs.getD i 0 = 0) : xs.set i 0 = xs := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    by_cases hk : k = i
    · subst hk; simp [List.getElem_set]; rw [getD_eq_getElem' xs k hi] at h; exact h.symm
    · rw [List.getElem_set_ne (Ne.symm hk)]

theorem kAfterG_eq (ys o : List Nat) (i c m : Nat) (toJ : Int)
    (hlen : o.length = m + ys.length) (him : i < m) (hz : o.getD (i + ys.length) 0 = 0)
    (hc : c < limbBase) (hfits : FitsLen (m + ys.length)) :
    kAfterG (Int.ofNat ys.length) (Int.ofNat i) (toJ, embed o, Int.ofNat c) =
      .ok (SudoRt.Flow.cont (embed (o.set (i + ys.length) c))) := by
  unfold kAfterG
  dsimp only
  rw [addI_ofNat i ys.length (FitsLen.of_le hfits (by omega)), ok_bind,
    listLen_embed, subI_ofNat_one o.length (by omega) (by rw [hlen]; exact hfits), ok_bind]
  rw [fuelRange_eq]
  have hk0 : i + ys.length ≤ o.length - 1 := by omega
  have hfit' : FitsLen (o.length - 1 + 1) := by
    rw [show o.length - 1 + 1 = o.length by omega, hlen]; exact hfits
  have hIdx : i + ys.length < o.length := by omega
  by_cases hc0 : c = 0
  · subst hc0
    rw [except_bind_pure]
    erw [kLoop_idle o (i + ys.length) (o.length - 1) hk0 hfit']
    rw [set_eq_self o _ hIdx hz]; rfl
  · rw [except_bind_pure]
    have h0 : o[i + ys.length]'hIdx = 0 := by rw [← getD_eq_getElem' o _ hIdx]; exact hz
    erw [kLoop_write o (i + ys.length) (o.length - 1) c hk0 (Nat.pos_of_ne_zero hc0) hc hIdx h0
      hfit']
    rfl

/-- One schoolbook cell of the emitted inner loop. -/
theorem mulJ_gen (xs ys : List Nat) (st : List Nat × Nat) (i j : Nat)
    (hi : i < xs.length) (hj : j < ys.length)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hst : ∀ d ∈ st.1, d < limbBase) (hc : st.2 < limbBase)
    (hidx : i + j < st.1.length) (hfits : FitsLen (st.1.length)) :
    mulJStep (bigOf xs) (bigOf ys) (Int.ofNat i) (Int.ofNat (ys.length - 1))
        (Int.ofNat j, embed st.1, Int.ofNat st.2) =
      if j = ys.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, embed (mulCell (xs.getD i 0) i ys st j).1,
          Int.ofNat (mulCell (xs.getD i 0) i ys st j).2))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed (mulCell (xs.getD i 0) i ys st j).1,
          Int.ofNat (mulCell (xs.getD i 0) i ys st j).2)) := by
  have hngt : ¬ (Int.ofNat j > Int.ofNat (ys.length - 1)) := ofNat_not_gt (by omega)
  have hfij : FitsLen (i + j) := FitsLen.of_le hfits (by omega)
  have ha : st.1.getD (i + j) 0 < limbBase := getD_lt_of_digits _ hst _
  have hx : xs.getD i 0 < limbBase := getD_lt_of_digits _ hxs _
  have hy : ys.getD j 0 < limbBase := getD_lt_of_digits _ hys _
  have hcur := cell_fits _ _ _ _ ha hx hy hc
  have hf1 : FitsLen (xs.getD i 0 * ys.getD j 0) := fitsB2 _ (by omega)
  have hf2 : FitsLen (st.1.getD (i + j) 0 + xs.getD i 0 * ys.getD j 0) := fitsB2 _ (by omega)
  have hf3 := fitsB2 _ hcur
  unfold mulJStep
  rw [if_neg hngt]
  dsimp only [bigOf]
  rw [addI_ofNat i j hfij, ok_bind, atL_embed st.1 (i + j) hidx, ok_bind,
    atL_embed xs i hi, ok_bind, atL_embed ys j hj, ok_bind,
    ← getD_eq_getElem' st.1 _ hidx, ← getD_eq_getElem' xs i hi, ← getD_eq_getElem' ys j hj,
    mulI_ofNat _ _ hf1, ok_bind, addI_ofNat _ _ hf2, ok_bind, addI_ofNat _ _ hf3, ok_bind,
    ok_bind]
  rw [show Megadreifach.limb_base = Int.ofNat limbBase from rfl, modI_ofNat _ limbBase_ne, ok_bind]
  have hsz : i + j < (embed st.1).size := by rw [size_embed]; exact hidx
  rw [putL_ofNat _ _ _ hsz, ok_bind, divI_ofNat _ limbBase_ne, ok_bind]
  rw [embed_set_nat st.1 (i + j) _ hidx]
  simp only [pure_eq_ok, ok_bind]
  by_cases heq : j = ys.length - 1
  · simp [heq, beq_int_iff, mulCell]
  · have hne : ¬ (Int.ofNat j = Int.ofNat (ys.length - 1)) := fun h => heq (Int.ofNat.inj h)
    have hfj : FitsLen (j + 1) := FitsLen.of_le hfits (by omega)
    simp only [heq, if_false, beq_iff_eq, hne, addI_ofNat_one j hfj, ok_bind, mulCell]


/-- The inner row loop plus carry tail of row `i`. -/
theorem innerLoop_gen (xs ys : List Nat) (i : Nat) (hi : i < xs.length) (hn : 0 < ys.length)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hfits : FitsLen (xs.length + ys.length)) :
    SudoRt.runLoopOn (Int.ofNat 0, embed (rowRun xs ys i), Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (ys.length - 1)))
        (mulJStep (bigOf xs) (bigOf ys) (Int.ofNat i) (Int.ofNat (ys.length - 1)))
        (kAfterG (Int.ofNat ys.length) (Int.ofNat i)) (fun r => pure (SudoRt.Flow.ret r)) =
      .ok (SudoRt.Flow.cont (embed (rowRun xs ys (i + 1)))) := by
  obtain ⟨hlen, hdig, _, hzero⟩ := row_inv xs ys hxs hys i (by omega)
  have hx : xs.getD i 0 < limbBase := getD_lt_of_digits _ hxs _
  have hroom : i + ys.length ≤ (rowRun xs ys i).length := by omega
  have II := inner_inv (xs.getD i 0) i ys (rowRun xs ys i) hx hys hdig hroom
  apply chain_loop
    (f := fun j => (embed (innerRun (xs.getD i 0) i ys (rowRun xs ys i) j).1,
      Int.ofNat (innerRun (xs.getD i 0) i ys (rowRun xs ys i) j).2))
    (fromN := 0) (toN := ys.length - 1) (hle := Nat.zero_le _)
  · intro j _ hj
    obtain ⟨hl, hd, hc, _, _⟩ := II j (by omega)
    have h := mulJ_gen xs ys (innerRun (xs.getD i 0) i ys (rowRun xs ys i) j) i j hi (by omega)
      hxs hys hd hc (by omega) (by rw [hl, hlen]; exact hfits)
    exact h
  · obtain ⟨hl, _, hc, _, hsame⟩ := II ys.length (Nat.le_refl _)
    rw [show ys.length - 1 + 1 = ys.length by omega]
    have hz : (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).1.getD (i + ys.length) 0
        = 0 := by
      rw [hsame _ (Nat.le_refl _)]; exact hzero _ (Nat.le_refl _)
    exact kAfterG_eq ys _ i _ xs.length _ (by rw [hl, hlen]) hi hz hc hfits

theorem mulSchool_gen (xs ys : List Nat) (i : Nat) (hi : i < xs.length) (hn : 0 < ys.length)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hfits : FitsLen (xs.length + ys.length)) :
    mulSchoolStep (bigOf xs) (bigOf ys) (Int.ofNat (xs.length - 1))
        (Int.ofNat i, embed (rowRun xs ys i)) =
      if i = xs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed (rowRun xs ys (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (rowRun xs ys (i + 1)))) := by
  have hngt : ¬ (Int.ofNat i > Int.ofNat (xs.length - 1)) := ofNat_not_gt (by omega)
  have hinner := innerLoop_gen xs ys i hi hn hxs hys hfits
  unfold mulSchoolStep
  rw [if_neg hngt]
  dsimp only [bigOf]
  rw [listLen_embed, subI_ofNat_one ys.length hn (FitsLen.of_le hfits (by omega)), ok_bind]
  rw [fuelRange_eq (0 : Int)]
  erw [hinner]
  simp only [pure_eq_ok, ok_bind]
  by_cases heq : i = xs.length - 1
  · simp [heq, beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat (xs.length - 1)) := fun h => heq (Int.ofNat.inj h)
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfits (by omega)
    simp only [heq, if_false, beq_iff_eq, hne, addI_ofNat_one i hfi, ok_bind]


theorem big_mul_gen_open (xs ys : List Nat) (hxne : xs ≠ []) (hyne : ys ≠ [])
    (hfits : FitsLen (xs.length + ys.length)) :
    Megadreifach.big_mul (bigOf xs) (bigOf ys) =
      SudoRt.runLoopOn ((0 : Int), embed (List.replicate (xs.length + ys.length) 0))
        (fuelRange (0 : Int) (Int.ofNat (xs.length - 1)))
        (mulSchoolStep (bigOf xs) (bigOf ys) (Int.ofNat (xs.length - 1)))
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  have hxpos : 0 < xs.length := List.length_pos.mpr hxne
  have hypos : 0 < ys.length := List.length_pos.mpr hyne
  unfold Megadreifach.big_mul
  dsimp only [bigOf]
  rw [listLen_embed, listLen_embed, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by omega : ¬ xs.length = 0),
    if_neg (by decide : ¬ ((false : Bool) = true)), sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by omega : ¬ ys.length = 0)]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_ofNat _ _ hfits, ok_bind, filledL_ofNat, ok_bind, embed_replicate_zero]
  rw [subI_ofNat_one xs.length hxpos (FitsLen.of_le hfits (by omega)), ok_bind]
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulSchoolStep (bigOf xs) (bigOf ys) (Int.ofNat (xs.length - 1)))
    intro σ
    unfold mulSchoolStep
    dsimp only [bigOf]
    rw [listLen_embed]
    rfl
  rw [fuelRange_eq]
  rfl

/-- General schoolbook `big_mul` on canonical digit strings. -/
theorem big_mul_gen_refines (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hfits : FitsLen (xs.length + ys.length)) :
    Megadreifach.big_mul (bigOf xs) (bigOf ys) =
      .ok (bigOf (natLimbs (limbVal xs * limbVal ys))) := by
  by_cases hx : xs = []
  · subst hx; rw [big_mul_zero_left]; simp [limbVal, natLimbs_zero]
  by_cases hy : ys = []
  · subst hy; rw [big_mul_zero_right]; simp [limbVal, natLimbs_zero]
  have hxpos : 0 < xs.length := List.length_pos.mpr hx
  have hypos : 0 < ys.length := List.length_pos.mpr hy
  rw [big_mul_gen_open xs ys hx hy hfits]
  rw [show (0 : Int) = Int.ofNat 0 from rfl,
    show embed (List.replicate (xs.length + ys.length) 0) = embed (rowRun xs ys 0) from rfl]
  apply chain_loop (f := fun i => embed (rowRun xs ys i)) (fromN := 0)
    (toN := xs.length - 1) (hle := Nat.zero_le _)
  · intro i _ hi
    exact mulSchool_gen xs ys i (by omega) hypos hxs hys hfits
  · rw [show xs.length - 1 + 1 = xs.length by omega]
    obtain ⟨hlen, _, _, _⟩ := row_inv xs ys hxs hys xs.length (Nat.le_refl _)
    dsimp only
    rw [make_big_false _ (by rw [hlen]; exact hfits), except_bind_pure,
      rowRun_final xs ys hxs hys]

/-- `big_mul` on the canonical limbs of two naturals. -/
theorem big_mul_nat_gen (a b : Nat)
    (hfits : FitsLen ((natLimbs a).length + (natLimbs b).length)) :
    Megadreifach.big_mul (bigOf (natLimbs a)) (bigOf (natLimbs b)) =
      .ok (bigOf (natLimbs (a * b))) := by
  have h := big_mul_gen_refines (natLimbs a) (natLimbs b) (natLimbs_digits a)
    (natLimbs_digits b) hfits
  rwa [limbVal_natLimbs, limbVal_natLimbs] at h

end MegaDreifach.Link2
