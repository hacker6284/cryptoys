/-
  LINK 2. Generated `deal_under` / `undeal_under` / `deal_step` /
  `undeal_step` (v12 PassKey deal) refine `dealUnder` / `undealUnder` /
  `maybeDeal` / `maybeDealInv` on the well-formed domain. Proof-only.
  Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

open DoubleDeal

/-- Reverse-index copy stepper: `for i = from to toV: out.append(xs[b - i])`.
    Proof-side twin of the emitted loop body, not a hand-edit of Generated. -/
def revStep (ρ : Type) (xs : Array Int) (b toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) ρ) :=
  if σ.1 > toV then
    pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, σ.2))
  else do
    let lift ← do
      let j ← SudoRt.subI b σ.1
      let t ← SudoRt.atL xs j
      pure (SudoRt.Flow.cont (ρ := ρ) (SudoRt.appendL σ.2 t).1)
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := ρ) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
    | .cont fs =>
      if σ.1 == toV then
        pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
      else do
        let i' ← SudoRt.addI σ.1 (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', fs))

theorem revStep_gt (ρ : Type) (xs : Array Int) (b toV i : Int) (acc : Array Int)
    (h : i > toV) :
    revStep ρ xs b toV (i, acc) = .ok (.brk (i, acc)) := by
  unfold revStep
  rw [if_pos h]
  rfl

theorem revStep_hit (ρ : Type) (xs : List Nat) (b toN fromN : Nat) (acc : Array Int)
    (hfrom : fromN ≤ toN) (hone : 1 ≤ fromN) (hb : toN ≤ b) (hbx : b ≤ xs.length)
    (hfits : FitsLen xs.length) :
    revStep ρ (embed xs) (Int.ofNat b) (Int.ofNat toN) (Int.ofNat fromN, acc) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN, acc.push (Int.ofNat (xs.getD (b - fromN) 0))))
      else
        .ok (.cont (Int.ofNat (fromN + 1),
          acc.push (Int.ofNat (xs.getD (b - fromN) 0)))) := by
  unfold revStep
  dsimp only
  have hngt : ¬ (Int.ofNat fromN > Int.ofNat toN) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr hfrom)
  rw [if_neg hngt]
  have hsub : SudoRt.subI (Int.ofNat b) (Int.ofNat fromN) = .ok (Int.ofNat (b - fromN)) :=
    subI_ofNat b fromN (FitsLen.of_le hfits hbx) (by omega)
  have hidx : b - fromN < xs.length := by omega
  have hat : SudoRt.atL (embed xs) (Int.ofNat (b - fromN)) =
      .ok (Int.ofNat (xs.getD (b - fromN) 0)) := by
    rw [atL_embed xs (b - fromN) hidx]
    congr 2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  rw [hsub]
  simp only [ok_bind]
  rw [hat]
  simp only [ok_bind, SudoRt.appendL]
  by_cases heq : fromN = toN
  · subst heq
    simp
    rfl
  · have hne : ¬ (Int.ofNat fromN = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    have hbeq : (Int.ofNat fromN == Int.ofNat toN) = false := by
      simp [beq_iff_eq]; exact hne
    rw [hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, if_neg heq]
    have hadd : SudoRt.addI (Int.ofNat fromN) 1 = .ok (Int.ofNat (fromN + 1)) :=
      addI_ofNat_one fromN (FitsLen.of_le hfits (by omega))
    rw [hadd]
    rfl

/-- Reverse-index copy, then an arbitrary continuation of the collected array. -/
theorem rev_loop_after {α} (xs : List Nat) (b fromN toN : Nat)
    (acc : Array Int) (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (hone : 1 ≤ fromN) (hfrom : fromN ≤ toN + 1) (hb : toN ≤ b) (hbx : b ≤ xs.length)
    (hfits : FitsLen xs.length) :
    SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat fromN, acc)
        (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        (revStep (Array Int) (embed xs) (Int.ofNat b) (Int.ofNat toN))
        (fun σ => after σ.2) onRet =
      after (Array.mk (acc.toList ++
        (List.range' fromN (toN + 1 - fromN)).map
          (fun i => Int.ofNat (xs.getD (b - i) 0)))) := by
  generalize hrem : toN + 1 - fromN = rem
  induction rem generalizing fromN acc with
  | zero =>
    have hEq : fromN = toN + 1 := by omega
    subst hEq
    have hgt : Int.ofNat (toN + 1) > Int.ofNat toN :=
      Int.ofNat_lt.mpr (Nat.lt_succ_self _)
    rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ,
      revStep_gt (Array Int) (embed xs) (Int.ofNat b) (Int.ofNat toN) _ acc hgt]
    simp [mk_toList]
  | succ rem ih =>
    have hle : fromN ≤ toN := by omega
    rw [fuelRange_le hle, runLoopOn_succ,
        revStep_hit (Array Int) xs b toN fromN acc hle hone hb hbx hfits]
    by_cases heq : fromN = toN
    · rw [if_pos heq]
      have hrem0 : rem = 0 := by omega
      subst hrem0
      apply congrArg after
      show _ = Array.mk (acc.toList ++ [Int.ofNat (xs.getD (b - fromN) 0)])
      rw [← toList_push, mk_toList]
    · rw [if_neg heq]
      have hlt : fromN < toN := Nat.lt_of_le_of_ne hle heq
      simp only []
      have hfuel : toN - fromN = fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) := by
        rw [fuelRange_le (Nat.succ_le_of_lt hlt)]
        omega
      rw [hfuel]
      have ih' := ih (fromN + 1) (acc.push (Int.ofNat (xs.getD (b - fromN) 0)))
        (by omega) (by omega) (by omega)
      rw [ih']
      apply congrArg after
      apply congrArg Array.mk
      rw [toList_push, List.range'_succ, List.map_cons]
      simp

/-- The reverse-index copy collects a reversed slice. -/
theorem range'_map_getD_rev (l : List Nat) (b m : Nat) (hm : m ≤ b) (hb : b ≤ l.length) :
    (List.range' 1 m).map (fun i => l.getD (b - i) 0) =
      ((l.drop (b - m)).take m).reverse := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat, List.map_append, ih (by omega)]
    have hidx : b - (m + 1) < l.length := by omega
    have hdrop : l.drop (b - (m + 1)) = l[b - (m + 1)] :: l.drop (b - m) := by
      have h1 : b - m = b - (m + 1) + 1 := by omega
      rw [h1]
      exact drop_eq_cons l (b - (m + 1)) hidx
    rw [hdrop, List.take_succ_cons, List.reverse_cons]
    have h1m : 1 + m = m + 1 := Nat.add_comm 1 m
    simp [h1m, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]

theorem runLoopOn_congr {σ ρ α} (s0 : σ) (fuel : Nat)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (h : ∀ s, step s = step' s)
    (after after' : σ → Except SudoRt.Trap α) (ha : ∀ s, after s = after' s)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ) s0 fuel step' after' onRet := by
  rw [show step = step' from funext h, show after = after' from funext ha]

/-- Generated `deal_under` is `dealUnder` on a well-formed list (`m < length`). -/
theorem deal_under_refines (xs : List Nat) (m : Nat) (hm : m < xs.length) (hfits : FitsLen xs.length) :
    Doubledeal.deal_under (embed xs) (Int.ofNat m) = .ok (embed (dealUnder xs m)) := by
  unfold Doubledeal.deal_under
  rw [listLen_embed]
  have hsubn : SudoRt.subI (Int.ofNat xs.length) 1 = .ok (Int.ofNat (xs.length - 1)) :=
    subI_ofNat_one xs.length (by omega) hfits
  rw [hsubn]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  simp only [except_bind_pure]
  refine (runLoopOn_congr _ _ _ (copyStep (Array Int) (embed xs) (Int.ofNat (xs.length - 1)))
    ?_ _ (fun σ => SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat 1, σ.2)
          (fuelRange (Int.ofNat 1) (Int.ofNat m))
          (revStep (Array Int) (embed xs) (Int.ofNat m) (Int.ofNat m))
          (fun σ => pure σ.2) (fun r => pure r)) ?_ _).trans ?_
  · intro s
    unfold copyStep
    by_cases hgt : s.fst > Int.ofNat (xs.length - 1)
    · simp [hgt]
    · simp [hgt]
  · intro s
    apply runLoopOn_congr
    · intro t
      unfold revStep
      by_cases hgt : t.fst > Int.ofNat m
      · simp [hgt]
      · simp [hgt]
    · intro t; rfl
  rw [copy_loop_after (embed xs) m (xs.length - 1) #[] (fun a => SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat 1, a)
          (fuelRange (Int.ofNat 1) (Int.ofNat m))
          (revStep (Array Int) (embed xs) (Int.ofNat m) (Int.ofNat m))
          (fun σ => pure σ.2) (fun r => pure r)) _ (by omega)
      (Or.inl (by rw [size_embed]; omega)) (by rw [size_embed]; exact hfits)
      (by rw [size_embed]; omega)]
  dsimp only
  rw [rev_loop_after xs m 1 m _ (fun a => pure a) (fun r => pure r) (by omega) (by omega) (by omega) (by omega) hfits]
  have hrev := range'_map_getD_rev xs m m (Nat.le_refl _) (Nat.le_of_lt hm)
  simp only [Nat.sub_self, List.drop_zero] at hrev
  have hmap : (List.range' 1 (m + 1 - 1)).map (fun i => Int.ofNat (xs.getD (m - i) 0)) =
      ((xs.take m).reverse).map Int.ofNat := by
    rw [Nat.add_sub_cancel, ← hrev, List.map_map]
    rfl
  have htk : List.take (xs.length - 1 + 1 - m) (List.drop m (embed xs).toList) =
      (xs.drop m).map Int.ofNat := by
    rw [toList_embed, ← List.map_drop]
    apply List.take_of_length_le
    simp; omega
  rw [hmap, htk]
  show Except.ok _ = _
  apply congrArg Except.ok
  unfold dealUnder embed
  simp [List.map_append]

/-- Generated `undeal_under` is `undealUnder` on a well-formed list (`m < length`). -/
theorem undeal_under_refines (xs : List Nat) (m : Nat) (hm : m < xs.length) (hfits : FitsLen xs.length) :
    Doubledeal.undeal_under (embed xs) (Int.ofNat m) = .ok (embed (undealUnder xs m)) := by
  unfold Doubledeal.undeal_under
  rw [listLen_embed]
  simp only []
  rw [except_bind_pure, fuelRange_eq]
  have hsub1 : SudoRt.subI (Int.ofNat xs.length) (Int.ofNat m) = .ok (Int.ofNat (xs.length - m)) :=
    subI_ofNat xs.length m hfits (Nat.le_of_lt hm)
  have hsub2 : SudoRt.subI (Int.ofNat (xs.length - m)) 1 = .ok (Int.ofNat (xs.length - m - 1)) :=
    subI_ofNat_one _ (by omega) (FitsLen.of_le hfits (Nat.sub_le _ _))
  simp only [hsub1, hsub2, ok_bind, except_bind_pure]
  let after2 : Array Int → Except SudoRt.Trap (Array Int) := fun a =>
    SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat 0, a)
      (fuelRange (Int.ofNat 0) (Int.ofNat (xs.length - m - 1)))
      (copyStep (Array Int) (embed xs) (Int.ofNat (xs.length - m - 1)))
      (fun σ => pure σ.2) (fun r => pure r)
  refine (runLoopOn_congr _ _ _
    (revStep (Array Int) (embed xs) (Int.ofNat xs.length) (Int.ofNat m))
    ?_ _ (fun σ => after2 σ.2) ?_ _).trans ?_
  · intro t
    unfold revStep
    by_cases hgt : t.fst > Int.ofNat m
    · simp [hgt]
    · simp [hgt]
  · intro s
    apply runLoopOn_congr
    · intro t
      unfold copyStep
      by_cases hgt : t.fst > Int.ofNat (xs.length - m - 1)
      · simp [hgt]
      · simp [hgt]
    · intro t; rfl
  rw [show (1 : Int) = Int.ofNat 1 from rfl]
  rw [rev_loop_after xs xs.length 1 m #[] after2 (fun r => pure r) (by omega) (by omega)
    (by omega) (Nat.le_refl _) hfits]
  simp only [after2]
  rw [copy_loop_after (embed xs) 0 (xs.length - m - 1) _ (fun a => pure a) _ (by omega)
      (Or.inl (by rw [size_embed]; omega)) (by rw [size_embed]; exact hfits)
      (by rw [size_embed]; omega)]
  have hrev := range'_map_getD_rev xs xs.length m (Nat.le_of_lt hm) (Nat.le_refl _)
  have hdl : (xs.drop (xs.length - m)).length = m := by rw [List.length_drop]; omega
  rw [List.take_of_length_le (by rw [hdl]; exact Nat.le_refl _)] at hrev
  have hmap : (List.range' 1 (m + 1 - 1)).map (fun i => Int.ofNat (xs.getD (xs.length - i) 0)) =
      ((xs.drop (xs.length - m)).reverse).map Int.ofNat := by
    rw [Nat.add_sub_cancel, ← hrev, List.map_map]
    rfl
  have htk : List.take (xs.length - m - 1 + 1 - 0) (List.drop 0 (embed xs).toList) =
      (xs.take (xs.length - m)).map Int.ofNat := by
    rw [toList_embed, List.drop_zero, ← List.map_take]
    congr 2
    omega
  rw [hmap]
  simp only [List.nil_append]
  rw [htk]
  show Except.ok _ = _
  apply congrArg Except.ok
  unfold undealUnder embed
  simp [List.map_append]

theorem addI_ofNat_two (n : Nat) (h : FitsLen (n + 2)) :
    SudoRt.addI (Int.ofNat n) 2 = .ok (Int.ofNat (n + 2)) :=
  narrowI_ofNat (n + 2) h

theorem fits_dealCount (c : Nat) (hc : FitsLen c) : FitsLen (dealCount c) := by
  unfold dealCount suit
  unfold FitsLen i64MaxNat at *
  omega

/-- Generated `deal_step` is `maybeDeal` on well-formed piles (card fits i64). -/
theorem deal_step_refines (c : Nat) (hand key : List Nat) (hc : FitsLen c)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    Doubledeal.deal_step (Int.ofNat c) (embed hand) (embed key) =
      .ok (embed (maybeDeal hand key c).1, embed (maybeDeal hand key c).2) := by
  unfold Doubledeal.deal_step
  rw [suit_of_refines]
  simp only [ok_bind]
  rw [addI_ofNat_two (suit c) (fits_dealCount c hc)]
  simp only [ok_bind, listLen_embed, decide_ofNat_lt]
  have hd : suit c + 2 = dealCount c := rfl
  rw [hd]
  unfold maybeDeal
  by_cases hH : dealCount c < hand.length
  · rw [decide_eq_true hH, dif_pos hH]
    simp only [↓reduceIte]
    rw [deal_under_refines hand (dealCount c) hH hh]
    rfl
  · rw [decide_eq_false hH, dif_neg hH]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hK : dealCount c < key.length
    · rw [decide_eq_true hK, dif_pos hK]
      simp only [↓reduceIte]
      rw [deal_under_refines key (dealCount c) hK hk]
      rfl
    · rw [decide_eq_false hK, dif_neg hK]
      rfl

/-- Generated `undeal_step` is `maybeDealInv` on well-formed piles (card fits i64). -/
theorem undeal_step_refines (c : Nat) (hand key : List Nat) (hc : FitsLen c)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    Doubledeal.undeal_step (Int.ofNat c) (embed hand) (embed key) =
      .ok (embed (maybeDealInv hand key c).1, embed (maybeDealInv hand key c).2) := by
  unfold Doubledeal.undeal_step
  rw [suit_of_refines]
  simp only [ok_bind]
  rw [addI_ofNat_two (suit c) (fits_dealCount c hc)]
  simp only [ok_bind, listLen_embed, decide_ofNat_lt]
  have hd : suit c + 2 = dealCount c := rfl
  rw [hd]
  unfold maybeDealInv
  by_cases hH : dealCount c < hand.length
  · rw [decide_eq_true hH, dif_pos hH]
    simp only [↓reduceIte]
    rw [undeal_under_refines hand (dealCount c) hH hh]
    rfl
  · rw [decide_eq_false hH, dif_neg hH]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hK : dealCount c < key.length
    · rw [decide_eq_true hK, dif_pos hK]
      simp only [↓reduceIte]
      rw [undeal_under_refines key (dealCount c) hK hk]
      rfl
    · rw [decide_eq_false hK, dif_neg hK]
      rfl

end DoubleDeal.Link2
