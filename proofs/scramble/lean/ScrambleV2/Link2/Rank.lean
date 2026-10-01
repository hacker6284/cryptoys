/-
  LINK 2. The emitted `rank_perm` against the model's `rank` (SPEC permutation rank),
  on any list of naturals of length at most 12 (the digest ranks 8 corners and 12
  edges; `fact` is proved on `0 … 11`, and every intermediate stays below `12!`).
  Proof-only.
-/
import ScrambleV2.Link2.Pieces

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-! ## Model side: the rank as a left-to-right sum -/

theorem getD_eq (p : List Nat) (n : Nat) (h : n < p.length) : p.getD n 0 = p[n] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem fact_mono : ∀ {m n}, m ≤ n → fact m ≤ fact n
  | m, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | m, n + 1, h => by
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have := fact_mono (Nat.le_of_lt_succ hlt)
      show fact m ≤ (n + 1) * fact n
      exact Nat.le_trans this (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
    · rw [Nat.le_antisymm h hge]; exact Nat.le_refl _

theorem rank_lt_fact : ∀ l : List Nat, rank l < fact l.length
  | [] => by decide
  | a :: t => by
    have ih := rank_lt_fact t
    have hc : t.countP (· < a) ≤ t.length := List.countP_le_length _
    show t.countP (· < a) * fact t.length + rank t < (t.length + 1) * fact t.length
    rw [Nat.succ_mul]
    have := Nat.mul_le_mul_right (fact t.length) hc
    omega

/-- The count the inner loop has made once it has looked at indices `n+1 … j-1`. -/
def cntTo (p : List Nat) (n j : Nat) : Nat :=
  ((p.take j).drop (n + 1)).countP (fun x => decide (x < p.getD n 0))

/-- Term `n` of the rank. -/
def termAt (p : List Nat) (n : Nat) : Nat :=
  (p.drop (n + 1)).countP (fun x => decide (x < p.getD n 0)) * fact (p.length - 1 - n)

/-- The outer loop's running total after indices `0 … n-1`. -/
def sumTo (p : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo p n + termAt p n

theorem cntTo_start (p : List Nat) (n : Nat) : cntTo p n (n + 1) = 0 := by
  unfold cntTo
  rw [List.drop_eq_nil_of_le (by simp; omega)]
  rfl

theorem cntTo_succ (p : List Nat) (n j : Nat) (hj : n + 1 ≤ j) (hjl : j < p.length) :
    cntTo p n (j + 1) = cntTo p n j + (if p[j] < p.getD n 0 then 1 else 0) := by
  unfold cntTo
  rw [List.take_succ, List.getElem?_eq_getElem hjl, Option.toList_some,
    List.drop_append_of_le_length (by simp; omega), List.countP_append]
  congr 1
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split <;> simp

theorem cntTo_end (p : List Nat) (n : Nat) :
    cntTo p n p.length = (p.drop (n + 1)).countP (fun x => decide (x < p.getD n 0)) := by
  unfold cntTo; rw [List.take_length]

theorem rank_drop (p : List Nat) (n : Nat) (hn : n < p.length) :
    rank (p.drop n) = termAt p n + rank (p.drop (n + 1)) := by
  rw [List.drop_eq_getElem_cons hn]
  show (p.drop (n + 1)).countP (· < p[n]) * fact (p.drop (n + 1)).length + rank (p.drop (n + 1)) = _
  unfold termAt
  rw [List.length_drop, getD_eq p n hn]
  congr 3
  omega

theorem sumTo_rank (p : List Nat) : ∀ n, n ≤ p.length → sumTo p n + rank (p.drop n) = rank p
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have ih := sumTo_rank p n (by omega)
    rw [rank_drop p n (by omega)] at ih
    simp only [sumTo]
    omega

theorem sumTo_le (p : List Nat) (n : Nat) (h : n ≤ p.length) : sumTo p n ≤ rank p := by
  have := sumTo_rank p n h; omega

theorem bind_ok_of {ε α β} {m : Except ε α} {v : α} (h : m = .ok v) (k : α → Except ε β) :
    m >>= k = k v := by rw [h]; rfl

theorem fits_fact12 : FitsLen (fact 12) := by unfold FitsLen i64MaxNat; decide

theorem rank_perm_pos (p : List Nat) (hlen : p.length ≤ 12) (hpos : 0 < p.length) :
    Scramble.rank_perm (embed p) = .ok (Int.ofNat (rank p)) := by
  have hbig : ∀ x, x ≤ rank p → FitsLen x := fun x hx =>
    FitsLen.of_le fits_fact12 (Nat.le_trans hx (Nat.le_trans (Nat.le_of_lt (rank_lt_fact p))
      (fact_mono hlen)))
  have hfit : FitsLen p.length := FitsLen.of_le (by unfold FitsLen i64MaxNat; omega) hlen
  unfold Scramble.rank_perm
  simp only [listLen_embed, fuelRange_eq, bind_pure_right]
  rw [subI_ofNat_one _ hpos hfit, ok_bind]
  refine chain_loop _ _ _ (fun n => Int.ofNat (sumTo p n)) 0 (p.length - 1) (Nat.zero_le _) ?_ _ ?_
  · intro n _ hn
    have hnl : n < p.length := by omega
    rw [if_neg (ofNat_not_gt hn)]
    simp only [addI_ofNat_one n (FitsLen.succ_le hnl hfit), subI_ofNat_one _ hpos hfit, ok_bind,
      fuelRange_eq]
    have hsum : sumTo p (n + 1) ≤ rank p := sumTo_le p (n + 1) (by omega)
    have hafter : ∀ c, c = (p.drop (n + 1)).countP (fun x => decide (x < p.getD n 0)) →
        (do
          let _t970 ← SudoRt.subI (Int.ofNat (p.length - 1)) (Int.ofNat n)
          let _t971 ← Scramble.fact _t970
          let _t972 ← SudoRt.mulI (Int.ofNat c) _t971
          let _t964 ← SudoRt.addI (Int.ofNat (sumTo p n)) _t972
          (pure (SudoRt.Flow.cont (ρ := Int) _t964) : Except SudoRt.Trap _)) =
          .ok (SudoRt.Flow.cont (Int.ofNat (sumTo p (n + 1)))) := by
      intro c hc
      have ht : sumTo p (n + 1) = sumTo p n + c * fact (p.length - 1 - n) := by
        simp only [sumTo, termAt, hc]
      rw [subI_ofNat _ _ (FitsLen.of_le hfit (Nat.sub_le _ _)) (by omega), ok_bind,
        fact_refines _ (by omega), ok_bind,
        mulI_ofNat _ _ (hbig _ (by omega)), ok_bind,
        addI_ofNat _ _ (hbig _ (by omega)), ← ht]
      rfl
    rw [bind_ok_of (v := SudoRt.Flow.cont (Int.ofNat (sumTo p (n + 1)))) ?inner]
    · simp only [beq_int_iff, pure_eq_ok]
      by_cases hl : n = p.length - 1
      · simp [hl]
      · simp [hl]; omega
    · by_cases hlast : n + 1 ≤ p.length - 1
      · rw [show ((Int.ofNat (n + 1), (0 : Int)) : Int × Int) =
            (Int.ofNat (n + 1), Int.ofNat (cntTo p n (n + 1))) by rw [cntTo_start]; rfl]
        refine chain_loop _ _ _ (fun j => Int.ofNat (cntTo p n j)) (n + 1) (p.length - 1) hlast
          ?_ _ ?_
        · intro j hj1 hj2
          have hjl : j < p.length := by omega
          rw [if_neg (ofNat_not_gt hj2)]
          simp only [atL_embed p j hjl, atL_embed p n hnl, ok_bind, ofNat_lt_iff]
          rw [cntTo_succ p n j hj1 hjl, getD_eq p n hnl]
          have hcnt : cntTo p n j + 1 ≤ p.length := by
            unfold cntTo
            have := List.countP_le_length (fun x => decide (x < p.getD n 0)) (l := (p.take j).drop (n + 1))
            simp only [List.length_drop, List.length_take] at this
            omega
          by_cases hlt : p[j] < p[n]
          · simp only [hlt, decide_True, if_true, pure_eq_ok,
              addI_ofNat_one (cntTo p n j) (FitsLen.of_le hfit hcnt), ok_bind]
            rw [asc_tail _ j (FitsLen.succ_le hjl hfit)]
          · simp only [hlt, decide_False, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind,
              Nat.add_zero]
            rw [asc_tail _ j (FitsLen.succ_le hjl hfit)]
        · simp only
          rw [show p.length - 1 + 1 = p.length by omega, cntTo_end]
          exact hafter _ rfl
      · have hgt : Int.ofNat (n + 1) > Int.ofNat (p.length - 1) := by
          simp only [gt_iff_lt, ofNat_lt_iff]; omega
        rw [asc_break _ _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
        simp only
        have : (p.drop (n + 1)).countP (fun x => decide (x < p.getD n 0)) = 0 := by
          rw [List.drop_eq_nil_of_le (by omega)]; rfl
        exact hafter 0 this.symm
  · simp only
    rw [show p.length - 1 + 1 = p.length by omega]
    have := sumTo_rank p p.length (Nat.le_refl _)
    rw [List.drop_length] at this
    simp only [pure_eq_ok]
    rw [show sumTo p p.length = rank p by simpa [rank] using this]

/-- `rank_perm` on any list of at most 12 naturals (i64-safe) is the Lehmer rank. -/
theorem rank_perm_refines (p : List Nat) (hlen : p.length ≤ 12) :
    Scramble.rank_perm (embed p) = .ok (Int.ofNat (rank p)) := by
  cases p with
  | nil => rfl
  | cons a t => exact rank_perm_pos _ hlen (Nat.succ_pos _)

end ScrambleV2.Link2
