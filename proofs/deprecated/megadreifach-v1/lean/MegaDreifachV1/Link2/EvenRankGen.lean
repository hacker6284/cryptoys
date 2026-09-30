/-
  LINK 2 (private copy). `Generated.even_perm_rank_big` refines algebraic
  `evenRank` on every length-`n` permutation of `0..n-1` (`3 ≤ n ≤ 30`,
  in particular the corner width 20 and the edge width 30), with
  multi-limb ranks. Uses the general schoolbook `big_mul_nat_gen`.

  CLOSED: `even_perm_rank_big_refines_gen`. Evenness is not required.
-/
import MegaDreifachV1.Link2.EvenRank
import MegaDreifachV1.Link2.MulGen
import MegaDreifachV1.Link2.MagAdd

namespace MegaDreifachV1.Link2

set_option maxHeartbeats 4000000

structure PermNWf (n : Nat) (perm : List Nat) : Prop where
  len : perm.length = n
  nodup : perm.Nodup
  bound : ∀ a ∈ perm, a < n

theorem availAt_specN (n : Nat) (perm : List Nat) (h : PermNWf n perm) :
    ∀ k, k ≤ n →
      (availAt perm k).Nodup ∧
      (availAt perm k).length = n - k ∧
      (∀ x, x ∈ availAt perm k ↔ x < n ∧ x ∉ perm.take k) := by
  intro k hk
  induction k with
  | zero =>
    have hlen : perm.length = n := h.len
    simp only [availAt, dropUsed, hlen, List.take_zero]
    refine ⟨List.nodup_range n, by simp [List.length_range], ?_⟩
    intro x
    simp [List.mem_range]
  | succ k ih =>
    have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
    have hklt : k < n := by omega
    have hklen : k < perm.length := by rw [h.len]; exact hklt
    obtain ⟨hnd, hlen, hmem⟩ := ih hk0
    have hnot : perm[k] ∉ perm.take k := not_mem_take_self perm h.nodup hklen
    have hin : perm[k] ∈ availAt perm k := by
      rw [hmem]
      exact ⟨h.bound _ (List.getElem_mem hklen), hnot⟩
    have hidx : (availAt perm k).findIdx (· == perm[k]) < (availAt perm k).length :=
      findIdx_lt_mem _ hin
    have hget := get_findIdx (availAt perm k) hin
    refine ⟨?_, ?_, ?_⟩
    · rw [availAt_erase perm k hklen]
      exact List.Nodup.eraseIdx _ hnd
    · rw [availAt_erase perm k hklen, List.length_eraseIdx_of_lt hidx, hlen]
      omega
    · intro x
      rw [availAt_erase perm k hklen, mem_eraseIdx_of_nodup _ hnd hidx, hmem, hget]
      have htake : perm.take (k + 1) = perm.take k ++ [perm[k]] :=
        take_succ_get perm k hklen
      constructor
      · intro ⟨⟨hx, hnin⟩, hne⟩
        refine ⟨hx, ?_⟩
        rw [htake, List.mem_append]
        intro hbad
        cases hbad with
        | inl hm => exact hnin hm
        | inr hm =>
          simp at hm
          exact hne hm
      · intro ⟨hx, hnin⟩
        have hnin0 : x ∉ perm.take k := by
          intro hm
          exact hnin (by rw [htake, List.mem_append]; exact Or.inl hm)
        have hne : x ≠ perm[k] := by
          intro heq
          exact hnin (by rw [htake, List.mem_append]; exact Or.inr (by simp [heq]))
        exact ⟨⟨hx, hnin0⟩, hne⟩

theorem availAt_lengthN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (k : Nat)
    (hk : k ≤ n) : (availAt perm k).length = n - k :=
  (availAt_specN n perm h k hk).2.1

theorem mem_availAtN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (k : Nat) (hk : k < n) :
    perm[k]'(by rw [h.len]; exact hk) ∈ availAt perm k := by
  have hmem := (availAt_specN n perm h k (Nat.le_of_lt hk)).2.2
  have hklen : k < perm.length := by rw [h.len]; exact hk
  rw [hmem]
  exact ⟨h.bound _ (List.getElem_mem hklen), not_mem_take_self perm h.nodup hklen⟩

theorem evenDigit_eqN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (k : Nat)
    (hk : k < n - 2) :
    (evenDigits perm)[k]'(by
        simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) =
      (availAt perm k).findIdx (· == perm[k]'(by rw [h.len]; omega)) ∧
    (availAt perm k).findIdx (· == perm[k]'(by rw [h.len]; omega)) < n - k := by
  have hklen : k < perm.length := by rw [h.len]; omega
  have hdig := digit_eq_find perm k hklen
  have hlt := findIdx_lt_mem _ (mem_availAtN n perm h k (by omega))
  have hlen := availAt_lengthN n perm h k (by omega)
  refine ⟨?_, by rw [← hlen]; exact hlt⟩
  have hidx :
      (evenDigits perm)[k]'(by
        simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) =
      (lehmerDigits (List.range perm.length) perm)[k]'(by
        rw [lehmerDigits_length]; exact hklen) := by
    simp [evenDigits, List.getElem_take]
  rw [hidx, hdig]

theorem rankAcc_boundN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 2 ≤ n)
    (k : Nat) (hk : k ≤ n - 2) :
    rankAcc perm k < product ((evenRadices n).take k) := by
  have hn' : 2 ≤ perm.length := by rw [h.len]; exact hn
  have hlenD : ((evenDigits perm).take k).length = k := by
    rw [List.length_take, evenDigits_length perm hn', h.len]
    exact Nat.min_eq_left (by omega)
  have hlenR : ((evenRadices n).take k).length = k := by
    rw [List.length_take, evenRadices_length n hn]
    exact Nat.min_eq_left (by omega)
  have hmix : rankAcc perm k =
      mixEncode ((evenRadices n).take k) ((evenDigits perm).take k) := by
    unfold rankAcc
    rw [h.len, hornerZip_mix _ _ (by rw [hlenD, hlenR])]
  rw [hmix]
  apply mixEncode_lt
  · rw [hlenD, hlenR]
  · intro i hi
    have hi' : i < k := by rw [hlenD] at hi; exact hi
    have hdg := evenDigit_eqN n perm h i (by omega)
    have hrad := evenRadix_get n i hn (by omega)
    have hdl : i < (evenDigits perm).length := by
      rw [evenDigits_length perm hn', h.len]; omega
    rw [List.getElem?_take_of_lt hi', List.getElem?_take_of_lt hi',
      List.getElem?_eq_getElem hdl,
      List.getElem?_eq_getElem (by rw [evenRadices_length n hn]; omega)]
    simp only [Option.getD_some, hrad, hdg.1]
    exact hdg.2

theorem product_take_evenN (n k : Nat) (hn : 2 ≤ n) :
    product ((evenRadices n).take k) ≤ evenPermCount n := by
  have hall : product (evenRadices n) = evenPermCount n := product_evenRadices n hn
  have happ := product_append ((evenRadices n).take k) ((evenRadices n).drop k)
  rw [List.take_append_drop] at happ
  rw [happ] at hall
  have hpos : 0 < product ((evenRadices n).drop k) := by
    apply product_pos
    intro r hr
    have hmem : r ∈ evenRadices n := List.mem_of_mem_drop hr
    have hdesc : r ∈ descending n := by
      rw [descending_eq_even n hn]
      exact List.mem_append.mpr (Or.inl hmem)
    exact mem_descending hdesc
  have hmul := Nat.le_mul_of_pos_right (product ((evenRadices n).take k)) hpos
  rw [hall] at hmul
  exact hmul

theorem rankAcc_lt_countN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 2 ≤ n)
    (k : Nat) (hk : k ≤ n - 2) : rankAcc perm k < evenPermCount n :=
  Nat.lt_of_lt_of_le (rankAcc_boundN n perm h hn k hk) (product_take_evenN n k hn)

theorem evenRank_lt_countN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 2 ≤ n) :
    evenRank perm < evenPermCount n := by
  rw [evenRank_eq_acc perm (by rw [h.len]; exact hn), h.len]
  exact rankAcc_lt_countN n perm h hn (n - 2) (Nat.le_refl _)

/-! ## Emitted loop -/

theorem big_from_int_small (v : Nat) (hv : v < limbBase) :
    Megadreifach.big_from_int (Int.ofNat v) = .ok (bigOf (natLimbs v)) := by
  rw [big_from_int_refines v (fits_of_lt_limb hv), limbsOfNat_small v hv]

private theorem fits_small (k : Nat) (hk : k ≤ 64) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 64) hk

theorem limbs_len_le4 (r : Nat) (h : r < limbBase ^ 4) : (natLimbs r).length ≤ 4 :=
  natLimbs_length_le r 4 h

/-- One Lehmer digit of the rank, as bigint arithmetic. -/
theorem rank_step_natN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 3 ≤ n)
    (hcount : evenPermCount n < limbBase ^ 4) (hn30 : n ≤ 30) (i : Nat) (hi : i ≤ n - 3) :
    let avail := availAt perm i
    let idx := avail.findIdx (· == perm[i]'(by rw [h.len]; omega))
    Megadreifach.big_mul (bigOf (natLimbs (rankAcc perm i))) (bigOf (natLimbs (n - i))) =
        .ok (bigOf (natLimbs (rankAcc perm i * (n - i)))) ∧
      Megadreifach.big_add (bigOf (natLimbs (rankAcc perm i * (n - i)))) (bigOf (natLimbs idx)) =
        .ok (bigOf (natLimbs (rankAcc perm (i + 1)))) := by
  intro avail idx
  have hdg := evenDigit_eqN n perm h i (by omega)
  have hn' : 2 ≤ perm.length := by rw [h.len]; omega
  have hv := evenRadix_get perm.length i hn' (by rw [h.len]; omega)
  have heq : rankAcc perm i * (n - i) + idx = rankAcc perm (i + 1) := by
    have hs := rankAcc_succ perm i (by rw [h.len]; omega)
    rw [hs]
    simp only [h.len, evenRadix_get n i (by omega) (by omega), hdg.1]
  have hacc4 : rankAcc perm i < limbBase ^ 4 :=
    Nat.lt_trans (rankAcc_lt_countN n perm h (by omega) i (by omega)) hcount
  have hnext4 : rankAcc perm (i + 1) < limbBase ^ 4 :=
    Nat.lt_trans (rankAcc_lt_countN n perm h (by omega) (i + 1) (by omega)) hcount
  have hprod4 : rankAcc perm i * (n - i) < limbBase ^ 4 := by
    have : rankAcc perm i * (n - i) ≤ rankAcc perm (i + 1) := by rw [← heq]; omega
    omega
  have hradL : n - i < limbBase := by unfold limbBase; omega
  have hidxL : idx < limbBase := by
    have := hdg.2; simp only [idx, avail]; unfold limbBase; omega
  have hl1 := limbs_len_le4 _ hacc4
  have hl2 := natLimbs_length_le (n - i) 1 (by simpa using hradL)
  have hl3 := limbs_len_le4 _ hprod4
  have hl4 := natLimbs_length_le idx 1 (by simpa using hidxL)
  refine ⟨big_mul_nat_gen _ _ (fits_small _ (by omega)), ?_⟩
  rw [big_add_nat _ _ (fits_small _ (by omega)), heq]

theorem rankStep_hitN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 3 ≤ n)
    (hcount : evenPermCount n < limbBase ^ 4) (hn30 : n ≤ 30) (i : Nat) (hi : i ≤ n - 3) :
    rankStep (embed perm) (Int.ofNat n) (Int.ofNat (n - 3))
        (Int.ofNat i, bigOf (natLimbs (rankAcc perm i)), embed (availAt perm i)) =
      if i = n - 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i,
          bigOf (natLimbs (rankAcc perm (i + 1))), embed (availAt perm (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          bigOf (natLimbs (rankAcc perm (i + 1))), embed (availAt perm (i + 1)))) := by
  have hin : i < n := by omega
  have hilen : i < perm.length := by rw [h.len]; exact hin
  have hlenA := availAt_lengthN n perm h i (by omega)
  have hmem := mem_availAtN n perm h i hin
  have hfitsA : FitsLen (availAt perm i).length := by rw [hlenA]; exact fits_small _ (by omega)
  have hfn : FitsLen n := fits_small n (by omega)
  unfold rankStep
  dsimp only
  have hngt : ¬ (Int.ofNat i) > (Int.ofNat (n - 3)) := ofNat_not_gt hi
  rw [if_neg hngt, negI_one, ok_bind, listLen_embed, hlenA]
  have hposA : 0 < n - i := by omega
  have hsubA := subI_ofNat_one (n - i) hposA (fits_small _ (by omega))
  rw [hsubA, ok_bind]
  have hfun : findPerm (embed (availAt perm i)) (embed perm) (Int.ofNat i)
        (Int.ofNat (n - i - 1)) =
      findStep (embed (availAt perm i)) (Int.ofNat (perm[i]'hilen))
        (Int.ofNat (n - i - 1)) := by
    funext σ
    exact findPerm_eq _ perm i hilen _ σ
  rw [hfun]
  rw [show (n - i - 1) = (availAt perm i).length - 1 by rw [hlenA]]
  rw [fuelRange_eq]
  rw [show (0 : Int) = (0 : Int) from rfl]
  have hfb := find_breaks (availAt perm i) (perm[i]'hilen) hmem hfitsA
    (rankAfter (Int.ofNat n) (Int.ofNat i) (bigOf (natLimbs (rankAcc perm i)))
      (embed (availAt perm i)))
    (fun r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r))
  simp only [ofNat_eq_natCast] at hfb ⊢
  rw [hfb]
  dsimp only [rankAfter]
  have hidxLt := findIdx_lt_mem (availAt perm i) hmem
  rw [show decide ((((availAt perm i).findIdx (· == perm[i]'hilen) : Nat) : Int) ≥ 0) = true from
    decide_eq_true (by omega), sudoAssert_true, ok_bind]
  have hsubN : SudoRt.subI (n : Int) (i : Int) = .ok ((n - i : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using subI_ofNat n i hfn (by omega)
  rw [hsubN, ok_bind]
  have hradL : n - i < limbBase := by unfold limbBase; omega
  rw [show ((n - i : Nat) : Int) = Int.ofNat (n - i) from rfl, big_from_int_small _ hradL, ok_bind]
  have hpair := rank_step_natN n perm h hn hcount hn30 i hi
  rw [hpair.1, ok_bind]
  have hidxB : (availAt perm i).findIdx (· == perm[i]'hilen) < limbBase := by
    rw [hlenA] at hidxLt; unfold limbBase; omega
  rw [show (((availAt perm i).findIdx (· == perm[i]'hilen) : Nat) : Int) =
      Int.ofNat ((availAt perm i).findIdx (· == perm[i]'hilen)) from rfl,
    big_from_int_small _ hidxB, ok_bind]
  rw [hpair.2, ok_bind, listLen_embed, hlenA]
  rw [subI_ofNat_one (n - i) hposA (fits_small _ (by omega)), ok_bind]
  rw [show (#[] : Array Int) = embed (takeSkip (availAt perm i)
        ((availAt perm i).findIdx (· == perm[i]'hilen)) 0) by
      rw [takeSkip_zero, embed_nil]]
  rw [fuelRange_eq]
  rw [show (n - i - 1) = (availAt perm i).length - 1 by rw [hlenA]]
  rw [erase_breaks (availAt perm i) _ hidxLt hfitsA]
  simp only [availAt_erase perm i hilen, pure_eq_ok, ok_bind]
  by_cases heq : i = n - 3
  · simp [heq, beq_int_iff]
  · have hneI : ¬ (Int.ofNat i = Int.ofNat (n - 3)) := fun hq => heq (Int.ofNat.inj hq)
    have haddI := addI_ofNat_one i (fits_small _ (by omega))
    have hneI' : ¬ ((i : Int) = ((n - 3 : Nat) : Int)) := by exact_mod_cast heq
    simp only [ofNat_eq_natCast] at haddI
    simp [beq_int_iff, hneI', haddI, ok_bind, heq]


private theorem availAt_zeroN (n : Nat) (perm : List Nat) (h : PermNWf n perm) :
    availAt perm 0 = List.range n := by
  simp [availAt, dropUsed, List.take_zero, h.len]

private theorem rankRunN (n : Nat) (perm : List Nat) (h : PermNWf n perm) (hn : 3 ≤ n)
    (hcount : evenPermCount n < limbBase ^ 4) (hn30 : n ≤ 30) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      (Int.ofNat 0, (bigOf (natLimbs (rankAcc perm 0)), embed (availAt perm 0)))
      (fuelRange (Int.ofNat 0) (Int.ofNat (n - 3)))
      (rankStep (embed perm) (Int.ofNat n) (Int.ofNat (n - 3)))
      (fun σ => pure σ.2.1)
      (fun r => pure r) =
      .ok (bigOf (natLimbs (evenRank perm))) := by
  apply chain_loop
    (f := fun i => (bigOf (natLimbs (rankAcc perm i)), embed (availAt perm i)))
    (fromN := 0) (toN := n - 3) (hle := Nat.zero_le _)
  · intro i _ hi
    exact rankStep_hitN n perm h hn hcount hn30 i hi
  · rw [evenRank_eq_acc perm (by rw [h.len]; omega), h.len,
      show n - 3 + 1 = n - 2 by omega]
    rfl

/-- `Generated.even_perm_rank_big` is algebraic `evenRank` on every permutation of
    `0..n-1`, `3 ≤ n ≤ 30` with `(n!/2) < 10^36` (true for `n = 20, 30`). -/
theorem even_perm_rank_big_refines_gen (n : Nat) (perm : List Nat) (h : PermNWf n perm)
    (hn : 3 ≤ n) (hn30 : n ≤ 30) (hcount : evenPermCount n < limbBase ^ 4) :
    Megadreifach.even_perm_rank_big (embed perm) = .ok (bigOf (natLimbs (evenRank perm))) := by
  have hfn : FitsLen n := fits_small n (by omega)
  unfold Megadreifach.even_perm_rank_big
  rw [listLen_embed, h.len]
  dsimp only
  rw [range_list_refines n (by omega) hfn, ok_bind]
  rw [big_zero_spec, ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl]
  rw [subI_ofNat n 3 hfn hn, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := rankStep (embed perm) (Int.ofNat n) (Int.ofNat (n - 3)))
    intro σ
    unfold rankStep findPerm rankAfter eraseStep
    dsimp only
    rfl
  · rw [show bigOf [] = bigOf (natLimbs (rankAcc perm 0)) by rw [rankAcc_zero, natLimbs_zero],
      show embed (List.range n) = embed (availAt perm 0) from
        (congrArg embed (availAt_zeroN n perm h)).symm]
    exact rankRunN n perm h hn hcount hn30

theorem evenPermCount20_lt : evenPermCount 20 < limbBase ^ 4 := by
  unfold evenPermCount factorial limbBase; decide

theorem evenPermCount30_lt : evenPermCount 30 < limbBase ^ 4 := by
  unfold evenPermCount limbBase; decide

end MegaDreifachV1.Link2
