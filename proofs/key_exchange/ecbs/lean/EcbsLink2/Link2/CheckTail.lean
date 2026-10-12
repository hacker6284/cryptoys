/-
  `invert_checked`: hole 0 of the check product is nonzero, the tail is zero,
  and a red peg mirrors the gap. That is `Spec.fieldInv`.
-/
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.Mirror

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem fieldMul_length (n k bench : Nat) (x y : List Nat) (hn : n ≤ bench) :
    (fieldMul n k bench x y).length = n := by
  unfold fieldMul
  rw [List.length_take]
  have hsch : (school n x y (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfold := laneFold_length n (n - k) (school n x y (List.replicate bench 0) false)
    (by rw [hsch]; exact hn)
  rw [laneFold] at hfold
  rw [hfold, hsch, Nat.min_eq_left hn]

theorem mul_span_n (n bench : Nat) (hpos : 0 < n) (h : 2 * (n - 1) < bench) :
    n ≤ bench := by omega

theorem cube_span_le (n bench comb : Nat) (h : 3 * (n - 1) + comb < bench) :
    3 * (n - 1) < bench :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ comb) h

theorem trit_nz_one_two (c : Nat) (hc : c ≤ 2) (hnz : c ≠ 0) : c = 1 ∨ c = 2 := by
  omega

theorem cubeTimes_trits (n k bench : Nat) (x : List Nat) (tally : Nat)
    (htri : allTritList x) (hspan : 3 * (n - 1) < bench) (hk : k ≤ n) :
    allTritList (cubeTimes n k bench x tally) := by
  induction tally with
  | zero => simpa [cubeTimes] using htri
  | succ tally ih =>
    rw [cubeTimes]
    exact fieldCube_trits n k bench _ ih hspan hk

private theorem fieldMul_self (n k bench : Nat) (a b : List Nat)
    (hb : b.length = n) (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench a b) ∧ (fieldMul n k bench a b).length = n := by
  have h := fieldMul_trits n k bench a b hspan hn
  have htb : b.take n = b := by rw [← hb, List.take_length]
  exact ⟨by simpa [htb] using h, fieldMul_length n k bench a b hn⟩

theorem invClimb_trits (n k bench : Nat) (x g : List Nat) (tally : Nat) (rs : List Nat)
    (_hx : x.length = n) (hg : g.length = n)
    (_hxt : allTritList x) (hgt : allTritList g)
    (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) (_hk : k ≤ n) :
    allTritList (invClimb n k bench x (g, tally) rs).1 ∧
      (invClimb n k bench x (g, tally) rs).1.length = n := by
  induction rs generalizing g tally with
  | nil =>
    exact ⟨by simpa [invClimb] using hgt, by simpa [invClimb] using hg⟩
  | cons r rs ih =>
    let s := cubeTimes n k bench g tally
    let g1 := fieldMul n k bench g s
    have hlenS := cubeTimes_length n k bench g tally hg hn
    have hmul := fieldMul_self n k bench g s hlenS hspan hn
    let g' := if r = 2 then fieldMul n k bench x (fieldCube n k bench g1) else g1
    have hg' : allTritList g' ∧ g'.length = n := by
      by_cases hred : r = 2
      · have hlenC := fieldCube_length n k bench g1 hn
        have hmul2 := fieldMul_self n k bench x (fieldCube n k bench g1) hlenC hspan hn
        simpa [g', hred] using ⟨hmul2.1, hmul2.2⟩
      · simpa [g', hred] using hmul
    have hfst : (invRung n k bench x g tally r rs.isEmpty).1 = g' := by
      by_cases hred : r = 2 <;> simp [invRung, g', g1, s, hred]
    have hstep := ih (invRung n k bench x g tally r rs.isEmpty).1
      (invRung n k bench x g tally r rs.isEmpty).2
      (by rw [hfst]; exact hg'.2) (by rw [hfst]; exact hg'.1)
    simpa [invClimb] using hstep

theorem invGap_trits (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (lay : TierShape t)
    (hpos : 0 < t.n) (hx : xs.length = t.n) (htri : allTritList xs) :
    allTritList (invGap t.n t.k t.benchlen xs) := by
  have hn := mul_span_n t.n t.benchlen hpos sat.mul_span
  have hspan := cube_span_le t.n t.benchlen t.combgap sat.cube_span
  have hclimb := invClimb_trits t.n t.k t.benchlen xs xs 1
    ((rungList (t.n - 1)).reverse) hx hx htri htri hspan hn lay.k_le
  simpa [invGap] using
    fieldCube_trits t.n t.k t.benchlen
      (invClimb t.n t.k t.benchlen xs (xs, 1) ((rungList (t.n - 1)).reverse)).1
      hclimb.1 hspan lay.k_le

theorem invGap_length (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hpos : 0 < t.n) :
    (invGap t.n t.k t.benchlen xs).length = t.n := by
  rw [invGap]
  exact fieldCube_length t.n t.k t.benchlen _
    (mul_span_n t.n t.benchlen hpos sat.mul_span)

/-- `zeroScan_ok` for the stepper the emitter wrote, once that stepper is
    `zeroScanStep`. The equality is `rfl` at the use site. -/
theorem zeroScan_ok_of {α : Type} (L : List Nat) (n i : Nat)
    {step : Int → Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board)}
    (hlen : L.length = n)
    (hstep : ∀ k, step k = zeroScanStep (embed L) (Int.ofNat (n - 1)) k)
    (hpos : 0 < L.length) (hi : 1 ≤ i) (hiL : i ≤ L.length) (hf : FitsLen L.length)
    (htail : ∀ j, i ≤ j → ∀ hj : j < L.length, L[j] = 0)
    (after : Int → Except SudoRt.Trap α) (onRet : Ecbs.Board → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (Int.ofNat i)
        (fuelRange (Int.ofNat i) (Int.ofNat (n - 1)))
        step after onRet =
      after (Int.ofNat (if L.length ≤ i then i else n - 1)) := by
  subst hlen
  rw [funext hstep]
  exact zeroScan_ok L i hpos hi hiL hf htail after onRet

theorem zeroScan_err_of {α : Type} (L : List Nat) (n j : Nat)
    {step : Int → Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board)}
    (hlen : L.length = n)
    (hstep : ∀ k, step k = zeroScanStep (embed L) (Int.ofNat (n - 1)) k)
    (hpos : 0 < L.length) (hj : 1 ≤ j) (hjL : j < L.length) (hf : FitsLen L.length)
    (hbad : L[j] ≠ 0)
    (hpre : ∀ k, 1 ≤ k → ∀ hk : k < j, L[k]'(Nat.lt_trans hk hjL) = 0)
    (after : Int → Except SudoRt.Trap α) (onRet : Ecbs.Board → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (Int.ofNat 1)
        (fuelRange (Int.ofNat 1) (Int.ofNat (n - 1)))
        step after onRet =
      .error { kind := "AssertFailed"
               detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat L[j])} != {SudoRt.Canon.canon (0 : Int)}" } := by
  subst hlen
  rw [funext hstep]
  rw [show Int.ofNat 1 = (1 : Int) from rfl]
  exact zeroScan_err L j hpos hj hjL hf hbad hpre after onRet

private theorem getD_eq_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.getD j 0 = xs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem pegList_length (c n : Nat) (hpos : 0 < n) :
    (c :: List.replicate (n - 1) 0).length = n := by
  simp [List.length_replicate]; omega

theorem eq_pegList (L : List Nat) (n c : Nat) (hpos : 0 < n) (hL : L.length = n)
    (hc : L[0]'(by rw [hL]; exact hpos) = c)
    (htail : ∀ j, 1 ≤ j → ∀ hj : j < n, L[j]'(by rw [hL]; exact hj) = 0) :
    L = c :: List.replicate (n - 1) 0 := by
  apply List.ext_getElem
  · rw [hL, pegList_length c n hpos]
  · intro j hjL hjR
    have hjn : j < n := by rw [hL] at hjL; exact hjL
    by_cases hj0 : j = 0
    · subst hj0
      simpa using hc
    · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      rw [htail j hj1 hjn]
      rw [← getD_eq_get _ j (by rw [pegList_length c n hpos]; exact hjn),
        ← Nat.sub_add_cancel hj1, List.getD_cons_succ]
      have hlt : j - 1 < n - 1 := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hlt, Option.getD_some]

theorem exists_nz_tail (L : List Nat) (n : Nat)
    (h : ¬ (∀ j, 1 ≤ j → j < n → L.getD j 0 = 0)) :
    ∃ j, 1 ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0 := by
  induction n with
  | zero => exact absurd (by intro j _hj1 hj; cases hj) h
  | succ m ih =>
    by_cases hm : 1 ≤ m ∧ L.getD m 0 ≠ 0
    · exact ⟨m, hm.1, Nat.lt_succ_self m, hm.2⟩
    · have h' : ¬ ∀ j, 1 ≤ j → j < m → L.getD j 0 = 0 := by
        intro hall
        apply h
        intro j hj1 hjn
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjn) with hlt | heq
        · exact hall j hj1 hlt
        · rw [heq]
          cases hdec : decide (L.getD m 0 = 0) with
          | true => exact of_decide_eq_true hdec
          | false =>
            have hj1' : 1 ≤ m := by rw [heq] at hj1; exact hj1
            exact absurd ⟨hj1', of_decide_eq_false hdec⟩ hm
      obtain ⟨j, hj1, hjn, hnz⟩ := ih h'
      exact ⟨j, hj1, Nat.lt_succ_of_lt hjn, hnz⟩

theorem first_tail (L : List Nat) (n i : Nat) (hi : 1 ≤ i) (_hiN : i ≤ n)
    (hex : ∃ j, i ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0) :
    ∃ j, i ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0 ∧
      ∀ k, i ≤ k → k < j → L.getD k 0 = 0 :=
  go L n i (n - i) hi rfl hex
where
  go (L : List Nat) (n i fuel : Nat) (hi : 1 ≤ i) (hfuel : n - i = fuel)
      (hex : ∃ j, i ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0) :
      ∃ j, i ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0 ∧
        ∀ k, i ≤ k → k < j → L.getD k 0 = 0 := by
    match fuel with
    | 0 =>
      rcases hex with ⟨j, hj1, hjn, _⟩
      have : n ≤ i := (Nat.sub_eq_zero_iff_le).mp hfuel
      omega
    | fuel + 1 =>
      have hiL : i < n := by
        rcases hex with ⟨j, hj1, hjn, _⟩
        exact Nat.lt_of_le_of_lt hj1 hjn
      by_cases hz : L.getD i 0 = 0
      · have hex' : ∃ j, i + 1 ≤ j ∧ j < n ∧ L.getD j 0 ≠ 0 := by
          rcases hex with ⟨j, hj1, hjn, hnz⟩
          have hne : i ≠ j := by intro h; subst h; exact hnz hz
          exact ⟨j, by omega, hjn, hnz⟩
        have hfuel' : n - (i + 1) = fuel := by omega
        obtain ⟨j, hj1, hjn, hnz, hpre⟩ :=
          go L n (i + 1) fuel (Nat.le_succ_of_le hi) hfuel' hex'
        refine ⟨j, Nat.le_trans (Nat.le_succ i) hj1, hjn, hnz, ?_⟩
        intro k hk1 hk
        by_cases hki : k = i
        · subst hki; exact hz
        · exact hpre k (by omega) hk
      · refine ⟨i, Nat.le_refl i, hiL, hz, ?_⟩
        intro k hk1 hk
        exact absurd (Nat.lt_of_lt_of_le hk hk1) (Nat.lt_irrefl k)

theorem fieldInv_some_shape (n k bench : Nat) (x ans : List Nat)
    (h : fieldInv n k bench x = some ans) :
    let g := invGap n k bench x
    let v := fieldMul n k bench g x
    (v = 1 :: List.replicate (n - 1) 0 ∧ ans = g) ∨
      (v = 2 :: List.replicate (n - 1) 0 ∧ ans = mirrorTrits g) := by
  unfold fieldInv at h
  dsimp at h
  split at h
  · next hv =>
    cases h
    exact Or.inl ⟨hv, rfl⟩
  · next _hv =>
    split at h
    · next hv2 =>
      cases h
      exact Or.inr ⟨hv2, rfl⟩
    · cases h

theorem fieldInv_none_shape (n k bench : Nat) (x : List Nat)
    (h : fieldInv n k bench x = none) :
    let g := invGap n k bench x
    let v := fieldMul n k bench g x
    v ≠ 1 :: List.replicate (n - 1) 0 ∧ v ≠ 2 :: List.replicate (n - 1) 0 := by
  unfold fieldInv at h
  dsimp at h
  split at h
  · next _hv => cases h
  · next hv =>
    split at h
    · next _hv2 => cases h
    · next hv2 => exact ⟨hv, hv2⟩

private theorem mirror_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    home < (mirrorHome b home hH arr mv).sudo_5Board_4home.size := by
  simp [mirrorHome, withMoves, Array.size_set]
  exact hH

private theorem head_of_peg (P : List Nat) (n c : Nat) (hP : 0 < P.length)
    (hv : P = c :: List.replicate (n - 1) 0) : P[0] = c := by
  have hgd : P.getD 0 0 = c := by rw [hv]; simp [List.getD_cons_zero]
  rw [getD_eq_get P 0 hP] at hgd
  exact hgd

/-- Accepted check: home 5 is the list `Spec.fieldInv` returns. -/
theorem invert_checked_some (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) (ans : List Nat)
    (hacc : fieldInv t.n t.k t.benchlen xs = some ans) :
    ∃ (b' : Ecbs.Board) (h5 : 5 < b'.sudo_5Board_4home.size)
      (h5D : 5 < b'.sudo_5Board_4held.size),
      Ecbs.invert_checked (bottomBoard t xs) ((2 : Nat) : Int) = .ok b' ∧
      b'.sudo_5Board_4home[5]'h5 = embed ans ∧
      b'.sudo_5Board_4held[5]'h5D = true ∧
      b'.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) ∧
      ans.length = t.n := by
  have hpos : 0 < t.n := hOk.n_pos
  have hnbench := mul_span_n t.n t.benchlen hpos sat.mul_span
  have hspan3 := cube_span_le t.n t.benchlen t.combgap sat.cube_span
  let g := invGap t.n t.k t.benchlen xs
  let P := fieldMul t.n t.k t.benchlen g xs
  have hlenP : P.length = t.n := fieldMul_length _ _ _ _ _ hnbench
  have hP0 : 0 < P.length := by rw [hlenP]; exact hpos
  have hshape := fieldInv_some_shape t.n t.k t.benchlen xs ans hacc
  have hpeg : P = 1 :: List.replicate (t.n - 1) 0 ∨
      P = 2 :: List.replicate (t.n - 1) 0 := by
    rcases hshape with ⟨hvP, _⟩ | ⟨hvP, _⟩
    · exact Or.inl (by simpa [P, g] using hvP)
    · exact Or.inr (by simpa [P, g] using hvP)
  have htriG : allTritList g := invGap_trits t xs sat lay hpos hx htri
  have hlenG : g.length = t.n := invGap_length t xs sat hpos
  obtain ⟨_bZ, _bM, bR, _v, h5, hinv, hmul, hread, hv, hhome5, _hbench, hframe, _⟩ :=
    check_mul t hOk xs hx htri sat hR lay
  obtain ⟨h5D, mv, hheld, hmv, hfit, hnT⟩ := hframe
  have hfitn : FitsLen t.n := FitsLen.of_le hfit (Nat.le_add_left t.n mv)
  unfold Ecbs.invert_checked
  rw [hinv, ok_bind]
  conv => zeta
  rw [hmul, ok_bind]
  conv => zeta
  rw [hread, ok_bind]
  dsimp
  rw [hv, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed P 0 hP0, ok_bind,
    sEq_ofNat (P[0]'(hP0)) 0]
  have hhead : (P[0]'(hP0)) ≠ 0 := by
    rcases hpeg with hvP | hvP
    · rw [head_of_peg P t.n 1 hP0 hvP]; decide
    · rw [head_of_peg P t.n 2 hP0 hvP]; decide
  rw [decide_eq_false hhead, Bool.not_false, sudoAssert_true, ok_bind]
  rw [listLen_embed, hlenP, subI_ofNat_one t.n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (1 : Int) = Int.ofNat 1 from rfl, fuelRange_eq, except_bind_pure]
  rw [zeroScan_ok_of P t.n 1 hlenP ?hstep hP0 (Nat.le_refl _)
      (by rw [hlenP]; exact Nat.succ_le_of_lt hpos) (by rwa [hlenP]) ?htail]
  · have heq :
        fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen xs) xs = P := by
      simp [P, g]
    rcases hpeg with hvP | hvP
    · have hc : (P[0]'(hP0)) = 1 := head_of_peg P t.n 1 hP0 hvP
      simp only [heq, sEq_int, hc, pure_eq_ok,
        show decide ((1 : Int) = (2 : Int)) = false by decide,
        Bool.false_eq_true, if_false]
      rcases hshape with ⟨_, hans⟩ | ⟨hv2, _⟩
      · refine ⟨bR, h5, h5D, rfl, ?_, hheld, hnT, ?_⟩
        · rw [hans]
          simpa [g] using hhome5
        · rw [hans]
          exact hlenG
      · have hv2' : P = 2 :: List.replicate (t.n - 1) 0 := by simpa [P, g] using hv2
        have h2 : (P[0]'(hP0)) = 2 := head_of_peg P t.n 2 hP0 hv2'
        rw [hc] at h2
        cases h2
    · have hc : (P[0]'(hP0)) = 2 := head_of_peg P t.n 2 hP0 hvP
      simp only [heq, sEq_int, hc, ok_bind,
        show decide (Int.ofNat 2 = 2) = true from rfl, if_true]
      have harr : bR.sudo_5Board_4home[5]'h5 = embed g := by
        simpa [g] using hhome5
      rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl]
      rw [mirror_refines bR 5 g t.n mv h5 h5D hheld harr hnT hlenG hpos htriG hmv hfit,
        ok_bind, pure_eq_ok]
      rcases hshape with ⟨hv1, _⟩ | ⟨_, hans⟩
      · have hv1' : P = 1 :: List.replicate (t.n - 1) 0 := by simpa [P, g] using hv1
        have h1 : (P[0]'(hP0)) = 1 := head_of_peg P t.n 1 hP0 hv1'
        rw [hc] at h1
        cases h1
      · let bM := mirrorHome bR 5 h5 (embed (mirrorTrits g)) (mv + pegCount g)
        have h5' : 5 < bM.sudo_5Board_4home.size := mirror_size _ _ _ _ _
        have h5D' : 5 < bM.sudo_5Board_4held.size := by
          rw [show bM.sudo_5Board_4held = bR.sudo_5Board_4held from
            mirrorHome_held bR 5 h5 _ _]
          exact h5D
        refine ⟨bM, h5', h5D', rfl, ?_, ?_, ?_, ?_⟩
        · rw [hans]
          exact mirrorHome_at bR 5 h5 (embed (mirrorTrits g)) (mv + pegCount g) h5'
        · exact hheld
        · rw [show bM.sudo_5Board_1t = bR.sudo_5Board_1t from
            mirrorHome_tier bR 5 h5 _ _]
          exact hnT
        · rw [hans, mirrorTrits_flip, List.length_map]
          exact hlenG
  · intro k
    rfl
  · intro j hj1 hj
    rw [← getD_eq_get P j hj]
    rcases hpeg with hvP | hvP
    · rw [hvP, show j = j - 1 + 1 from (Nat.sub_add_cancel hj1).symm, List.getD_cons_succ,
        List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos (by omega : j - 1 < t.n - 1), Option.getD_some]
    · rw [hvP, show j = j - 1 + 1 from (Nat.sub_add_cancel hj1).symm, List.getD_cons_succ,
        List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos (by omega : j - 1 < t.n - 1), Option.getD_some]

/-- Rejected check: the hole-0 assert or the zero tail fails. -/
theorem invert_checked_none (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t)
    (hrej : fieldInv t.n t.k t.benchlen xs = none) :
    ∃ e, Ecbs.invert_checked (bottomBoard t xs) ((2 : Nat) : Int) = .error e ∧
      e.kind = "AssertFailed" := by
  have hpos : 0 < t.n := hOk.n_pos
  have hnbench := mul_span_n t.n t.benchlen hpos sat.mul_span
  let g := invGap t.n t.k t.benchlen xs
  let P := fieldMul t.n t.k t.benchlen g xs
  have hlenP : P.length = t.n := fieldMul_length _ _ _ _ _ hnbench
  have hP0 : 0 < P.length := by rw [hlenP]; exact hpos
  have hne := fieldInv_none_shape t.n t.k t.benchlen xs hrej
  obtain ⟨_bZ, _bM, _bR, _v, _h5, hinv, hmul, hread, hv, _hhome, _hbench, hframe, _⟩ :=
    check_mul t hOk xs hx htri sat hR lay
  obtain ⟨_h5D, mv, _hheld, _hmv, hfit, _hnT⟩ := hframe
  have hfitn : FitsLen t.n := FitsLen.of_le hfit (Nat.le_add_left t.n mv)
  unfold Ecbs.invert_checked
  rw [hinv, ok_bind]
  conv => zeta
  rw [hmul, ok_bind]
  conv => zeta
  rw [hread, ok_bind]
  dsimp
  rw [hv, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed P 0 hP0, ok_bind,
    sEq_ofNat (P[0]'(hP0)) 0]
  by_cases hhead : (P[0]'(hP0)) = 0
  · rw [hhead]
    rw [show decide ((0 : Nat) = 0) = true from rfl, Bool.not_true]
    unfold SudoRt.sudoAssert SudoRt.fail
    simp only [Bool.false_eq_true, if_false, bind, Except.bind, error_bind]
    exact ⟨{ kind := "AssertFailed", detail := s!"line {728}" }, rfl, rfl⟩
  · rw [decide_eq_false hhead, Bool.not_false, sudoAssert_true, ok_bind]
    have htriP : allTritList P := by
      have h := fieldMul_trits t.n t.k t.benchlen g xs
        (cube_span_le _ _ _ sat.cube_span) hnbench
      simpa [P, g, show xs.take t.n = xs from by rw [← hx, List.take_length]] using h
    have hnot : ¬ ∀ j, 1 ≤ j → ∀ hj : j < t.n, P[j]'(by rw [hlenP]; exact hj) = 0 := by
      intro hall
      have hlist := eq_pegList P t.n (P[0]'(hP0)) hpos hlenP rfl hall
      have hc := trit_nz_one_two _ (trit_get htriP hP0) hhead
      rcases hc with hc | hc
      · exact hne.1 (by simpa [P, g, hc] using hlist)
      · exact hne.2 (by simpa [P, g, hc] using hlist)
    have hex : ∃ j, 1 ≤ j ∧ j < t.n ∧ P.getD j 0 ≠ 0 :=
      exists_nz_tail P t.n (by
        intro hall
        apply hnot
        intro j hj1 hj
        have h0 := hall j hj1 hj
        rw [getD_eq_get P j (by rw [hlenP]; exact hj)] at h0
        exact h0)
    obtain ⟨j, hj1, hjn, hbad, hpre⟩ :=
      first_tail P t.n 1 (Nat.le_refl _) (Nat.succ_le_of_lt hpos) hex
    have hjL : j < P.length := by rw [hlenP]; exact hjn
    rw [listLen_embed, hlenP, subI_ofNat_one t.n hpos hfitn, ok_bind]
    conv => zeta
    rw [show (1 : Int) = Int.ofNat 1 from rfl, fuelRange_eq, except_bind_pure]
    rw [zeroScan_err_of P t.n j hlenP ?hstep hP0 hj1 hjL (by rwa [hlenP])
        (by rw [getD_eq_get P j hjL] at hbad; exact hbad) ?hpre]
    · let e730 : SudoRt.Trap :=
        { kind := "AssertFailed"
          detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat (P[j]'(hjL)))} != {SudoRt.Canon.canon (0 : Int)}" }
      exact ⟨e730, rfl, rfl⟩
    · intro k; rfl
    · intro k hk1 hk
      have hkL : k < P.length := Nat.lt_trans hk hjL
      have h0 := hpre k hk1 hk
      rw [getD_eq_get P k hkL] at h0
      exact h0

private theorem n_le_four (n : Nat) : n ≤ 4 * n + 8 := by omega

/-- Exported inverse: `new_board`, `put` at the bottom, the checked inverse, `value` of the gap. -/
theorem invert_number_refines (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) (ans : List Nat)
    (hacc : fieldInv t.n t.k t.benchlen xs = some ans) :
    Ecbs.invert_number (embTier t) (embed xs) = .ok (embed ans) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  unfold Ecbs.invert_number
  rw [new_board_refines t hOk, ok_bind]
  conv => zeta
  rw [put_bottom_board t hOk xs hx, ok_bind]
  obtain ⟨b', h5, h5D, hok, hhome, hheld, hn, hlenA⟩ :=
    invert_checked_some t hOk xs hx htri sat hR lay ans hacc
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hok, ok_bind]
  conv => zeta
  rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl,
    value_held_refines b' 5 ans t.n h5D h5 hheld hhome hn
      (Nat.le_of_eq hlenA.symm) hfn]
  rw [show ans.take t.n = ans from by rw [← hlenA, List.take_length], ok_bind, pure_eq_ok]

theorem invert_number_none (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t)
    (hrej : fieldInv t.n t.k t.benchlen xs = none) :
    ∃ e, Ecbs.invert_number (embTier t) (embed xs) = .error e ∧
      e.kind = "AssertFailed" := by
  unfold Ecbs.invert_number
  rw [new_board_refines t hOk, ok_bind]
  conv => zeta
  rw [put_bottom_board t hOk xs hx, ok_bind]
  obtain ⟨e, hok, hk⟩ := invert_checked_none t hOk xs hx htri sat hR lay hrej
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hok]
  simp only [error_bind]
  exact ⟨e, rfl, hk⟩

/-- One peg in hole 0, zeros after. A trit list of length `n`, so the inverse domain is inhabited. -/
def onePeg (n : Nat) : List Nat := 1 :: List.replicate (n - 1) 0

theorem onePeg_length (n : Nat) (h : 0 < n) : (onePeg n).length = n := by
  simp [onePeg, List.length_replicate]; omega

theorem onePeg_trits (n : Nat) : allTritList (onePeg n) := by
  intro x hx
  simp [onePeg, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨_, rfl⟩ <;> decide

theorem demo_inv_domain :
    BoardOk Spec.demo ∧ TierSat Spec.demo ∧ TierShape Spec.demo ∧
      0 < tierR Spec.demo ∧ (onePeg Spec.demo.n).length = Spec.demo.n ∧
      allTritList (onePeg Spec.demo.n) :=
  ⟨demo_board, demo_tier_sat, demo_shape,
    by rw [tierR, demo_rungs]; decide, onePeg_length _ demo_board.n_pos, onePeg_trits _⟩

theorem toy_inv_domain :
    BoardOk Spec.toy ∧ TierSat Spec.toy ∧ TierShape Spec.toy ∧
      0 < tierR Spec.toy ∧ (onePeg Spec.toy.n).length = Spec.toy.n ∧
      allTritList (onePeg Spec.toy.n) :=
  ⟨toy_board, toy_tier_sat, toy_shape,
    by rw [tierR, toy_rungs]; decide, onePeg_length _ toy_board.n_pos, onePeg_trits _⟩

theorem hobby_inv_domain :
    BoardOk Spec.hobby ∧ TierSat Spec.hobby ∧ TierShape Spec.hobby ∧
      0 < tierR Spec.hobby ∧ (onePeg Spec.hobby.n).length = Spec.hobby.n ∧
      allTritList (onePeg Spec.hobby.n) :=
  ⟨hobby_board, hobby_tier_sat, hobby_shape,
    by rw [tierR, hobby_rungs]; decide, onePeg_length _ hobby_board.n_pos, onePeg_trits _⟩

theorem serious_inv_domain :
    BoardOk Spec.serious ∧ TierSat Spec.serious ∧ TierShape Spec.serious ∧
      0 < tierR Spec.serious ∧ (onePeg Spec.serious.n).length = Spec.serious.n ∧
      allTritList (onePeg Spec.serious.n) :=
  ⟨serious_board, serious_tier_sat, serious_shape,
    by rw [tierR, serious_rungs]; decide, onePeg_length _ serious_board.n_pos, onePeg_trits _⟩

end EcbsLink2.Link2
