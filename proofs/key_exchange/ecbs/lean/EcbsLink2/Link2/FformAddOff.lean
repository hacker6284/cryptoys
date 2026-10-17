/-
  `Ecbs.add` with the mirror flag off. The destination becomes `fieldAdd` of
  the two homes, not the mirrored source. On the gap that is `u²Z + v³`
  plus `v²Z`, which is SPEC.md §3 R7's `fformF`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.FieldLin
import EcbsLink2.Link2.FieldComm
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_id (b : Ecbs.Board) (m : Int)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) : withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

/-- First `k` holes are `dst[j] + src[j]` in GF(3). The mirror stays off. -/
def addPlain (n k : Nat) (dst src : List Nat) : List Nat :=
  (List.range n).map fun j =>
    if j < k then tritAdd (coeff dst j) (coeff src j) else coeff dst j

theorem addPlain_length (n k : Nat) (dst src : List Nat) :
    (addPlain n k dst src).length = n := by
  simp [addPlain, List.length_map, List.length_range]

theorem addPlain_get (n k : Nat) (dst src : List Nat) (j : Nat) (hj : j < n) :
    (addPlain n k dst src)[j]'(by rw [addPlain_length]; exact hj) =
      if j < k then tritAdd (coeff dst j) (coeff src j) else coeff dst j := by
  simp [addPlain, List.getElem_map, List.getElem_range, hj]

theorem addPlain_succ (n i : Nat) (dst src : List Nat)
    (hi : i < n) (_hd : dst.length = n) (_hs : src.length = n) :
    addPlain n (i + 1) dst src =
      (addPlain n i dst src).set i (tritAdd (coeff dst i) (coeff src i)) := by
  have hlen : (addPlain n i dst src).length = n := addPlain_length n i dst src
  apply List.ext_getElem
  · simp [addPlain_length, List.length_set]
  · intro j hj1 hj2
    have hj : j < n := by rw [addPlain_length] at hj1; exact hj1
    rw [addPlain_get n (i + 1) dst src j hj]
    by_cases hji : j = i
    · subst hji
      simp [List.getElem_set_self, hi, hlen]
    · rw [List.getElem_set_ne (Ne.symm hji)]
      rw [addPlain_get n i dst src j hj]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · simp [hlt, show ¬ j < i + 1 by omega, hji]

theorem addPlain_skip (n i : Nat) (dst src : List Nat)
    (hi : i < n) (hd : dst.length = n) (hs : src.length = n)
    (hz : src[i] = 0) (hdt : dst[i] ≤ 2) :
    addPlain n (i + 1) dst src = addPlain n i dst src := by
  rw [addPlain_succ n i dst src hi hd hs]
  have hidx : i < (addPlain n i dst src).length := by rw [addPlain_length]; exact hi
  have hlt : ¬ i < i := Nat.lt_irrefl i
  have hcell : (addPlain n i dst src)[i] = coeff dst i := by
    rw [addPlain_get n i dst src i hi, if_neg hlt]
  have hval : tritAdd (coeff dst i) (coeff src i) = coeff dst i := by
    rw [coeff_eq_get src i (hs.symm ▸ hi), hz, coeff_eq_get dst i (hd.symm ▸ hi)]
    exact tritAdd_right_zero _ hdt
  rw [hval, ← hcell]
  apply List.ext_getElem
  · simp [List.length_set]
  · intro j hj1 hj2
    by_cases h : j = i
    · subst h
      simp [List.getElem_set_self, hcell]
    · simp [List.getElem_set_ne (Ne.symm h)]

theorem addPlain_done (n : Nat) (dst src : List Nat)
    (_hd : dst.length = n) (_hs : src.length = n) :
    addPlain n n dst src = fieldAdd n dst src := by
  apply List.ext_getElem
  · simp [addPlain_length, fieldAdd, List.length_map, List.length_range]
  · intro i hi1 hi2
    have hi : i < n := by rw [addPlain_length] at hi1; exact hi1
    rw [addPlain_get n n dst src i hi, if_pos hi]
    have hlen : i < (fieldAdd n dst src).length := by
      simp [fieldAdd, List.length_map, List.length_range, hi]
    rw [← coeff_eq_get _ i hlen, fieldAdd_at n dst src i hi]

private theorem addStep_zero_off (src cur : List Nat) (i n : Nat) (b : Ecbs.Board)
    (hi : i < src.length) (hz : src[i] = 0) (hto : i ≤ n - 1) (hfi : FitsLen (i + 1)) :
    addStep (embed src) (Int.ofNat (n - 1)) false
        (Int.ofNat i, (embed cur, b)) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, (embed cur, b)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (embed cur, b)))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hto
  simp only [addStep, hng, if_false, if_pos rfl, if_true]
  rw [atL_embed src i hi]
  simp only [bind, Except.bind, pure, Except.pure, sEq_ofNat_zero, hz, decide_True,
    Bool.not_true, Bool.false_eq_true, if_false]
  exact asc_tail (n - 1) i hfi _

private theorem addStep_nz_off (src cur : List Nat) (i n moves : Nat) (b : Ecbs.Board)
    (hiS : i < src.length) (hiC : i < cur.length) (hnz : src[i] ≠ 0) (hc : src[i] ≤ 2)
    (hd : cur[i] ≤ 2) (hto : i ≤ n - 1)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) (hfi : FitsLen (i + 1)) :
    addStep (embed src) (Int.ofNat (n - 1)) false
        (Int.ofNat i, (embed cur, b)) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            (embed (cur.set i (tritAdd cur[i] src[i])),
              withMoves b (Int.ofNat (moves + 1)))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            (embed (cur.set i (tritAdd cur[i] src[i])),
              withMoves b (Int.ofNat (moves + 1)))))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hto
  simp only [addStep, hng, if_false, if_pos rfl]
  rw [atL_embed src i hiS]
  simp only [bind, Except.bind, pure, Except.pure, sEq_ofNat_zero, hnz, decide_False,
    Bool.not_false, if_true, Bool.false_eq_true, if_false]
  rw [atL_embed cur i hiC]
  simp only [bind, Except.bind, pure, Except.pure]
  have hsum : FitsLen (cur[i] + src[i]) := by
    exact fits_small (by omega)
  rw [addI_ofNat _ _ hsum]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide)]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [embed_put cur i ((cur[i] + src[i]) % 3) hiC]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [hm, addI_ofNat_one moves hfm]
  simp only [bind, Except.bind, pure, Except.pure, tritAdd, withMoves]
  exact asc_tail (n - 1) i hfi _

/-- `mirror = false`. The destination becomes `fieldAdd` of the two homes.
    Moves grow by `pegCount` of the source. -/
theorem add_off (b : Ecbs.Board) (dst src : Nat) (ys xs : List Nat) (n moves : Nat)
    (hHd : dst < b.sudo_5Board_4home.size) (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : src < b.sudo_5Board_4home.size) (hDs : src < b.sudo_5Board_4held.size)
    (hheldD : b.sudo_5Board_4held[dst] = true)
    (harrD : b.sudo_5Board_4home[dst] = embed ys)
    (hheldS : b.sudo_5Board_4held[src] = true)
    (harrS : b.sudo_5Board_4home[src] = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : xs.length = n) (hy : ys.length = n)
    (hpos : 0 < n)
    (htriD : allTritList ys) (htriS : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    Ecbs.add b (dst : Int) (src : Int) false =
      .ok (addBoard b dst hHd (embed (fieldAdd n ys xs)) (moves + pegCount xs)) := by
  have hfitn : FitsLen n := FitsLen.of_le hfit (Nat.le_add_left n moves)
  have hmI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hm, ofNat_eq_natCast]
  unfold Ecbs.add
  rw [value_held_refines b src xs n hDs hHs hheldS harrS hn
    (by rw [hx]; exact Nat.le_refl _) hfitn, ok_bind]
  have htake : xs.take n = xs := by rw [← hx]; exact List.take_length xs
  rw [htake]
  rw [get_number_held b dst hHd hDd hheldD, harrD, ok_bind]
  rw [hn, show (n : Int) = Int.ofNat n from ofNat_eq_natCast n,
    subI_ofNat_one n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
    change addStep (embed xs) (Int.ofNat (n - 1)) false
  rw [except_bind_pure]
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Array Int × Ecbs.Board) =>
      st.1 = embed (addPlain n i ys xs) ∧
      st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
    (Nat.zero_le _) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have hbase : addPlain n 0 ys xs = ys := by
        apply List.ext_getElem
        · simp [addPlain_length, hy]
        · intro j hj1 hj2
          have hj : j < n := by rw [addPlain_length] at hj1; exact hj1
          rw [addPlain_get n 0 ys xs j hj]
          simp [coeff_eq_get ys j (by omega)]
      simp [hbase]
    · rw [pegCount_take_zero, Nat.add_zero]
      exact (withMoves_id b _ hmI).symm
  · intro i st _ hi hI
    have hii : i < xs.length := by omega
    have hiy : i < ys.length := by omega
    have hin : i < n := Nat.lt_of_le_of_lt hi (Nat.sub_lt hpos (Nat.succ_pos 0))
    have hc : xs[i] ≤ 2 := trit_get htriS hii
    have hdy : ys[i] ≤ 2 := trit_get htriD hiy
    have hpc : pegCount (xs.take i) + 1 ≤ n :=
      Nat.le_trans (Nat.succ_le_succ (pegCount_take_le xs i)) (Nat.succ_le_of_lt hin)
    have hfm : FitsLen (moves + pegCount (xs.take i) + 1) :=
      FitsLen.of_le hfit (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hpc moves)
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfitn (Nat.succ_le_of_lt hin)
    have hpref : i < (addPlain n i ys xs).length := by rw [addPlain_length]; exact hin
    have hcell : (addPlain n i ys xs)[i] = ys[i] := by
      rw [addPlain_get n i ys xs i hin]
      simp [coeff_eq_get ys i hiy]
    have htriC : (addPlain n i ys xs)[i] ≤ 2 := by rw [hcell]; exact hdy
    let nxtArr := embed (addPlain n (i + 1) ys xs)
    let nxtMv := moves + pegCount (xs.take i) + if xs[i] = 0 then 0 else 1
    have hpegS : pegCount (xs.take (i + 1)) =
        pegCount (xs.take i) + if xs[i] = 0 then 0 else 1 :=
      pegCount_take_succ xs i hii
    refine ⟨(nxtArr, withMoves b (Int.ofNat nxtMv)), ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      simp [nxtMv, hpegS, Nat.add_assoc]
    · have hb : st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))) := hI.2
      have ha : st.1 = embed (addPlain n i ys xs) := hI.1
      have hmNow : st.2.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (moves + pegCount (xs.take i)) := by
        rw [hb]; exact withMoves_moves _ _
      have hpair :
          (embed (addPlain n i ys xs),
            withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) = st :=
        Prod.ext ha.symm hb.symm
      by_cases hz : xs[i] = 0
      · have hstep := addStep_zero_off xs (addPlain n i ys xs) i n
          (withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) hii hz hi hfi
        rw [hpair] at hstep
        rw [hstep, ← hpair]
        simp only [nxtArr, nxtMv, hz, if_true, Nat.add_zero]
        rw [addPlain_skip n i ys xs hin hy hx hz hdy]
      · have hstep := addStep_nz_off xs (addPlain n i ys xs) i n
          (moves + pegCount (xs.take i))
          (withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
          hii hpref hz hc htriC hi (withMoves_moves _ _) hfm hfi
        rw [hpair] at hstep
        rw [hstep]
        simp only [nxtArr, nxtMv, if_neg hz]
        rw [addPlain_succ n i ys xs hin hy hx, coeff_eq_get ys i hiy, coeff_eq_get xs i hii,
          hcell, withMoves_withMoves]
  · intro st hs
    have hdone : addPlain n n ys xs = fieldAdd n ys xs :=
      addPlain_done n ys xs hy hx
    have htake : xs.take n = xs := by rw [← hx, List.take_length]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), hdone, htake] at hs
    conv =>
      lhs
      zeta
    rw [hs.1, hs.2]
    have hHw : dst < (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4home.size := hHd
    have hDw : dst < (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4held.size := hDd
    have hheldW : (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4held[dst] = true :=
      hheldD
    rw [set_number_held _ dst _ hHw hDw hheldW, ok_bind, pure_eq_ok]
    unfold addBoard
    have hhome : (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4home =
        b.sudo_5Board_4home := rfl
    rw [Array.set_congr_arr hhome hHw (embed (fieldAdd n ys xs))]

private theorem fieldMul_trits (n k bench : Nat) (xs ys : List Nat)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench xs ys) := by
  have hrep : allTritList (List.replicate bench 0) := by
    intro x hx
    simp [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    exact Nat.zero_le _
  have hwide : ∀ i, i < n → i + (n - 1) < (List.replicate bench 0).length := by
    intro i hi
    rw [List.length_replicate]
    have : i + (n - 1) ≤ 2 * (n - 1) := by omega
    omega
  have hsch := school_trits xs ys (List.replicate bench 0) false n hrep hwide
  have hlen : (school n xs ys (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  have hfold := laneFold_trits n (n - k)
    (school n xs ys (List.replicate bench 0) false) hsch (Nat.sub_le _ _) (by rw [hlen]; exact hn)
  simpa [fieldMul, laneFold] using allTritList_take hfold n

/-- `(u²Z + v³) + v²Z = F`. The onto-keep sum is the first parenthesis.
    The mirror-off add contributes `v²Z`. -/
theorem gap_fform (n k bench : Nat) (u v z : List Nat)
    (_hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fieldAdd n
        (fieldAdd n (fieldMul n k bench (fieldMul n k bench u u) z)
          (fieldMul n k bench v (fieldMul n k bench v v)))
        (fieldMul n k bench (fieldMul n k bench v v) z) =
      fformF n k bench u v z := by
  have hv2 : allTritList (fieldMul n k bench v v) := fieldMul_trits n k bench v v hspan hn
  dsimp only [fformF]
  rw [fieldMul_comm n k bench v (fieldMul n k bench v v) hv hv2]
  rw [fieldAdd_assoc]
  rw [← fieldMul_right_add n k bench (fieldMul n k bench v v) v z hv2 hv hz hn]

private theorem fieldAdd_trits (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
  intro a ha
  simp only [fieldAdd, List.mem_map] at ha
  rcases ha with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

private theorem fieldMul_len (n k bench : Nat) (xs ys : List Nat) (hn : n ≤ bench) :
    (fieldMul n k bench xs ys).length = n := by
  unfold fieldMul
  rw [List.length_take]
  have hstrip : (school n xs ys (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hred : (reduceStrip n (n - k) (school n xs ys (List.replicate bench 0) false)).length =
      bench := by
    have h := laneFold_length n (n - k) (school n xs ys (List.replicate bench 0) false)
      (by rw [hstrip]; exact hn)
    simpa [laneFold, hstrip] using h
  rw [hred]
  exact Nat.min_eq_left hn

/-- The mirror-off add of `u²Z + v³` and `v²Z` is `fformF`. Both values are
    held homes. -/
theorem gap_add_f (b : Ecbs.Board) (dst src : Nat) (u v z : List Nat)
    (n k bench moves : Nat)
    (hHd : dst < b.sudo_5Board_4home.size) (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : src < b.sudo_5Board_4home.size) (hDs : src < b.sudo_5Board_4held.size)
    (hheldD : b.sudo_5Board_4held[dst] = true)
    (hheldS : b.sudo_5Board_4held[src] = true)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < n)
    (hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hnb : n ≤ bench)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    let u2 := fieldMul n k bench u u
    let v2 := fieldMul n k bench v v
    let sum := fieldAdd n (fieldMul n k bench u2 z) (fieldMul n k bench v v2)
    let v2z := fieldMul n k bench v2 z
    b.sudo_5Board_4home[dst] = embed sum →
    b.sudo_5Board_4home[src] = embed v2z →
      Ecbs.add b (dst : Int) (src : Int) false =
        .ok (addBoard b dst hHd (embed (fformF n k bench u v z)) (moves + pegCount v2z)) := by
  intro u2 v2 sum v2z harrD harrS
  have hlenS : sum.length = n := by
    simp [sum, fieldAdd, List.length_map, List.length_range]
  have hlenZ : v2z.length = n := fieldMul_len n k bench v2 z hnb
  have htriS : allTritList sum := by
    simpa [sum] using fieldAdd_trits n _ _
  have htriZ : allTritList v2z := fieldMul_trits n k bench v2 z hspan hnb
  have h := add_off b dst src sum v2z n moves hHd hDd hHs hDs hheldD harrD hheldS harrS
    hn hlenZ hlenS hpos htriS htriZ hm hfit
  have hsum : fieldAdd n sum v2z = fformF n k bench u v z := by
    simpa [sum, v2z, u2, v2] using
      gap_fform n k bench u v z hu hv hz hspan hnb
  simpa [hsum] using h

end EcbsLink2.Link2
