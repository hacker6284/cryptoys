/-
  The gap add on the board `gap_sum_on_v2z` leaves. The gap is empty and the
  bench, aimed at the gap, holds `u²Z + v³`. `Ecbs.add` of the bottom reads
  that bench and writes `fformF` back onto it. `gap_add_f` is the other
  branch, where both homes are held. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAddOff

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

private theorem beq_ofNat (b : Ecbs.Board) (home : Nat)
    (h : b.sudo_5Board_8bench_to = (home : Int)) :
    SudoRt.SEq.beq b.sudo_5Board_8bench_to (Int.ofNat home) = true := by
  rw [show Int.ofNat home = (home : Int) from (ofNat_eq_natCast home).symm, h, sEq_int]
  exact decide_eq_true rfl

/-- The bench `add` rewrites, plus the move counter. Homes and the aim stay. -/
def addOnBench (b : Ecbs.Board) (arr : Array Int) (mv : Nat) : Ecbs.Board :=
  { withMoves b (Int.ofNat mv) with sudo_5Board_5bench := arr }

theorem addOnBench_home (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_4home = b.sudo_5Board_4home := rfl

theorem addOnBench_held (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_4held = b.sudo_5Board_4held := rfl

theorem addOnBench_on (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := rfl

theorem addOnBench_to (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := rfl

theorem addOnBench_bench (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_5bench = arr := rfl

theorem addOnBench_moves (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := rfl

theorem addOnBench_marker (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_6marker = b.sudo_5Board_6marker := rfl

theorem addOnBench_flag (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (addOnBench b arr mv).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := rfl

/-- Empty home, bench aimed at it: `get_number` is the bench array. -/
theorem get_number_bench (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (hD : home < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hbench : b.sudo_5Board_5bench = embed xs) :
    Ecbs.get_number b (home : Int) = .ok (embed xs) := by
  unfold Ecbs.get_number Ecbs.where_bench
  rw [show (home : Int) = Int.ofNat home from ofNat_eq_natCast home,
    atL_ofNat _ home hD, hempty]
  simp only [ok_bind, Bool.false_eq_true, ite_false, hon, if_true]
  rw [beq_ofNat b home hto, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind, pure_eq_ok,
    ok_bind, if_pos rfl, hbench]

/-- Empty home, bench aimed at it: `set_number` writes the bench. -/
theorem set_number_bench (b : Ecbs.Board) (home : Nat) (v : Array Int)
    (hD : home < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int)) :
    Ecbs.set_number b (home : Int) v =
      .ok { b with sudo_5Board_5bench := v } := by
  unfold Ecbs.set_number Ecbs.where_bench
  rw [show (home : Int) = Int.ofNat home from ofNat_eq_natCast home,
    atL_ofNat _ home hD, hempty]
  simp only [ok_bind, Bool.false_eq_true, ite_false, hon, if_true]
  rw [beq_ofNat b home hto, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind, pure_eq_ok,
    ok_bind, if_pos rfl]

/-- Prefix `addPlain`, tail of `lane` kept. Length stays `lane.length`. -/
def laneAdd (lane src : List Nat) (n i : Nat) : List Nat :=
  addPlain n i (lane.take n) src ++ lane.drop n

theorem laneAdd_length (lane src : List Nat) (n i : Nat) (hn : n ≤ lane.length) :
    (laneAdd lane src n i).length = lane.length := by
  simp [laneAdd, addPlain_length, List.length_drop, hn]

theorem addPlain_zero (n : Nat) (dst src : List Nat) (hd : dst.length = n) :
    addPlain n 0 dst src = dst := by
  apply List.ext_getElem
  · simp [addPlain_length, hd]
  · intro j hj1 hj2
    have hj : j < n := by rw [addPlain_length] at hj1; exact hj1
    rw [addPlain_get n 0 dst src j hj, if_neg (Nat.not_lt_zero j)]
    rw [coeff_eq_get dst j (hd ▸ hj)]

theorem laneAdd_zero (lane src : List Nat) (n : Nat) (hn : n ≤ lane.length) :
    laneAdd lane src n 0 = lane := by
  have hlen : (lane.take n).length = n := by rw [List.length_take, Nat.min_eq_left hn]
  unfold laneAdd
  rw [addPlain_zero n (lane.take n) src hlen, List.take_append_drop]

private theorem append_get_left (xs ys : List Nat) (i : Nat) (hi : i < xs.length)
    (hj : i < (xs ++ ys).length) : (xs ++ ys)[i]'hj = xs[i] := by
  rw [List.getElem_append_left hi]

private theorem append_set_left (xs ys : List Nat) (i v : Nat) (hi : i < xs.length) :
    (xs ++ ys).set i v = xs.set i v ++ ys := by
  induction xs generalizing i with
  | nil => cases hi
  | cons a xs ih =>
    cases i with
    | zero => simp [List.set_cons_zero, List.cons_append]
    | succ i =>
      simp only [List.set_cons_succ, List.cons_append]
      have hi' : i < xs.length := by
        simp [List.length_cons] at hi
        omega
      exact congrArg (fun t => a :: t) (ih i hi')

private theorem laneAdd_cell (lane src : List Nat) (n i : Nat)
    (hn : n ≤ lane.length) (hi : i < n) :
    (laneAdd lane src n i)[i]'(by rw [laneAdd_length lane src n i hn]; exact Nat.lt_of_lt_of_le hi hn) =
      (lane.take n)[i]'(by rw [List.length_take, Nat.min_eq_left hn]; exact hi) := by
  have hplain : i < (addPlain n i (lane.take n) src).length := by rw [addPlain_length]; exact hi
  have hlen : i < (laneAdd lane src n i).length := by
    rw [laneAdd_length lane src n i hn]; exact Nat.lt_of_lt_of_le hi hn
  unfold laneAdd
  rw [append_get_left _ _ i hplain hlen, addPlain_get n i (lane.take n) src i hi,
    if_neg (Nat.lt_irrefl i), coeff_eq_get (lane.take n) i
      (by rw [List.length_take, Nat.min_eq_left hn]; exact hi)]

private theorem laneAdd_succ (lane src : List Nat) (n i : Nat)
    (hn : n ≤ lane.length) (hi : i < n) (hs : src.length = n)
    (hidx : i < (laneAdd lane src n i).length) (hsi : i < src.length) :
    (laneAdd lane src n i).set i
        (tritAdd ((laneAdd lane src n i)[i]'hidx) (src[i]'hsi)) =
      laneAdd lane src n (i + 1) := by
  have htake : (lane.take n).length = n := by rw [List.length_take, Nat.min_eq_left hn]
  have hcell := laneAdd_cell lane src n i hn hi
  have hv : tritAdd ((laneAdd lane src n i)[i]'hidx) (src[i]'hsi) =
      tritAdd (coeff (lane.take n) i) (coeff src i) := by
    have hie : ((laneAdd lane src n i)[i]'hidx) =
        ((laneAdd lane src n i)[i]'(by
          rw [laneAdd_length lane src n i hn]; exact Nat.lt_of_lt_of_le hi hn)) := rfl
    rw [hie, hcell, coeff_eq_get (lane.take n) i (by rw [htake]; exact hi),
      coeff_eq_get src i hsi]
  rw [hv]
  conv =>
    lhs
    unfold laneAdd
  rw [append_set_left _ _ i _ (by rw [addPlain_length]; exact hi),
    ← addPlain_succ n i (lane.take n) src hi htake hs]
  rfl

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

/-- The gap is empty and the bench is aimed at it. `add` reads that bench as
    the destination and the held source home, and writes the sum back onto the
    bench. The length-`n` prefix becomes `fieldAdd`. The tail of the bench stays.
    Homes stay. -/
theorem add_on_bench (b : Ecbs.Board) (dst src : Nat) (lane ys xs : List Nat) (n moves : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (dst : Int))
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hHs : src < b.sudo_5Board_4home.size)
    (hDs : src < b.sudo_5Board_4held.size)
    (hheldS : b.sudo_5Board_4held[src] = true)
    (harrS : b.sudo_5Board_4home[src] = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hnle : n ≤ lane.length) (hx : xs.length = n) (hy : ys.length = n)
    (htake : lane.take n = ys)
    (hpos : 0 < n)
    (htriD : allTritList ys) (htriS : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    let lane' := laneAdd lane xs n n
    Ecbs.add b (dst : Int) (src : Int) false =
      .ok (addOnBench b (embed lane') (moves + pegCount xs)) ∧
    lane'.take n = fieldAdd n ys xs ∧
    lane'.length = lane.length := by
  intro lane'
  have hfitn : FitsLen n := FitsLen.of_le hfit (Nat.le_add_left n moves)
  have hmI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hm, ofNat_eq_natCast]
  unfold Ecbs.add
  rw [value_held_refines b src xs n hDs hHs hheldS harrS hn
      (by rw [hx]; exact Nat.le_refl _) hfitn, ok_bind]
  have hxs : xs.take n = xs := by rw [← hx]; exact List.take_length xs
  rw [hxs]
  rw [get_number_bench b dst lane hD hempty hon hto hbench, ok_bind]
  rw [hn, show (n : Int) = Int.ofNat n from ofNat_eq_natCast n,
    subI_ofNat_one n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
    change addStep (embed xs) (Int.ofNat (n - 1)) false
  rw [except_bind_pure]
  have hbase : laneAdd lane xs n 0 = lane := laneAdd_zero lane xs n hnle
  refine And.intro ?_ ?_
  · refine asc_goal (fromN := 0) (toN := n - 1)
      (fun i (st : Array Int × Ecbs.Board) =>
        st.1 = embed (laneAdd lane xs n i) ∧
        st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
      (Nat.zero_le _) ?_ ?_ ?_
    · refine ⟨?_, ?_⟩
      · rw [hbase]
      · rw [pegCount_take_zero, Nat.add_zero]
        exact (withMoves_id b _ hmI).symm
    · intro i st _ hi hI
      have hii : i < xs.length := by omega
      have hin : i < n := Nat.lt_of_le_of_lt hi (Nat.sub_lt hpos (Nat.succ_pos 0))
      have hc : xs[i] ≤ 2 := trit_get htriS hii
      have htakeLen : (lane.take n).length = n := by
        rw [List.length_take, Nat.min_eq_left hnle]
      have hdy : (lane.take n)[i]'(by rw [htakeLen]; exact hin) ≤ 2 := by
        have htys : allTritList (lane.take n) := by rw [htake]; exact htriD
        exact trit_get htys (by rw [htakeLen]; exact hin)
      have hpc : pegCount (xs.take i) + 1 ≤ n :=
        Nat.le_trans (Nat.succ_le_succ (pegCount_take_le xs i)) (Nat.succ_le_of_lt hin)
      have hfm : FitsLen (moves + pegCount (xs.take i) + 1) :=
        FitsLen.of_le hfit (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hpc moves)
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfitn (Nat.succ_le_of_lt hin)
      have hcur : i < (laneAdd lane xs n i).length := by
        rw [laneAdd_length lane xs n i hnle]; exact Nat.lt_of_lt_of_le hin hnle
      have htriC : (laneAdd lane xs n i)[i] ≤ 2 := by
        rw [laneAdd_cell lane xs n i hnle hin]
        exact hdy
      let nxt := laneAdd lane xs n (i + 1)
      let nxtMv := moves + pegCount (xs.take i) + if xs[i] = 0 then 0 else 1
      have hpegS : pegCount (xs.take (i + 1)) =
          pegCount (xs.take i) + if xs[i] = 0 then 0 else 1 :=
        pegCount_take_succ xs i hii
      refine ⟨(embed nxt, withMoves b (Int.ofNat nxtMv)), ?_, ?_⟩
      · refine ⟨rfl, ?_⟩
        simp [nxtMv, hpegS, Nat.add_assoc]
      · have hb : st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))) := hI.2
        have ha : st.1 = embed (laneAdd lane xs n i) := hI.1
        have hmNow : st.2.sudo_5Board_4cost.sudo_5Costs_5moves =
            Int.ofNat (moves + pegCount (xs.take i)) := by
          rw [hb]; exact withMoves_moves _ _
        have hpair :
            (embed (laneAdd lane xs n i),
              withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) = st :=
          Prod.ext ha.symm hb.symm
        by_cases hz : xs[i] = 0
        · have hstep := addStep_zero_off xs (laneAdd lane xs n i) i n
            (withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) hii hz hi hfi
          rw [hpair] at hstep
          rw [hstep, ← hpair]
          simp only [nxt, nxtMv, hz, if_true, Nat.add_zero]
          have hskip : laneAdd lane xs n (i + 1) = laneAdd lane xs n i := by
            have hplain := addPlain_skip n i (lane.take n) xs hin htakeLen hx hz hdy
            simpa [laneAdd] using congrArg (fun p => p ++ lane.drop n) hplain
          rw [hskip]
        · have hstep := addStep_nz_off xs (laneAdd lane xs n i) i n
            (moves + pegCount (xs.take i))
            (withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
            hii hcur hz hc htriC hi (withMoves_moves _ _) hfm hfi
          rw [hpair] at hstep
          rw [hstep]
          simp only [nxt, nxtMv, if_neg hz]
          rw [laneAdd_succ lane xs n i hnle hin hx hcur (by rw [hx]; exact hin),
            withMoves_withMoves]
    · intro st hs
      have hdone : laneAdd lane xs n n =
          fieldAdd n (lane.take n) xs ++ lane.drop n := by
        have hplain := addPlain_done n (lane.take n) xs
          (by rw [List.length_take, Nat.min_eq_left hnle]) hx
        simpa [laneAdd] using congrArg (fun p => p ++ lane.drop n) hplain
      have htakeXs : xs.take n = xs := by rw [← hx, List.take_length]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), htakeXs] at hs
      conv =>
        lhs
        zeta
      rw [hs.1, hs.2]
      have hDw : dst < (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4held.size :=
        hD
      have hemptyW : (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_4held[dst] =
          false := hempty
      have honW : (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_8bench_on = true :=
        hon
      have htoW : (withMoves b (Int.ofNat (moves + pegCount xs))).sudo_5Board_8bench_to =
          (dst : Int) := hto
      rw [set_number_bench _ dst _ hDw hemptyW honW htoW, ok_bind, pure_eq_ok]
      unfold addOnBench
      rw [hdone]
  · refine ⟨?_, laneAdd_length lane xs n n hnle⟩
    · have hplain := addPlain_done n (lane.take n) xs
        (by rw [List.length_take, Nat.min_eq_left hnle]) hx
      have hlenF : (fieldAdd n (lane.take n) xs).length = n := by
        simp [fieldAdd, List.length_map, List.length_range]
      unfold laneAdd
      rw [hplain, List.take_append_of_le_length (Nat.le_of_eq hlenF.symm)]
      have htn : (fieldAdd n (lane.take n) xs).take n = fieldAdd n (lane.take n) xs := by
        simpa [hlenF] using List.take_length (fieldAdd n (lane.take n) xs)
      rw [htn, htake]

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

/-- The gap is empty. The bench aimed at it holds `u²Z + v³`. Adding the
    bottom, which holds `v²Z`, writes `fformF` onto that bench. The gap stays
    empty and the bottom stays `v²Z`. -/
theorem gap_add_on_sum (b : Ecbs.Board) (gap bot : Nat) (u v z lane : List Nat)
    (n k bench moves : Nat)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[gap] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (gap : Int))
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hBH : bot < b.sudo_5Board_4home.size)
    (hBD : bot < b.sudo_5Board_4held.size)
    (hHeldB : b.sudo_5Board_4held[bot] = true)
    (hArrB : b.sudo_5Board_4home[bot] =
      embed (fieldMul n k bench (fieldMul n k bench v v) z))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hnle : n ≤ lane.length) (hpos : 0 < n) (hnb : n ≤ bench)
    (htake : lane.take n =
      fieldAdd n
        (fieldMul n k bench z (fieldMul n k bench u u))
        (fieldMul n k bench v (fieldMul n k bench v v)))
    (hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    ∃ (b' : Ecbs.Board) (lane' : List Nat),
      Ecbs.add b (gap : Int) (bot : Int) false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fformF n k bench u v z ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (gap : Int) ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      (∀ h : gap < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[gap]'h = false) ∧
      (∀ h : bot < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[bot]'h =
          embed (fieldMul n k bench (fieldMul n k bench v v) z)) := by
  let u2 := fieldMul n k bench u u
  let v2 := fieldMul n k bench v v
  let sum := fieldAdd n (fieldMul n k bench z u2) (fieldMul n k bench v v2)
  let v2z := fieldMul n k bench v2 z
  have hu2 : allTritList u2 := fieldMul_trits n k bench u u hspan hnb
  have hv2 : allTritList v2 := fieldMul_trits n k bench v v hspan hnb
  have hzv : allTritList v2z := fieldMul_trits n k bench v2 z hspan hnb
  have hsumT : allTritList sum := by
    intro a ha
    simp only [sum, fieldAdd, List.mem_map] at ha
    rcases ha with ⟨_, _, rfl⟩
    exact tritAdd_le _ _
  have hlenS : sum.length = n := by
    simp [sum, fieldAdd, List.length_map, List.length_range]
  have hlenZ : v2z.length = n := by
    unfold v2z fieldMul
    rw [List.length_take]
    have hstrip : (school n v2 z (List.replicate bench 0) false).length = bench := by
      simpa [List.length_replicate] using school_length v2 z (List.replicate bench 0) false n
    have hred : (reduceStrip n (n - k) (school n v2 z (List.replicate bench 0) false)).length =
        bench := by
      have h := laneFold_length n (n - k) (school n v2 z (List.replicate bench 0) false)
        (by rw [hstrip]; exact hnb)
      simpa [laneFold, hstrip] using h
    rw [hred]
    exact Nat.min_eq_left hnb
  have hcomm : fieldMul n k bench z u2 = fieldMul n k bench u2 z :=
    fieldMul_comm n k bench z u2 hz hu2
  have hadd := add_on_bench b gap bot lane sum v2z n moves hGD hempty hon hto hbench
    hBH hBD hHeldB (by simpa [v2z] using hArrB) hn hnle hlenZ hlenS
    (by simpa [sum, u2, v2] using htake) hpos hsumT hzv hm hfit
  obtain ⟨hok, hpre, _hlen⟩ := hadd
  let arr := embed (laneAdd lane v2z n n)
  let mv := moves + pegCount v2z
  refine ⟨addOnBench b arr mv, laneAdd lane v2z n n, hok, addOnBench_bench b arr mv, ?_,
      addOnBench_on b arr mv ▸ hon, addOnBench_to b arr mv ▸ hto,
      addOnBench_home b arr mv, addOnBench_held b arr mv, ?_, ?_⟩
  · rw [hpre]
    have hF := gap_fform n k bench u v z hu hv hz hspan hnb
    simpa [sum, u2, v2, v2z, hcomm] using hF
  · intro h
    simpa [addOnBench_held] using hempty
  · intro h
    simpa [addOnBench_home] using hArrB

end EcbsLink2.Link2
