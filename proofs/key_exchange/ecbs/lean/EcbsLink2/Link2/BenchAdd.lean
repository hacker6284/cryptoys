/-
  `bench_add` lays a home onto the bench. The length-`n` prefix becomes
  `fieldAdd` with that home, or with `mirrorTrits` when the mirror is on.
  The bridge is `bench_add_emit` (`rfl`). Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordAcross
import EcbsLink2.Link2.Add

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The trit `bench_add` lays: the source, flipped when `mirror` is on. -/
def srcTrit (mirror : Bool) (c : Nat) : Nat :=
  if mirror then flipTrit c else c

theorem srcTrit_zero (mirror : Bool) : srcTrit mirror 0 = 0 := by
  cases mirror <;> simp [srcTrit, flipTrit]

/-- First `k` holes are the bench plus the (mirrored) source; the rest stay. -/
def addOnto (bench src : List Nat) (mirror : Bool) (k : Nat) : List Nat :=
  (List.range bench.length).map fun j =>
    if j < k then tritAdd (coeff bench j) (srcTrit mirror (coeff src j)) else coeff bench j

theorem addOnto_length (bench src : List Nat) (mirror : Bool) (k : Nat) :
    (addOnto bench src mirror k).length = bench.length := by
  simp [addOnto, List.length_map, List.length_range]

theorem addOnto_get (bench src : List Nat) (mirror : Bool) (k j : Nat)
    (hj : j < bench.length) :
    (addOnto bench src mirror k)[j]'(by rw [addOnto_length]; exact hj) =
      if j < k then tritAdd (coeff bench j) (srcTrit mirror (coeff src j))
      else coeff bench j := by
  simp [addOnto, List.getElem_map, List.getElem_range, hj]

theorem addOnto_zero (bench src : List Nat) (mirror : Bool) :
    addOnto bench src mirror 0 = bench := by
  apply List.ext_getElem
  · simp [addOnto_length]
  · intro j _ hj
    rw [addOnto_get bench src mirror 0 j hj, if_neg (by omega), coeff_eq_get bench j hj]

private theorem list_set_id (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.set i xs[i] = xs := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    by_cases h : j = i
    · subst h
      simp
    · simp [List.getElem_set_ne (Ne.symm h)]

theorem addOnto_succ (bench src : List Nat) (mirror : Bool) (i : Nat)
    (hi : i < bench.length) :
    addOnto bench src mirror (i + 1) =
      (addOnto bench src mirror i).set i
        (tritAdd (coeff bench i) (srcTrit mirror (coeff src i))) := by
  have hlen : (addOnto bench src mirror i).length = bench.length :=
    addOnto_length bench src mirror i
  apply List.ext_getElem
  · simp [addOnto_length, List.length_set]
  · intro j hj1 _
    have hj : j < bench.length := by rw [addOnto_length] at hj1; exact hj1
    rw [addOnto_get bench src mirror (i + 1) j hj]
    by_cases hji : j = i
    · subst hji
      simp [List.getElem_set_self, hi, hlen]
    · rw [List.getElem_set_ne (Ne.symm hji), addOnto_get bench src mirror i j hj]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · simp [hlt, show ¬ j < i + 1 by omega]

theorem addOnto_skip (bench src : List Nat) (mirror : Bool) (i : Nat)
    (hi : i < bench.length) (hz : coeff src i = 0) (hdt : coeff bench i ≤ 2) :
    addOnto bench src mirror (i + 1) = addOnto bench src mirror i := by
  rw [addOnto_succ bench src mirror i hi]
  have hidx : i < (addOnto bench src mirror i).length := by
    rw [addOnto_length]; exact hi
  have hcell : (addOnto bench src mirror i)[i] = coeff bench i := by
    rw [addOnto_get bench src mirror i i hi]
    simp
  rw [hz, srcTrit_zero, tritAdd_right_zero _ hdt, ← hcell]
  exact list_set_id _ i hidx

theorem coeff_take (xs : List Nat) (n i : Nat) (hi : i < n) (hn : n ≤ xs.length) :
    coeff (xs.take n) i = coeff xs i := by
  have hi1 : i < (xs.take n).length := by rw [List.length_take]; omega
  have hi2 : i < xs.length := Nat.lt_of_lt_of_le hi hn
  rw [coeff_eq_get (xs.take n) i hi1, coeff_eq_get xs i hi2, List.getElem_take]

theorem coeff_added (src : List Nat) (mirror : Bool) (i : Nat) :
    coeff (if mirror then mirrorTrits src else src) i =
      srcTrit mirror (coeff src i) := by
  cases mirror <;> simp [srcTrit, coeff_mirror]

/-- At `k = n` the length-`n` prefix is `fieldAdd` with the source, mirrored
    when asked. `mirrorTrits` is what `mirror_refines` writes. -/
theorem addOnto_field (bench src : List Nat) (n : Nat) (mirror : Bool)
    (hn : n ≤ bench.length) :
    (addOnto bench src mirror n).take n =
      fieldAdd n (bench.take n) (if mirror then mirrorTrits src else src) := by
  apply List.ext_getElem
  · rw [List.length_take, addOnto_length, Nat.min_eq_left hn]
    simp [fieldAdd, List.length_map, List.length_range]
  · intro j hj1 _
    have hjn : j < n := by
      rw [List.length_take, addOnto_length, Nat.min_eq_left hn] at hj1
      exact hj1
    have hjb : j < bench.length := Nat.lt_of_lt_of_le hjn hn
    rw [List.getElem_take, addOnto_get bench src mirror n j hjb, if_pos hjn]
    simp [fieldAdd, List.getElem_map, List.getElem_range]
    rw [coeff_take bench n j hjn hn, coeff_added src mirror j]

theorem addOnto_off (bench src : List Nat) (n : Nat) (hn : n ≤ bench.length) :
    (addOnto bench src false n).take n = fieldAdd n (bench.take n) src := by
  simpa using addOnto_field bench src n false hn

theorem addOnto_on (bench src : List Nat) (n : Nat) (hn : n ≤ bench.length) :
    (addOnto bench src true n).take n =
      fieldAdd n (bench.take n) (mirrorTrits src) := by
  simpa using addOnto_field bench src n true hn

private theorem tritAdd_le (a b : Nat) : tritAdd a b ≤ 2 := by
  have : (a + b) % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold tritAdd
  omega

theorem fieldAdd_span_trits (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

/-- The emitted loop body. `v` is the source home, closed over as in `benchAddEmit`. -/
def benchAddStep (v : Array Int) (toV : Int) (mirror : Bool) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  let i := σ.1
  let b := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, b))
    else
      match ← ((do
        let _t1075 ← SudoRt.atL v i
        let c := _t1075
        if !(SudoRt.SEq.beq c (0 : Int)) then
          do
            if mirror then
              do
                let _t1077 ← Ecbs.flip c
                let c := _t1077
                let _ix1078 := i
                let _t1079 ← SudoRt.atL (b).sudo_5Board_5bench i
                let _t1080 ← SudoRt.addI _t1079 c
                let _t1081 ← SudoRt.modI _t1080 (3 : Int)
                let _t1082 ← SudoRt.putL (b).sudo_5Board_5bench _ix1078 _t1081
                let _t1083 := ({ b with sudo_5Board_5bench := _t1082 } : Ecbs.Board)
                let b := _t1083
                let _t1084 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (1 : Int)
                let _t1085 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t1084 } : Ecbs.Costs)
                let _t1086 := ({ b with sudo_5Board_4cost := _t1085 } : Ecbs.Board)
                let b := _t1086
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
            else
              do
                let _ix1087 := i
                let _t1088 ← SudoRt.atL (b).sudo_5Board_5bench i
                let _t1089 ← SudoRt.addI _t1088 c
                let _t1090 ← SudoRt.modI _t1089 (3 : Int)
                let _t1091 ← SudoRt.putL (b).sudo_5Board_5bench _ix1087 _t1090
                let _t1092 := ({ b with sudo_5Board_5bench := _t1091 } : Ecbs.Board)
                let b := _t1092
                let _t1093 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (1 : Int)
                let _t1094 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t1093 } : Ecbs.Costs)
                let _t1095 := ({ b with sudo_5Board_4cost := _t1094 } : Ecbs.Board)
                let b := _t1095
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
        else
          do
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) :
          Except SudoRt.Trap (SudoRt.Flow _ (Ecbs.Board))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
      | .cont _fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', _fs))

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

/-- Bench array replaced, and the move counter set. Same field order as the emit. -/
def withBenchMoves (b : Ecbs.Board) (arr : Array Int) (mv : Nat) : Ecbs.Board :=
  { { b with sudo_5Board_5bench := arr } with
    sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_5moves := Int.ofNat mv } }

/-- The board `bench_add` returns: the bench is the laid list, moves grew by the
    source's nonzero count. -/
def benchAddBoard (b : Ecbs.Board) (arr : Array Int) (mv : Nat) : Ecbs.Board :=
  { withMoves b (Int.ofNat mv) with sudo_5Board_5bench := arr }

theorem benchAddBoard_row (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_3row = b.sudo_5Board_3row := by
  simp [benchAddBoard, withMoves]

theorem benchAddBoard_bench (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_5bench = arr := rfl

theorem benchAddBoard_moves (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
  unfold benchAddBoard withMoves
  rw [ofNat_eq_natCast]

theorem benchAddBoard_home (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4home = b.sudo_5Board_4home := rfl

private theorem benchAddBoard_id (b : Ecbs.Board) (xs : List Nat) (mv : Nat)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv) :
    benchAddBoard b (embed xs) mv = b := by
  have hw : withMoves b (Int.ofNat mv) = b := by
    rw [← hm]
    unfold withMoves
    rfl
  unfold benchAddBoard
  rw [hw, ← hbench]

private theorem withBenchMoves_board (b : Ecbs.Board) (arr arr' : Array Int) (mv mv' : Nat) :
    withBenchMoves (benchAddBoard b arr mv) arr' mv' = benchAddBoard b arr' mv' := by
  unfold withBenchMoves benchAddBoard withMoves
  rfl

private theorem benchAddBoard_seq (b : Ecbs.Board) (arr₁ arr₂ : Array Int) (mv₁ mv₂ : Nat) :
    benchAddBoard (benchAddBoard b arr₁ mv₁) arr₂ mv₂ = benchAddBoard b arr₂ mv₂ := by
  unfold benchAddBoard withMoves
  rfl

theorem benchStep_zero (src : List Nat) (i n : Nat) (mirror : Bool) (st : Ecbs.Board)
    (hi : i < src.length) (hz : src[i] = 0) (hto : i ≤ n - 1) (hfi : FitsLen (i + 1)) :
    benchAddStep (embed src) (Int.ofNat (n - 1)) mirror (Int.ofNat i, st) =
      (if i = n - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hto
  simp only [benchAddStep, hng, if_false]
  rw [atL_embed src i hi]
  simp only [bind, Except.bind, pure, Except.pure, sEq_ofNat_zero, hz, decide_True,
    Bool.not_true, Bool.false_eq_true, if_false]
  exact asc_tail (n - 1) i hfi _

theorem benchStep_nz (src cur : List Nat) (i n moves : Nat) (st : Ecbs.Board) (mirror : Bool)
    (hiS : i < src.length) (hiC : i < cur.length) (hnz : src[i] ≠ 0) (hc : src[i] ≤ 2)
    (hd : cur[i] ≤ 2) (hto : i ≤ n - 1)
    (hbench : st.sudo_5Board_5bench = embed cur)
    (hm : st.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) (hfi : FitsLen (i + 1)) :
    benchAddStep (embed src) (Int.ofNat (n - 1)) mirror (Int.ofNat i, st) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            withBenchMoves st (embed (cur.set i (tritAdd cur[i] (srcTrit mirror src[i]))))
              (moves + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            withBenchMoves st (embed (cur.set i (tritAdd cur[i] (srcTrit mirror src[i]))))
              (moves + 1)))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hto
  simp only [benchAddStep, hng, if_false]
  rw [atL_embed src i hiS]
  simp only [bind, Except.bind, pure, Except.pure, sEq_ofNat_zero, hnz, decide_False,
    Bool.not_false, if_true]
  cases mirror with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [hbench, atL_embed cur i hiC]
    simp only [bind, Except.bind, pure, Except.pure]
    have hsum : FitsLen (cur[i] + src[i]) := fits_small (by omega)
    rw [addI_ofNat _ _ hsum]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide)]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [embed_put cur i ((cur[i] + src[i]) % 3) hiC]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hm, addI_ofNat_one moves hfm]
    simp only [bind, Except.bind, pure, Except.pure, tritAdd, srcTrit, withBenchMoves]
    exact asc_tail (n - 1) i hfi _
  | true =>
    simp only [if_true]
    rw [flip_refines _ hc]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hbench, atL_embed cur i hiC]
    simp only [bind, Except.bind, pure, Except.pure]
    have hsum : FitsLen (cur[i] + flipTrit src[i]) := by
      have hf : flipTrit src[i] ≤ 2 := by unfold flipTrit; split <;> omega
      exact fits_small (by omega)
    rw [addI_ofNat _ _ hsum]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide)]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [embed_put cur i ((cur[i] + flipTrit src[i]) % 3) hiC]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hm, addI_ofNat_one moves hfm]
    simp only [bind, Except.bind, pure, Except.pure, tritAdd, srcTrit, withBenchMoves]
    exact asc_tail (n - 1) i hfi _

/-- The ascending loop. The bench becomes `addOnto`, and moves grow by `pegCount`
    of the source. The bridge to the emit is `bench_add_emit`. -/
theorem bench_add_prefix (b : Ecbs.Board) (src : Nat) (xs bench : List Nat)
    (n moves : Nat) (mirror : Bool)
    (hS : src < b.sudo_5Board_4home.size)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hbench : b.sudo_5Board_5bench = embed bench)
    (hx : xs.length = n) (hpos : 0 < n) (hbLen : n ≤ bench.length)
    (htriS : allTritList xs) (htriB : allTritList (bench.take n))
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    Ecbs.bench_add b (src : Int) mirror =
      .ok (benchAddBoard b (embed (addOnto bench xs mirror n)) (moves + pegCount xs)) := by
  have hfitn : FitsLen n := FitsLen.of_le hfit (Nat.le_add_left n moves)
  have hmI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hm, ofNat_eq_natCast]
  rw [bench_add_emit]
  unfold benchAddEmit
  rw [show (src : Int) = Int.ofNat src from ofNat_eq_natCast src,
    atL_ofNat _ src hS, harr, ok_bind]
  conv => zeta
  rw [listLen_embed, hx, subI_ofNat_one n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    pattern (fun σ : Int × Ecbs.Board => _)
    change benchAddStep (embed xs) (Int.ofNat (n - 1)) mirror
  rw [except_bind_pure]
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Ecbs.Board) =>
      st = benchAddBoard b (embed (addOnto bench xs mirror i))
        (moves + pegCount (xs.take i)))
    (Nat.zero_le _) ?_ ?_ ?_
  · change b = benchAddBoard b (embed (addOnto bench xs mirror 0))
      (moves + pegCount (xs.take 0))
    rw [addOnto_zero, pegCount_take_zero, Nat.add_zero]
    exact (benchAddBoard_id b bench moves hbench hmI).symm
  · intro i st _ hi hI
    have hin : i < n := Nat.lt_of_le_of_lt hi (Nat.sub_lt hpos (Nat.succ_pos 0))
    have hii : i < xs.length := by omega
    have hib : i < bench.length := Nat.lt_of_lt_of_le hin hbLen
    have hc : xs[i] ≤ 2 := trit_get htriS hii
    have hpc : pegCount (xs.take i) + 1 ≤ n :=
      Nat.le_trans (Nat.succ_le_succ (pegCount_take_le xs i)) (Nat.succ_le_of_lt hin)
    have hfm : FitsLen (moves + pegCount (xs.take i) + 1) :=
      FitsLen.of_le hfit (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hpc moves)
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfitn (Nat.succ_le_of_lt hin)
    let cur := addOnto bench xs mirror i
    have hpref : i < cur.length := by rw [addOnto_length]; exact hib
    have hcell : cur[i] = coeff bench i := by
      simpa [cur, Nat.lt_irrefl i] using addOnto_get bench xs mirror i i hib
    have hcoe : coeff bench i = bench[i] := coeff_eq_get bench i hib
    have hidxT : i < (bench.take n).length := by rw [List.length_take]; omega
    have hbi : bench[i] ≤ 2 := by
      have hte : (bench.take n)[i] = bench[i] := by simp [List.getElem_take]
      rw [← hte]
      exact trit_get htriB hidxT
    have htriC : cur[i] ≤ 2 := by rw [hcell, hcoe]; exact hbi
    let nxtArr := embed (addOnto bench xs mirror (i + 1))
    let nxtMv := moves + pegCount (xs.take i) + if xs[i] = 0 then 0 else 1
    have hpegS : pegCount (xs.take (i + 1)) =
        pegCount (xs.take i) + if xs[i] = 0 then 0 else 1 :=
      pegCount_take_succ xs i hii
    refine ⟨benchAddBoard b nxtArr nxtMv, ?_, ?_⟩
    · simp [nxtArr, nxtMv, hpegS, Nat.add_assoc]
    · have hmNow : st.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (moves + pegCount (xs.take i)) := by rw [hI]; rfl
      have hbArr : st.sudo_5Board_5bench = embed cur := by rw [hI]; rfl
      by_cases hz : xs[i] = 0
      · have hstep := benchStep_zero xs i n mirror st hii hz hi hfi
        rw [hstep]
        simp only [nxtArr, nxtMv, hz, if_true, Nat.add_zero]
        rw [addOnto_skip bench xs mirror i hib (by rw [coeff_eq_get xs i hii]; exact hz)
          (by rw [hcoe]; exact hbi), ← hI]
      · have hstep := benchStep_nz xs cur i n (moves + pegCount (xs.take i)) st mirror
          hii hpref hz hc htriC hi hbArr hmNow hfm hfi
        rw [hstep]
        simp only [nxtArr, nxtMv, if_neg hz]
        rw [hI, withBenchMoves_board]
        have hset : cur.set i (tritAdd cur[i] (srcTrit mirror xs[i])) =
            addOnto bench xs mirror (i + 1) := by
          rw [addOnto_succ bench xs mirror i hib, hcell, coeff_eq_get xs i hii]
        rw [hset]
  · intro st hs
    have htake : xs.take n = xs := by rw [← hx]; exact List.take_length xs
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), htake] at hs
    conv =>
      lhs
      zeta
    rw [hs, pure_eq_ok]

/-- The length-`n` prefix `bench_add` leaves is `fieldAdd`. -/
theorem bench_add_field (b : Ecbs.Board) (src : Nat) (xs bench : List Nat)
    (n moves : Nat) (mirror : Bool)
    (hS : src < b.sudo_5Board_4home.size)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hbench : b.sudo_5Board_5bench = embed bench)
    (hx : xs.length = n) (hpos : 0 < n) (hbLen : n ≤ bench.length)
    (htriS : allTritList xs) (htriB : allTritList (bench.take n))
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    ∃ arr, Ecbs.bench_add b (src : Int) mirror =
        .ok (benchAddBoard b arr (moves + pegCount xs)) ∧
      arr = embed (addOnto bench xs mirror n) ∧
      (addOnto bench xs mirror n).take n =
        fieldAdd n (bench.take n) (if mirror then mirrorTrits xs else xs) := by
  exact ⟨embed (addOnto bench xs mirror n), bench_add_prefix b src xs bench n moves mirror
    hS harr hbench hx hpos hbLen htriS htriB hm hfit, rfl,
    addOnto_field bench xs n mirror hbLen⟩

/-- Across with the mirror off, then the bottom with the mirror on.
    The length-`n` prefix is `fieldAdd` with the across, then with `mirrorTrits`
    of the bottom. SPEC.md §3 R7 line 156: add its across, take away the bottom.
    One `FitsLen (moves + 2 * n)` covers both, because each home has at most `n` pegs. -/
theorem bench_add_across_bottom (b : Ecbs.Board) (xHome zHome : Nat)
    (xs zs bench : List Nat) (n moves : Nat)
    (hxH : xHome < b.sudo_5Board_4home.size)
    (hxA : b.sudo_5Board_4home[xHome] = embed xs)
    (hzH : zHome < b.sudo_5Board_4home.size)
    (hzA : b.sudo_5Board_4home[zHome] = embed zs)
    (hbench : b.sudo_5Board_5bench = embed bench)
    (hx : xs.length = n) (hz : zs.length = n)
    (hpos : 0 < n) (hbLen : n ≤ bench.length)
    (htriX : allTritList xs) (htriZ : allTritList zs)
    (htriB : allTritList (bench.take n))
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + 2 * n)) :
    (do
        let b ← Ecbs.bench_add b (xHome : Int) false
        Ecbs.bench_add b (zHome : Int) true) =
      .ok (benchAddBoard b
        (embed (addOnto (addOnto bench xs false n) zs true n))
        (moves + pegCount xs + pegCount zs)) ∧
    (addOnto (addOnto bench xs false n) zs true n).take n =
      fieldAdd n (fieldAdd n (bench.take n) xs) (mirrorTrits zs) := by
  have hfit1 : FitsLen (moves + n) := FitsLen.of_le hfit (by omega)
  have h1 := bench_add_prefix b xHome xs bench n moves false hxH hxA hbench hx hpos hbLen
    htriX htriB hm hfit1
  rw [h1, ok_bind]
  let L1 := addOnto bench xs false n
  let mv1 := moves + pegCount xs
  have hlen1 : L1.length = bench.length := addOnto_length bench xs false n
  have hpre1 : L1.take n = fieldAdd n (bench.take n) xs := addOnto_off bench xs n hbLen
  have htri1 : allTritList (L1.take n) := by rw [hpre1]; exact fieldAdd_span_trits _ _ _
  have hpx : pegCount xs ≤ n := by rw [← hx]; exact pegCount_le xs
  have hfit2 : FitsLen (mv1 + n) := FitsLen.of_le hfit (by omega)
  have h2 := bench_add_prefix (benchAddBoard b (embed L1) mv1) zHome zs L1 n mv1 true
    (by simpa [benchAddBoard, withMoves] using hzH)
    (by simpa [benchAddBoard, withMoves] using hzA)
    rfl hz hpos (by rw [hlen1]; exact hbLen) htriZ htri1
    (benchAddBoard_moves b (embed L1) mv1) hfit2
  rw [h2, benchAddBoard_seq]
  refine ⟨rfl, ?_⟩
  · rw [addOnto_on L1 zs n (by rw [hlen1]; exact hbLen), hpre1]

end EcbsLink2.Link2
