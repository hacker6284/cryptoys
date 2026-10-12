/-
  One coefficient of `Ecbs.add` with `mirror = true`: flip the source trit
  and add it to the destination in GF(3). A zero source is skipped, which
  is the same as adding zero.
-/
import EcbsLink2.Link2.Mirror
import EcbsLink2.SpecCurve

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The mirror arm of one `add` step. `mirror = true` is inlined. -/
def addMirrorCell (s d : Array Int) (i : Int) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board) :=
  do
    let c ← SudoRt.atL s i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let f ← Ecbs.flip c
        let cur ← SudoRt.atL d i
        let sum ← SudoRt.addI cur f
        let m ← SudoRt.modI sum (3 : Int)
        let d ← SudoRt.putL d i m
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))
    else
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

theorem addMirrorCell_zero (src dst : List Nat) (i : Nat) (b : Ecbs.Board)
    (hi : i < src.length) (hz : src[i] = 0) :
    addMirrorCell (embed src) (embed dst) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont (embed dst, b)) := by
  unfold addMirrorCell
  rw [atL_embed src i hi, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

theorem addMirrorCell_nz (src dst : List Nat) (i moves : Nat) (b : Ecbs.Board)
    (hiS : i < src.length) (hiD : i < dst.length) (hnz : src[i] ≠ 0) (hc : src[i] ≤ 2)
    (hd : dst[i] ≤ 2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) :
    addMirrorCell (embed src) (embed dst) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont
        (embed (dst.set i (tritAdd dst[i] (flipTrit src[i]))),
          withMoves b (Int.ofNat (moves + 1)))) := by
  unfold addMirrorCell
  rw [atL_embed src i hiS, ok_bind, sEq_ofNat_zero]
  simp only [hnz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [flip_refines _ hc, ok_bind, atL_embed dst i hiD, ok_bind]
  have hsum : FitsLen (dst[i] + flipTrit src[i]) := by
    have hle : dst[i] + flipTrit src[i] ≤ 4 := by
      have hf : flipTrit src[i] ≤ 2 := by
        unfold flipTrit
        split <;> omega
      omega
    exact fits_small (by omega)
  rw [addI_ofNat _ _ hsum, ok_bind, show (3 : Int) = Int.ofNat 3 from rfl,
    modI_ofNat _ (by decide), ok_bind]
  rw [embed_put dst i ((dst[i] + flipTrit src[i]) % 3) hiD, ok_bind]
  rw [hm, addI_ofNat_one moves hfm, ok_bind, pure_eq_ok]
  simp [withMoves, tritAdd]

/-- The emitted `add` closure: guard, `match ←` join, last-index test, `addI`.
    `mirror` is the flag the emitter closes over. -/
def addStep (s : Array Int) (toV : Int) (mirror : Bool)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board) :=
  let i := σ.1
  let d := σ.2.1
  let _sp429 := σ.2.2
  let b := _sp429
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, (d, b)))
    else
      match ← ((do
        let _t408 ← SudoRt.atL s i
        let c := _t408
        if !(SudoRt.SEq.beq c (0 : Int)) then
          do
            if mirror then
              do
                let _t410 ← Ecbs.flip c
                let c := _t410
                let _ix411 := i
                let _t412 ← SudoRt.atL d i
                let _t413 ← SudoRt.addI _t412 c
                let _t414 ← SudoRt.modI _t413 (3 : Int)
                let _t415 ← SudoRt.putL d _ix411 _t414
                let d := _t415
                let _t416 ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
                let _t417 := ({ b.sudo_5Board_4cost with sudo_5Costs_5moves := _t416 } : Ecbs.Costs)
                let _t418 := ({ b with sudo_5Board_4cost := _t417 } : Ecbs.Board)
                let b := _t418
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))
            else
              do
                let _ix419 := i
                let _t420 ← SudoRt.atL d i
                let _t421 ← SudoRt.addI _t420 c
                let _t422 ← SudoRt.modI _t421 (3 : Int)
                let _t423 ← SudoRt.putL d _ix419 _t422
                let d := _t423
                let _t424 ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
                let _t425 := ({ b.sudo_5Board_4cost with sudo_5Costs_5moves := _t424 } : Ecbs.Costs)
                let _t426 := ({ b with sudo_5Board_4cost := _t425 } : Ecbs.Board)
                let b := _t426
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))
        else
          do
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))) :
          Except SudoRt.Trap (SudoRt.Flow _ Ecbs.Board)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
      | .cont _fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', _fs))

/-- First `k` holes are `dst[j] + flip(src[j])` in GF(3); the rest stay `dst`. -/
def addPrefix (n k : Nat) (dst src : List Nat) : List Nat :=
  (List.range n).map fun j =>
    if j < k then tritAdd (coeff dst j) (flipTrit (coeff src j)) else coeff dst j

theorem addPrefix_length (n k : Nat) (dst src : List Nat) :
    (addPrefix n k dst src).length = n := by
  simp [addPrefix, List.length_map, List.length_range]

theorem addPrefix_get (n k : Nat) (dst src : List Nat) (j : Nat) (hj : j < n) :
    (addPrefix n k dst src)[j]'(by rw [addPrefix_length]; exact hj) =
      if j < k then tritAdd (coeff dst j) (flipTrit (coeff src j)) else coeff dst j := by
  simp [addPrefix, List.getElem_map, List.getElem_range, hj]

theorem flipTrit_zero : flipTrit 0 = 0 := by simp [flipTrit]

theorem tritAdd_right_zero (a : Nat) (ha : a ≤ 2) : tritAdd a 0 = a := by
  simp [tritAdd]; omega

private theorem list_set_same (xs : List Nat) (i v : Nat) (hi : i < xs.length) (hv : xs[i] = v) :
    xs.set i v = xs := by
  apply List.ext_getElem
  · simp [List.length_set]
  · intro j hj1 hj2
    by_cases h : j = i
    · subst h; simp [List.getElem_set_self, hv]
    · simp [List.getElem_set_ne (Ne.symm h)]

theorem addPrefix_succ (n i : Nat) (dst src : List Nat)
    (hi : i < n) (hd : dst.length = n) (hs : src.length = n) :
    addPrefix n (i + 1) dst src =
      (addPrefix n i dst src).set i (tritAdd (coeff dst i) (flipTrit (coeff src i))) := by
  have hlen : (addPrefix n i dst src).length = n := addPrefix_length n i dst src
  apply List.ext_getElem
  · simp [addPrefix_length, List.length_set]
  · intro j hj1 hj2
    have hj : j < n := by rw [addPrefix_length] at hj1; exact hj1
    rw [addPrefix_get n (i + 1) dst src j hj]
    by_cases hji : j = i
    · subst hji
      simp [List.getElem_set_self, hi, hlen]
    · rw [List.getElem_set_ne (Ne.symm hji)]
      rw [addPrefix_get n i dst src j hj]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · simp [hlt, show ¬ j < i + 1 by omega, hji]

theorem addPrefix_skip (n i : Nat) (dst src : List Nat)
    (hi : i < n) (hd : dst.length = n) (hs : src.length = n)
    (hz : src[i] = 0) (hdt : dst[i] ≤ 2) :
    addPrefix n (i + 1) dst src = addPrefix n i dst src := by
  rw [addPrefix_succ n i dst src hi hd hs]
  have hidx : i < (addPrefix n i dst src).length := by rw [addPrefix_length]; exact hi
  have hlt : ¬ i < i := Nat.lt_irrefl i
  have hcell : (addPrefix n i dst src)[i] = coeff dst i := by
    rw [addPrefix_get n i dst src i hi, if_neg hlt]
  have hval : tritAdd (coeff dst i) (flipTrit (coeff src i)) = coeff dst i := by
    rw [coeff_eq_get src i (hs.symm ▸ hi), hz, flipTrit_zero,
      coeff_eq_get dst i (hd.symm ▸ hi)]
    exact tritAdd_right_zero _ hdt
  rw [hval, ← hcell]
  exact list_set_same _ i _ hidx rfl

theorem coeff_mirror (xs : List Nat) (i : Nat) :
    coeff (mirrorTrits xs) i = flipTrit (coeff xs i) := by
  unfold mirrorTrits coeff
  by_cases hi : i < xs.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map, Option.getD_some, flipTrit]
  · have hge : xs.length ≤ i := Nat.le_of_not_gt hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [List.length_map] using hge),
      List.getElem?_eq_none hge, flipTrit]

/-- On equal lengths, the spec sum is `zipWith`. -/
theorem fieldAdd_zipWith (xs ys : List Nat) (h : xs.length = ys.length) :
    fieldAdd xs.length xs ys = List.zipWith tritAdd xs ys := by
  apply List.ext_getElem
  · simp [fieldAdd, List.length_map, List.length_range, List.length_zipWith, h]
  · intro i hi1 hi2
    simp [fieldAdd, List.getElem_map, List.getElem_range, List.getElem_zipWith,
      coeff_eq_get xs i (by simp [List.length_zipWith, h] at hi2; omega),
      coeff_eq_get ys i (by simp [List.length_zipWith, h] at hi2; omega)]

theorem addPrefix_done (n : Nat) (dst src : List Nat)
    (hd : dst.length = n) (hs : src.length = n) :
    addPrefix n n dst src = fieldAdd n dst (mirrorTrits src) := by
  apply List.ext_getElem
  · simp [addPrefix_length, fieldAdd, List.length_map, List.length_range]
  · intro i hi1 hi2
    have hi : i < n := by rw [addPrefix_length] at hi1; exact hi1
    rw [addPrefix_get n n dst src i hi]
    simp [hi, fieldAdd, List.getElem_map, List.getElem_range, coeff_mirror]

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves; rfl

private theorem withMoves_id (b : Ecbs.Board)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) : withMoves b m = b := by
  rw [← hm]; unfold withMoves; rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves; rfl

theorem addStep_zero (src cur : List Nat) (i n : Nat) (b : Ecbs.Board)
    (hi : i < src.length) (hz : src[i] = 0) (hto : i ≤ n - 1) (hfi : FitsLen (i + 1)) :
    addStep (embed src) (Int.ofNat (n - 1)) true
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

theorem addStep_nz (src cur : List Nat) (i n moves : Nat) (b : Ecbs.Board)
    (hiS : i < src.length) (hiC : i < cur.length) (hnz : src[i] ≠ 0) (hc : src[i] ≤ 2)
    (hd : cur[i] ≤ 2) (hto : i ≤ n - 1)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) (hfi : FitsLen (i + 1)) :
    addStep (embed src) (Int.ofNat (n - 1)) true
        (Int.ofNat i, (embed cur, b)) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            (embed (cur.set i (tritAdd cur[i] (flipTrit src[i]))),
              withMoves b (Int.ofNat (moves + 1)))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            (embed (cur.set i (tritAdd cur[i] (flipTrit src[i]))),
              withMoves b (Int.ofNat (moves + 1)))))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hto
  simp only [addStep, hng, if_false, if_pos rfl, if_true]
  rw [atL_embed src i hiS]
  simp only [bind, Except.bind, pure, Except.pure, sEq_ofNat_zero, hnz, decide_False,
    Bool.not_false, if_true]
  rw [flip_refines _ hc]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [atL_embed cur i hiC]
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
  simp only [bind, Except.bind, pure, Except.pure, tritAdd, withMoves]
  exact asc_tail (n - 1) i hfi _

/-- The board `add` returns: home `dst` is the sum, moves grew by the source's
    nonzero count. -/
def addBoard (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) : Ecbs.Board :=
  { withMoves b (Int.ofNat mv) with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ arr }

/-- `mirror = true`: destination becomes `fieldAdd dst (mirrorTrits src)`, which is
    `zipWith tritAdd` on equal lengths. Moves grow by `pegCount src`. -/
theorem add_refines (b : Ecbs.Board) (dst src : Nat) (ys xs : List Nat) (n moves : Nat)
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
    Ecbs.add b (dst : Int) (src : Int) true =
      .ok (addBoard b dst hHd (embed (fieldAdd n ys (mirrorTrits xs))) (moves + pegCount xs)) := by
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
    change addStep (embed xs) (Int.ofNat (n - 1)) true
  rw [except_bind_pure]
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Array Int × Ecbs.Board) =>
      st.1 = embed (addPrefix n i ys xs) ∧
      st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
    (Nat.zero_le _) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have hbase : addPrefix n 0 ys xs = ys := by
        apply List.ext_getElem
        · simp [addPrefix_length, hy]
        · intro j hj1 hj2
          have hj : j < n := by rw [addPrefix_length] at hj1; exact hj1
          rw [addPrefix_get n 0 ys xs j hj]
          simp [coeff_eq_get ys j (by omega)]
      simp [hbase]
    · rw [pegCount_take_zero, Nat.add_zero]
      exact (withMoves_id b hmI).symm
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
    have hpref : i < (addPrefix n i ys xs).length := by rw [addPrefix_length]; exact hin
    have hcell : (addPrefix n i ys xs)[i] = ys[i] := by
      rw [addPrefix_get n i ys xs i hin]
      simp [coeff_eq_get ys i hiy]
    have htriC : (addPrefix n i ys xs)[i] ≤ 2 := by rw [hcell]; exact hdy
    let nxtArr := embed (addPrefix n (i + 1) ys xs)
    let nxtMv := moves + pegCount (xs.take i) + if xs[i] = 0 then 0 else 1
    have hpegS : pegCount (xs.take (i + 1)) =
        pegCount (xs.take i) + if xs[i] = 0 then 0 else 1 :=
      pegCount_take_succ xs i hii
    refine ⟨(nxtArr, withMoves b (Int.ofNat nxtMv)), ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      simp [nxtMv, hpegS, Nat.add_assoc]
    · have hb : st.2 = withMoves b (Int.ofNat (moves + pegCount (xs.take i))) := hI.2
      have ha : st.1 = embed (addPrefix n i ys xs) := hI.1
      have hmNow : st.2.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (moves + pegCount (xs.take i)) := by
        rw [hb]; exact withMoves_moves _ _
      have hpair :
          (embed (addPrefix n i ys xs),
            withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) = st :=
        Prod.ext ha.symm hb.symm
      by_cases hz : xs[i] = 0
      · have hstep := addStep_zero xs (addPrefix n i ys xs) i n
          (withMoves b (Int.ofNat (moves + pegCount (xs.take i)))) hii hz hi hfi
        rw [hpair] at hstep
        rw [hstep, ← hpair]
        simp only [nxtArr, nxtMv, hz, if_true, Nat.add_zero]
        rw [addPrefix_skip n i ys xs hin hy hx hz hdy]
      · have hstep := addStep_nz xs (addPrefix n i ys xs) i n
          (moves + pegCount (xs.take i))
          (withMoves b (Int.ofNat (moves + pegCount (xs.take i))))
          hii hpref hz hc htriC hi (withMoves_moves _ _) hfm hfi
        rw [hpair] at hstep
        rw [hstep]
        simp only [nxtArr, nxtMv, if_neg hz]
        rw [addPrefix_succ n i ys xs hin hy hx, coeff_eq_get ys i hiy, coeff_eq_get xs i hii,
          hcell, withMoves_withMoves]
  · intro st hs
    have hdone : addPrefix n n ys xs = fieldAdd n ys (mirrorTrits xs) :=
      addPrefix_done n ys xs hy hx
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
    rw [Array.set_congr_arr hhome hHw (embed (fieldAdd n ys (mirrorTrits xs)))]

/-- Base-3 value, hole 0 in the units place. -/
def toNum : List Nat → Nat
  | [] => 0
  | c :: cs => c + 3 * toNum cs

theorem toNum_inj (xs ys : List Nat) (hx : allTritList xs) (hy : allTritList ys)
    (hl : xs.length = ys.length) (h : toNum xs = toNum ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons c cs ih =>
    cases ys with
    | nil => simp at hl
    | cons d ds =>
      simp [toNum] at h
      have hc : c ≤ 2 := hx c (by simp)
      have hd : d ≤ 2 := hy d (by simp)
      have hcs : allTritList cs := fun z hz => hx z (by simp [hz])
      have hds : allTritList ds := fun z hz => hy z (by simp [hz])
      have hlen : cs.length = ds.length := by simp at hl; exact hl
      have hmod : c = d := by
        have h3 : c + 3 * toNum cs = d + 3 * toNum ds := h
        omega
      have hrest : toNum cs = toNum ds := by omega
      simp [ih ds hcs hds hlen hrest, hmod]

end EcbsLink2.Link2
