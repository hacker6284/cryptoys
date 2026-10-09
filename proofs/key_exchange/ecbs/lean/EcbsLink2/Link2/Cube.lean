/-
  Comb cube: the ascending loop writes `v[i]` at hole `3*i` (two moves per nonzero peg),
  then the same lane fold as multiplication. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Lane
import EcbsLink2.Link2.Mul
import EcbsLink2.Link2.Settle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Prefix of the comb: the first `k` pegs of `xs`, each nonzero coefficient at hole `3*i`. -/
def combAt (xs : List Nat) (bench : Nat) : Nat → List Nat
  | 0 => List.replicate bench 0
  | k + 1 =>
    let prev := combAt xs bench k
    let c := coeff xs k
    if c = 0 then prev else prev.set (3 * k) c

private theorem combAt_zero (xs : List Nat) (bench : Nat) :
    combAt xs bench 0 = List.replicate bench 0 := rfl

private theorem combAt_succ (xs : List Nat) (bench k : Nat) :
    combAt xs bench (k + 1) =
      (let prev := combAt xs bench k
       let c := coeff xs k
       if c = 0 then prev else prev.set (3 * k) c) := rfl

private theorem combAt_foldl (xs : List Nat) (bench : Nat) :
    ∀ k, combAt xs bench k =
      (List.range k).foldl (fun s i =>
          let c := coeff xs i
          if c = 0 then s else s.set (3 * i) c)
        (List.replicate bench 0)
  | 0 => by simp [combAt, List.range_zero]
  | k + 1 => by
    rw [combAt_succ, List.range_succ, List.foldl_append, combAt_foldl xs bench k]
    simp

private theorem combStrip_eq (n bench : Nat) (xs : List Nat) :
    combStrip n bench xs = combAt xs bench n := by
  unfold combStrip
  exact (combAt_foldl xs bench n).symm

private theorem coeff_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    coeff xs j = xs[j] := by
  unfold coeff
  simp [hj]

private theorem coeff_set_same (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    coeff (xs.set i v) i = v := by
  have hi' : i < (xs.set i v).length := by rw [List.length_set]; exact hi
  rw [coeff_get _ _ hi', List.getElem_set_self]

private theorem coeff_set_ne (xs : List Nat) (i v j : Nat) (hj : j < xs.length) (hne : i ≠ j) :
    coeff (xs.set i v) j = coeff xs j := by
  have hj' : j < (xs.set i v).length := by rw [List.length_set]; exact hj
  rw [coeff_get _ _ hj', List.getElem_set, if_neg hne, ← coeff_get xs j hj]

private theorem combAt_length (xs : List Nat) (bench : Nat) :
    ∀ k, (combAt xs bench k).length = bench
  | 0 => by simp [combAt, List.length_replicate]
  | k + 1 => by
    rw [combAt_succ]
    dsimp only
    by_cases h0 : coeff xs k = 0
    · simp [h0, combAt_length xs bench k]
    · simp [h0, List.length_set, combAt_length xs bench k]

theorem combStrip_length (n bench : Nat) (xs : List Nat) :
    (combStrip n bench xs).length = bench := by
  rw [combStrip_eq]
  exact combAt_length xs bench n

/-- Before step `i`, hole `3*i` is still empty. Later steps are the only ones that can fill it. -/
private theorem combAt_cell_zero (xs : List Nat) (bench i : Nat) (h3 : 3 * i < bench) :
    ∀ k, k ≤ i → coeff (combAt xs bench k) (3 * i) = 0
  | 0, _ => by
    have hlen : 3 * i < (List.replicate bench 0).length := by
      rw [List.length_replicate]; exact h3
    rw [combAt_zero, coeff_get _ _ hlen, List.getElem_replicate]
  | k + 1, hk => by
    have hk' : k < i := by omega
    have hk0 : k ≤ i := Nat.le_of_lt hk'
    rw [combAt_succ]
    dsimp only
    by_cases h0 : coeff xs k = 0
    · simp only [h0, ite_true]
      exact combAt_cell_zero xs bench i h3 k hk0
    · simp only [h0, ite_false]
      have hlen : 3 * i < (combAt xs bench k).length := by
        rw [combAt_length]; exact h3
      have hne : 3 * k ≠ 3 * i := by
        intro h
        exact Nat.ne_of_lt hk' (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h)
      rw [coeff_set_ne _ _ _ _ hlen hne]
      exact combAt_cell_zero xs bench i h3 k hk0

/-- Hole `3*i` of the comb is `v[i]`, once step `i` has run and no later step shares that hole. -/
private theorem combAt_cell (xs : List Nat) (bench i : Nat) (h3 : 3 * i < bench) :
    ∀ m, i < m → coeff (combAt xs bench m) (3 * i) = coeff xs i
  | 0, hm => by omega
  | m + 1, hm => by
    rw [combAt_succ]
    dsimp only
    by_cases h0 : coeff xs m = 0
    · simp only [h0, ite_true]
      by_cases hlt : i < m
      · exact combAt_cell xs bench i h3 m hlt
      · have heq : i = m := by omega
        subst heq
        rw [combAt_cell_zero xs bench i h3 i (Nat.le_refl _)]
        exact h0.symm
    · simp only [h0, ite_false]
      have hlen : 3 * i < (combAt xs bench m).length := by
        rw [combAt_length]; exact h3
      by_cases hlt : i < m
      · have hne : 3 * m ≠ 3 * i := by
          intro h
          exact Nat.ne_of_lt hlt (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h).symm
        rw [coeff_set_ne _ _ _ _ hlen hne]
        exact combAt_cell xs bench i h3 m hlt
      · have heq : i = m := by omega
        subst heq
        exact coeff_set_same _ (3 * i) _ hlen

/-- `strip[3*i] = v[i]` on `Spec.combStrip`. A zero coefficient leaves the hole empty. -/
theorem comb_cell (xs : List Nat) (bench n i : Nat) (hi : i < n) (h3 : 3 * i < bench) :
    coeff (combStrip n bench xs) (3 * i) = coeff xs i := by
  rw [combStrip_eq]
  exact combAt_cell xs bench i h3 n hi

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

private theorem coeff_le (xs : List Nat) (h : allTritList xs) (i : Nat) : coeff xs i ≤ 2 := by
  by_cases hi : i < xs.length
  · rw [coeff_get xs i hi]
    exact h _ (List.getElem_mem hi)
  · unfold coeff
    have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hi)
    simp [List.getD, hnone]

private theorem allTritList_set {xs : List Nat} (h : allTritList xs) {i v : Nat}
    (_hi : i < xs.length) (hv : v ≤ 2) : allTritList (xs.set i v) := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hlen : (xs.set i v).length = xs.length := by rw [List.length_set]
  have hj' : j < xs.length := by rw [← hlen]; exact hj
  rw [List.getElem_set]
  by_cases hij : i = j
  · simp [hij, hv]
  · simp [hij]
    exact h _ (List.getElem_mem hj')

private theorem combAt_trits (xs : List Nat) (bench n : Nat) (hxs : allTritList xs)
    (hspan : 3 * (n - 1) < bench) : ∀ k, k ≤ n → allTritList (combAt xs bench k)
  | 0, _ => replicate_trits bench
  | k + 1, hk => by
    have hn : 0 < n := by omega
    have hidx : 3 * k < bench := by
      have hk' : k ≤ n - 1 := by omega
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 hk') hspan
    rw [combAt_succ]
    dsimp only
    have hprev := combAt_trits xs bench n hxs hspan k (Nat.le_of_succ_le hk)
    by_cases h0 : coeff xs k = 0
    · simp only [h0, ite_true]
      exact hprev
    · simp only [h0, ite_false]
      exact allTritList_set hprev (by rw [combAt_length]; exact hidx) (coeff_le xs hxs k)

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_id (b : Ecbs.Board)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) :
    withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro i hi hi'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem laid_step (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    2 * laidCount xs (j + 1) =
      2 * laidCount xs j + if xs[j] = 0 then 0 else 2 := by
  rw [laidCount_succ, coeff_get xs j hj]
  by_cases h : xs[j] = 0
  · simp [h]
  · simp [h]
    omega

private theorem combAt_step (xs : List Nat) (bench j : Nat) (hj : j < xs.length)
    (h3 : 3 * j < bench) :
    (if xs[j] = 0 then combAt xs bench j else (combAt xs bench j).set (3 * j) xs[j]) =
      combAt xs bench (j + 1) := by
  have _ := h3
  rw [combAt_succ]
  dsimp only
  have hc : coeff xs j = xs[j] := coeff_get xs j hj
  rw [hc]

/-- One emitted comb step. A zero peg is left alone; a nonzero peg is copied to hole `3*i`
    and charged two moves. -/
def combBody (v strip : Array Int) (i : Int) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board) :=
  do
    let c ← SudoRt.atL v i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let ix ← SudoRt.mulI (3 : Int) i
        let c2 ← SudoRt.atL v i
        let strip ← SudoRt.putL strip ix c2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        let b := withMoves b mv
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (strip, b))
    else
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (strip, b))

/-- Ascending `for i = 0 to n - 1` comb. `Ecbs.cube` inlines this loop. -/
def combStep (v : Array Int) (toV : Int) (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board) :=
  let i := σ.1
  let strip := σ.2.1
  let b := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, (strip, b)))
    else
      match ← combBody v strip i b with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem combBody_zero (xs strip : List Nat) (j : Nat) (b : Ecbs.Board)
    (hx : j < xs.length) (hz : xs[j] = 0) :
    combBody (embed xs) (embed strip) (Int.ofNat j) b =
      .ok (.cont (embed strip, b)) := by
  unfold combBody
  rw [atL_embed xs j hx, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

private theorem combBody_pos (xs strip : List Nat) (j m : Nat) (b : Ecbs.Board)
    (hx : j < xs.length) (hz : xs[j] ≠ 0) (hidx : 3 * j < strip.length)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat m)
    (h3 : FitsLen (3 * j)) (h2 : FitsLen (m + 2)) :
    combBody (embed xs) (embed strip) (Int.ofNat j) b =
      .ok (.cont (embed (strip.set (3 * j) xs[j]), withMoves b (Int.ofNat (m + 2)))) := by
  unfold combBody
  rw [atL_embed xs j hx, ok_bind, sEq_ofNat_zero]
  simp only [hz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl]
  rw [mulI_ofNat 3 j h3, ok_bind]
  rw [embed_put strip (3 * j) xs[j] hidx, ok_bind]
  rw [hm, show (2 : Int) = Int.ofNat 2 from rfl, addI_ofNat m 2 h2, ok_bind]
  rfl

private theorem combStep_hit (xs strip : List Nat) (j toN m : Nat) (b : Ecbs.Board)
    (hj : j ≤ toN) (hx : j < xs.length) (hidx : 3 * j < strip.length)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat m)
    (h3 : FitsLen (3 * j)) (h2 : FitsLen (m + 2)) (hfj : FitsLen (j + 1)) :
    combStep (embed xs) (Int.ofNat toN) (Int.ofNat j, (embed strip, b)) =
      (if j = toN then
          .ok (.brk (Int.ofNat j,
            (embed (if xs[j] = 0 then strip else strip.set (3 * j) xs[j]),
              if xs[j] = 0 then b else withMoves b (Int.ofNat (m + 2)))))
        else
          .ok (.cont (Int.ofNat (j + 1),
            (embed (if xs[j] = 0 then strip else strip.set (3 * j) xs[j]),
              if xs[j] = 0 then b else withMoves b (Int.ofNat (m + 2)))))) := by
  unfold combStep
  dsimp only
  have hngt : ¬ (Int.ofNat j > Int.ofNat toN) := not_gt_cast hj
  rw [if_neg hngt]
  by_cases hz : xs[j] = 0
  · rw [combBody_zero xs strip j b hx hz, ok_bind]
    simp only [hz, pure_eq_ok]
    exact asc_tail toN j hfj _
  · rw [combBody_pos xs strip j m b hx hz hidx hm h3 h2, ok_bind]
    simp only [hz, pure_eq_ok]
    exact asc_tail toN j hfj _

/-- The comb loop of `Ecbs.cube`. Nonzero `v[i]` is written at hole `3*i` (`comb_cell`)
    and charged two moves. The strip is `Spec.combStrip`. -/
theorem comb_loop_refines {β}
    (xs : List Nat) (moves bench n : Nat) (b : Ecbs.Board)
    (after : Int × (Array Int × Ecbs.Board) → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : 0 < n) (hx : n ≤ xs.length) (hspan : 3 * (n - 1) < bench)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfn : FitsLen n) (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n)) :
    SudoRt.runLoopOn (ρ := Ecbs.Board)
        (Int.ofNat 0, (embed (List.replicate bench 0), b))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)))
        (combStep (embed xs) (Int.ofNat (n - 1)))
        after onRet =
      after (Int.ofNat (n - 1),
        (embed (combStrip n bench xs),
          withMoves b (Int.ofNat (moves + 2 * laidCount xs n)))) := by
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Array Int × Ecbs.Board) =>
      st.1 = embed (combAt xs bench i) ∧
      st.2 = withMoves b (Int.ofNat (moves + 2 * laidCount xs i)))
    (Nat.zero_le _) ?_ ?_ ?_
  · refine ⟨rfl, ?_⟩
    rw [laidCount_zero, Nat.mul_zero, Nat.add_zero]
    exact (withMoves_id b hm).symm
  · intro i st _ hi hI
    have hin : i < n := by omega
    have hix : i < xs.length := by omega
    have hidx : 3 * i < (combAt xs bench i).length := by
      rw [combAt_length]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 (Nat.le_sub_one_of_lt hin)) hspan
    have h3f : FitsLen (3 * i) := FitsLen.of_le h3 (by omega)
    have hlaid : laidCount xs i ≤ i := laidCount_le xs i
    have h2 : FitsLen (moves + 2 * laidCount xs i + 2) := FitsLen.of_le hfm (by omega)
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfn (by omega)
    have hm' : st.2.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + 2 * laidCount xs i) := by
      rw [hI.2]
      exact withMoves_moves _ _
    have hstep := combStep_hit xs (combAt xs bench i) i (n - 1)
      (moves + 2 * laidCount xs i) st.2 hi hix hidx hm' h3f h2 hfi
    have hpair : st = (embed (combAt xs bench i), st.2) := Prod.ext hI.1 rfl
    rw [hpair]
    refine ⟨(embed (if xs[i] = 0 then combAt xs bench i
            else (combAt xs bench i).set (3 * i) xs[i]),
        if xs[i] = 0 then st.2
        else withMoves st.2 (Int.ofNat (moves + 2 * laidCount xs i + 2))), ?_, hstep⟩
    refine ⟨?_, ?_⟩
    · apply congrArg embed
      exact combAt_step xs bench i hix (by rw [combAt_length] at hidx; exact hidx)
    · rw [hI.2]
      by_cases hz : xs[i] = 0
      · simp only [hz, ite_true, laid_step xs i hix, Nat.add_zero]
      · simp only [hz, ite_false, laid_step xs i hix, withMoves_withMoves, Nat.add_assoc]
  · intro st hI
    have hn1 : n - 1 + 1 = n := by omega
    have hs : st = (embed (combStrip n bench xs),
        withMoves b (Int.ofNat (moves + 2 * laidCount xs n))) := by
      refine Prod.ext ?_ ?_
      · rw [hI.1, hn1, combStrip_eq]
      · rw [hI.2, hn1]
    rw [hs]

/-- The tail of `Ecbs.cube`: the comb-gap check, then `lane_fold`, then `note_peak`. -/
def combAfter (dst : Int) (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap Ecbs.Board :=
  do
    let last ← SudoRt.subI σ.2.2.sudo_5Board_1t.sudo_4Tier_1n (1 : Int)
    let span ← SudoRt.mulI (3 : Int) last
    let reach ← SudoRt.addI span σ.2.2.sudo_5Board_1t.sudo_4Tier_7combgap
    SudoRt.sudoAssert (decide (reach < σ.2.2.sudo_5Board_1t.sudo_4Tier_8benchlen)) 614
    let folded ← Ecbs.lane_fold
      { σ.2.2 with
          sudo_5Board_8bench_on := true
          sudo_5Board_8bench_to := dst } σ.2.1
    let out ← Ecbs.note_peak { folded.1 with sudo_5Board_5bench := folded.2 }
    pure out

private theorem set_on {α : Type} {a b : Array α} (hab : a = b) (i : Nat)
    (ha : i < a.size) (v : α) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, hab ▸ ha⟩ v := by
  subst hab
  rfl

private theorem overwrite {α : Type} (a : Array α) (i : Nat) (h : i < a.size) (v w : α)
    (h2 : i < (a.set ⟨i, h⟩ v).size) :
    (a.set ⟨i, h⟩ v).set ⟨i, h2⟩ w = a.set ⟨i, h⟩ w := by
  apply Array.ext
  · rw [Array.size_set, Array.size_set, Array.size_set]
  · intro j _hj1 _hj2
    by_cases hje : i = j
    · simp [Array.getElem_set, hje]
    · simp [Array.getElem_set, hje]

private theorem withMoves_tier (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold withMoves
  rfl

private theorem withMoves_hole (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold withMoves
  rfl

private theorem withMoves_held (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold withMoves
  rfl

/-- Moves `Ecbs.cube` leaves: the incoming counter, two per nonzero comb peg, and the lane fold. -/
def cubeMoves (moves : Nat) (xs : List Nat) (n k bench : Nat) : Nat :=
  let sch := combStrip n bench xs
  moves + 2 * laidCount xs n + foldCharge n (n - k) sch

/-- Marker off, bench off. The board `Ecbs.cube` returns: ops slot 1 bumped, the source
    home cleared, the bench on and aimed at `dst` holding the folded comb. `peak_strict`
    is the held-count before that clear. `peak` is the held-count after it. -/
def cubeOffBoard (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) : Ecbs.Board :=
  let sch := combStrip n bench xs
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨src, hHome⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨src, hF⟩ false
    sudo_5Board_8bench_on := true
    sudo_5Board_8bench_to := (dst : Int)
    sudo_5Board_5bench := embed (laneFold n (n - k) sch)
    sudo_5Board_9marker_on := false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (cubeMoves moves xs n k bench)
      sudo_5Costs_4peak :=
        Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hF⟩ false) 7))
      sudo_5Costs_11peak_strict :=
        Int.ofNat (raisedPeak peakS (countHeld b.sudo_5Board_4held 7))
      sudo_5Costs_14max_bench_hole := Int.ofNat (raisedHole hole (topIdx sch))
      sudo_5Costs_3ops :=
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) } }

theorem cube_off_bench (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_5bench =
      embed (laneFold n (n - k) (combStrip n bench xs)) := rfl

theorem cube_off_prefix (n k bench : Nat) (xs : List Nat) :
    (laneFold n (n - k) (combStrip n bench xs)).take n = fieldCube n k bench xs := by
  unfold fieldCube laneFold
  rfl

theorem cube_off_high (xs : List Nat) (n k bench : Nat) (hn0 : 0 < n) (hgap0 : 0 < n - k) :
    ∀ i, n ≤ i → i < bench →
      coeff (laneFold n (n - k) (combStrip n bench xs)) i = 0 := by
  intro i hlo hi
  have hlen : (combStrip n bench xs).length = bench := combStrip_length n bench xs
  exact laneFold_high n (n - k) (combStrip n bench xs) i hn0 hgap0
    (by rw [hlen]; omega) hlo (by rw [hlen]; exact hi)

theorem cube_off_home (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨src, hHome⟩ #[] := rfl

theorem cube_off_held (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨src, hF⟩ false := rfl

theorem cube_off_moves (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves moves xs n k bench) := rfl

theorem cube_off_slides (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := rfl

theorem cube_off_peak (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hF⟩ false) 7)) := rfl

theorem cube_off_tally (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 := rfl

theorem cube_off_highest (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := rfl

theorem cube_off_row (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_3row =
      b.sudo_5Board_3row := rfl

theorem cube_off_tier (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_1t =
      b.sudo_5Board_1t := rfl

theorem cube_off_ctrl (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := rfl

theorem cube_off_marker (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_9marker_on =
      false := rfl

theorem cube_off_on (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_8bench_on =
      true := rfl

theorem cube_off_to (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_8bench_to =
      (dst : Int) := rfl

theorem cube_off_ops (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := rfl

/-- Marker off, bench off. `Ecbs.cube` returns `cubeOffBoard`: it combs `xs` onto every
    third hole, folds, and leaves the bench on, aimed at `dst`. -/
theorem cube_off_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hxsT : allTritList xs)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b (dst : Int) (src : Int) =
      .ok (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome) := by
  unfold Ecbs.cube Ecbs.log_op
  simp only [hmk, hoff, Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  rw [show Ecbs.op_cube = Int.ofNat 1 from rfl, atL_ofNat _ 1 hops, hop1, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 1 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    pattern Ecbs.settle _
    rw [settle_off _ rfl]
  simp only [ok_bind, pure_eq_ok]
  let b1 : Ecbs.Board :=
    { b with
      sudo_5Board_8bench_on := false
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict b1
  have h7₁ : 7 ≤ b1.sudo_5Board_4held.size := by simpa [b1] using h7
  have hp1 : b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [b1] using hpeakS
  rw [note_strict_eq b1 peakS h7₁ hp1]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard b1 peakS
  have hS : strictBoard b1 peakS = bS := rfl
  conv =>
    pattern (strictBoard b1 peakS)
    rw [hS]
  have hheldS : bS.sudo_5Board_4held = b1.sudo_5Board_4held := rfl
  have hhomeS : bS.sudo_5Board_4home = b1.sudo_5Board_4home := rfl
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves =
      b1.sudo_5Board_4cost.sudo_5Costs_5moves := rfl
  have htS : bS.sudo_5Board_1t = b1.sudo_5Board_1t := rfl
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl
  have hpeakKeep : bS.sudo_5Board_4cost.sudo_5Costs_4peak =
      b1.sudo_5Board_4cost.sudo_5Costs_4peak := rfl
  have hslidesS : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
      b1.sudo_5Board_4cost.sudo_5Costs_6slides := rfl
  have hrowS : bS.sudo_5Board_3row = b1.sudo_5Board_3row := rfl
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
      b1.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  have htallyS : bS.sudo_5Board_6tally0 = b1.sudo_5Board_6tally0 := rfl
  have hhighS : bS.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b1.sudo_5Board_4cost.sudo_5Costs_15control_highest := rfl
  have hctrlS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b1.sudo_5Board_4cost.sudo_5Costs_4ctrl := rfl
  have hmkS : bS.sudo_5Board_9marker_on = b1.sudo_5Board_9marker_on := rfl
  have hFs : src < bS.sudo_5Board_4held.size := by rw [hheldS]; simpa [b1] using hF
  have hHome1 : src < b1.sudo_5Board_4home.size := by simpa [b1] using hHome
  have hHomes : src < bS.sudo_5Board_4home.size := by rw [hhomeS]; exact hHome1
  rw [hheldS, ← ofNat_eq_natCast src, atL_ofNat _ src hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [hhomeS, atL_ofNat _ src hHome1, hArr, ok_bind]
  rw [putL_ofNat _ src false hF, ok_bind]
  rw [putL_ofNat _ src (#[] : Array Int) hHome1, ok_bind]
  have ht1 : b1.sudo_5Board_1t = b.sudo_5Board_1t := by simp [b1]
  conv =>
    pattern (SudoRt.filledL _ _)
    rw [htS, ht1, hbl, filledL_ofNat]
  rw [ok_bind, ← embed_replicate_zero]
  conv =>
    pattern (SudoRt.subI _ _)
    rw [htS, ht1, hn, ← ofNat_eq_natCast n, subI_ofNat_one n hn0 hf]
  rw [ok_bind]
  have hfuel :
      (if (0 : Int) > Int.ofNat (n - 1) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bC : Ecbs.Board :=
    { bS with
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨src, hF⟩ false
      sudo_5Board_4home := b1.sudo_5Board_4home.set ⟨src, hHome1⟩ #[] }
  conv =>
    pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
    change combStep (embed xs) (Int.ofNat (n - 1))
  conv =>
    pattern ((0 : Int), _)
    change (Int.ofNat 0, (embed (List.replicate bench 0), bC))
  have hmC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simpa [bC, hmovS, b1, ofNat_eq_natCast] using hmoves
  have hspan3 : 3 * (n - 1) < bench := by omega
  conv =>
    pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
    change combAfter (dst : Int)
  rw [comb_loop_refines xs moves bench n bC _ _ hn0
      (by rw [hlenx]; exact Nat.le_refl _) hspan3 hmC hf h3 hfm]
  unfold combAfter
  dsimp only
  have htC : bC.sudo_5Board_1t = b.sudo_5Board_1t := by simp [bC, htS, ht1]
  have hmovW :
      (withMoves bC (Int.ofNat (moves + 2 * laidCount xs n))).sudo_5Board_1t =
        b.sudo_5Board_1t := by
    rw [withMoves_tier, htC]
  conv =>
    pattern (SudoRt.subI _ _)
    rw [hmovW, hn, ← ofNat_eq_natCast n, subI_ofNat_one n hn0 hf]
  rw [ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl, mulI_ofNat 3 (n - 1) h3, ok_bind]
  have hcgW :
      (withMoves bC (Int.ofNat (moves + 2 * laidCount xs n))).sudo_5Board_1t.sudo_4Tier_7combgap =
        Int.ofNat cg := by rw [hmovW, hcg]
  rw [hcgW]
  have hfitSum : FitsLen (3 * (n - 1) + cg) := FitsLen.of_le hfitB (Nat.le_of_lt hspan)
  have hblW :
      (withMoves bC (Int.ofNat (moves + 2 * laidCount xs n))).sudo_5Board_1t.sudo_4Tier_8benchlen =
        Int.ofNat bench := by rw [hmovW, hbl]
  rw [addI_ofNat (3 * (n - 1)) cg hfitSum, ok_bind, hblW]
  have hdec : decide (Int.ofNat (3 * (n - 1) + cg) < Int.ofNat bench) = true :=
    decide_eq_true ((ofNat_lt_iff _ _).mpr hspan)
  rw [hdec, sudoAssert_true, ok_bind]
  let mv := moves + 2 * laidCount xs n
  let sch := combStrip n bench xs
  let bW := withMoves bC (Int.ofNat mv)
  let bF : Ecbs.Board :=
    { bW with sudo_5Board_8bench_on := true, sudo_5Board_8bench_to := (dst : Int) }
  conv =>
    pattern (Ecbs.lane_fold _ _)
    change Ecbs.lane_fold bF (embed sch)
  have hlenS : sch.length = bench := by
    simp [sch, combStrip_eq, combAt_length]
  have hfitS : FitsLen sch.length := by simpa [hlenS] using hfitB
  have htF : bF.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp only [bF, bW, withMoves, bC]
    rw [htS, ht1]
  have hwB : bF.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htF, hwF]
  have hhB : bF.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htF, hhF]
  have hrB : bF.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htF, hrF]
  have hnB : bF.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    rw [htF, hn, ofNat_eq_natCast]
  have hkB : bF.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htF, hkF]
  have hblB : bF.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [htF, hbl]
  rw [lane_fold_eq sch w h r n k bench bF hfitS hwB hhB hrB hnB hkB hblB]
  have hmovF : bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    simp [bF, bW, withMoves]
  have hholeF : bF.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bF, bW, withMoves, bC, hholeS, b1, hHole]
  have htri : allTritList sch := by
    simpa [sch, combStrip_eq] using
      combAt_trits xs bench n hxsT hspan3 n (Nat.le_refl _)
  have hlaid : laidCount xs n ≤ n := laidCount_le xs n
  have hfitF : FitsLen (mv + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by omega)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  rw [lane_fold_refines sch w h r n k mv hole bench bF
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmovF hholeF hsmS hnsm hfitF hfitS
      (by rw [hlenS]; exact Nat.le_refl _) (by omega : 0 < bench)]
  simp only [ok_bind, pure_eq_ok, Prod.fst, Prod.snd]
  let nb := noteBench bF (Int.ofNat (topIdx sch))
      (Int.ofNat (mv + foldCharge n (n - k) sch))
  let bN : Ecbs.Board := { nb with sudo_5Board_5bench := embed (laneFold n (n - k) sch) }
  conv =>
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak bN
  have h7N : 7 ≤ bN.sudo_5Board_4held.size := by
    dsimp [bN, nb]
    unfold noteBench
    split
    · simp only [withMoves, withHole, bF, bW, bC, Array.size_set]
      exact h7
    · simp only [withMoves, bF, bW, bC, Array.size_set]
      exact h7
  have honN : bN.sudo_5Board_8bench_on = true := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    dsimp [bF, bW]
    split <;> rfl
  have htoN : bN.sudo_5Board_8bench_to = (dst : Int) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    dsimp [bF, bW]
    split <;> rfl
  have _hhigh : ∀ i, n ≤ i → i < bench → coeff (laneFold n (n - k) sch) i = 0 := by
    intro i hlo hi
    have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
    have hnb : n ≤ bench := by omega
    exact laneFold_high n (n - k) sch i hn0 hgap0 (by rw [hlenS]; exact hnb) hlo
      (by rw [hlenS]; exact hi)
  have _hpre : (laneFold n (n - k) sch).take n = fieldCube n k bench xs := by
    unfold fieldCube laneFold sch
    rfl
  have hpeakN : bN.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hpeakKeep, b1, hpeak]
  have hmovN : bN.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv + foldCharge n (n - k) sch) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> rfl
  have hmovEq : mv + foldCharge n (n - k) sch = cubeMoves moves xs n k bench := by
    simp [cubeMoves, mv, sch]
  have hslidesN : bN.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hslidesS, b1]
  have hheldN : bN.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨src, hF⟩ false := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hheldS, b1]
  have htN : bN.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, htS, b1]
  have _hhomeSz : bN.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hhomeS, b1, Array.size_set]
  have hhomeN : bN.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨src, hHome⟩ #[] := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hhomeS, b1, hHome]
  have hmkN : bN.sudo_5Board_9marker_on = false := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hmkS, b1]
  have hrowN : bN.sudo_5Board_3row = b.sudo_5Board_3row := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hrowS, b1]
  have hopN : bN.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hopS, b1]
  have htallyN : bN.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, htallyS, b1]
  have hhighN : bN.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hhighS, b1]
  have hctrlN : bN.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, hctrlS, b1]
  have hstrictN : bN.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak peakS (countHeld b.sudo_5Board_4held 7)) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  have hholeN : bN.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx sch)) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    rw [hholeF]
    by_cases hgt : hole < topIdx sch
    · have hdec : decide (↑(topIdx sch) > Int.ofNat hole) = true := by
        rw [decide_eq_true_eq, ← ofNat_eq_natCast (topIdx sch)]
        exact (ofNat_lt_iff hole (topIdx sch)).mpr hgt
      rw [hdec]
      rw [if_pos rfl]
      unfold raisedHole
      rw [if_pos hgt]
    · have hdec : decide (↑(topIdx sch) > Int.ofNat hole) = false := by
        rw [decide_eq_false_iff_not]
        intro hgtI
        rw [← ofNat_eq_natCast (topIdx sch)] at hgtI
        exact hgt ((ofNat_lt_iff hole (topIdx sch)).mp hgtI)
      rw [hdec]
      simp only [Bool.false_eq_true, if_false]
      unfold raisedHole
      rw [if_neg hgt]
      simp [bW, withMoves, bC, hholeS, b1, hHole, ofNat_eq_natCast]
  rw [note_peak_eq bN peak h7N hpeakN]
  simp only [ok_bind, pure_eq_ok]
  apply congrArg Except.ok
  apply board_ext
  · exact htN
  · exact hhomeN
  · exact hheldN
  · exact honN
  · exact htoN
  · dsimp [bN]; rfl
  · apply cost_ext
    · exact hmovN.trans (congrArg Int.ofNat hmovEq)
    · exact hslidesN
    · exact hctrlN
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · exact congrArg (fun held => Int.ofNat (raisedPeak peak (countHeld held 7))) hheldN
    · exact hstrictN
    · exact hholeN
    · exact hhighN
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · dsimp [bN, nb, peakBoard]
      unfold noteBench withMoves withHole
      split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
    · exact hopN
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · exact hrowN
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · exact htallyN
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · exact hmkN
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]
  · dsimp [bN, nb, peakBoard]
    unfold noteBench withMoves withHole
    split <;> simp [bF, bW, withMoves, bC, bS, strictBoard, b1, cubeOffBoard]

/-- The field-by-field reading of `cubeOffBoard`. Callers that still open an
    existential use this; the equation is `cube_off_eq`. -/
theorem cube_refines (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hxsT : allTritList xs)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    ∃ b', Ecbs.cube b (dst : Int) (src : Int) = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (dst : Int) ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (combStrip n bench xs)) ∧
      (laneFold n (n - k) (combStrip n bench xs)).take n =
        fieldCube n k bench xs ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (combStrip n bench xs)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (cubeMoves moves xs n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hF⟩ false) 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨src, hHome⟩ #[] ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨src, hF⟩ false ∧
      b'.sudo_5Board_9marker_on = false ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) ∧
      b'.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  rw [cube_off_eq b dst src xs w h r n k moves hole bench peak peakS cOps cg
      hmk hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf
      hmoves hpeak hpeakS hxsT h3 hfm hw0 hh0 hrR hrP hnE hkLe hgap hwF hhF hrF hkF
      hHole hsm hnsm hfitB hfold]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold fieldCube laneFold
    rfl
  · exact cube_off_high xs n k bench hn0 (by rw [hgap]; exact Nat.mul_pos hw0 hrP)
  · simp [cubeOffBoard, Array.size_set]

/-- `settle` then `value` on a bench whose tail is empty. `settle_refines` writes the
    length-`n` prefix and sets the home held; `value_after_set` reads it back. -/
theorem folded_read (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (n moves slides peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n))) :
    (do
        let b2 ← Ecbs.settle b
        Ecbs.value b2 (home : Int)) =
      .ok (embed (xs.take n)) := by
  rw [settle_refines b home xs n moves slides peak hH hD h7 hon hto hempty hbench hn hpos hnle
      hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS, ok_bind]
  unfold settleBoard
  dsimp only
  let pegs := pegCount (xs.take n)
  let held1 := b.sudo_5Board_4held.set ⟨home, hD⟩ true
  split
  · let b0 : Ecbs.Board :=
      { b with
        sudo_5Board_4held := held1
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs)
          sudo_5Costs_4peak := Int.ofNat (countHeld held1 7) } }
    have hH0 : home < b0.sudo_5Board_4home.size := by simpa [b0] using hH
    have hD0 : home < b0.sudo_5Board_4held.size := by
      simpa [b0, held1, Array.size_set] using hD
    have hheld0 : b0.sudo_5Board_4held[home] = true := by
      simp [b0, held1, Array.getElem_set]
    have hn0 : b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
      simp [b0, hn, ofNat_eq_natCast]
    conv =>
      pattern (Ecbs.value _ _)
      change Ecbs.value
        { b0 with sudo_5Board_4home :=
            b0.sudo_5Board_4home.set ⟨home, hH0⟩ (embed (xs.take n)) }
        (home : Int)
    exact value_after_set b0 home xs n hH0 hD0 hheld0 hn0 hf hnle
  · let b0 : Ecbs.Board :=
      { b with
        sudo_5Board_4held := held1
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs) } }
    have hH0 : home < b0.sudo_5Board_4home.size := by simpa [b0] using hH
    have hD0 : home < b0.sudo_5Board_4held.size := by
      simpa [b0, held1, Array.size_set] using hD
    have hheld0 : b0.sudo_5Board_4held[home] = true := by
      simp [b0, held1, Array.getElem_set]
    have hn0 : b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
      simp [b0, hn, ofNat_eq_natCast]
    conv =>
      pattern (Ecbs.value _ _)
      change Ecbs.value
        { b0 with sudo_5Board_4home :=
            b0.sudo_5Board_4home.set ⟨home, hH0⟩ (embed (xs.take n)) }
        (home : Int)
    exact value_after_set b0 home xs n hH0 hD0 hheld0 hn0 hf hnle

private theorem array_get_congr {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  induction h
  rfl

/-- `cube` on a live bench equals `cube` after that bench has been slid into `src`.
    The opening op-count bump and `settle` commute, and with the marker off `log_op`
    is the identity, so the bench-off lemma applies to the slid board. -/
theorem cube_live_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n moves slides peak cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (src : Int))
    (hH : src < b.sudo_5Board_4home.size)
    (hD : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[src] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.cube b (dst : Int) (src : Int) =
      Ecbs.cube (settleBoard b src hH hD xs n moves slides peak) (dst : Int) (src : Int) := by
  let bS := settleBoard b src hH hD xs n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7
    · rw [show bS = settleBoard b src hH hD xs n moves slides peak from rfl,
        settle_peak b src hH hD xs n moves slides peak hpk, hmk]
    · rw [show bS = settleBoard b src hH hD xs n moves slides peak from rfl,
        settle_keep b src hH hD xs n moves slides peak hpk, hmk]
  have hmkRaw :
      (settleBoard b src hH hD xs n moves slides peak).sudo_5Board_9marker_on = false :=
    hmkS
  unfold Ecbs.cube Ecbs.log_op
  simp only [hmk, hmkRaw, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 src hops hH hD xs n moves slides peak
  have hop1S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    have hget := array_get_congr (settle_ops b src hH hD xs n moves slides peak) 1 hopsS
    exact hget.trans hop1
  conv =>
    lhs
    rw [show Ecbs.op_cube = Int.ofNat 1 from rfl, atL_ofNat _ 1 hops, hop1, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 1 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    rhs
    rw [show Ecbs.op_cube = Int.ofNat 1 from rfl, atL_ofNat _ 1 hopsS, hop1S, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 1 (Int.ofNat (cOps + 1)) hopsS, ok_bind]
  let bL : Ecbs.Board :=
    { b with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    lhs
    pattern (Ecbs.settle _)
    change Ecbs.settle bL
  have hbL : bL = bumpOp b 1 cOps hops := by
    apply board_ext
    case hmon => simp [bL, bumpOp, hmk]
    all_goals simp [bL, bumpOp]
  rw [hbL]
  have hsetL := settle_refines (bumpOp b 1 cOps hops) src xs n moves slides peak
      (bump_home_lt b 1 cOps src hops hH) (bump_held_lt b 1 cOps src hops hD) h7
      (by simp [bumpOp, hon]) (by simp [bumpOp, hto]) (by simpa [bumpOp] using hempty)
      (by simp [bumpOp, hbench]) hn hpos hnle hzero hf hfitL
      (by simp [bumpOp, hmoves]) (by simp [bumpOp, hslides]) (by simp [bumpOp, hpeak])
      hpeg hfitM hfitS
  rw [hsetL, ok_bind]
  rw [settle_bump_comm b 1 cOps hops src hH hD xs n moves slides peak]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7
    · rw [show bS = settleBoard b src hH hD xs n moves slides peak from rfl,
        settle_peak b src hH hD xs n moves slides peak hpk]
    · rw [show bS = settleBoard b src hH hD xs n moves slides peak from rfl,
        settle_keep b src hH hD xs n moves slides peak hpk]
  let bR : Ecbs.Board :=
    { bS with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { bS.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hopsS⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    rhs
    zeta
    pattern (Ecbs.settle _)
    change Ecbs.settle bR
  have hbR : bR = bumpOp bS 1 cOps hopsS := by
    apply board_ext
    case hmon => simp [bR, bumpOp, hmkS]
    all_goals simp [bR, bumpOp]
  rw [hbR]
  rw [settle_off (bumpOp bS 1 cOps hopsS) (by simp [bumpOp, hoffS]), ok_bind]

/-- `Ecbs.cube` on a live bench: slide into `src`, then the bench-off cube.
    The op-count bump is the one inside `cubeOffBoard`, applied to the slid board. -/
def cubeLiveBoard (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size)
    (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) : Ecbs.Board :=
  let bS := settleBoard b src hH hD xs n moves slides peak
  let ys := xs.take n
  let mv := moves + 2 * pegCount ys
  let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)
  cubeOffBoard bS dst src ys n k mv hole bench pk peakS cOps
    (settle_ops_lt b 1 src hops hH hD xs n moves slides peak)
    (settle_held_lt b src hH hD xs n moves slides peak)
    (settle_home_lt b src hH hD xs n moves slides peak)

/-- Bench on and aimed at `src`, with a zero tail. `Ecbs.cube` returns `cubeLiveBoard`. -/
theorem cube_eq_live (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (src : Int))
    (hH : src < b.sudo_5Board_4home.size)
    (hD : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[src] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hn0 : 0 < n)
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hxsT : allTritList (xs.take n))
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b (dst : Int) (src : Int) =
      .ok (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops) := by
  rw [cube_live_eq b dst src xs n moves slides peak cOps hmk hon hto hH hD h7 hempty hbench
      hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops]
  let bS := settleBoard b src hH hD xs n moves slides peak
  let ys := xs.take n
  let mv := moves + 2 * pegCount ys
  let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)
  let hFs := settle_held_lt b src hH hD xs n moves slides peak
  have hHomes := settle_home_lt b src hH hD xs n moves slides peak
  have hleny : ys.length = n := by
    simp [ys, List.length_take, Nat.min_eq_left hnle]
  have htS := settle_tier_eq b src hH hD xs n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    rw [settle_marker_eq b src hH hD xs n moves slides peak]; exact hmk
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b src hH hD xs n moves slides peak
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 src hops hH hD xs n moves slides peak
  have hop1S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    exact (array_get_congr (settle_ops b src hH hD xs n moves slides peak) 1 hopsS).trans hop1
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b src hH hD xs n moves slides peak, Array.size_set]; exact h7
  have hHF : bS.sudo_5Board_4held[src]'hFs = true := by
    have hset : bS.sudo_5Board_4held =
        b.sudo_5Board_4held.set ⟨src, hD⟩ true :=
      settle_held_eq b src hH hD xs n moves slides peak
    have hFsB : src < bS.sudo_5Board_4held.size := hFs
    rw [show bS.sudo_5Board_4held[src] =
        (b.sudo_5Board_4held.set ⟨src, hD⟩ true)[src]'(hset ▸ hFsB) from
      array_get_congr hset src hFsB]
    simp [Array.getElem_set]
  have hArr : bS.sudo_5Board_4home[src]'hHomes = embed ys := by
    have hset : bS.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨src, hH⟩ (embed (xs.take n)) :=
      settle_home_eq b src hH hD xs n moves slides peak
    have hHomeB : src < bS.sudo_5Board_4home.size := hHomes
    rw [show bS.sudo_5Board_4home[src] =
        (b.sudo_5Board_4home.set ⟨src, hH⟩ (embed (xs.take n)))[src]'(hset ▸ hHomeB) from
      array_get_congr hset src hHomeB]
    simp [ys, Array.getElem_set]
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [settle_moves_eq b src hH hD xs n moves slides peak]
    simp [mv, ys, ofNat_eq_natCast]
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [settle_peak_eq b src hH hD xs n moves slides peak hpeak]
    simp [pk, raisedPeak, ofNat_eq_natCast]
  have hstrict : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq b src hH hD xs n moves slides peak]; exact hpeakS
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [htS]; exact hbl
  have hcgS : bS.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by rw [htS]; exact hcg
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [htS]; exact hn
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htS]; exact hwF
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htS]; exact hhF
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htS]; exact hrF
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htS]; exact hkF
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b src hH hD xs n moves slides peak]; exact hHole
  rw [cube_off_eq bS dst src ys w h r n k mv hole bench pk peakS cOps cg
      hmkS hoffS hopsS hop1S hfops hblS hcgS hspan hFs hHomes hHF hArr h7S hn0 hnS hleny hf
      hmovS hpkS hstrict hxsT h3 hfm hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS hholeS
      hsm hnsm hfitB hfold]
  rfl

private theorem settle_row_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_3row =
      b.sudo_5Board_3row := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem cube_live_bench (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let ys := xs.take n
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_5bench =
      embed (laneFold n (n - k) (combStrip n bench ys)) := by
  simp [cubeLiveBoard, cube_off_bench]

theorem cube_live_prefix (n k bench : Nat) (xs : List Nat) :
    (laneFold n (n - k) (combStrip n bench (xs.take n))).take n =
      fieldCube n k bench (xs.take n) :=
  cube_off_prefix n k bench (xs.take n)

theorem cube_live_home (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨src, hH⟩ #[] := by
  unfold cubeLiveBoard
  rw [cube_off_home]
  rw [set_on (settle_home_eq b src hH hD xs n moves slides peak) src
      (settle_home_lt b src hH hD xs n moves slides peak) (#[])]
  exact overwrite b.sudo_5Board_4home src hH (embed (xs.take n)) #[]
    (settle_home_eq b src hH hD xs n moves slides peak ▸
      settle_home_lt b src hH hD xs n moves slides peak)

theorem cube_live_held (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let hFs := settle_held_lt b src hH hD xs n moves slides peak
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4held =
      (settleBoard b src hH hD xs n moves slides peak).sudo_5Board_4held.set ⟨src, hFs⟩ false := by
  simp [cubeLiveBoard, cube_off_held]

theorem cube_live_moves (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let ys := xs.take n
    let mv := moves + 2 * pegCount ys
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves mv ys n k bench) := by
  simp [cubeLiveBoard, cube_off_moves]

theorem cube_live_slides (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let ys := xs.take n
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount ys) := by
  unfold cubeLiveBoard
  rw [cube_off_slides, settle_slides_eq]

theorem cube_live_peak (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let bS := settleBoard b src hH hD xs n moves slides peak
    let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)
    let hFs := settle_held_lt b src hH hD xs n moves slides peak
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pk (countHeld (bS.sudo_5Board_4held.set ⟨src, hFs⟩ false) 7)) := by
  simp [cubeLiveBoard, cube_off_peak]

theorem cube_live_tally (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 := by
  unfold cubeLiveBoard
  rw [cube_off_tally, settle_tally_eq]

theorem cube_live_highest (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold cubeLiveBoard
  rw [cube_off_highest, settle_high_eq]

theorem cube_live_row (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_3row =
      b.sudo_5Board_3row := by
  unfold cubeLiveBoard
  rw [cube_off_row, settle_row_eq]

theorem cube_live_tier (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold cubeLiveBoard
  rw [cube_off_tier, settle_tier_eq]

theorem cube_live_ctrl (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold cubeLiveBoard
  rw [cube_off_ctrl, settle_ctrl_eq]

theorem cube_live_marker (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9marker_on =
      false := by
  simp [cubeLiveBoard, cube_off_marker]

theorem cube_live_on (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_on =
      true := by
  simp [cubeLiveBoard, cube_off_on]

theorem cube_live_to (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_to =
      (dst : Int) := by
  simp [cubeLiveBoard, cube_off_to]

theorem cube_live_high (xs : List Nat) (n k bench : Nat) (hn0 : 0 < n) (hgap0 : 0 < n - k) :
    ∀ i, n ≤ i → i < bench →
      coeff (laneFold n (n - k) (combStrip n bench (xs.take n))) i = 0 :=
  cube_off_high (xs.take n) n k bench hn0 hgap0

end EcbsLink2.Link2
