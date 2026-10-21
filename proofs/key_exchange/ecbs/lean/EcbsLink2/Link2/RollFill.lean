/-
  `roll_key` fills cells from the face stream. One die is `readFace` then
  `writePair`. The dice loop is `Spec.fill`. The attempt loop is `Spec.rollKey`.
  A face outside `0 .. 9` is assert 1216. The roll does not invert.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.RollScan
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem writePair_len (cells : Nat) (acc : List Nat) (pair face : Nat) :
    (writePair cells acc pair face).length = acc.length := by
  unfold writePair
  split <;> simp [List.length_set]

private theorem pair_lt_cells (cells pair : Nat) (h : pair < (cells + 1) / 2) :
    2 * pair < cells := by
  have hmul : 2 * pair < 2 * ((cells + 1) / 2) :=
    Nat.mul_lt_mul_of_pos_left h (by decide)
  have hlt : 2 * pair < cells + 1 :=
    Nat.lt_of_lt_of_le hmul (Nat.mul_div_le (cells + 1) 2)
  have hle : 2 * pair ≤ cells := Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hlt)
  cases Nat.eq_or_lt_of_le hle with
  | inr hlt' => exact hlt'
  | inl heq =>
    have hhalf : (2 * pair + 1) / 2 = pair := by
      have he : 2 * pair + 1 = 1 + 2 * pair := by omega
      rw [he, Nat.add_mul_div_left 1 pair (by decide),
        Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]
    have : pair < pair := by
      have h' : pair < (2 * pair + 1) / 2 := by rw [heq]; exact h
      rw [hhalf] at h'
      exact h'
    exact absurd this (Nat.lt_irrefl _)

private theorem filled_zero (n : Nat) :
    SudoRt.filledL (Int.ofNat n) (0 : Int) = .ok (embed (List.replicate n 0)) := by
  rw [filledL_ofNat]
  congr 1
  apply Array.ext
  · simp [embed, Array.size_mkArray, List.length_replicate, size_embed]
  · intro i h1 h2
    simp [embed, Array.getElem_mkArray, Array.getElem_mk, List.getElem_map,
      List.getElem_replicate]

/-- The scan when the index is already past the stream. -/
theorem face_lay_ge (faces : List Nat) (cells : Nat) (acc : List Nat)
    (pair i : Nat) (hi : faces.length ≤ i) (hfit : FitsLen faces.length) :
    (do
        let toV ← SudoRt.subI (Int.ofNat faces.length) (1 : Int)
        let fuel := if Int.ofNat i > toV then 1 else (toV - Int.ofNat i).natAbs + 1
        let r ← SudoRt.runLoopOn (Int.ofNat i, ((0 : Int), Int.ofNat i)) fuel
          (faceStep (embed faces) toV) (faceLayAfter cells acc pair)
          (fun r => pure (SudoRt.Flow.ret r))
        pure r) =
      .ok (SudoRt.Flow.ret (none : Option Rolled)) := by
  simp only [bind_pure]
  cases hL : faces.length with
  | zero =>
    rw [show Int.ofNat 0 = (0 : Int) by rfl, subI_zero_one, ok_bind]
    have hgt : Int.ofNat i > (-1 : Int) := by
      have hz : (0 : Int) ≤ Int.ofNat i := Int.ofNat_zero_le i
      omega
    have hstep :
        faceStep (embed faces) (-1) (Int.ofNat i, ((0 : Int), Int.ofNat i)) =
          .ok (SudoRt.Flow.brk (Int.ofNat i, ((0 : Int), Int.ofNat i))) := by
      unfold faceStep
      conv => lhs; zeta
      rw [if_pos hgt, pure_eq_ok]
    rw [fuelRange_eq]
    rw [asc_break (Int.ofNat i) (-1) ((0 : Int), Int.ofNat i)
      (faceStep (embed faces) (-1)) (faceLayAfter cells acc pair)
      (fun r => pure (SudoRt.Flow.ret r)) hgt hstep]
    unfold faceLayAfter
    conv => lhs; zeta
    dsimp
    rw [sEq_int, decide_eq_true (by rfl : (0 : Int) = 0), if_pos rfl, pure_eq_ok]
  | succ n =>
    rw [hL] at hfit hi
    rw [subI_ofNat_one _ (Nat.succ_pos _) hfit, ok_bind]
    have hsub : n.succ - 1 = n := Nat.succ_sub_one n
    have hgt : Int.ofNat i > Int.ofNat n :=
      (Int.ofNat_lt).mpr (Nat.lt_of_succ_le hi)
    rw [hsub, fuelRange_eq]
    have hstep :
        faceStep (embed faces) (Int.ofNat n)
          (Int.ofNat i, ((0 : Int), Int.ofNat i)) =
          .ok (SudoRt.Flow.brk (Int.ofNat i, ((0 : Int), Int.ofNat i))) := by
      unfold faceStep
      conv => lhs; zeta
      rw [if_pos hgt, pure_eq_ok]
    rw [asc_break (Int.ofNat i) (Int.ofNat n) ((0 : Int), Int.ofNat i)
      (faceStep (embed faces) (Int.ofNat n)) (faceLayAfter cells acc pair)
      (fun r => pure (SudoRt.Flow.ret r)) hgt hstep]
    unfold faceLayAfter
    conv => lhs; zeta
    dsimp
    rw [sEq_int, decide_eq_true (by rfl : (0 : Int) = 0), if_pos rfl, pure_eq_ok]

private theorem embed_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (embed xs)[i]'(by rw [size_embed]; exact hi) = Int.ofNat (xs[i]) := by
  simp [embed, Array.getElem_mk, List.getElem_map]

private theorem allZero_iff (xs : List Nat) :
    allZero xs = true ↔ ∀ i (hi : i < xs.length), xs[i] = 0 := by
  rw [allZero, List.all_eq_true]
  constructor
  · intro h i hi
    exact (decide_eq_true_eq).mp (h _ (List.getElem_mem hi))
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := (List.mem_iff_getElem).mp ha
    exact decide_eq_true (h i hi)

private theorem is_empty_all (xs : List Nat) (hf : FitsLen xs.length) :
    Ecbs.is_empty (embed xs) = .ok (allZero xs) := by
  rw [is_empty_refines (embed xs) (by rw [size_embed]; exact hf)]
  congr 1
  by_cases h : ∀ i (hi : i < xs.length), xs[i] = 0
  · have ha : allZero xs = true := by simpa [allZero_iff] using h
    have hd : decide (∀ i (hi : i < (embed xs).size), (embed xs)[i] = 0) = true := by
      apply decide_eq_true
      intro i hi
      have hi0 : i < xs.length := by rw [size_embed] at hi; exact hi
      rw [embed_get xs i hi0, h i hi0]
      rfl
    rw [hd, ha]
  · have ha : allZero xs = false := by
      cases hA : allZero xs with
      | false => rfl
      | true => exact absurd ((allZero_iff xs).mp hA) h
    have hd : decide (∀ i (hi : i < (embed xs).size), (embed xs)[i] = 0) = false := by
      apply decide_eq_false
      intro hall
      apply h
      intro i hi
      have hg := hall i (by rw [size_embed]; exact hi)
      rw [embed_get xs i hi] at hg
      exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using hg)
    rw [hd, ha]

/-- `is_empty` after a filled list: a zero list continues, any other list
    returns the roll. -/
private theorem empty_after (attempt : Nat) (cs : List Nat) (n : Nat)
    (hf : FitsLen cs.length) :
    (do
        let e ← Ecbs.is_empty (embed cs)
        if !e then
          pure (SudoRt.Flow.ret (some {
            sudo_6Rolled_5cells := embed cs
            sudo_6Rolled_4used := Int.ofNat n
            sudo_6Rolled_5rolls := Int.ofNat attempt } : Option Rolled))
        else
          pure (SudoRt.Flow.cont (Int.ofNat n))) =
      if allZero cs then .ok (SudoRt.Flow.cont (Int.ofNat n))
      else .ok (SudoRt.Flow.ret (some {
        sudo_6Rolled_5cells := embed cs
        sudo_6Rolled_4used := Int.ofNat n
        sudo_6Rolled_5rolls := Int.ofNat attempt })) := by
  rw [is_empty_all cs hf, ok_bind]
  by_cases hz : allZero cs = true
  · rw [hz, Bool.not_true, if_neg (by decide : ¬ ((false : Bool) = true)), pure_eq_ok]
    simp [hz]
  · have hfse : allZero cs = false := by
      cases h : allZero cs with
      | false => rfl
      | true => exact absurd h hz
    rw [hfse, Bool.not_false, if_pos rfl, pure_eq_ok]
    simp [hfse]

/-- What one attempt's pair loop returns: `none` leaves the roll, an all-zero
    filling continues, anything else is the rolled key. -/
private def filledEnd (attempt : Nat) (got : Option (List Nat × Nat)) :
    Except SudoRt.Trap (SudoRt.Flow Int (Option Rolled)) :=
  match got with
  | none => .ok (SudoRt.Flow.ret none)
  | some (cs, n) =>
    if allZero cs then .ok (SudoRt.Flow.cont (Int.ofNat n))
    else .ok (SudoRt.Flow.ret (some {
      sudo_6Rolled_5cells := embed cs
      sudo_6Rolled_4used := Int.ofNat n
      sudo_6Rolled_5rolls := Int.ofNat attempt }))

/-- Lay into the array the loop is holding. At `embed acc` this is `faceLayAfter`. -/
private def dieAfter (cells : Nat) (arr0 : Array Int) (pair : Int)
    (σ : Int × (Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Option Rolled)) := do
  let face := σ.2.1
  let next := σ.2.2
  if SudoRt.SEq.beq face (0 : Int) then
    pure (SudoRt.Flow.ret (none : Option Rolled))
  else
    let arr ← (do
      let ix ← SudoRt.mulI (Int.ofNat 2) pair
      let d ← Ecbs.keypad_first face
      let acc ← SudoRt.putL arr0 ix d
      let j ← SudoRt.addI ix (1 : Int)
      if decide (j < Int.ofNat cells) then
        let d2 ← Ecbs.keypad_second face
        SudoRt.putL acc j d2
      else
        pure acc)
    pure (SudoRt.Flow.cont (next, arr))

private theorem dieAfter_eq (cells : Nat) (acc : List Nat) (pair : Nat) :
    dieAfter cells (embed acc) (Int.ofNat pair) = faceLayAfter cells acc pair := by
  funext σ
  unfold dieAfter faceLayAfter
  rfl

/-- The face scan whose after writes one die. -/
private def dieGo (faces : List Nat) (cells : Nat) (arr : Array Int)
    (pair next : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Option Rolled)) := do
  let toV ← SudoRt.subI (Int.ofNat faces.length) (1 : Int)
  let fuel := if next > toV then 1 else (toV - next).natAbs + 1
  let r ← SudoRt.runLoopOn (next, ((0 : Int), next)) fuel
    (faceStep (embed faces) toV) (dieAfter cells arr pair)
    (fun r => pure (SudoRt.Flow.ret r))
  pure r

private theorem dieGo_ge
    (faces : List Nat) (cells : Nat) (acc : List Nat) (pair next : Nat)
    (hi : faces.length ≤ next) (hfit : FitsLen faces.length) :
    dieGo faces cells (embed acc) (Int.ofNat pair) (Int.ofNat next) =
      .ok (SudoRt.Flow.ret (none : Option Rolled)) := by
  unfold dieGo
  rw [dieAfter_eq cells acc pair]
  exact face_lay_ge faces cells acc pair next hi hfit

private theorem dieGo_face
    (faces : List Nat) (cells : Nat) (acc : List Nat) (pair next : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hlen : acc.length = cells) (hix : 2 * pair < cells)
    (hfit2 : FitsLen (2 * pair + 1)) (hfit : FitsLen faces.length)
    (hi : next < faces.length) :
    dieGo faces cells (embed acc) (Int.ofNat pair) (Int.ofNat next) =
      match readFace faces next with
      | none => .ok (SudoRt.Flow.ret (none : Option Rolled))
      | some (f, n) =>
        .ok (SudoRt.Flow.cont (Int.ofNat n, embed (writePair cells acc pair f))) := by
  unfold dieGo
  rw [dieAfter_eq cells acc pair]
  exact face_lay faces cells acc pair next h9 hlen hix hfit2 hfit hi

/-- One pair: past the end, break; otherwise scan and either return `none`
    or step the pair index. -/
private def pairBody (faces : List Nat) (cells : Nat) (toV : Int)
    (σ : Int × (Int × Array Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Int × Array Int)) (Option Rolled)) := do
  let pair := σ.1
  let next := σ.2.1
  let arr := σ.2.2
  if pair > toV then
    pure (SudoRt.Flow.brk (pair, (next, arr)))
  else
    match ← dieGo faces cells arr pair next with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (pair, fs))
    | .cont fs => do
        if pair == toV then
          pure (SudoRt.Flow.brk (pair, fs))
        else
          let i' ← SudoRt.addI pair 1
          pure (SudoRt.Flow.cont (i', fs))

/-- After every pair: an empty filling continues, any other returns the roll. -/
private def pairAfter (attempt : Nat) (σ : Int × (Int × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow Int (Option Rolled)) := do
  let next := σ.2.1
  let cells := σ.2.2
  let e ← Ecbs.is_empty cells
  if !e then
    pure (SudoRt.Flow.ret (some {
      sudo_6Rolled_5cells := cells
      sudo_6Rolled_4used := next
      sudo_6Rolled_5rolls := Int.ofNat attempt }))
  else
    pure (SudoRt.Flow.cont next)

private theorem pairAfter_some (attempt n : Nat) (cs : List Nat)
    (hf : FitsLen cs.length) (pair : Nat) :
    pairAfter attempt (Int.ofNat pair, (Int.ofNat n, embed cs)) =
      filledEnd attempt (some (cs, n)) := by
  unfold pairAfter
  conv => lhs; zeta
  rw [empty_after attempt cs n hf]
  dsimp [filledEnd]

private theorem fill_stop (faces : List Nat) (cells next pair : Nat)
    (acc : List Nat) (h : (cells + 1) / 2 ≤ pair) :
    fill cells faces next pair acc = some (acc, next) := by
  conv => lhs; unfold fill
  rw [if_pos h]

private theorem fill_none (faces : List Nat) (cells next pair : Nat)
    (acc : List Nat) (h : pair < (cells + 1) / 2)
    (hread : readFace faces next = none) :
    fill cells faces next pair acc = none := by
  conv => lhs; unfold fill
  rw [if_neg (by omega : ¬ pair ≥ (cells + 1) / 2), hread]

private theorem fill_step (faces : List Nat) (cells next pair f n : Nat)
    (acc : List Nat) (h : pair < (cells + 1) / 2)
    (hread : readFace faces next = some (f, n)) :
    fill cells faces next pair acc =
      fill cells faces n (pair + 1) (writePair cells acc pair f) := by
  conv => lhs; unfold fill
  rw [if_neg (by omega : ¬ pair ≥ (cells + 1) / 2), hread]

private theorem pair_step_at
    (faces : List Nat) (cells toN pair next : Nat) (acc : List Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hlen : acc.length = cells) (hfitF : FitsLen faces.length)
    (hfitC : FitsLen (cells + 1))
    (hpair : pair < (cells + 1) / 2) (hle : pair ≤ toN) :
    pairBody faces cells (Int.ofNat toN)
        (Int.ofNat pair, (Int.ofNat next, embed acc)) =
      match readFace faces next with
      | none => .ok (SudoRt.Flow.ret (none : Option Rolled))
      | some (f, n) =>
        if pair = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat pair,
            (Int.ofNat n, embed (writePair cells acc pair f))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (pair + 1),
            (Int.ofNat n, embed (writePair cells acc pair f)))) := by
  unfold pairBody
  conv => lhs; zeta
  have hng : ¬ Int.ofNat pair > Int.ofNat toN := by
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    omega
  rw [if_neg hng]
  by_cases hi : next < faces.length
  · have hix : 2 * pair < cells := pair_lt_cells cells pair hpair
    have hfit2 : FitsLen (2 * pair + 1) := FitsLen.of_le hfitC (by omega)
    have hdie := dieGo_face faces cells acc pair next h9 hlen hix hfit2 hfitF hi
    rw [hdie]
    cases hread : readFace faces next with
    | none =>
      dsimp
      rw [pure_eq_ok]
    | some fn =>
      rcases fn with ⟨f, n⟩
      dsimp
      rw [show (pair : Int) = Int.ofNat pair from rfl,
        show (toN : Int) = Int.ofNat toN from rfl,
        show (n : Int) = Int.ofNat n from rfl]
      have hfitP : FitsLen (pair + 1) := FitsLen.of_le hfitC (by omega)
      by_cases hlast : pair = toN
      · have hbeq : (Int.ofNat pair == Int.ofNat toN) = true := by
          subst hlast
          simp [beq_int_iff]
        rw [if_pos hbeq, pure_eq_ok, if_pos hlast]
      · have hne : Int.ofNat pair ≠ Int.ofNat toN :=
          fun h => hlast (Int.ofNat.inj h)
        have hbeq : (Int.ofNat pair == Int.ofNat toN) = false := by
          cases hb : (Int.ofNat pair == Int.ofNat toN) with
          | false => rfl
          | true => exact absurd ((beq_int_iff _ _).mp hb) hne
        rw [if_neg (by rw [hbeq]; decide : ¬ ((Int.ofNat pair == Int.ofNat toN) = true))]
        rw [addI_ofNat_one pair hfitP, ok_bind, pure_eq_ok, if_neg hlast]
        rfl
  · rw [dieGo_ge faces cells acc pair next (Nat.le_of_not_lt hi) hfitF, ok_bind]
    dsimp
    rw [pure_eq_ok, readFace_ge (Nat.le_of_not_lt hi)]

/-- Pairs from `pair` through `(cells + 1) / 2 - 1`, starting from a list of
    length `cells`. `toN + 1` is that half. -/
private theorem fill_loop_at
    (faces : List Nat) (cells attempt toN pair next : Nat) (acc : List Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hlen : acc.length = cells) (hfitF : FitsLen faces.length)
    (hfitC : FitsLen (cells + 1))
    (hhalf : (cells + 1) / 2 = toN + 1) :
    SudoRt.runLoopOn (Int.ofNat pair, (Int.ofNat next, embed acc))
        (fuelRange (Int.ofNat pair) (Int.ofNat toN))
        (pairBody faces cells (Int.ofNat toN)) (pairAfter attempt)
        (fun r => pure (SudoRt.Flow.ret r)) =
      filledEnd attempt (fill cells faces next pair acc) := by
  obtain ⟨k, hk⟩ : ∃ k, toN + 1 - pair = k := ⟨toN + 1 - pair, rfl⟩
  induction k generalizing pair next acc hlen with
  | zero =>
    have hge : toN + 1 ≤ pair := Nat.le_of_sub_eq_zero hk
    have hgt : Int.ofNat pair > Int.ofNat toN :=
      (Int.ofNat_lt).mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self toN) hge)
    have hstep :
        pairBody faces cells (Int.ofNat toN)
          (Int.ofNat pair, (Int.ofNat next, embed acc)) =
          .ok (SudoRt.Flow.brk (Int.ofNat pair, (Int.ofNat next, embed acc))) := by
      unfold pairBody
      conv => lhs; zeta
      rw [if_pos hgt, pure_eq_ok]
    rw [asc_break (Int.ofNat pair) (Int.ofNat toN) (Int.ofNat next, embed acc)
      (pairBody faces cells (Int.ofNat toN)) (pairAfter attempt)
      (fun r => pure (SudoRt.Flow.ret r)) hgt hstep]
    have hf : FitsLen acc.length := by
      rw [hlen]
      exact FitsLen.of_le hfitC (Nat.le_succ _)
    rw [pairAfter_some attempt next acc hf pair,
      fill_stop faces cells next pair acc (by rw [hhalf]; exact hge)]
  | succ k ih =>
    have hlt : pair < toN + 1 := by
      apply Nat.lt_of_not_le
      intro hle
      have hz : toN + 1 - pair = 0 := Nat.sub_eq_zero_of_le hle
      rw [hk] at hz
      exact Nat.succ_ne_zero k hz
    have hle : pair ≤ toN := Nat.le_of_lt_succ hlt
    have hpair : pair < (cells + 1) / 2 := by rw [hhalf]; exact hlt
    have hstep := pair_step_at faces cells toN pair next acc h9 hlen hfitF hfitC
      hpair hle
    rw [fuelRange_le hle, runLoopOn_succ, hstep]
    cases hread : readFace faces next with
    | none =>
      dsimp
      rw [pure_eq_ok, fill_none faces cells next pair acc hpair hread]
      unfold filledEnd
      rfl
    | some fn =>
      rcases fn with ⟨f, n⟩
      dsimp
      by_cases hlast : pair = toN
      · rw [if_pos hlast]
        dsimp
        have hlen' : (writePair cells acc pair f).length = cells := by
          rw [writePair_len, hlen]
        have hf : FitsLen (writePair cells acc pair f).length := by
          rw [hlen']
          exact FitsLen.of_le hfitC (Nat.le_succ _)
        have hdone : (cells + 1) / 2 ≤ pair + 1 := by
          rw [hhalf, hlast]
          exact Nat.le_refl _
        rw [show (pair : Int) = Int.ofNat pair from rfl,
          show (n : Int) = Int.ofNat n from rfl,
          pairAfter_some attempt n (writePair cells acc pair f) hf pair,
          fill_step faces cells next pair f n acc hpair hread,
          fill_stop faces cells n (pair + 1) (writePair cells acc pair f) hdone]
      · rw [if_neg hlast]
        dsimp
        have hle1 : pair + 1 ≤ toN :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hle hlast)
        have hrest : toN - pair =
            fuelRange (Int.ofNat (pair + 1)) (Int.ofNat toN) := by
          rw [fuelRange_le hle1]
          omega
        rw [hrest, fill_step faces cells next pair f n acc hpair hread]
        exact ih (pair + 1) n (writePair cells acc pair f)
          (by rw [writePair_len, hlen]) (by omega)

/-- The pair loop is `Spec.fill`, then the empty check. A face outside `0 .. 9`
    is assert 1216, outside this statement. No inversion. -/
private theorem fill_from
    (faces : List Nat) (cells attempt next pair : Nat) (acc : List Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hlen : acc.length = cells) (hfitF : FitsLen faces.length)
    (hfitC : FitsLen (cells + 1)) :
    (do
        let sum ← SudoRt.addI (Int.ofNat cells) (1 : Int)
        let half ← SudoRt.divI sum (2 : Int)
        let toV ← SudoRt.subI half (1 : Int)
        let fuel :=
          if Int.ofNat pair > toV then 1 else (toV - Int.ofNat pair).natAbs + 1
        let r ← SudoRt.runLoopOn (Int.ofNat pair, (Int.ofNat next, embed acc)) fuel
          (pairBody faces cells toV) (pairAfter attempt)
          (fun r => pure (SudoRt.Flow.ret r))
        pure r) =
      filledEnd attempt (fill cells faces next pair acc) := by
  simp only [bind_pure]
  rw [addI_ofNat_one cells hfitC, ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl,
    divI_ofNat (cells + 1) (by decide), ok_bind]
  cases hhalf : (cells + 1) / 2 with
  | zero =>
    rw [show Int.ofNat 0 = (0 : Int) by rfl, subI_zero_one, ok_bind]
    have hgt : Int.ofNat pair > (-1 : Int) := by
      have hz : (0 : Int) ≤ Int.ofNat pair := Int.ofNat_zero_le pair
      omega
    have hstep :
        pairBody faces cells (-1)
          (Int.ofNat pair, (Int.ofNat next, embed acc)) =
          .ok (SudoRt.Flow.brk (Int.ofNat pair, (Int.ofNat next, embed acc))) := by
      unfold pairBody
      conv => lhs; zeta
      rw [if_pos hgt, pure_eq_ok]
    rw [fuelRange_eq]
    rw [asc_break (Int.ofNat pair) (-1) (Int.ofNat next, embed acc)
      (pairBody faces cells (-1)) (pairAfter attempt)
      (fun r => pure (SudoRt.Flow.ret r)) hgt hstep]
    have hf : FitsLen acc.length := by
      rw [hlen]
      exact FitsLen.of_le hfitC (Nat.le_succ _)
    rw [pairAfter_some attempt next acc hf pair,
      fill_stop faces cells next pair acc (by rw [hhalf]; omega)]
  | succ toN =>
    have hfitH : FitsLen (toN + 1) := by
      rw [← hhalf]
      exact FitsLen.of_le hfitC (Nat.div_le_self _ _)
    rw [subI_ofNat_one (toN + 1) (Nat.succ_pos _) hfitH, ok_bind]
    have hsub : toN + 1 - 1 = toN := Nat.succ_sub_one toN
    rw [hsub, fuelRange_eq]
    exact fill_loop_at faces cells attempt toN pair next acc h9 hlen hfitF hfitC hhalf

end EcbsLink2.Link2
