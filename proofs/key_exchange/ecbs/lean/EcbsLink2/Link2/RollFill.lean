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
private def pairAfter (rolls : Int) (σ : Int × (Int × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow Int (Option Rolled)) := do
  let next := σ.2.1
  let cells := σ.2.2
  let e ← Ecbs.is_empty cells
  if !e then
    pure (SudoRt.Flow.ret (some {
      sudo_6Rolled_5cells := cells
      sudo_6Rolled_4used := next
      sudo_6Rolled_5rolls := rolls }))
  else
    pure (SudoRt.Flow.cont next)

private theorem pairAfter_some (attempt n : Nat) (cs : List Nat)
    (hf : FitsLen cs.length) (pair : Nat) :
    pairAfter (Int.ofNat attempt) (Int.ofNat pair, (Int.ofNat n, embed cs)) =
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
        (pairBody faces cells (Int.ofNat toN)) (pairAfter (Int.ofNat attempt))
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
      (pairBody faces cells (Int.ofNat toN)) (pairAfter (Int.ofNat attempt))
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
        rw [show (attempt : Int) = Int.ofNat attempt from rfl,
          show (pair : Int) = Int.ofNat pair from rfl,
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
          (pairBody faces cells toV) (pairAfter (Int.ofNat attempt))
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
      (pairBody faces cells (-1)) (pairAfter (Int.ofNat attempt))
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

private def rolledOf (got : Option (List Nat × Nat × Nat)) : Option Rolled :=
  match got with
  | none => none
  | some (cs, used, rolls) => some {
      sudo_6Rolled_5cells := embed cs
      sudo_6Rolled_4used := Int.ofNat used
      sudo_6Rolled_5rolls := Int.ofNat rolls }

private theorem rollGo_stop (cells : Nat) (faces : List Nat) (attempt next : Nat)
    (h : attempt > faces.length + 1) :
    rollGo cells faces attempt next = none := by
  conv => lhs; unfold rollGo
  rw [if_pos h]

private theorem rollGo_none (cells : Nat) (faces : List Nat) (attempt next : Nat)
    (h : ¬ attempt > faces.length + 1)
    (hf : fill cells faces next 0 (List.replicate cells 0) = none) :
    rollGo cells faces attempt next = none := by
  conv => lhs; unfold rollGo
  rw [if_neg h, hf]

private theorem rollGo_live (cells : Nat) (faces : List Nat)
    (attempt next : Nat) (cs : List Nat) (n : Nat)
    (h : ¬ attempt > faces.length + 1)
    (hf : fill cells faces next 0 (List.replicate cells 0) = some (cs, n))
    (hz : allZero cs = false) :
    rollGo cells faces attempt next = some (cs, n, attempt) := by
  conv => lhs; unfold rollGo
  rw [if_neg h, hf]
  dsimp
  rw [if_neg (by rw [hz]; decide : ¬ (allZero cs = true))]

private theorem rollGo_again (cells : Nat) (faces : List Nat)
    (attempt next : Nat) (cs : List Nat) (n : Nat)
    (h : ¬ attempt > faces.length + 1)
    (hf : fill cells faces next 0 (List.replicate cells 0) = some (cs, n))
    (hz : allZero cs = true) :
    rollGo cells faces attempt next = rollGo cells faces (attempt + 1) n := by
  conv => lhs; unfold rollGo
  rw [if_neg h, hf]
  dsimp
  rw [if_pos hz]

/-- One attempt: a fresh row of zeros, then the pair loop. -/
private def attemptBody (faces : List Nat) (cells : Nat) (toV : Int)
    (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Option Rolled)) := do
  let attempt := σ.1
  let next := σ.2
  if attempt > toV then
    pure (SudoRt.Flow.brk (attempt, next))
  else
    match ← (do
      let arr ← SudoRt.filledL (Int.ofNat cells) (0 : Int)
      let sum ← SudoRt.addI (Int.ofNat cells) (1 : Int)
      let half ← SudoRt.divI sum (2 : Int)
      let toP ← SudoRt.subI half (1 : Int)
      let fuel :=
        if Int.ofNat 0 > toP then 1 else (toP - Int.ofNat 0).natAbs + 1
      let r ← SudoRt.runLoopOn (Int.ofNat 0, (next, arr)) fuel
        (pairBody faces cells toP) (pairAfter attempt)
        (fun r => pure (SudoRt.Flow.ret r))
      pure r) with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (attempt, fs))
    | .cont fs => do
        if attempt == toV then
          pure (SudoRt.Flow.brk (attempt, fs))
        else
          let i' ← SudoRt.addI attempt 1
          pure (SudoRt.Flow.cont (i', fs))

private theorem attempt_step_at
    (faces : List Nat) (cells lim attempt next : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hfitF : FitsLen faces.length) (hfitC : FitsLen (cells + 1))
    (hfitL : FitsLen (faces.length + 1)) (hle : attempt ≤ lim)
    (hlim : faces.length + 1 = lim) :
    attemptBody faces cells (Int.ofNat lim) (Int.ofNat attempt, Int.ofNat next) =
      match fill cells faces next 0 (List.replicate cells 0) with
      | none => .ok (SudoRt.Flow.ret (none : Option Rolled))
      | some (cs, n) =>
        if allZero cs then
          if attempt = lim then
            .ok (SudoRt.Flow.brk (Int.ofNat attempt, Int.ofNat n))
          else
            .ok (SudoRt.Flow.cont (Int.ofNat (attempt + 1), Int.ofNat n))
        else
          .ok (SudoRt.Flow.ret (some {
            sudo_6Rolled_5cells := embed cs
            sudo_6Rolled_4used := Int.ofNat n
            sudo_6Rolled_5rolls := Int.ofNat attempt })) := by
  unfold attemptBody
  conv => lhs; zeta
  have hng : ¬ Int.ofNat attempt > Int.ofNat lim := by
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    omega
  rw [if_neg hng, filled_zero, ok_bind]
  have hlen : (List.replicate cells 0).length = cells := List.length_replicate _ _
  rw [fill_from faces cells attempt next 0 (List.replicate cells 0) h9 hlen hfitF hfitC]
  cases hfill : fill cells faces next 0 (List.replicate cells 0) with
  | none =>
    dsimp [filledEnd]
    rw [pure_eq_ok]
  | some csn =>
    rcases csn with ⟨cs, n⟩
    dsimp [filledEnd]
    by_cases hz : allZero cs = true
    · rw [if_pos hz]
      dsimp
      rw [show (attempt : Int) = Int.ofNat attempt from rfl,
        show (lim : Int) = Int.ofNat lim from rfl,
        show (n : Int) = Int.ofNat n from rfl]
      by_cases hlast : attempt = lim
      · have hbeq : (Int.ofNat attempt == Int.ofNat lim) = true := by
          subst hlast
          simp [beq_int_iff]
        rw [if_pos hbeq, pure_eq_ok, if_pos hlast, hz, if_pos rfl]
      · have hfitA : FitsLen (attempt + 1) := by
          have hlt : attempt < lim := Nat.lt_of_le_of_ne hle hlast
          rw [← hlim] at hlt
          exact FitsLen.of_le hfitL (Nat.succ_le_of_lt hlt)
        have hne : Int.ofNat attempt ≠ Int.ofNat lim :=
          fun h => hlast (Int.ofNat.inj h)
        have hbeq : (Int.ofNat attempt == Int.ofNat lim) = false := by
          cases hb : (Int.ofNat attempt == Int.ofNat lim) with
          | false => rfl
          | true => exact absurd ((beq_int_iff _ _).mp hb) hne
        rw [if_neg (by rw [hbeq]; decide :
          ¬ ((Int.ofNat attempt == Int.ofNat lim) = true))]
        rw [addI_ofNat_one attempt hfitA, ok_bind, pure_eq_ok, if_neg hlast, hz]
        rfl
    · have hzf : allZero cs = false := by
        cases h : allZero cs with
        | false => rfl
        | true => exact absurd h hz
      rw [if_neg (by rw [hzf]; decide : ¬ (allZero cs = true))]
      dsimp
      rw [pure_eq_ok, hzf, if_neg (by decide : ¬ ((false : Bool) = true))]

/-- Attempts `attempt .. faces.length + 1`. `lim` is `faces.length + 1`. -/
private theorem roll_loop_at
    (faces : List Nat) (cells lim attempt next : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hfitF : FitsLen faces.length) (hfitC : FitsLen (cells + 1))
    (hfitL : FitsLen (faces.length + 1))
    (hlim : faces.length + 1 = lim) :
    SudoRt.runLoopOn (Int.ofNat attempt, Int.ofNat next)
        (fuelRange (Int.ofNat attempt) (Int.ofNat lim))
        (attemptBody faces cells (Int.ofNat lim))
        (fun _ => pure (none : Option Rolled))
        (fun r => pure r) =
      .ok (rolledOf (rollGo cells faces attempt next)) := by
  obtain ⟨k, hk⟩ : ∃ k, lim + 1 - attempt = k := ⟨lim + 1 - attempt, rfl⟩
  induction k generalizing attempt next with
  | zero =>
    have hge : lim + 1 ≤ attempt := Nat.le_of_sub_eq_zero hk
    have hgt : Int.ofNat attempt > Int.ofNat lim :=
      (Int.ofNat_lt).mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self lim) hge)
    have hstep :
        attemptBody faces cells (Int.ofNat lim)
          (Int.ofNat attempt, Int.ofNat next) =
          .ok (SudoRt.Flow.brk (Int.ofNat attempt, Int.ofNat next)) := by
      unfold attemptBody
      conv => lhs; zeta
      rw [if_pos hgt, pure_eq_ok]
    rw [asc_break (Int.ofNat attempt) (Int.ofNat lim) (Int.ofNat next)
      (attemptBody faces cells (Int.ofNat lim))
      (fun _ => pure (none : Option Rolled)) (fun r => pure r) hgt hstep]
    rw [pure_eq_ok, rollGo_stop cells faces attempt next (by
      rw [hlim]
      omega)]
    unfold rolledOf
    rfl
  | succ k ih =>
    have hlt : attempt < lim + 1 := by
      apply Nat.lt_of_not_le
      intro hle
      have hz : lim + 1 - attempt = 0 := Nat.sub_eq_zero_of_le hle
      rw [hk] at hz
      exact Nat.succ_ne_zero k hz
    have hle : attempt ≤ lim := Nat.le_of_lt_succ hlt
    have hstep := attempt_step_at faces cells lim attempt next h9 hfitF hfitC
      hfitL hle hlim
    rw [fuelRange_le hle, runLoopOn_succ, hstep]
    cases hfill : fill cells faces next 0 (List.replicate cells 0) with
    | none =>
      dsimp
      rw [pure_eq_ok,
        rollGo_none cells faces attempt next (by rw [hlim]; omega) hfill]
      unfold rolledOf
      rfl
    | some csn =>
      rcases csn with ⟨cs, n⟩
      dsimp
      by_cases hz : allZero cs = true
      · rw [if_pos hz]
        by_cases hlast : attempt = lim
        · rw [if_pos hlast]
          dsimp
          rw [pure_eq_ok, rollGo_again cells faces attempt next cs n
            (by rw [hlim]; omega) hfill hz,
            rollGo_stop cells faces (attempt + 1) n (by rw [hlim, hlast]; omega)]
          unfold rolledOf
          rfl
        · rw [if_neg hlast]
          dsimp
          have hle1 : attempt + 1 ≤ lim :=
            Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hle hlast)
          have hrest : lim - attempt =
              fuelRange (Int.ofNat (attempt + 1)) (Int.ofNat lim) := by
            rw [fuelRange_le hle1]
            omega
          rw [hrest, rollGo_again cells faces attempt next cs n
            (by rw [hlim]; omega) hfill hz]
          exact ih (attempt + 1) n (by omega)
      · have hzf : allZero cs = false := by
          cases h : allZero cs with
          | false => rfl
          | true => exact absurd h hz
        rw [if_neg (by rw [hzf]; decide : ¬ (allZero cs = true))]
        dsimp
        rw [pure_eq_ok, rollGo_live cells faces attempt next cs n
          (by rw [hlim]; omega) hfill hzf]
        unfold rolledOf
        rfl

/-- The attempt loop is `Spec.rollKey`. No inversion. -/
private theorem roll_from
    (faces : List Nat) (cells : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hfitC : FitsLen (cells + 1)) (hfitL : FitsLen (faces.length + 1)) :
    (do
        let lim ← SudoRt.addI (SudoRt.listLen (embed faces)) (1 : Int)
        let fuel :=
          if Int.ofNat 1 > lim then 1 else (lim - Int.ofNat 1).natAbs + 1
        let r ← SudoRt.runLoopOn (Int.ofNat 1, Int.ofNat 0) fuel
          (attemptBody faces cells lim)
          (fun _ => pure (none : Option Rolled))
          (fun r => pure r)
        pure r) =
      .ok (rolledOf (rollKey cells faces)) := by
  simp only [bind_pure]
  rw [listLen_embed, addI_ofNat_one faces.length hfitL, ok_bind, fuelRange_eq]
  have hfitF : FitsLen faces.length := FitsLen.of_le hfitL (Nat.le_succ _)
  rw [roll_loop_at faces cells (faces.length + 1) 1 0 h9 hfitF hfitC hfitL rfl]
  rfl

/-- The emitted face step is `faceStep`. -/
private theorem faceStep_gen (faces : Array Int) (toV : Int) :
    faceStep faces toV = fun σ =>
      let f := σ.1
      let face := σ.2.1
      let _sp := σ.2.2
      let next := _sp
      (do
        if f > toV then
          pure (SudoRt.Flow.brk (ρ := Option Rolled) (f, (face, next)))
        else
          match ← ((do
            let _t1768 ← SudoRt.atL faces f
            let face := _t1768
            let _t1769 ← SudoRt.addI f (1 : Int)
            let next := _t1769
            let _t1771 ← (if decide (face ≥ (0 : Int)) then (do
              pure (decide (face ≤ (9 : Int)))) else pure false)
            let _as1773 ← SudoRt.sudoAssert _t1771 1216
            if !(SudoRt.SEq.beq face (0 : Int)) then
              do
                pure (SudoRt.Flow.brk (ρ := Option Rolled) (face, next))
            else
              do
                pure (SudoRt.Flow.cont (ρ := Option Rolled) (face, next))) :
              Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Option Rolled))) with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Option Rolled) r)
          | .brk _fs => pure (SudoRt.Flow.brk (ρ := Option Rolled) (f, _fs))
          | .cont _fs => do
              if f == toV then
                pure (SudoRt.Flow.brk (ρ := Option Rolled) (f, _fs))
              else do
                let i' ← SudoRt.addI f (1 : Int)
                pure (SudoRt.Flow.cont (ρ := Option Rolled) (i', _fs))) := by
  unfold faceStep faceBody
  funext σ
  rfl

/-- A second `mulI` of the same arguments is the first result, or the same trap. -/
private theorem mulI_skip {α : Type} (a b : Int) (f : Int → Except SudoRt.Trap α) :
    (SudoRt.mulI a b >>= fun _x => SudoRt.mulI a b >>= f) =
      (SudoRt.mulI a b >>= f) := by
  cases h : SudoRt.mulI a b with
  | error _ =>
    simp [error_bind]
  | ok _ =>
    simp [ok_bind]

/-- The emitted three-multiplication lay is the one multiplication in `dieAfter`. -/
private def genAfter (cellsI : Int) (arr0 : Array Int) (pair : Int)
    (σ : Int × (Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Option Rolled)) :=
  let face := σ.2.1
  let _sp1791 := σ.2.2
  let next := _sp1791
  do
    if SudoRt.SEq.beq face (0 : Int) then
      do
        pure (SudoRt.Flow.ret (ρ := Option Rolled) (none : Option Rolled))
    else
      do
        let _t1778 ← SudoRt.mulI (2 : Int) pair
        let _ix1779 := _t1778
        let _t1780 ← Ecbs.keypad_first face
        let _t1781 ← SudoRt.putL arr0 _ix1779 _t1780
        let cells := _t1781
        let _t1782 ← SudoRt.mulI (2 : Int) pair
        let _t1783 ← SudoRt.addI _t1782 (1 : Int)
        if decide (_t1783 < cellsI) then
          do
            let _t1785 ← SudoRt.mulI (2 : Int) pair
            let _t1786 ← SudoRt.addI _t1785 (1 : Int)
            let _ix1787 := _t1786
            let _t1788 ← Ecbs.keypad_second face
            let _t1789 ← SudoRt.putL cells _ix1787 _t1788
            let cells := _t1789
            pure (SudoRt.Flow.cont (ρ := Option Rolled) (next, cells))
        else
          do
            pure (SudoRt.Flow.cont (ρ := Option Rolled) (next, cells))

private theorem genAfter_eq (cells : Nat) (arr0 : Array Int) (pair : Int) :
    genAfter (Int.ofNat cells) arr0 pair = dieAfter cells arr0 pair := by
  funext σ
  unfold genAfter dieAfter
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  cases hface : SudoRt.SEq.beq σ.2.1 (0 : Int) with
  | true =>
    simp [hface, pure_eq_ok]
  | false =>
    simp [hface, pure_eq_ok]
    cases hmul : SudoRt.mulI (Int.ofNat 2) pair with
    | error _ =>
      simp [hmul, error_bind]
    | ok v =>
      simp [hmul, ok_bind, pure_eq_ok]
      cases hadd : SudoRt.addI v (1 : Int) with
      | error _ =>
        simp [hadd, error_bind]
      | ok j =>
        simp [hadd, ok_bind, pure_eq_ok]
        split
        · rw [← bind_assoc, ← bind_assoc, ← bind_assoc]
          simp only [bind_assoc]
        · rfl

/-- The emitted face loop, with the three-multiplication lay, is `dieGo`. -/
private theorem emitted_die
    (faces : List Nat) (cells : Nat) (arr : Array Int) (pair next : Int) :
    (do
        let toV ← SudoRt.subI (SudoRt.listLen (embed faces)) (1 : Int)
        let fuel := if next > toV then 1 else (toV - next).natAbs + 1
        let r ← SudoRt.runLoopOn (next, ((0 : Int), next)) fuel
          (faceStep (embed faces) toV) (genAfter (Int.ofNat cells) arr pair)
          (fun r => pure (SudoRt.Flow.ret r))
        pure r) =
      dieGo faces cells arr pair next := by
  rw [listLen_embed, genAfter_eq cells arr pair]
  unfold dieGo
  rfl

end EcbsLink2.Link2
