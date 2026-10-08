/-
  Export-path multiplication: `onto = false`, `copy_second` does not change the polynomial,
  `mirror = false`. The zero strip, `school_loop_refines`, then `lane_fold_refines`.
  The first `n` holes are `Spec.fieldMul`. Holes at and above `n` are empty, which is what
  `settle` asserts before it slides. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Lane
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.Settle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

/-- The `multiply` flags: lay `ys` against `xs` on a fresh bench, then the lane fold.
    Copying the second number onto the spare does not change the polynomial. -/
def exportMul (w h r n k bench : Nat) (xs ys : List Nat) (b : Ecbs.Board) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let st ← SudoRt.runLoopOn (ρ := Ecbs.Board)
      (Int.ofNat (n - 1), (b, embed (List.replicate bench 0)))
      (fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0))
      (rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int))
      (fun σ => pure σ.2)
      (fun _ => pure (b, embed (List.replicate bench 0)))
    laneFoldGo w h r n k (Int.ofNat bench) st.1 st.2

private theorem withMoves_here (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_hole (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold withMoves
  rfl

/-- Shared-loop pipeline for a fresh bench and `mirror = false`. The bench prefix is
    `Spec.fieldMul`, and every hole from `n` up is empty. This is not `Ecbs.mul`. -/
theorem mulPipeline_spec (xs ys : List Nat) (w h r n k moves hole bench : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (hn0 : 0 < n) (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (hspan : 2 * (n - 1) < bench)
    (hxs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfn : FitsLen n) (hfi : FitsLen (2 * (n - 1)))
    (hff : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    exportMul w h r n k bench xs ys b =
      .ok (noteBench (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)))
          (Int.ofNat (topIdx (school n xs ys (List.replicate bench 0) false)))
          (Int.ofNat (moves + schoolMoves xs ys n n +
            foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false))),
        embed (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false))) ∧
    (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)).take n =
      fieldMul n k bench xs ys ∧
    ∀ i, n ≤ i → i < bench →
      coeff (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)) i = 0 := by
  have hrep : allTritList (List.replicate bench 0) := replicate_trits bench
  have hlen0 : (List.replicate bench 0).length = bench := List.length_replicate bench 0
  have hfs : FitsLen (moves + n * (n + 1)) :=
    FitsLen.of_le hff (Nat.le_add_right _ _)
  have hschool := school_loop_refines xs ys (List.replicate bench 0) moves n false b
    (fun σ => pure σ.2) (fun _ => pure (b, embed (List.replicate bench 0)))
    hn0 hx hy (by rw [hlen0]; exact hspan) hxs hrep hm hfn hfi hfs
  unfold exportMul
  rw [hschool]
  dsimp
  rw [toPure_eq_ok, ok_bind]
  dsimp
  generalize hstEq : school n xs ys (List.replicate bench 0) false = hst
  have hlenS : hst.length = bench := by
    rw [← hstEq, school_length, hlen0]
  have htri : allTritList hst := by
    rw [← hstEq]
    refine school_trits xs ys (List.replicate bench 0) false n hrep ?_
    intro i hi
    rw [hlen0]
    have : i + (n - 1) ≤ 2 * (n - 1) := by omega
    exact Nat.lt_of_le_of_lt this hspan
  have hmov : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
  have hfitF : FitsLen (moves + schoolMoves xs ys n n + 3 * (hst.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hff (by omega)
  have hnb : n ≤ bench := by omega
  have hgap0 : 0 < n - k := by
    rw [hgap]
    exact Nat.mul_pos hw hr0
  have hm' : (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n))).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + schoolMoves xs ys n n) := withMoves_here _ _
  have hh' : (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n))).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat hole := by rw [withMoves_hole, hhole]
  have hsm' : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ hst.length ≤ 1000001 := by
    rw [hlenS]
    exact hsm
  have hfitL : FitsLen hst.length := by
    rw [hlenS]
    unfold FitsLen i64MaxNat
    have := hsm.2.2.2
    omega
  rw [← ofNat_eq_natCast bench, ← ofNat_eq_natCast (moves + schoolMoves xs ys n n),
    ← ofNat_eq_natCast (topIdx hst),
    ← ofNat_eq_natCast (moves + schoolMoves xs ys n n + foldCharge n (n - k) hst)]
  rw [lane_fold_refines hst w h r n k (moves + schoolMoves xs ys n n) hole bench
    (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)))
    hw hh hr hr0 hn hk hgap htri hm' hh' hsm' hnsm hfitF
    hfitL (by rw [hlenS]; exact Nat.le_refl _) (by omega : 0 < bench)]
  refine ⟨rfl, ?_, ?_⟩
  · rw [← hstEq]
    unfold fieldMul laneFold
    rfl
  · intro i hlo hi
    exact laneFold_high n (n - k) hst i hn0 hgap0 (by rw [hlenS]; exact hnb) hlo
      (by rw [hlenS]; exact hi)

private theorem array_get_congr {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  induction h
  rfl

private theorem decide_gt_nat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

/-- `note_strict` touches only `peak_strict`. The bench, the homes, held, moves,
    and the tier are unchanged, so a later schoolbook still sees the same numbers. -/
private theorem note_strict_keeps (b : Ecbs.Board) (peakS : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)) :
    ∃ b', Ecbs.note_strict b = .ok b' ∧
      b'.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold Ecbs.note_strict
  rw [occupied_refines b h7, ok_bind, hp]
  dsimp only
  rw [decide_gt_nat]
  by_cases hlt : peakS < countHeld b.sudo_5Board_4held 7
  · have hc : decide (peakS < countHeld b.sudo_5Board_4held 7) = true :=
      decide_eq_true hlt
    rw [hc, if_pos rfl, pure_eq_ok]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hc : decide (peakS < countHeld b.sudo_5Board_4held 7) = false := by
      rw [decide_eq_false_iff_not]; exact hlt
    rw [hc]
    simp only [Bool.false_eq_true, if_false, pure_eq_ok]
    refine ⟨b, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `peak` becomes `occ` when the held-count of homes `0 .. 6` is strictly larger. -/
def raisedPeak (peak occ : Nat) : Nat :=
  if peak < occ then occ else peak

/-- `note_peak` may raise `peak`. Moves, slides, the bench, and `held` stay.
    The resulting peak is `raisedPeak` of the old peak and the held-count. -/
private theorem note_peak_bench (b : Ecbs.Board) (peak : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)) :
    ∃ b', Ecbs.note_peak b = .ok b' ∧
      b'.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak peak (countHeld b.sudo_5Board_4held 7)) := by
  unfold Ecbs.note_peak raisedPeak
  rw [occupied_refines b h7, ok_bind, hp]
  dsimp only
  rw [decide_gt_nat]
  by_cases hlt : peak < countHeld b.sudo_5Board_4held 7
  · have hc : decide (peak < countHeld b.sudo_5Board_4held 7) = true :=
      decide_eq_true hlt
    rw [hc, if_pos rfl, pure_eq_ok]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hlt]⟩
  · have hc : decide (peak < countHeld b.sudo_5Board_4held 7) = false := by
      rw [decide_eq_false_iff_not]; exact hlt
    rw [hc]
    simp only [Bool.false_eq_true, if_false, pure_eq_ok]
    exact ⟨b, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa [raisedPeak, hlt] using hp⟩

private theorem spare_beq_false (second : Nat) (h : second ≠ 6) :
    SudoRt.SEq.beq (second : Int) Ecbs.spare = false := by
  rw [sEq_int, show Ecbs.spare = ((6 : Nat) : Int) from rfl, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast second, ← ofNat_eq_natCast 6] at hEq
    exact hEq))

/-- Moves `Ecbs.mul` leaves: the incoming counter, one copy of the second number,
    the schoolbook, and the lane fold. -/
def mulMoves (moves : Nat) (xs ys : List Nat) (n k bench : Nat) : Nat :=
  let sch := school n xs ys (List.replicate bench 0) false
  moves + pegCount ys + schoolMoves xs ys n n + foldCharge n (n - k) sch

/-- Peak `Ecbs.mul` leaves. Copying onto the empty spare may raise it; clearing the
    spare does not lower it; the final `note_peak` raises it only when the remaining
    held homes outnumber that value. -/
def mulPeak (held0 heldF : Array Bool) (h6 : 6 < held0.size) (peak : Nat) : Nat :=
  raisedPeak (raisedPeak peak (countHeld (held0.set ⟨6, h6⟩ true) 7)) (countHeld heldF 7)

/-- Export flags `copy_second = true`, `onto = false`, `mirror = false`, marker off,
    bench off. The bench is the lane fold of the schoolbook product: the prefix is
    `Spec.fieldMul`, and holes from `n` up are empty. The move counter is `mulMoves`
    and the peak is `mulPeak`. Slides are unchanged. -/
theorem mul_refines (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hSpH : 6 < b.sudo_5Board_4held.size) (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneS : second ≠ 6) (hneF : first ≠ 6)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitC : FitsLen (moves + pegCount ys))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
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
    (hfold : FitsLen (moves + pegCount ys + n * (n + 1) + 3 * (bench - n))) :
    ∃ b', Ecbs.mul b (dst : Int) (first : Int) (second : Int) true false false = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (dst : Int) ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)) ∧
      (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)).take n =
        fieldMul n k bench xs ys ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mulMoves moves xs ys n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (mulPeak b.sudo_5Board_4held b'.sudo_5Board_4held hSpH peak) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held =
        (b.sudo_5Board_4held.set ⟨6, hSpH⟩ true).set
          ⟨6, by rw [Array.size_set]; exact hSpH⟩ false := by
  unfold Ecbs.mul Ecbs.log_op
  simp only [hmk, hoff, Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    pattern Ecbs.settle _
    rw [settle_off _ rfl]
  simp only [ok_bind, pure_eq_ok]
  rw [hbl, filledL_ofNat, ok_bind]
  rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ first hHome, hArr, ok_bind]
  simp only [if_true]
  rw [spare_beq_false second hneS]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let bCopy : Ecbs.Board :=
    { b with
      sudo_5Board_8bench_on := true
      sudo_5Board_8bench_to := (dst : Int)
      sudo_5Board_5bench := Array.mkArray bench 0
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) }
      sudo_5Board_9marker_on := false }
  have hcopy := copy_band_refines bCopy 6 second ys moves peak
    (by simpa [bCopy] using hSpHome) (by simpa [bCopy] using hSpH)
    (by simpa [bCopy] using hHomeS) (by simpa [bCopy] using hS)
    (by simpa [bCopy] using h7)
    (by simpa [bCopy] using hHS) (by simpa [bCopy] using hYs)
    (by simpa [bCopy] using hSpE)
    (by simpa [bCopy, hleny] using hn) (by simpa [bCopy, hleny] using hf)
    (by simpa [bCopy] using hmoves)     (by simpa [bCopy] using hpeak) hfitC
  conv =>
    pattern (Ecbs.copy_band _ _ _ false)
    change Ecbs.copy_band bCopy ((6 : Nat) : Int) (second : Int) false
  rw [hcopy]
  simp only [ok_bind, pure_eq_ok]
  have hbf : SudoRt.SEq.beq Ecbs.spare (Int.ofNat first) = false := by
    rw [sEq_int, show Ecbs.spare = Int.ofNat 6 from rfl, decide_eq_false_iff_not]
    intro hEq
    exact hneF (Int.ofNat.inj hEq.symm)
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  generalize hPB : placeBoard bCopy 6 (by simpa [bCopy] using hSpHome)
      (by simpa [bCopy] using hSpH) ys moves peak = bP
  have h7b : 7 ≤ bP.sudo_5Board_4held.size := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rw [Array.size_set] <;> exact h7
  have hpB : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bCopy, hpeakS]
  obtain ⟨bS, hbS, hbenchS, hhomeS, hheldS, hmovS, honS, htoS, htS, hmkS, hholeS, hpeakKeep, hslidesS⟩ :=
    note_strict_keeps bP peakS h7b hpB
  rw [hbS]
  simp only [ok_bind, pure_eq_ok]
  have h6 : 6 < bP.sudo_5Board_4held.size := Nat.lt_of_lt_of_le (by decide : 6 < 7) h7b
  have h6h : 6 < bP.sudo_5Board_4home.size := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rw [Array.size_set] <;> simpa [bCopy] using hSpHome
  have hHeld6 : bP.sudo_5Board_4held[6]'h6 = true := by
    subst hPB
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  have hHome6 : bP.sudo_5Board_4home[6]'h6h = embed ys := by
    subst hPB
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  rw [hheldS, show Ecbs.spare = Int.ofNat 6 from rfl, atL_ofNat _ 6 h6, hHeld6]
  simp only [sudoAssert_true, ok_bind]
  rw [hhomeS, atL_ofNat _ 6 h6h, hHome6, ok_bind]
  rw [putL_ofNat _ 6 false h6, ok_bind]
  rw [putL_ofNat _ 6 (#[] : Array Int) h6h, ok_bind]
  rw [hn, ← ofNat_eq_natCast n]
  conv =>
    pattern (SudoRt.subI (Int.ofNat n) _)
    rw [subI_ofNat_one n hn0 hf]
  rw [ok_bind]
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  rw [← embed_replicate_zero]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  have hmL : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    rw [hmovS, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> rfl
  let bL : Ecbs.Board :=
    { bS with
      sudo_5Board_4home := bP.sudo_5Board_4home.set ⟨6, h6h⟩ #[]
      sudo_5Board_4held := bP.sudo_5Board_4held.set ⟨6, h6⟩ false }
  have hmL2 : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    simpa [bL] using hmL
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, embed (List.replicate bench 0)))
  rw [school_loop_refines xs ys (List.replicate bench 0) (moves + pegCount ys) n false bL
      _ _ hn0 (by rw [hlenx]; exact Nat.le_refl _) (by rw [hleny]; exact Nat.le_refl _)
      (by simp [List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL2 hf hfi hfm]
  simp only [Prod.fst, Prod.snd]
  let sch := school n xs ys (List.replicate bench 0) false
  let mvF := moves + pegCount ys + schoolMoves xs ys n n
  let bF := withMoves bL (Int.ofNat mvF)
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  have hfitS : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have htP : bP.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [← hPB]; unfold placeBoard; dsimp only; split <;> rfl
  have htL : bL.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp [bL, htS, htP]
  have hholeP : bP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    rw [← hPB]; unfold placeBoard; dsimp only; split <;> rfl
  have hholeL : bL.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bL, hholeS, hholeP, hHole]
  have hmovF : bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF := by
    simp [bF, withMoves]
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hchg : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
  have hfitF : FitsLen (mvF + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by omega)
  have hwB : bF.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bF, withMoves, bL, htS, htP, hwF]
  have hhB : bF.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bF, withMoves, bL, htS, htP, hhF]
  have hrB : bF.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bF, withMoves, bL, htS, htP, hrF]
  have hnB : bF.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bF, withMoves, bL, htS, htP, hn, ofNat_eq_natCast]
  have hkB : bF.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bF, withMoves, bL, htS, htP, hkF]
  have hblB : bF.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bF, withMoves, bL, htS, htP, hbl]
  rw [lane_fold_eq sch w h r n k bench bF hfitS hwB hhB hrB hnB hkB hblB]
  rw [lane_fold_refines sch w h r n k mvF hole bench bF
      hw0 hh0 hrR hrP hnE hkLe hgap
      (by
        have htri : allTritList sch := by
          simpa [sch] using school_trits xs ys (List.replicate bench 0) false n (replicate_trits _)
            (fun i hi => by
              rw [List.length_replicate]
              have : i + (n - 1) ≤ 2 * (n - 1) := by omega
              exact Nat.lt_of_le_of_lt this hspan)
        exact htri)
      hmovF (by simp [bF, withMoves, bL, hholeS, hholeP, hHole]) hsmS hnsm hfitF hfitS
      (by rw [hlenS]; exact Nat.le_refl _) (by omega : 0 < bench)]
  simp only [ok_bind, pure_eq_ok, Prod.fst, Prod.snd]
  let nb := noteBench bF (Int.ofNat (topIdx sch)) (Int.ofNat (mvF + foldCharge n (n - k) sch))
  let bN : Ecbs.Board := { nb with sudo_5Board_5bench := embed (laneFold n (n - k) sch) }
  conv =>
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak bN
  have h7N : 7 ≤ bN.sudo_5Board_4held.size := by
    dsimp [bN, nb]
    unfold noteBench
    split
    · simp only [withMoves, withHole, bF, bL, Array.size_set]
      exact h7b
    · simp only [withMoves, bF, bL, Array.size_set]
      exact h7b
  have honP : bP.sudo_5Board_8bench_on = true := by
    rw [← hPB]; unfold placeBoard; dsimp only; split <;> rfl
  have htoP : bP.sudo_5Board_8bench_to = (dst : Int) := by
    rw [← hPB]; unfold placeBoard; dsimp only [bCopy]; split <;> rfl
  have honN : bN.sudo_5Board_8bench_on = true := by
    dsimp [bN, nb]; unfold noteBench withMoves withHole; dsimp [bF, bL]
    rw [honS, honP]; split <;> rfl
  have htoN : bN.sudo_5Board_8bench_to = (dst : Int) := by
    dsimp [bN, nb]; unfold noteBench withMoves withHole; dsimp [bF, bL]
    rw [htoS, htoP]; split <;> rfl
  have hpeakP : bP.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨6, hSpH⟩ true) 7)) := by
    rw [← hPB]
    unfold placeBoard raisedPeak
    dsimp only
    simp only [bCopy, hpeak]
    split <;> rfl
  have hslidesP : bP.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bCopy]
  have hpeakL : bL.sudo_5Board_4cost.sudo_5Costs_4peak = bP.sudo_5Board_4cost.sudo_5Costs_4peak := by
    simp [bL, hpeakKeep]
  have hpeakF : bF.sudo_5Board_4cost.sudo_5Costs_4peak = bL.sudo_5Board_4cost.sudo_5Costs_4peak := by
    simp [bF, withMoves]
  have hpeakNB : (noteBench bF (Int.ofNat (topIdx sch)) (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_4cost.sudo_5Costs_4peak =
      bF.sudo_5Board_4cost.sudo_5Costs_4peak := by
    unfold noteBench withMoves withHole
    split <;> rfl
  let copied := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨6, hSpH⟩ true) 7)
  have hpeakN : bN.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat copied := by
    change (noteBench bF (Int.ofNat (topIdx sch))
        (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat copied
    rw [hpeakNB, hpeakF, hpeakL, hpeakP]
  have hmovN : bN.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mvF + foldCharge n (n - k) sch) := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> rfl
  have hslidesN : bN.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
    dsimp [bN, nb]
    unfold noteBench withMoves withHole
    split <;> simp [bF, withMoves, bL, hslidesS, hslidesP]
  have hmovEq : mvF + foldCharge n (n - k) sch = mulMoves moves xs ys n k bench := by
    simp [mulMoves, mvF, sch]
  have hheldP : bP.sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨6, hSpH⟩ true := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bCopy]
  have hheldNB : (noteBench bF (Int.ofNat (topIdx sch))
      (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_4held =
      bF.sudo_5Board_4held := by
    unfold noteBench withMoves withHole
    split <;> rfl
  have hheldN : bN.sudo_5Board_4held =
      (b.sudo_5Board_4held.set ⟨6, hSpH⟩ true).set
        ⟨6, by rw [Array.size_set]; exact hSpH⟩ false := by
    change (noteBench bF (Int.ofNat (topIdx sch))
        (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_4held = _
    rw [hheldNB]
    simp only [bF, withMoves, bL]
    apply Array.ext
    · rw [Array.size_set, Array.size_set]
      exact congrArg Array.size hheldP
    · intro i hi1 hi2
      have hszP : i < bP.sudo_5Board_4held.size := by
        simpa [Array.size_set] using hi1
      have hget : bP.sudo_5Board_4held[i] =
          (b.sudo_5Board_4held.set ⟨6, hSpH⟩ true)[i]'(hheldP ▸ hszP) :=
        array_get_congr hheldP i hszP
      by_cases hi : i = 6
      · simp [hi, Array.getElem_set, hget]
      · simp [Array.getElem_set, hi, hget]
  have htN : bN.sudo_5Board_1t = b.sudo_5Board_1t := by
    change (noteBench bF (Int.ofNat (topIdx sch))
        (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_1t = _
    unfold noteBench withMoves withHole
    split <;> simp [bF, withMoves, bL, htS, htP]
  have hhomeSz : bN.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    change (noteBench bF (Int.ofNat (topIdx sch))
        (Int.ofNat (mvF + foldCharge n (n - k) sch))).sudo_5Board_4home.size = _
    unfold noteBench withMoves withHole
    split
    · simp only [bF, withMoves, bL, Array.size_set]
      rw [← hPB]; unfold placeBoard; dsimp only; split <;> simp [bCopy, Array.size_set]
    · simp only [bF, withMoves, bL, Array.size_set]
      rw [← hPB]; unfold placeBoard; dsimp only; split <;> simp [bCopy, Array.size_set]
  unfold Ecbs.note_peak
  rw [occupied_refines bN h7N, ok_bind, hpeakN]
  conv => zeta
  rw [ofNat_eq_natCast copied, decide_gt_nat]
  by_cases hlt : copied < countHeld bN.sudo_5Board_4held 7
  · rw [decide_eq_true hlt, if_pos rfl, pure_eq_ok, ok_bind]
    refine ⟨_, rfl, honN, htoN, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold fieldMul; rfl
    · intro i hlo hi
      have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
      have hnb : n ≤ bench := by omega
      exact laneFold_high n (n - k) sch i hn0 hgap0 (by rw [hlenS]; exact hnb) hlo
        (by rw [hlenS]; exact hi)
    · change bN.sudo_5Board_4cost.sudo_5Costs_5moves = _
      rw [hmovN, hmovEq]
    · change (countHeld bN.sudo_5Board_4held 7 : Int) =
        Int.ofNat (mulPeak b.sudo_5Board_4held bN.sudo_5Board_4held hSpH peak)
      rw [← ofNat_eq_natCast (countHeld bN.sudo_5Board_4held 7)]
      apply congrArg Int.ofNat
      unfold mulPeak
      change countHeld bN.sudo_5Board_4held 7 =
        raisedPeak copied (countHeld bN.sudo_5Board_4held 7)
      conv =>
        rhs
        unfold raisedPeak
      exact (if_pos (c := copied < countHeld bN.sudo_5Board_4held 7)
        (t := countHeld bN.sudo_5Board_4held 7) (e := copied) hlt).symm
    · change bN.sudo_5Board_4cost.sudo_5Costs_6slides = _
      exact hslidesN
    · exact htN
    · change bN.sudo_5Board_4home.size = _
      exact hhomeSz
    · change bN.sudo_5Board_4held = _
      exact hheldN
  · rw [(decide_eq_false_iff_not).mpr hlt]
    simp only [Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
    refine ⟨bN, rfl, honN, htoN, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold fieldMul; rfl
    · intro i hlo hi
      have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
      have hnb : n ≤ bench := by omega
      exact laneFold_high n (n - k) sch i hn0 hgap0 (by rw [hlenS]; exact hnb) hlo
        (by rw [hlenS]; exact hi)
    · rw [hmovN, hmovEq]
    · rw [hpeakN, ofNat_eq_natCast]
      change (copied : Int) =
        (mulPeak b.sudo_5Board_4held bN.sudo_5Board_4held hSpH peak : Int)
      apply congrArg
      unfold mulPeak
      change copied = raisedPeak copied (countHeld bN.sudo_5Board_4held 7)
      conv =>
        rhs
        unfold raisedPeak
      exact (if_neg (c := copied < countHeld bN.sudo_5Board_4held 7)
        (t := countHeld bN.sudo_5Board_4held 7) (e := copied) hlt).symm
    · exact hslidesN
    · exact htN
    · exact hhomeSz
    · exact hheldN

end EcbsLink2.Link2
