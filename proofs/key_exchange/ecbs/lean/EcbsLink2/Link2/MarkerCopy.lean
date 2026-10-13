/-
  A copy multiply (`copy_second = true`, `onto = false`, `mirror = false`) after
  `log_op`. The spare receives the second home, the schoolbook is
  `school_loop_refines`, and the lane fold is `mulAfter`. The marker flag is
  not read. `mul_copy_off_after` is the marker-off bridge. `mul_copy_up_after` and
  `mul_copy_down_after` are the marker-on bridges.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerMul

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

private theorem spare_beq_false (second : Nat) (h : second ≠ 6) :
    SudoRt.SEq.beq (second : Int) Ecbs.spare = false := by
  rw [sEq_int, show Ecbs.spare = Int.ofNat 6 from rfl, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

private theorem spare_neq_first (first : Nat) (h : first ≠ 6) :
    SudoRt.SEq.beq ((6 : Nat) : Int) (Int.ofNat first) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast 6] at hEq
    exact hEq.symm))

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

theorem place_home_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  unfold placeBoard
  dsimp only
  split <;> simp

theorem place_held_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold placeBoard
  dsimp only
  split <;> simp

theorem mulAimed_markerOn (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    mulAimed (markerOn b) dst strip = markerOn (mulAimed b dst strip) := by
  unfold mulAimed markerOn
  rfl

theorem strict_markerOn (b : Ecbs.Board) (peakS : Nat) :
    strictBoard (markerOn b) peakS = markerOn (strictBoard b peakS) := by
  unfold strictBoard markerOn
  rfl

/-- `place` does not read the marker flag. -/
theorem placeBoard_markerOn (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hH' : home < (markerOn b).sudo_5Board_4home.size)
    (hD' : home < (markerOn b).sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard (markerOn b) home hH' hD' xs moves peak =
      markerOn (placeBoard b home hH hD xs moves peak) := by
  unfold placeBoard
  dsimp only
  have hHf : (⟨home, hH'⟩ : Fin (markerOn b).sudo_5Board_4home.size) = ⟨home, hH⟩ :=
    Fin.ext rfl
  have hDf : (⟨home, hD'⟩ : Fin (markerOn b).sudo_5Board_4held.size) = ⟨home, hD⟩ :=
    Fin.ext rfl
  simp only [hHf, hDf]
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · simp only [hlt, markerOn_def]
    apply board_ext <;> rfl
  · simp only [hlt, markerOn_def]
    apply board_ext <;> rfl

/-- Copy-second body after `log_op`. `onto = false`, `mirror = false`. -/
def mulCopyGo (b : Ecbs.Board) (dst first second : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
    let n := b.sudo_5Board_1t.sudo_4Tier_1n
    let b ← Ecbs.settle b
    let strip ← SudoRt.filledL b.sudo_5Board_1t.sudo_4Tier_8benchlen (0 : Int)
    let b := { b with sudo_5Board_8bench_on := true }
    let b := { b with sudo_5Board_8bench_to := dst }
    let b := { b with sudo_5Board_5bench := strip }
    let held ← SudoRt.atL b.sudo_5Board_4held first
    let _ ← SudoRt.sudoAssert held 568
    let a ← SudoRt.atL b.sudo_5Board_4home first
    let _ ← SudoRt.sudoAssert (!(SudoRt.SEq.beq second Ecbs.spare)) 572
    let b ← Ecbs.copy_band b Ecbs.spare second false
    let _ ← SudoRt.sudoAssert (!(SudoRt.SEq.beq Ecbs.spare first)) 575
    let b ← Ecbs.note_strict b
    let held2 ← SudoRt.atL b.sudo_5Board_4held Ecbs.spare
    let _ ← SudoRt.sudoAssert held2 577
    let s ← SudoRt.atL b.sudo_5Board_4home Ecbs.spare
    let heldA ← SudoRt.putL b.sudo_5Board_4held Ecbs.spare false
    let b := { b with sudo_5Board_4held := heldA }
    let homeA ← SudoRt.putL b.sudo_5Board_4home Ecbs.spare (#[] : Array Int)
    let b := { b with sudo_5Board_4home := homeA }
    let fromV ← SudoRt.subI n (1 : Int)
    let toV : Int := 0
    let fuel : Nat := if fromV < toV then 1 else (fromV - toV).natAbs + 1
    SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, (b, strip)) fuel
      (mulSchoolStep a s false n toV) mulAfter (fun r => pure r)

/-- The board the schoolbook sees: the second home copied onto the spare, that
    spare cleared, the marker flag left as it stood. -/
def mulCopyLoop (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size) : Ecbs.Board :=
  let placed := placeBoard (mulAimed b dst strip) 6 hH hD ys moves peak
  let strict := strictBoard placed peakS
  { strict with
    sudo_5Board_4home := strict.sudo_5Board_4home.set ⟨6, by
      rw [strict_home, place_home_size]
      exact hH⟩ #[]
    sudo_5Board_4held := strict.sudo_5Board_4held.set ⟨6, by
      rw [strict_held, place_held_size]
      exact hD⟩ false }

/-- Peak after the spare copy. Clearing the spare does not lower it. -/
def copyPeak (held : Array Bool) (h6 : 6 < held.size) (peak : Nat) : Nat :=
  raisedPeak peak (countHeld (held.set ⟨6, h6⟩ true) 7)

theorem mulCopyLoop_marker (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size)
    (hH' : 6 < (mulAimed (markerOn b) dst strip).sudo_5Board_4home.size)
    (hD' : 6 < (mulAimed (markerOn b) dst strip).sudo_5Board_4held.size) :
    mulCopyLoop (markerOn b) dst strip ys moves peak peakS hH' hD' =
      markerOn (mulCopyLoop b dst strip ys moves peak peakS hH hD) := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed markerOn
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · by_cases hlt' : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD'⟩ true) 7
    · simp only [if_pos hlt, if_pos hlt']
      apply board_ext <;> first
        | rfl
        | (apply Array.ext
           · simp only [if_pos hlt, if_pos hlt', Array.size_set]
           · intro i _ _
             simp only [if_pos hlt, if_pos hlt', Array.getElem_set])
    · exact absurd hlt hlt'
  · by_cases hlt' : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD'⟩ true) 7
    · exact absurd hlt' hlt
    · simp only [if_neg hlt, if_neg hlt']
      apply board_ext <;> first
        | rfl
        | (apply Array.ext
           · simp only [if_neg hlt, if_neg hlt', Array.size_set]
           · intro i _ _
             simp only [if_neg hlt, if_neg hlt', Array.getElem_set])

theorem mulCopyLoop_moves (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount ys) := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · simp [hlt]
  · simp [hlt]

theorem mulCopyLoop_tier (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · simp [hlt]
  · simp [hlt]

theorem mulCopyLoop_hole (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · simp [hlt]
  · simp [hlt]

theorem mulCopyLoop_held_size (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · simp [hlt]
  · simp [hlt]

theorem mulCopyLoop_flag (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size)
    (hflag : b.sudo_5Board_9marker_on = false) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_9marker_on = false := by
  unfold mulCopyLoop strictBoard placeBoard mulAimed
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, hD⟩ true) 7
  · simp [hlt, hflag]
  · simp [hlt, hflag]

theorem mulCopyLoop_peak (b : Ecbs.Board) (dst : Int) (strip : Array Int) (ys : List Nat)
    (moves peak peakS : Nat)
    (hH : 6 < (mulAimed b dst strip).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b dst strip).sudo_5Board_4held.size)
    (h6 : 6 < b.sudo_5Board_4held.size)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)) :
    (mulCopyLoop b dst strip ys moves peak peakS hH hD).sudo_5Board_4cost.sudo_5Costs_4peak =
      ((copyPeak b.sudo_5Board_4held h6 peak : Nat) : Int) := by
  unfold mulCopyLoop copyPeak strictBoard placeBoard mulAimed
  dsimp only
  have hfin : (⟨6, hD⟩ : Fin b.sudo_5Board_4held.size) = ⟨6, h6⟩ := Fin.ext rfl
  simp only [hfin]
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨6, h6⟩ true) 7
  · simp only [if_pos hlt, raisedPeak]
    rfl
  · simp only [if_neg hlt, raisedPeak, hpeak]

/-- `mulCopyGo` on a bench that is off. The bench prefix is not read here; the lane
    fold stays inside `mulAfter`. -/
theorem mul_copy_tail (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peak peakS : Nat)
    (hoff : b.sudo_5Board_8bench_on = false)
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitC : FitsLen (moves + pegCount ys))
    (hH : 6 < (mulAimed b ((dst : Nat) : Int) (embed (List.replicate bench 0))).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed b ((dst : Nat) : Int) (embed (List.replicate bench 0))).sudo_5Board_4held.size) :
    mulCopyGo b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int) =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulCopyLoop b ((dst : Nat) : Int) (embed (List.replicate bench 0)) ys
              moves peak peakS hH hD)
            (Int.ofNat (moves + pegCount ys + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold mulCopyGo
  rw [settle_off b hoff]
  simp only [ok_bind]
  conv =>
    lhs
    rw [hbl, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b ((dst : Nat) : Int) strip
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ first hHome, hArr, ok_bind]
  conv =>
    lhs
    rw [spare_beq_false second hneS]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  have hcopy := copy_band_refines bA 6 second ys moves peak hH hD
    (by simpa [bA, mulAimed, strip] using hHomeS)
    (by simpa [bA, mulAimed, strip] using hS)
    (by simpa [bA, mulAimed, strip] using h7)
    (by simpa [bA, mulAimed, strip] using hHS)
    (by simpa [bA, mulAimed, strip] using hYs)
    (by simpa [bA, mulAimed, strip] using hSpE)
    (by simpa [bA, mulAimed, strip, hleny] using hn)
    (by rw [hleny]; exact hf)
    (by simpa [bA, mulAimed, strip] using hmoves)
    (by simpa [bA, mulAimed, strip] using hpeak)
    hfitC
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.spare ((second : Nat) : Int) false)
    change Ecbs.copy_band bA Ecbs.spare ((second : Nat) : Int) false
  rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hcopy]
  simp only [ok_bind, pure_eq_ok]
  conv =>
    lhs
    rw [spare_neq_first first hneF]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  generalize hPB : placeBoard bA 6 hH hD ys moves peak = bP
  have h7b : 7 ≤ bP.sudo_5Board_4held.size := by
    rw [← hPB, place_held_size]
    simpa [bA, mulAimed, strip] using h7
  have hpB : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bA, mulAimed, strip, hpeakS]
  rw [note_strict_eq bP peakS h7b hpB]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bP peakS
  have h6 : 6 < bS.sudo_5Board_4held.size := by
    rw [strict_held, ← hPB, place_held_size]
    simpa [bA, mulAimed, strip] using hSpH
  have h6h : 6 < bS.sudo_5Board_4home.size := by
    rw [strict_home, ← hPB, place_home_size]
    simpa [bA, mulAimed, strip] using hSpHome
  have hHeld6 : bS.sudo_5Board_4held[6] = true := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  have hHome6 : bS.sudo_5Board_4home[6] = embed ys := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  conv =>
    lhs
    rw [← ofNat_eq_natCast 6, atL_ofNat _ 6 h6, hHeld6]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ 6 h6h, hHome6, ok_bind]
  conv =>
    lhs
    rw [putL_ofNat _ 6 false h6, ok_bind, putL_ofNat _ 6 (#[] : Array Int) h6h, ok_bind]
  conv =>
    lhs
    rw [show b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
      simpa [ofNat_eq_natCast] using hn]
  conv =>
    lhs
    rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  conv =>
    lhs
    rw [hfuel]
  generalize hBLdef :
    { {bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false} with
      sudo_5Board_4home :=
        ({bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false}).sudo_5Board_4home.set
          ⟨6, h6h⟩ #[] } = bL
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    rw [← hBLdef]
    simp only [bS, strictBoard]
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rfl
  conv =>
    lhs
    rw [mulSchool_step]
  conv =>
    lhs
    pattern (rowStep _ _ _ _ _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    lhs
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  change (SudoRt.runLoopOn (ρ := Ecbs.Board)
      (Int.ofNat (n - 1), (bL, embed (List.replicate bench 0)))
      (fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0))
      (rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int))
      mulAfter (fun r => pure r)) = _
  rw [school_loop_refines xs ys (List.replicate bench 0) (moves + pegCount ys) n false bL
      mulAfter (fun r => pure r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  have hLoop : bL = mulCopyLoop b ((dst : Nat) : Int) strip ys moves peak peakS hH hD := by
    rw [← hBLdef]
    subst hPB
    simp only [bS]
    unfold mulCopyLoop
    rfl
  rw [hLoop]

/-- The copy body does not read the marker flag. `mulAfter_flag` is the lane fold. -/
theorem mul_copy_flag (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitC : FitsLen (moves + pegCount ys))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + pegCount ys + n * (n + 1) + 3 * (bench - n))) :
    mulCopyGo (markerOn b) ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int) =
      (do
        let r ← mulCopyGo b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  let strip := embed (List.replicate bench 0)
  have hH : 6 < (mulAimed b ((dst : Nat) : Int) strip).sudo_5Board_4home.size := by
    simpa [mulAimed, strip] using hSpHome
  have hD : 6 < (mulAimed b ((dst : Nat) : Int) strip).sudo_5Board_4held.size := by
    simpa [mulAimed, strip] using hSpH
  have hH' : 6 < (mulAimed (markerOn b) ((dst : Nat) : Int) strip).sudo_5Board_4home.size := by
    simpa [mulAimed, markerOn, strip] using hSpHome
  have hD' : 6 < (mulAimed (markerOn b) ((dst : Nat) : Int) strip).sudo_5Board_4held.size := by
    simpa [mulAimed, markerOn, strip] using hSpH
  have hOff := mul_copy_tail b dst first second xs ys n moves bench peak peakS
    hoff hbl hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneS hneF hn0 hn
    hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitC hH hD
  have hOn := mul_copy_tail (markerOn b) dst first second xs ys n moves bench peak peakS
    (by simpa [markerOn] using hoff)
    (by simpa [markerOn] using hbl)
    (by simpa [markerOn] using hF) (by simpa [markerOn] using hHome)
    (by simpa [markerOn] using hHF) (by simpa [markerOn] using hArr)
    (by simpa [markerOn] using hS) (by simpa [markerOn] using hHomeS)
    (by simpa [markerOn] using hHS) (by simpa [markerOn] using hYs)
    (by simpa [markerOn] using hSpH) (by simpa [markerOn] using hSpHome)
    (by simpa [markerOn] using hSpE) (by simpa [markerOn] using h7)
    hneS hneF hn0 (by simpa [markerOn] using hn) hlenx hleny hf
    (by simpa [markerOn] using hmoves) (by simpa [markerOn] using hpeak)
    (by simpa [markerOn] using hpeakS) hspan hxsT hfi hfm hfitC hH' hD'
  rw [hOn, hOff]
  have hmark := mulCopyLoop_marker b ((dst : Nat) : Int) strip ys moves peak peakS hH hD hH' hD'
  rw [hmark, withMoves_markerOn]
  let sch := school n xs ys (List.replicate bench 0) false
  let mvW := moves + pegCount ys + schoolMoves xs ys n n
  let bL := mulCopyLoop b ((dst : Nat) : Int) strip ys moves peak peakS hH hD
  let bW := withMoves bL (Int.ofNat mvW)
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  have hfit : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have hflagW : bW.sudo_5Board_9marker_on = false := by
    simpa [bW, marker_withMoves, bL] using mulCopyLoop_flag b ((dst : Nat) : Int) strip ys
      moves peak peakS hH hD hflag
  have htier := mulCopyLoop_tier b ((dst : Nat) : Int) strip ys moves peak peakS hH hD
  have hnW : bW.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp only [bW, withMoves, bL]
    rw [htier]
    simpa [ofNat_eq_natCast] using hn
  have hwW : bW.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp only [bW, withMoves, bL]
    rw [htier]
    exact hw
  have hhW : bW.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp only [bW, withMoves, bL]
    rw [htier]
    exact hh
  have hrW : bW.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp only [bW, withMoves, bL]
    rw [htier]
    exact hr
  have hkW : bW.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp only [bW, withMoves, bL]
    rw [htier]
    exact hk
  have hblW : bW.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp only [bW, withMoves, bL]
    rw [htier]
    exact hbl
  have hmW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvW := by
    simp [bW, mvW]
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simpa [bW, bL] using
      (mulCopyLoop_hole b ((dst : Nat) : Int) strip ys moves peak peakS hH hD).trans hhole
  have hpeakW : bW.sudo_5Board_4cost.sudo_5Costs_4peak =
      ((copyPeak b.sudo_5Board_4held hSpH peak : Nat) : Int) := by
    simpa [bW, bL] using mulCopyLoop_peak b ((dst : Nat) : Int) strip ys moves peak peakS
      hH hD hSpH hpeak
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by
    simpa [bW, bL] using (mulCopyLoop_held_size b ((dst : Nat) : Int) strip ys moves peak peakS
      hH hD).symm ▸ h7
  have htri : allTritList sch := by
    simpa [sch] using school_trits xs ys (List.replicate bench 0) false n (replicate_trits _)
      (fun i hi => by
        rw [List.length_replicate]
        have : i + (n - 1) ≤ 2 * (n - 1) := by omega
        exact Nat.lt_of_le_of_lt this hspan)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hposB : 0 < bench := by omega
  have hfitF : FitsLen (mvW + 3 * (sch.length - n)) := by
    rw [hlenS, show mvW = moves + pegCount ys + schoolMoves xs ys n n from rfl]
    exact FitsLen.of_le hfold (by
      have := schoolMoves_bound xs ys n
      omega)
  simpa [bW, bL, strip, sch, mvW] using mulAfter_flag bW sch w h r n k mvW hole bench
      (copyPeak b.sudo_5Board_4held hSpH peak) hflagW hfit hwW hhW hrW hnW hkW hblW
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hposB

/-- A product of trit data is trits when the schoolbook fits on the bench. -/
theorem fieldMul_span_trits (n k bench : Nat) (xs ys : List Nat)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench xs ys) := by
  have hrep : allTritList (List.replicate bench 0) := replicate_trits bench
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

/-- Marker off, bench off. The emitted copy multiply is the schoolbook of the
    spare copy, then `mulAfter`. -/
theorem mul_copy_off_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peak peakS cOps : Nat)
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitC : FitsLen (moves + pegCount ys))
    (hH : 6 < (mulAimed (bumpOp b 0 cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed (bumpOp b 0 cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4held.size) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulCopyLoop (bumpOp b 0 cOps hops) ((dst : Nat) : Int)
              (embed (List.replicate bench 0)) ys moves peak peakS hH hD)
            (Int.ofNat (moves + pegCount ys + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, if_true, pure_eq_ok, toPure_eq_ok, ok_bind]
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_off (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  simp only [ok_bind]
  let b0 := bumpOp b 0 cOps hops
  rw [settle_off b0 (by simp [b0, bumpOp, hoff])]
  simp only [ok_bind, pure_eq_ok]
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, bumpOp, hbl]
  conv =>
    lhs
    rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [show b0.sudo_5Board_4held = b.sudo_5Board_4held from by simp [b0, bumpOp],
        show b0.sudo_5Board_4home = b.sudo_5Board_4home from by simp [b0, bumpOp]]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ first hHome, hArr, ok_bind]
  conv =>
    lhs
    rw [spare_beq_false second hneS]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  have hcopy := copy_band_refines bA 6 second ys moves peak hH hD
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hHomeS)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hS)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using h7)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hHS)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hYs)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hSpE)
    (by simpa [bA, mulAimed, strip, b0, bumpOp, hleny] using hn)
    (by rw [hleny]; exact hf)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hmoves)
    (by simpa [bA, mulAimed, strip, b0, bumpOp] using hpeak)
    hfitC
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.spare ((second : Nat) : Int) false)
    change Ecbs.copy_band bA Ecbs.spare ((second : Nat) : Int) false
  rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hcopy]
  simp only [ok_bind, pure_eq_ok]
  conv =>
    lhs
    rw [spare_neq_first first hneF]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  generalize hPB : placeBoard bA 6 hH hD ys moves peak = bP
  have h7b : 7 ≤ bP.sudo_5Board_4held.size := by
    rw [← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, bumpOp] using h7
  have hpB : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bA, mulAimed, strip, b0, bumpOp, hpeakS]
  rw [note_strict_eq bP peakS h7b hpB]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bP peakS
  have h6 : 6 < bS.sudo_5Board_4held.size := by
    rw [strict_held, ← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, bumpOp] using hSpH
  have h6h : 6 < bS.sudo_5Board_4home.size := by
    rw [strict_home, ← hPB, place_home_size]
    simpa [bA, mulAimed, strip, b0, bumpOp] using hSpHome
  have hHeld6 : bS.sudo_5Board_4held[6] = true := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  have hHome6 : bS.sudo_5Board_4home[6] = embed ys := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  conv =>
    lhs
    rw [← ofNat_eq_natCast 6, atL_ofNat _ 6 h6, hHeld6]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ 6 h6h, hHome6, ok_bind]
  conv =>
    lhs
    rw [putL_ofNat _ 6 false h6, ok_bind, putL_ofNat _ 6 (#[] : Array Int) h6h, ok_bind]
  conv =>
    lhs
    rw [show b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
      simp [b0, bumpOp, hn, ofNat_eq_natCast]]
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  conv =>
    lhs
    rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  conv =>
    lhs
    rw [hfuel]
  generalize hBLdef :
    { {bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false} with
      sudo_5Board_4home :=
        ({bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false}).sudo_5Board_4home.set
          ⟨6, h6h⟩ #[] } = bL
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    rw [← hBLdef]
    simp only [bS, strictBoard]
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rfl
  conv =>
    lhs
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) (moves + pegCount ys) n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]
  have hLoop : bL = mulCopyLoop b0 ((dst : Nat) : Int) strip ys moves peak peakS hH hD := by
    rw [← hBLdef]
    subst hPB
    simp only [bS]
    unfold mulCopyLoop
    rfl
  rw [hLoop]

/-- Op bump of the marker-off feed, with the flag put back on. -/
def copyUpBoard (b : Ecbs.Board) (m ctrl mx cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) : Ecbs.Board :=
  { bumpOp (markerUpFeed b m ctrl mx) 0 cOps (by simpa [markerUpFeed] using hops) with
      sudo_5Board_9marker_on := true }

/-- Op bump after seating a lifted marker, with the flag put back on. -/
def copyDownBoard (b : Ecbs.Board) (ctrl mx cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) : Ecbs.Board :=
  { bumpOp (markerDownFeed b ctrl mx) 0 cOps (by simpa [markerDownFeed] using hops) with
      sudo_5Board_9marker_on := true }

/-- Marker seated, bench off. The emitted copy multiply is the schoolbook on
    the board `marker_step` leaves. -/
theorem mul_copy_up_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitCtrl : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitC : FitsLen (moves + pegCount ys))
    (hH : 6 < (mulAimed (copyUpBoard b m ctrl mx cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed (copyUpBoard b m ctrl mx cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4held.size) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulCopyLoop (copyUpBoard b m ctrl mx cOps hops) ((dst : Nat) : Int)
              (embed (List.replicate bench 0)) ys moves peak peakS hH hD)
            (Int.ofNat (moves + pegCount ys + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, if_true, pure_eq_ok, toPure_eq_ok, ok_bind]
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by
    simpa [bumpOp] using hm
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hscript
  rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitM hfitCtrl hfit2]
  rw [← mul_up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [markerUpFeed] using hops
  let b0 := { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true }
  rw [settle_off b0 (by simp [b0, copyUpBoard, bumpOp, feed, markerUpFeed, hoff])]
  simp only [ok_bind, pure_eq_ok]
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, copyUpBoard, bumpOp, feed, markerUpFeed, hbl]
  conv =>
    lhs
    rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [show b0.sudo_5Board_4held = b.sudo_5Board_4held from by simp [b0, copyUpBoard, bumpOp, feed, markerUpFeed],
        show b0.sudo_5Board_4home = b.sudo_5Board_4home from by simp [b0, copyUpBoard, bumpOp, feed, markerUpFeed]]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ first hHome, hArr, ok_bind]
  conv =>
    lhs
    rw [spare_beq_false second hneS]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  have hcopy := copy_band_refines bA 6 second ys moves peak hH hD
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hHomeS)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hS)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using h7)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hHS)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hYs)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hSpE)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed, hleny] using hn)
    (by rw [hleny]; exact hf)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hmoves)
    (by simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hpeak)
    hfitC
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.spare ((second : Nat) : Int) false)
    change Ecbs.copy_band bA Ecbs.spare ((second : Nat) : Int) false
  rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hcopy]
  simp only [ok_bind, pure_eq_ok]
  conv =>
    lhs
    rw [spare_neq_first first hneF]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  generalize hPB : placeBoard bA 6 hH hD ys moves peak = bP
  have h7b : 7 ≤ bP.sudo_5Board_4held.size := by
    rw [← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using h7
  have hpB : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed, hpeakS]
  rw [note_strict_eq bP peakS h7b hpB]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bP peakS
  have h6 : 6 < bS.sudo_5Board_4held.size := by
    rw [strict_held, ← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hSpH
  have h6h : 6 < bS.sudo_5Board_4home.size := by
    rw [strict_home, ← hPB, place_home_size]
    simpa [bA, mulAimed, strip, b0, copyUpBoard, bumpOp, feed, markerUpFeed] using hSpHome
  have hHeld6 : bS.sudo_5Board_4held[6] = true := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  have hHome6 : bS.sudo_5Board_4home[6] = embed ys := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  conv =>
    lhs
    rw [← ofNat_eq_natCast 6, atL_ofNat _ 6 h6, hHeld6]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ 6 h6h, hHome6, ok_bind]
  conv =>
    lhs
    rw [putL_ofNat _ 6 false h6, ok_bind, putL_ofNat _ 6 (#[] : Array Int) h6h, ok_bind]
  conv =>
    lhs
    rw [show b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
      simp [b0, copyUpBoard, bumpOp, feed, markerUpFeed, hn, ofNat_eq_natCast]]
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  conv =>
    lhs
    rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  conv =>
    lhs
    rw [hfuel]
  generalize hBLdef :
    { {bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false} with
      sudo_5Board_4home :=
        ({bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false}).sudo_5Board_4home.set
          ⟨6, h6h⟩ #[] } = bL
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    rw [← hBLdef]
    simp only [bS, strictBoard]
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rfl
  conv =>
    lhs
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) (moves + pegCount ys) n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]
  have hLoop : bL = mulCopyLoop b0 ((dst : Nat) : Int) strip ys moves peak peakS hH hD := by
    rw [← hBLdef]
    subst hPB
    simp only [bS]
    unfold mulCopyLoop
    rfl
  have hb0 : b0 = copyUpBoard b m ctrl mx cOps hops := by
    simp [b0, feed, hopsF, copyUpBoard]
  rw [hLoop]
  simp only [hb0, strip]

/-- Marker lifted, bench off. The emitted copy multiply is the schoolbook on
    the board that seats the marker. -/
theorem mul_copy_down_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peak peakS cOps ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitD : FitsLen (ctrl + 1))
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitC : FitsLen (moves + pegCount ys))
    (hH : 6 < (mulAimed (copyDownBoard b ctrl mx cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4home.size)
    (hD : 6 < (mulAimed (copyDownBoard b ctrl mx cOps hops) ((dst : Nat) : Int)
      (embed (List.replicate bench 0))).sudo_5Board_4held.size) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulCopyLoop (copyDownBoard b ctrl mx cOps hops) ((dst : Nat) : Int)
              (embed (List.replicate bench 0)) ys moves peak peakS hH hD)
            (Int.ofNat (moves + pegCount ys + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, if_true, pure_eq_ok, toPure_eq_ok, ok_bind]
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker < 0 := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hscript
  rw [marker_step_down (bumpOp b 0 cOps hops) ctrl mx script hmB hcB hxB hsB hpos hfitD]
  rw [← mul_down_bump b ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let feed := markerDownFeed b ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [markerDownFeed] using hops
  let b0 := { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true }
  rw [settle_off b0 (by simp [b0, copyDownBoard, bumpOp, feed, markerDownFeed, hoff])]
  simp only [ok_bind, pure_eq_ok]
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, copyDownBoard, bumpOp, feed, markerDownFeed, hbl]
  conv =>
    lhs
    rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [show b0.sudo_5Board_4held = b.sudo_5Board_4held from by simp [b0, copyDownBoard, bumpOp, feed, markerDownFeed],
        show b0.sudo_5Board_4home = b.sudo_5Board_4home from by simp [b0, copyDownBoard, bumpOp, feed, markerDownFeed]]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ first hHome, hArr, ok_bind]
  conv =>
    lhs
    rw [spare_beq_false second hneS]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  have hcopy := copy_band_refines bA 6 second ys moves peak hH hD
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hHomeS)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hS)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using h7)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hHS)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hYs)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hSpE)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed, hleny] using hn)
    (by rw [hleny]; exact hf)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hmoves)
    (by simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hpeak)
    hfitC
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.spare ((second : Nat) : Int) false)
    change Ecbs.copy_band bA Ecbs.spare ((second : Nat) : Int) false
  rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hcopy]
  simp only [ok_bind, pure_eq_ok]
  conv =>
    lhs
    rw [spare_neq_first first hneF]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  generalize hPB : placeBoard bA 6 hH hD ys moves peak = bP
  have h7b : 7 ≤ bP.sudo_5Board_4held.size := by
    rw [← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using h7
  have hpB : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed, hpeakS]
  rw [note_strict_eq bP peakS h7b hpB]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bP peakS
  have h6 : 6 < bS.sudo_5Board_4held.size := by
    rw [strict_held, ← hPB, place_held_size]
    simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hSpH
  have h6h : 6 < bS.sudo_5Board_4home.size := by
    rw [strict_home, ← hPB, place_home_size]
    simpa [bA, mulAimed, strip, b0, copyDownBoard, bumpOp, feed, markerDownFeed] using hSpHome
  have hHeld6 : bS.sudo_5Board_4held[6] = true := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  have hHome6 : bS.sudo_5Board_4home[6] = embed ys := by
    simp only [bS, strictBoard, ← hPB]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.getElem_set]
  conv =>
    lhs
    rw [← ofNat_eq_natCast 6, atL_ofNat _ 6 h6, hHeld6]
  simp only [sudoAssert_true, ok_bind]
  conv =>
    lhs
    rw [atL_ofNat _ 6 h6h, hHome6, ok_bind]
  conv =>
    lhs
    rw [putL_ofNat _ 6 false h6, ok_bind, putL_ofNat _ 6 (#[] : Array Int) h6h, ok_bind]
  conv =>
    lhs
    rw [show b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
      simp [b0, copyDownBoard, bumpOp, feed, markerDownFeed, hn, ofNat_eq_natCast]]
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    lhs
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  conv =>
    lhs
    rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  conv =>
    lhs
    rw [hfuel]
  generalize hBLdef :
    { {bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false} with
      sudo_5Board_4home :=
        ({bS with sudo_5Board_4held := bS.sudo_5Board_4held.set ⟨6, h6⟩ false}).sudo_5Board_4home.set
          ⟨6, h6h⟩ #[] } = bL
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) := by
    rw [← hBLdef]
    simp only [bS, strictBoard]
    rw [← hPB]
    unfold placeBoard
    dsimp only
    split <;> rfl
  conv =>
    lhs
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) (moves + pegCount ys) n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]
  have hLoop : bL = mulCopyLoop b0 ((dst : Nat) : Int) strip ys moves peak peakS hH hD := by
    rw [← hBLdef]
    subst hPB
    simp only [bS]
    unfold mulCopyLoop
    rfl
  have hb0 : b0 = copyDownBoard b ctrl mx cOps hops := by
    simp [b0, feed, hopsF, copyDownBoard]
  rw [hLoop]
  simp only [hb0, strip]

end EcbsLink2.Link2
