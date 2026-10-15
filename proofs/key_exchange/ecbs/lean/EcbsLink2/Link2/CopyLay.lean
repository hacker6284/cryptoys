/-
  The marker-off board `chordCopyAddGo` leaves. The bottom is the run, the gap
  and the spare are still empty, and the control frame is the painted ladder.
  That board is `OpenLay`. A climb budget on those counters is `OpenMatch`,
  so `open_checked` can read the run. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordIf
import EcbsLink2.Link2.InvertWalk

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves after copying the base across and subtracting the accumulator across. -/
def runMoves (moves : Nat) (baseX accX : List Nat) : Nat :=
  moves + pegCount baseX + pegCount accX

private theorem tritAdd_le (a b : Nat) : tritAdd a b ≤ 2 := by
  have : (a + b) % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold tritAdd
  omega

private theorem fieldSub_trits (n : Nat) (xs ys : List Nat) :
    allTritList (fieldSub n xs ys) := by
  intro z hz
  rw [fieldSub, fieldAdd] at hz
  rcases List.mem_map.mp hz with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

/-- `bumpOp` writes one ops cell. The frame `OpenLay` reads is unchanged. -/
private theorem bumpKeep (b : Ecbs.Board) (i c : Nat)
    (h : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let bB := bumpOp b i c h
    bB.sudo_5Board_1t = b.sudo_5Board_1t ∧
    bB.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
    bB.sudo_5Board_3row = b.sudo_5Board_3row ∧
    bB.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
    bB.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    bB.sudo_5Board_6ladder = b.sudo_5Board_6ladder ∧
    bB.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    bB.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    bB.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
    bB.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from ∧
    bB.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx ∧
    bB.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    bB.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    bB.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    bB.sudo_5Board_4cost.sudo_5Costs_9tally_max = b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    bB.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    bB.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold bumpOp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `add` writes the destination home and the move counter. -/
private theorem addKeep (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    let bA := addBoard b home hH arr mv
    bA.sudo_5Board_4held = b.sudo_5Board_4held ∧
    bA.sudo_5Board_1t = b.sudo_5Board_1t ∧
    bA.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
    bA.sudo_5Board_3row = b.sudo_5Board_3row ∧
    bA.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
    bA.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    bA.sudo_5Board_6ladder = b.sudo_5Board_6ladder ∧
    bA.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    bA.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    bA.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
    bA.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from ∧
    bA.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx ∧
    bA.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    bA.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
    bA.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    bA.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    bA.sudo_5Board_4cost.sudo_5Costs_9tally_max = b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    bA.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
    bA.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
    bA.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    bA.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hH⟩ arr := by
  unfold addBoard withMoves
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Holding the marker off touches only that flag. -/
private theorem addIx (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold addBoard withMoves
  rfl

private theorem addMx (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold addBoard withMoves
  rfl

private theorem bumpIx (b : Ecbs.Board) (i c : Nat)
    (h : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i c h).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold bumpOp
  rfl

private theorem bumpMx (b : Ecbs.Board) (i c : Nat)
    (h : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i c h).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold bumpOp
  rfl

private theorem offKeep (b : Ecbs.Board) :
    let b' := { b with sudo_5Board_9marker_on := false }
    b'.sudo_5Board_9marker_on = false ∧
    b'.sudo_5Board_4home = b.sudo_5Board_4home ∧
    b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
    b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
    b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
    b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
    b'.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder ∧
    b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    b'.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
    b'.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from ∧
    b'.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx ∧
    b'.sudo_5Board_4cost = b.sudo_5Board_4cost := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Slot 3 grows by one. Slot 2 still has room for the inverse bump, and every
    other slot keeps the room it had. -/
private theorem ops_chord_cap (ops : Array Int) (c0 cap : Nat)
    (h3 : 3 < ops.size)
    (hc : ops[3]'h3 = Int.ofNat c0)
    (h : ∀ i (hi : i < ops.size), ∃ c,
      ops[i]'hi = Int.ofNat c ∧
        (if i = 2 then c + 1 else if i = 3 then c + 1 else c) ≤ cap) :
    ∀ i (hi : i < (ops.set ⟨3, h3⟩ (Int.ofNat (c0 + 1))).size),
      ∃ c,
        (ops.set ⟨3, h3⟩ (Int.ofNat (c0 + 1)))[i]'hi = Int.ofNat c ∧
          (if i = 2 then c + 1 else c) ≤ cap := by
  intro i hi
  have hi0 : i < ops.size := by
    rw [Array.size_set] at hi
    exact hi
  obtain ⟨c, hval, hle⟩ := h i hi0
  by_cases h3i : i = 3
  · subst h3i
    have hget := Array.getElem_set_eq ops ⟨3, h3⟩ (Int.ofNat (c0 + 1)) rfl hi
    have hc0 : c = c0 := by
      apply Int.ofNat.inj
      exact hval.symm.trans (idx_irrel.trans hc)
    refine ⟨c0 + 1, hget, ?_⟩
    have hle' : c + 1 ≤ cap := by simpa using hle
    rw [hc0] at hle'
    simpa using hle'
  · have hne : (3 : Nat) ≠ i := fun h => h3i h.symm
    have hget := Array.getElem_set_ne ops ⟨3, h3⟩ (Int.ofNat (c0 + 1)) hi hne
    refine ⟨c, hget.trans (idx_irrel.trans hval), ?_⟩
    by_cases h2 : i = 2
    · subst h2
      simpa using hle
    · simpa [h2, h3i] using hle

/-- What `chordCopyAddGo` reads off a walk board. Home 2 is empty, homes 0 and 3
    hold the two across lists, and the control frame is still the painted ladder.
    The marker flag is not part of this frame: the copy does not read it. -/
structure RunFrame (b : Ecbs.Board) (t : Spec.Tier) (baseX accX : List Nat) where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  bench : b.sudo_5Board_8bench_on = false
  held5 : b.sudo_5Board_4held[5]'(by rw [szD]; decide) = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  held2 : b.sudo_5Board_4held[2]'(by rw [szD]; decide) = false
  held0 : b.sudo_5Board_4held[0]'(by rw [szD]; decide) = true
  home0 : b.sudo_5Board_4home[0]'(by rw [szH]; decide) = embed accX
  held3 : b.sudo_5Board_4held[3]'(by rw [szD]; decide) = true
  home3 : b.sudo_5Board_4home[3]'(by rw [szH]; decide) = embed baseX
  /-- Homes 1 and 4, which the copy does not write. Home 0 is the accumulator. -/
  y1 : List Nat
  y4 : List Nat
  flag1 : Bool
  flag4 : Bool
  home1 : b.sudo_5Board_4home[1]'(by rw [szH]; decide) = embed y1
  held1 : b.sudo_5Board_4held[1]'(by rw [szD]; decide) = flag1
  home4 : b.sudo_5Board_4home[4]'(by rw [szH]; decide) = embed y4
  held4 : b.sudo_5Board_4held[4]'(by rw [szD]; decide) = flag4
  mark : Nat
  mx : Nat
  hmark : b.sudo_5Board_6marker = Int.ofNat mark
  hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  lenX : baseX.length = t.n
  lenA : accX.length = t.n
  triX : allTritList baseX
  triA : allTritList accX
  tier : b.sudo_5Board_1t = embTier t
  moves : Nat
  slides : Nat
  peak : Nat
  ctrl : Nat
  high : Nat
  cOps : Nat
  chordOps : Nat
  opsCap : Nat
  peakS : Nat
  hole : Nat
  hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak
  hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = Int.ofNat high
  highLt : high < tallyOrigin t
  htally : b.sudo_5Board_9tally_len = 0
  ht0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  hrow : b.sudo_5Board_3row = embed (paintedRow t)
  htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0
  hlad : b.sudo_5Board_6ladder = embed (tierClimb t)
  hl0 : b.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2)
  hnr : b.sudo_5Board_6nrungs = Int.ofNat (tierR t)
  hpark : b.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t)
  hfrom : b.sudo_5Board_11parked_from = -1
  hridx : b.sudo_5Board_8rung_idx = 0
  hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS
  hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  ops2 : 2 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop2 : b.sudo_5Board_4cost.sudo_5Costs_3ops[2]'ops2 = Int.ofNat cOps
  hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'ops3 = Int.ofNat chordOps
  fitInv : FitsLen (cOps + 1)
  fitChord : FitsLen (chordOps + 1)
  fitCtrl : FitsLen (ctrl + 1)
  /-- The two across copies and the gap copy `invert` does next. A length-`n`
      home has at most `n` pegs, so `3 · n` covers all three. -/
  fitRoom : FitsLen (moves + 3 * t.n)
  opsRoom : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ c, b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = Int.ofNat c ∧
      (if i = 2 then c + 1 else if i = 3 then c + 1 else c) ≤ opsCap

/-- Placing at home 2, then adding at home 2, leaves every other home. -/
private theorem copy_side_home
    (b bB b1 bOff : Ecbs.Board) (baseX : List Nat) (arr : Array Int)
    (hin : HomeIn bB 2) (h2H1 : 2 < b1.sudo_5Board_4home.size)
    (hhomeB : bB.sudo_5Board_4home = b.sudo_5Board_4home)
    (hszHB : bB.sudo_5Board_4home.size = 8)
    (hszH1 : b1.sudo_5Board_4home.size = 8)
    (hplace : b1.sudo_5Board_4home =
      bB.sudo_5Board_4home.set ⟨2, hin.hH⟩ (embed baseX))
    (hadd : bOff.sudo_5Board_4home = b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr)
    (i : Nat) (hne : (2 : Nat) ≠ i) {hiB : i < b.sudo_5Board_4home.size} {v : Array Int}
    (hv : b.sudo_5Board_4home[i]'hiB = v)
    (hOff : i < bOff.sudo_5Board_4home.size) :
    bOff.sudo_5Board_4home[i]'hOff = v := by
  have hneF : (⟨2, hin.hH⟩ : Fin _).1 ≠ i := hne
  have hi8 : i < 8 := by rw [← hhomeB, hszHB] at hiB; exact hiB
  have hsz1 : i < (bB.sudo_5Board_4home.set ⟨2, hin.hH⟩ (embed baseX)).size := by
    rw [Array.size_set, hszHB]; exact hi8
  have hget1 := Array.getElem_set_ne bB.sudo_5Board_4home ⟨2, hin.hH⟩
    (embed baseX) hsz1 hneF
  have hB : bB.sudo_5Board_4home[i]'(by rw [hszHB]; exact hi8) = v :=
    cell_eq_of hhomeB hv
  have h1 : b1.sudo_5Board_4home[i]'(by rw [hszH1]; exact hi8) = v :=
    (cell_eq_of hplace hget1).trans (idx_irrel.trans hB)
  have hneA : (⟨2, h2H1⟩ : Fin _).1 ≠ i := hne
  have hszA : i < (b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr).size := by
    rw [Array.size_set, hszH1]; exact hi8
  have hgetA := Array.getElem_set_ne b1.sudo_5Board_4home ⟨2, h2H1⟩ arr hszA hneA
  exact cell_eq_of hadd (hgetA.trans (idx_irrel.trans h1))

/-- The same for held flags. `add` does not write them; `place` writes home 2. -/
private theorem copy_side_held
    (b bB b1 bOff : Ecbs.Board) (hin : HomeIn bB 2)
    (hheldB : bB.sudo_5Board_4held = b.sudo_5Board_4held)
    (hszDB : bB.sudo_5Board_4held.size = 8)
    (hszD1 : b1.sudo_5Board_4held.size = 8)
    (hplace : b1.sudo_5Board_4held = bB.sudo_5Board_4held.set ⟨2, hin.hD⟩ true)
    (hadd : bOff.sudo_5Board_4held = b1.sudo_5Board_4held)
    (i : Nat) (hne : (2 : Nat) ≠ i) {hiB : i < b.sudo_5Board_4held.size} {v : Bool}
    (hv : b.sudo_5Board_4held[i]'hiB = v)
    (hOff : i < bOff.sudo_5Board_4held.size) :
    bOff.sudo_5Board_4held[i]'hOff = v := by
  have hneF : (⟨2, hin.hD⟩ : Fin _).1 ≠ i := hne
  have hi8 : i < 8 := by rw [← hheldB, hszDB] at hiB; exact hiB
  have hsz1 : i < (bB.sudo_5Board_4held.set ⟨2, hin.hD⟩ true).size := by
    rw [Array.size_set, hszDB]; exact hi8
  have hget1 := Array.getElem_set_ne bB.sudo_5Board_4held ⟨2, hin.hD⟩ true hsz1 hneF
  have hB : bB.sudo_5Board_4held[i]'(by rw [hszDB]; exact hi8) = v :=
    cell_eq_of hheldB hv
  have h1 : b1.sudo_5Board_4held[i]'(by rw [hszD1]; exact hi8) = v :=
    (cell_eq_of hplace hget1).trans (idx_irrel.trans hB)
  exact cell_eq_of hadd h1

/-- `chordCopyAddGo`, with the marker held off, is `OpenLay` for the run.
    The counters after that copy, plus the climb room, are `OpenMatch`. -/
private theorem finish_copy
    (b : Ecbs.Board) (t : Spec.Tier) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX) (hOk : BoardOk t) (sat : TierSat t)
    (hM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t)))
    (hS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t)))
    (hO : FitsLen (fr.opsCap + tierR t * (rowRoom t + 3)))
    (hTailM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen))
    (hTailS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t) +
      2 * t.n))
    (hCheck : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
      3 * (t.benchlen - t.n) + 2 * t.n))
    (hCtrl : FitsLen ((fr.ctrl + 1) + (tierR t + 1) * (3 * rowRoom t + 5)))
    (xs : List Nat) (bA bOff bB b1 : Ecbs.Board) (arr : Array Int) (mv pk : Nat)
    (hinB : HomeIn bB 2) (h2H1 : 2 < b1.sudo_5Board_4home.size)
    (hdo : chordCopyAddGo b = .ok bA)
    (hhomeB : bB.sudo_5Board_4home = b.sudo_5Board_4home)
    (hszHB : bB.sudo_5Board_4home.size = 8)
    (hszH1 : b1.sudo_5Board_4home.size = 8)
    (hplaceH : b1.sudo_5Board_4home =
      bB.sudo_5Board_4home.set ⟨2, hinB.hH⟩ (embed baseX))
    (hhomeOff : bOff.sudo_5Board_4home = b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr)
    (hheldB : bB.sudo_5Board_4held = b.sudo_5Board_4held)
    (hszDB : bB.sudo_5Board_4held.size = 8)
    (hszD1 : b1.sudo_5Board_4held.size = 8)
    (hplaceD : b1.sudo_5Board_4held = bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true)
    (hheldBA : bOff.sudo_5Board_4held = b1.sudo_5Board_4held)
    (hszHOff : bOff.sudo_5Board_4home.size = 8)
    (hszDOff : bOff.sudo_5Board_4held.size = 8)
    (hmkO : bOff.sudo_5Board_9marker_on = false)
    (hbenchOff : bOff.sudo_5Board_8bench_on = false)
    (hheld2 : bOff.sudo_5Board_4held[2]'(by rw [hszDOff]; decide) = true)
    (hhome2 : bOff.sudo_5Board_4home[2]'(by rw [hszHOff]; decide) = embed xs)
    (hheld5 : bOff.sudo_5Board_4held[5]'(by rw [hszDOff]; decide) = false)
    (hheld6 : bOff.sudo_5Board_4held[6]'(by rw [hszDOff]; decide) = false)
    (htierOff : bOff.sudo_5Board_1t = embTier t)
    (hmovesOff : bOff.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hslidesOff : bOff.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat fr.slides)
    (hpkOff : bOff.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hctrlOff : bOff.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat fr.ctrl)
    (hhighOff : bOff.sudo_5Board_4cost.sudo_5Costs_15control_highest = Int.ofNat fr.high)
    (htallyOff : bOff.sudo_5Board_9tally_len = 0)
    (ht0Off : bOff.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t))
    (hrowOff : bOff.sudo_5Board_3row = embed (paintedRow t))
    (htmaxOff : bOff.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0)
    (hladOff : bOff.sudo_5Board_6ladder = embed (tierClimb t))
    (hl0Off : bOff.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2))
    (hnrOff : bOff.sudo_5Board_6nrungs = Int.ofNat (tierR t))
    (hparkOff : bOff.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t))
    (hfromOff : bOff.sudo_5Board_11parked_from = -1)
    (hridxOff : bOff.sudo_5Board_8rung_idx = 0)
    (hstrictOff : bOff.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat fr.peakS)
    (hholeOff : bOff.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat fr.hole)
    (hopsEq : bOff.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, fr.ops3⟩ (Int.ofNat (fr.chordOps + 1)))
    (hops2Off : 2 < bOff.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hhop2 : bOff.sudo_5Board_4cost.sudo_5Costs_3ops[2]'hops2Off = Int.ofNat fr.cOps)
    (hmarkOff : bOff.sudo_5Board_6marker = Int.ofNat fr.mark)
    (hmxOff : bOff.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat fr.mx)
    (hfitCopy : FitsLen (mv + pegCount xs))
    (hxsDef : xs = fieldSub t.n baseX accX)
    (hmvEq : mv = runMoves fr.moves baseX accX)
    (hbOff : bOff = { bA with sudo_5Board_9marker_on := false })
    (hflag : bA.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on) :
    ∃ bA,
      chordCopyAddGo b = .ok bA ∧
      bA.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      ∃ (lay : OpenLay { bA with sudo_5Board_9marker_on := false } t xs)
        (base : ClimbBudget),
        OpenMatch lay base ∧
        lay.moves = runMoves fr.moves baseX accX ∧
        lay.slides = fr.slides ∧
        lay.ctrl = fr.ctrl ∧
        lay.cOps = fr.cOps ∧
        lay.opsCap = fr.opsCap ∧
        lay.mark = fr.mark ∧
        lay.mx = fr.mx ∧
        lay.side1 = fr.y1 ∧
        lay.flag1 = fr.flag1 ∧
        lay.side4 = fr.y4 ∧
        lay.flag4 = fr.flag4 ∧
        lay.side0 = accX ∧
        lay.flag0 = true := by
  have h0HOff : 0 < bOff.sudo_5Board_4home.size := by rw [hszHOff]; decide
  have h0DOff : 0 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have h1HOff : 1 < bOff.sudo_5Board_4home.size := by rw [hszHOff]; decide
  have h1DOff : 1 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have h4HOff : 4 < bOff.sudo_5Board_4home.size := by rw [hszHOff]; decide
  have h4DOff : 4 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have hside0 : bOff.sudo_5Board_4home[0]'h0HOff = embed accX :=
    copy_side_home b bB b1 bOff baseX arr hinB h2H1 hhomeB hszHB hszH1 hplaceH
      hhomeOff 0 (by decide) fr.home0 h0HOff
  have hflag0 : bOff.sudo_5Board_4held[0]'h0DOff = true :=
    copy_side_held b bB b1 bOff hinB hheldB hszDB hszD1 hplaceD hheldBA
      0 (by decide) fr.held0 h0DOff
  have hside1 : bOff.sudo_5Board_4home[1]'h1HOff = embed fr.y1 :=
    copy_side_home b bB b1 bOff baseX arr hinB h2H1 hhomeB hszHB hszH1 hplaceH
      hhomeOff 1 (by decide) fr.home1 h1HOff
  have hflag1 : bOff.sudo_5Board_4held[1]'h1DOff = fr.flag1 :=
    copy_side_held b bB b1 bOff hinB hheldB hszDB hszD1 hplaceD hheldBA
      1 (by decide) fr.held1 h1DOff
  have hside4 : bOff.sudo_5Board_4home[4]'h4HOff = embed fr.y4 :=
    copy_side_home b bB b1 bOff baseX arr hinB h2H1 hhomeB hszHB hszH1 hplaceH
      hhomeOff 4 (by decide) fr.home4 h4HOff
  have hflag4 : bOff.sudo_5Board_4held[4]'h4DOff = fr.flag4 :=
    copy_side_held b bB b1 bOff hinB hheldB hszDB hszD1 hplaceD hheldBA
      4 (by decide) fr.held4 h4DOff
  let lay : OpenLay bOff t xs :=
    { szH := hszHOff
      szD := hszDOff
      marker := hmkO
      bench := hbenchOff
      held2 := idx_irrel.trans hheld2
      home2 := idx_irrel.trans hhome2
      held5 := idx_irrel.trans hheld5
      held6 := idx_irrel.trans hheld6
      side0 := accX
      side1 := fr.y1
      side4 := fr.y4
      flag0 := true
      flag1 := fr.flag1
      flag4 := fr.flag4
      home0 := idx_irrel.trans hside0
      held0 := idx_irrel.trans hflag0
      home1 := idx_irrel.trans hside1
      held1 := idx_irrel.trans hflag1
      home4 := idx_irrel.trans hside4
      held4 := idx_irrel.trans hflag4
      mark := fr.mark
      mx := fr.mx
      hmark := hmarkOff
      hmx := hmxOff
      len := by rw [hxsDef]; exact fieldSub_length t.n baseX accX
      tri := by rw [hxsDef]; exact fieldSub_trits t.n baseX accX
      tier := htierOff
      moves := mv
      slides := fr.slides
      peak := pk
      ctrl := fr.ctrl
      high := fr.high
      cOps := fr.cOps
      opsCap := fr.opsCap
      peakS := fr.peakS
      hole := fr.hole
      hmoves := hmovesOff
      hslides := hslidesOff
      hpeak := hpkOff
      hctrl := hctrlOff
      hhigh := hhighOff
      highLt := fr.highLt
      htally := htallyOff
      ht0 := ht0Off
      hrow := hrowOff
      htmax := htmaxOff
      hlad := hladOff
      hl0 := hl0Off
      hnr := hnrOff
      hpark := hparkOff
      hfrom := hfromOff
      hridx := hridxOff
      hstrict := hstrictOff
      hhole := hholeOff
      ops2 := hops2Off
      hop2 := idx_irrel.trans hhop2
      fitOps := fr.fitInv
      fitCopy := hfitCopy
      fitCtrl := fr.fitCtrl
      opsAll := by
        intro i hi
        have hi' : i < (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, fr.ops3⟩
            (Int.ofNat (fr.chordOps + 1))).size := by
          rw [← hopsEq]; exact hi
        obtain ⟨c, hc, hle⟩ := ops_chord_cap b.sudo_5Board_4cost.sudo_5Costs_3ops
          fr.chordOps fr.opsCap fr.ops3 fr.hop3 fr.opsRoom i hi'
        exact ⟨c, cell_eq_of hopsEq hc, hle⟩ }
  let baseB : ClimbBudget :=
    { n := t.n
      bench := t.benchlen
      moves0 := mv + pegCount xs
      slides0 := fr.slides
      ops0 := fr.opsCap
      peak0 := raisedPeak pk
        (countHeld (bOff.sudo_5Board_4held.set ⟨5, by rw [lay.szD]; decide⟩ true) 7)
      tally0 := 1
      R := tierR t
      mMax := rowRoom t
      mMax_le := by simpa [geomCap] using sat.room_le_geom
      fitM := by rw [hmvEq, hxsDef]; exact hM
      fitS := hS
      fitO := hO
      fitTailM := by rw [hmvEq, hxsDef]; exact hTailM
      fitTailS := hTailS
      fitCheckM := by rw [hmvEq, hxsDef]; exact hCheck
      ctrl0 := fr.ctrl + 1
      fitCtrl := hCtrl
      x := xs
      xHome := 2
      w := t.w
      h := t.h
      r := t.r
      cg := t.combgap
      control := t.control
      fitControl := fits_of hOk.fits_control
      ladder0 := t.script + 2
      side0 := accX
      side1 := fr.y1
      side4 := fr.y4
      held0 := true
      held1 := fr.flag1
      held4 := fr.flag4
      tierSnap := embTier t
      markSnap := Int.ofNat fr.mark
      mxSnap := Int.ofNat fr.mx }
  have hmatch : OpenMatch lay baseB := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply congrArg (fun occ => raisedPeak lay.peak occ)
    apply countHeld_congr
    apply congrArg (fun i => bOff.sudo_5Board_4held.set i true)
    exact Fin.ext rfl
  cases hbOff
  exact ⟨bA, hdo, hflag, lay, baseB, hmatch, hmvEq, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem copy_add_open (b : Ecbs.Board) (t : Spec.Tier) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX) (hOk : BoardOk t) (sat : TierSat t)
    (hM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t)))
    (hS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t)))
    (hO : FitsLen (fr.opsCap + tierR t * (rowRoom t + 3)))
    (hTailM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen))
    (hTailS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t) +
      2 * t.n))
    (hCheck : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
      3 * (t.benchlen - t.n) + 2 * t.n))
    (hCtrl : FitsLen ((fr.ctrl + 1) + (tierR t + 1) * (3 * rowRoom t + 5))) :
    ∃ bA,
      chordCopyAddGo b = .ok bA ∧
      bA.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      ∃ (lay : OpenLay { bA with sudo_5Board_9marker_on := false } t
          (fieldSub t.n baseX accX))
        (base : ClimbBudget),
        OpenMatch lay base ∧
        lay.moves = runMoves fr.moves baseX accX ∧
        lay.slides = fr.slides ∧
        lay.ctrl = fr.ctrl ∧
        lay.cOps = fr.cOps ∧
        lay.opsCap = fr.opsCap ∧
        lay.mark = fr.mark ∧
        lay.mx = fr.mx ∧
        lay.side1 = fr.y1 ∧
        lay.flag1 = fr.flag1 ∧
        lay.side4 = fr.y4 ∧
        lay.flag4 = fr.flag4 ∧
        lay.side0 = accX ∧
        lay.flag0 = true := by
  let xs := fieldSub t.n baseX accX
  have hpos : 0 < t.n := hOk.n_pos
  have hpegB : pegCount baseX ≤ t.n := by rw [← fr.lenX]; exact pegCount_le baseX
  have hpegA : pegCount accX ≤ t.n := by rw [← fr.lenA]; exact pegCount_le accX
  have hfitn : FitsLen t.n := FitsLen.of_le fr.fitRoom (by omega)
  have hfitC : FitsLen (fr.moves + pegCount baseX) :=
    FitsLen.of_le fr.fitRoom (by omega)
  have hfitA : FitsLen (fr.moves + pegCount baseX + t.n) :=
    FitsLen.of_le fr.fitRoom (by omega)
  let bB := bumpOp b 3 fr.chordOps fr.ops3
  have hszHB : bB.sudo_5Board_4home.size = 8 := by
    rw [show bB.sudo_5Board_4home = b.sudo_5Board_4home from rfl, fr.szH]
  have hszDB : bB.sudo_5Board_4held.size = 8 := by
    rw [bumpOp_held b 3 fr.chordOps fr.ops3, fr.szD]
  let hinB : HomeIn bB 2 := ⟨by rw [hszHB]; decide, by rw [hszDB]; decide⟩
  have h3H : 3 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h3D : 3 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h0H : 0 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h0D : 0 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h7 : 7 ≤ bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have hheldB : bB.sudo_5Board_4held = b.sudo_5Board_4held :=
    bumpOp_held b 3 fr.chordOps fr.ops3
  have hhomeB : bB.sudo_5Board_4home = b.sudo_5Board_4home := rfl
  have h2eB : bB.sudo_5Board_4held[2]'hinB.hD = false := by
    simpa [hheldB] using fr.held2
  have h3tB : bB.sudo_5Board_4held[3]'h3D = true := by
    simpa [hheldB] using fr.held3
  have h3aB : bB.sudo_5Board_4home[3]'h3H = embed baseX := by
    simpa [hhomeB] using fr.home3
  have h0tB : bB.sudo_5Board_4held[0]'h0D = true := by
    simpa [hheldB] using fr.held0
  have h0aB : bB.sudo_5Board_4home[0]'h0H = embed accX := by
    simpa [hhomeB] using fr.home0
  have hnB : bB.sudo_5Board_1t.sudo_4Tier_1n = (baseX.length : Int) := by
    rw [show bB.sudo_5Board_1t = b.sudo_5Board_1t from rfl, fr.tier, fr.lenX]
    simp [embTier, ofNat_eq_natCast]
  have hmovesB : bB.sudo_5Board_4cost.sudo_5Costs_5moves = (fr.moves : Int) := by
    rw [bumpOp_moves b 3 fr.chordOps fr.ops3, fr.hmoves, ofNat_eq_natCast]
  have hpeakB : bB.sudo_5Board_4cost.sudo_5Costs_4peak = (fr.peak : Int) := by
    rw [bumpOp_peak b 3 fr.chordOps fr.ops3, fr.hpeak, ofNat_eq_natCast]
  have hpeakN : bB.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat fr.peak := by
    rw [bumpOp_peak b 3 fr.chordOps fr.ops3, fr.hpeak]
  have hcopy := copy_band_refines bB 2 3 baseX fr.moves fr.peak
    hinB.hH hinB.hD h3H h3D h7 h3tB h3aB h2eB hnB
    (by rw [fr.lenX]; exact hfitn) hmovesB hpeakB hfitC
  let b1 := placeBoard bB 2 hinB.hH hinB.hD baseX fr.moves fr.peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_size_home bB 2 hinB baseX fr.moves fr.peak, hszHB]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_size_held bB 2 hinB baseX fr.moves fr.peak, hszDB]
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h2D1 : 2 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h0H1 : 0 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h0D1 : 0 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hheld1 : b1.sudo_5Board_4held[2]'h2D1 = true := by
    have hsz : 2 < (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true).size := by
      rw [Array.size_set]; exact hinB.hD
    have hget := Array.getElem_set_eq bB.sudo_5Board_4held ⟨2, hinB.hD⟩ true rfl hsz
    exact cell_eq_of (place_held_out bB 2 hinB baseX fr.moves fr.peak) hget
  have hhome1 : b1.sudo_5Board_4home[2]'h2H1 = embed baseX := by
    have hsz : 2 < (bB.sudo_5Board_4home.set ⟨2, hinB.hH⟩ (embed baseX)).size := by
      rw [Array.size_set]; exact hinB.hH
    have hget := Array.getElem_set_eq bB.sudo_5Board_4home ⟨2, hinB.hH⟩
      (embed baseX) rfl hsz
    exact cell_eq_of (place_home_out bB 2 hinB baseX fr.moves fr.peak) hget
  have h0t1 : b1.sudo_5Board_4held[0]'h0D1 = true := by
    have hsz : 0 < (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true).size := by
      rw [Array.size_set]; exact h0D
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨2, hinB.hD⟩ true hsz
      (by decide : (2 : Nat) ≠ 0)
    exact (cell_eq_of (place_held_out bB 2 hinB baseX fr.moves fr.peak) hget).trans
      (idx_irrel.trans h0tB)
  have h0a1 : b1.sudo_5Board_4home[0]'h0H1 = embed accX := by
    have hsz : 0 < (bB.sudo_5Board_4home.set ⟨2, hinB.hH⟩ (embed baseX)).size := by
      rw [Array.size_set]; exact h0H
    have hget := Array.getElem_set_ne bB.sudo_5Board_4home ⟨2, hinB.hH⟩ (embed baseX) hsz
      (by decide : (2 : Nat) ≠ 0)
    exact (cell_eq_of (place_home_out bB 2 hinB baseX fr.moves fr.peak) hget).trans
      (idx_irrel.trans h0aB)
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [place_tier_eq bB 2 hinB.hH hinB.hD baseX fr.moves fr.peak]
    rw [show bB.sudo_5Board_1t = b.sudo_5Board_1t from rfl, fr.tier]
    simp [embTier, ofNat_eq_natCast]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((fr.moves + pegCount baseX : Nat) : Int) := by
    rw [place_moves_eq bB 2 hinB.hH hinB.hD baseX fr.moves fr.peak, ofNat_eq_natCast]
  let mv := runMoves fr.moves baseX accX
  let bA := addBoard b1 2 h2H1 (embed (fieldAdd t.n baseX (mirrorTrits accX))) mv
  have hadd := add_refines b1 2 0 baseX accX t.n (fr.moves + pegCount baseX)
    h2H1 h2D1 h0H1 h0D1 hheld1 hhome1 h0t1 h0a1 hn1 fr.lenA fr.lenX hpos
    fr.triX fr.triA hmoves1 hfitA
  have hmv : mv = fr.moves + pegCount baseX + pegCount accX := by
    simp [mv, runMoves]
  have hdo : chordCopyAddGo b = .ok bA := by
    unfold chordCopyAddGo
    rw [show Ecbs.op_chord = Int.ofNat 3 from rfl, atL_ofNat _ 3 fr.ops3, fr.hop3, ok_bind]
    rw [addI_ofNat_one fr.chordOps fr.fitChord, ok_bind]
    rw [putL_ofNat _ 3 (Int.ofNat (fr.chordOps + 1)) fr.ops3, ok_bind]
    have hbEq : ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops := b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, fr.ops3⟩
          (Int.ofNat (fr.chordOps + 1)) } } : Ecbs.Board) = bB := rfl
    have hrest :
        (do
          let b ← Ecbs.copy_band bB Ecbs.bottom Ecbs.base_across false
          Ecbs.add b Ecbs.bottom Ecbs.across true) = .ok bA := by
      rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
          show Ecbs.base_across = ((3 : Nat) : Int) from rfl,
          show Ecbs.across = ((0 : Nat) : Int) from rfl, hcopy, ok_bind, hadd,
          show bA = addBoard b1 2 h2H1
            (embed (fieldAdd t.n baseX (mirrorTrits accX))) mv from rfl, hmv]
    simpa [hbEq] using hrest
  rcases place_rest bB 2 hinB.hH hinB.hD baseX fr.moves fr.peak with
    ⟨htier1, _, _, _, _, _, _, _, hl01, hnr1, hpark1, ht01, hmark1, hfrom1, htlen1, _,
      hridx1, hlad1, _, hctrl1, _, _, _, _, hstrict1, hhole1, hhigh1, hmx1, htmax1, _, _,
      hops1⟩
  have hrow1 := place_row_out bB 2 hinB baseX fr.moves fr.peak
  have hslide1 := place_slides_out bB 2 hinB baseX fr.moves fr.peak
  have hon1 := place_on_out bB 2 hinB baseX fr.moves fr.peak
  have hpk1 := place_peak_out bB 2 hinB baseX fr.moves fr.peak hpeakN
  let bOff := { bA with sudo_5Board_9marker_on := false }
  let arr := embed (fieldAdd t.n baseX (mirrorTrits accX))
  obtain ⟨hheldA, htA, hbenchA, hrowA, htlenA, ht0A, hladA, hl0A, hnrA, hparkA, hfromA,
      hridxA, hslA, hpkA, hcA, hhiA, htmaxA, hstA, hhoA, hopsA, hmvA, hhomeA⟩ :=
    addKeep b1 2 h2H1 arr mv
  obtain ⟨hmkO, hhomeO, hheldO, htO, hbenchO, hrowO, htlenO, ht0O, hladO, hl0O, hnrO, hparkO,
      hfromO, hridxO, hcostO⟩ := offKeep bA
  obtain ⟨htB, hbenchB, hrowB, htlenB, ht0B, hladB, hl0B, hnrB, hparkB, hfromB, hridxB,
      hslB, hcB, hhiB, htmaxB, hstB, hhoB⟩ :=
    bumpKeep b 3 fr.chordOps fr.ops3
  have hszHOff : bOff.sudo_5Board_4home.size = 8 := by
    rw [hhomeO, hhomeA, Array.size_set, hszH1]
  have hszDOff : bOff.sudo_5Board_4held.size = 8 := by
    rw [hheldO, hheldA, hszD1]
  have h2HOff : 2 < bOff.sudo_5Board_4home.size := by rw [hszHOff]; decide
  have h2DOff : 2 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have h5DOff : 5 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have h6DOff : 6 < bOff.sudo_5Board_4held.size := by rw [hszDOff]; decide
  have hhome2 : bOff.sudo_5Board_4home[2]'h2HOff = embed xs := by
    have hset : bOff.sudo_5Board_4home = b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr :=
      hhomeO.trans hhomeA
    have hsz : 2 < (b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr).size := by
      rw [Array.size_set]; exact h2H1
    have hget := Array.getElem_set_eq b1.sudo_5Board_4home ⟨2, h2H1⟩ arr rfl hsz
    simpa [xs, fieldSub, arr] using cell_eq_of hset hget
  have hheldBA : bOff.sudo_5Board_4held = b1.sudo_5Board_4held := hheldO.trans hheldA
  have hheld2 : bOff.sudo_5Board_4held[2]'h2DOff = true :=
    cell_eq_of hheldBA hheld1
  have hheld5 : bOff.sudo_5Board_4held[5]'h5DOff = false := by
    have h5B : 5 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
    have hsz : 5 < (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true).size := by
      rw [Array.size_set]; exact h5B
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨2, hinB.hD⟩ true hsz
      (by decide : (2 : Nat) ≠ 5)
    have h1 : b1.sudo_5Board_4held[5]'(by rw [hszD1]; decide) =
        bB.sudo_5Board_4held[5]'h5B :=
      cell_eq_of (place_held_out bB 2 hinB baseX fr.moves fr.peak) hget
    have hB : bB.sudo_5Board_4held[5]'h5B = false := by
      simpa [hheldB] using fr.held5
    exact cell_eq_of hheldBA (h1.trans hB)
  have hheld6 : bOff.sudo_5Board_4held[6]'h6DOff = false := by
    have h6B : 6 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
    have hsz : 6 < (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true).size := by
      rw [Array.size_set]; exact h6B
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨2, hinB.hD⟩ true hsz
      (by decide : (2 : Nat) ≠ 6)
    have h1 : b1.sudo_5Board_4held[6]'(by rw [hszD1]; decide) =
        bB.sudo_5Board_4held[6]'h6B :=
      cell_eq_of (place_held_out bB 2 hinB baseX fr.moves fr.peak) hget
    have hB : bB.sudo_5Board_4held[6]'h6B = false := by
      simpa [hheldB] using fr.held6
    exact cell_eq_of hheldBA (h1.trans hB)
  have htierOff : bOff.sudo_5Board_1t = embTier t := by
    rw [htO, htA, htier1, htB, fr.tier]
  have hmovesOff : bOff.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    rw [congrArg (fun c => c.sudo_5Costs_5moves) hcostO, hmvA]
  have hslidesOff : bOff.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat fr.slides := by
    rw [congrArg (fun c => c.sudo_5Costs_6slides) hcostO, hslA, hslide1, hslB, fr.hslides]
  have hpkOff : bOff.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak fr.peak
        (countHeld (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true) 7)) := by
    rw [congrArg (fun c => c.sudo_5Costs_4peak) hcostO, hpkA, hpk1]
  have hctrlOff : bOff.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat fr.ctrl := by
    rw [congrArg (fun c => c.sudo_5Costs_4ctrl) hcostO, hcA, hctrl1, hcB, fr.hctrl]
  have hhighOff : bOff.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      Int.ofNat fr.high := by
    rw [congrArg (fun c => c.sudo_5Costs_15control_highest) hcostO, hhiA, hhigh1, hhiB,
      fr.hhigh]
  have htallyOff : bOff.sudo_5Board_9tally_len = 0 := by
    rw [htlenO, htlenA, htlen1, htlenB, fr.htally]
  have ht0Off : bOff.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
    rw [ht0O, ht0A, ht01, ht0B, fr.ht0]
  have hrowOff : bOff.sudo_5Board_3row = embed (paintedRow t) := by
    rw [hrowO, hrowA, hrow1, hrowB, fr.hrow]
  have htmaxOff : bOff.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0 := by
    rw [congrArg (fun c => c.sudo_5Costs_9tally_max) hcostO, htmaxA, htmax1, htmaxB, fr.htmax]
  have hladOff : bOff.sudo_5Board_6ladder = embed (tierClimb t) := by
    rw [hladO, hladA, hlad1, hladB, fr.hlad]
  have hl0Off : bOff.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) := by
    rw [hl0O, hl0A, hl01, hl0B, fr.hl0]
  have hnrOff : bOff.sudo_5Board_6nrungs = Int.ofNat (tierR t) := by
    rw [hnrO, hnrA, hnr1, hnrB, fr.hnr]
  have hparkOff : bOff.sudo_5Board_9park_hole =
      Int.ofNat (t.script + 2 + tierR t) := by
    rw [hparkO, hparkA, hpark1, hparkB, fr.hpark]
  have hfromOff : bOff.sudo_5Board_11parked_from = -1 := by
    rw [hfromO, hfromA, hfrom1, hfromB, fr.hfrom]
  have hridxOff : bOff.sudo_5Board_8rung_idx = 0 := by
    rw [hridxO, hridxA, hridx1, hridxB, fr.hridx]
  have hstrictOff : bOff.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat fr.peakS := by
    rw [congrArg (fun c => c.sudo_5Costs_11peak_strict) hcostO, hstA, hstrict1, hstB,
      fr.hstrict]
  have hholeOff : bOff.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat fr.hole := by
    rw [congrArg (fun c => c.sudo_5Costs_14max_bench_hole) hcostO, hhoA, hhole1, hhoB,
      fr.hhole]
  have hbenchOff : bOff.sudo_5Board_8bench_on = false := by
    rw [hbenchO, hbenchA, hon1, hbenchB, fr.bench]
  have hhomeOff : bOff.sudo_5Board_4home = b1.sudo_5Board_4home.set ⟨2, h2H1⟩ arr :=
    hhomeO.trans hhomeA
  have hplaceH : b1.sudo_5Board_4home =
      bB.sudo_5Board_4home.set ⟨2, hinB.hH⟩ (embed baseX) :=
    place_home_out bB 2 hinB baseX fr.moves fr.peak
  have hplaceD : b1.sudo_5Board_4held =
      bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true :=
    place_held_out bB 2 hinB baseX fr.moves fr.peak
  have hopsEq : bOff.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, fr.ops3⟩
        (Int.ofNat (fr.chordOps + 1)) := by
    rw [congrArg (fun c => c.sudo_5Costs_3ops) hcostO, hopsA, hops1]
    exact bumpOp_ops b 3 fr.chordOps fr.ops3
  have hops2Off : 2 < bOff.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq, Array.size_set]
    exact Nat.lt_trans (by decide : (2 : Nat) < 3) fr.ops3
  have hhop2 : bOff.sudo_5Board_4cost.sudo_5Costs_3ops[2]'hops2Off = Int.ofNat fr.cOps := by
    have hsz : 2 < (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, fr.ops3⟩
        (Int.ofNat (fr.chordOps + 1))).size := by
      rw [Array.size_set]
      exact Nat.lt_trans (by decide : (2 : Nat) < 3) fr.ops3
    have hget := Array.getElem_set_ne b.sudo_5Board_4cost.sudo_5Costs_3ops
      ⟨3, fr.ops3⟩ (Int.ofNat (fr.chordOps + 1)) hsz (by decide : (3 : Nat) ≠ 2)
    exact (cell_eq_of hopsEq hget).trans (idx_irrel.trans fr.hop2)
  have hfitCopy : FitsLen (mv + pegCount xs) := by
    apply FitsLen.of_le fr.fitRoom
    have hxs : pegCount xs ≤ t.n := by
      have hlen : xs.length = t.n := fieldSub_length t.n baseX accX
      rw [← hlen]
      exact pegCount_le xs
    simp only [mv, runMoves]
    omega
  have hmarkOff : bOff.sudo_5Board_6marker = Int.ofNat fr.mark := by
    have hEq : bOff.sudo_5Board_6marker = bA.sudo_5Board_6marker := by simp [bOff]
    rw [hEq, addIx b1 2 h2H1 arr mv, hmark1, bumpIx b 3 fr.chordOps fr.ops3, fr.hmark]
  have hmxOff : bOff.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat fr.mx := by
    have hEq : bOff.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        bA.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by simp [bOff]
    rw [hEq, addMx b1 2 h2H1 arr mv, hmx1, bumpMx b 3 fr.chordOps fr.ops3, fr.hmx]
  let pk := raisedPeak fr.peak
    (countHeld (bB.sudo_5Board_4held.set ⟨2, hinB.hD⟩ true) 7)
  have hflag : bA.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
    have hB : bB.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
      simp [bB, bumpOp]
    have h1 : b1.sudo_5Board_9marker_on = bB.sudo_5Board_9marker_on :=
      (place_idle bB 2 hinB baseX fr.moves fr.peak).1
    have hA : bA.sudo_5Board_9marker_on = b1.sudo_5Board_9marker_on := by
      simp [bA, addBoard, withMoves]
    exact hA.trans (h1.trans hB)
  exact finish_copy b t baseX accX fr hOk sat hM hS hO hTailM hTailS hCheck hCtrl
    xs bA bOff bB b1 arr mv pk hinB h2H1 hdo hhomeB hszHB hszH1 hplaceH hhomeOff
    hheldB hszDB hszD1 hplaceD hheldBA hszHOff hszDOff hmkO hbenchOff hheld2 hhome2
    hheld5 hheld6 htierOff hmovesOff hslidesOff hpkOff hctrlOff hhighOff htallyOff
    ht0Off hrowOff htmaxOff hladOff hl0Off hnrOff hparkOff hfromOff hridxOff
    hstrictOff hholeOff hopsEq hops2Off hhop2 hmarkOff hmxOff hfitCopy
    rfl rfl rfl hflag



end EcbsLink2.Link2
