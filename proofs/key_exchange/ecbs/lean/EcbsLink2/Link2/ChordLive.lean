/-
  A live white or red cell. `RunFrame` is the board `frobenius` leaves: the
  accumulator is already cubed, the base point is still in homes 3 and 4, and
  the control frame is the fresh ladder. Five rooms — moves, slides, control,
  ops, and the script marker — cover the climb and the chord tail. The emitted
  add is `.ok`, and `walkStep` is Spec `chordAdd` of that cubed point.
  The trailing `high` is the board's `control_highest`, a natural at least
  the tally origin. It is not an export result. `walk_key` returns a point.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopyLay
import EcbsLink2.Link2.ChordOpen
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves through the copy, the climb, the check, and the chord tail. -/
def liveMoveRoom (t : Spec.Tier) (moves : Nat) (baseX accX : List Nat) : Nat :=
  (runMoves moves baseX accX + pegCount (fieldSub t.n baseX accX)) +
    tierR t * rungCharge t.n t.benchlen (rowRoom t) +
    pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
    3 * (t.benchlen - t.n) + 2 * t.n + tailMoveCap t.n t.benchlen

/-- Slides through the climb's outer settle and the chord tail. -/
def liveSlideRoom (t : Spec.Tier) (slides : Nat) : Nat :=
  slides + tierR t * rungSlideCharge t.n (rowRoom t) + 2 * t.n + tailSlideCap t.n

/-- The climb's extra control step, plus six for the tail. -/
def liveCtrlRoom (t : Spec.Tier) (ctrl : Nat) : Nat :=
  (ctrl + 1) + (tierR t + 1) * (3 * rowRoom t + 5) + 6

/-- Ops through the climb, plus three for the tail. -/
def liveOpsRoom (t : Spec.Tier) (ops : Nat) : Nat :=
  ops + tierR t * (rowRoom t + 3) + 3

private theorem fieldSub_trits (n : Nat) (xs ys : List Nat) :
    allTritList (fieldSub n xs ys) := by
  intro z hz
  rw [fieldSub, fieldAdd] at hz
  rcases List.mem_map.mp hz with ⟨i, _, rfl⟩
  unfold tritAdd
  have hmod : (coeff xs i + coeff (mirrorTrits ys) i) % 3 < 3 :=
    Nat.mod_lt _ (by decide)
  omega

private theorem mirror_trits (xs : List Nat) (h : allTritList xs) :
    allTritList (mirrorTrits xs) := by
  intro z hz
  rw [mirrorTrits] at hz
  rcases List.mem_map.mp hz with ⟨c, hc, rfl⟩
  have hc2 : c ≤ 2 := h c hc
  by_cases h0 : c = 0
  · simp [h0]
  · have h1 : c = 1 ∨ c = 2 := by omega
    rcases h1 with rfl | rfl <;> simp

private theorem inv_len (t : Spec.Tier) (xs inv : List Nat) (sat : TierSat t)
    (hpos : 0 < t.n)
    (hacc : fieldInv t.n t.k t.benchlen xs = some inv) :
    inv.length = t.n := by
  rcases fieldInv_some_shape t.n t.k t.benchlen xs inv hacc with ⟨_, hans⟩ | ⟨_, hans⟩
  · rw [hans]
    exact invGap_length t xs sat hpos
  · rw [hans, mirrorTrits, List.length_map]
    exact invGap_length t xs sat hpos

private theorem inv_trits (t : Spec.Tier) (xs inv : List Nat) (sat : TierSat t)
    (hsh : TierShape t) (hpos : 0 < t.n) (hx : xs.length = t.n) (htri : allTritList xs)
    (hacc : fieldInv t.n t.k t.benchlen xs = some inv) :
    allTritList inv := by
  rcases fieldInv_some_shape t.n t.k t.benchlen xs inv hacc with ⟨_, hans⟩ | ⟨_, hans⟩
  · rw [hans]
    exact invGap_trits t xs sat hsh hpos hx htri
  · rw [hans]
    exact mirror_trits _ (invGap_trits t xs sat hsh hpos hx htri)

/-- A live white or red cell. The five rooms are the climb plus the tail.
    `chord_add_demo` returns the new point, and `walkStep` is Spec `chordAdd`
    of the cubed accumulator. -/
theorem chord_add_live (b : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat) (c : Nat)
    (fr : RunFrame b t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hMove : FitsLen (liveMoveRoom t fr.moves baseX accX))
    (hSlide : FitsLen (liveSlideRoom t fr.slides))
    (hCtrl : FitsLen (liveCtrlRoom t fr.ctrl))
    (hOps : FitsLen (liveOpsRoom t fr.opsCap))
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4)) :
    ∃ b',
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed
        (chordX3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
            inv)
          accX (fieldSub t.n baseX accX))) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed
        (chordY3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
            inv)
          (fieldSub t.n accX
            (chordX3 t.n t.k t.benchlen
              (fieldMul t.n t.k t.benchlen
                (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
                inv)
              accX (fieldSub t.n baseX accX)))
          accY)) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY) c =
        some (true,
          (chordX3 t.n t.k t.benchlen
            (fieldMul t.n t.k t.benchlen
              (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
              inv)
            accX (fieldSub t.n baseX accX),
          chordY3 t.n t.k t.benchlen
            (fieldMul t.n t.k t.benchlen
              (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
              inv)
            (fieldSub t.n accX
              (chordX3 t.n t.k t.benchlen
                (fieldMul t.n t.k t.benchlen
                  (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY)
                  inv)
                accX (fieldSub t.n baseX accX)))
            accY)) ∧
      ∃ high : Nat,
        b'.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) ∧
        tallyOrigin t ≤ high := by
  let red := decide (c = 2)
  let run := fieldSub t.n baseX accX
  let y := if red then mirrorTrits baseY else baseY
  let rise := fieldSub t.n y accY
  let slope := fieldMul t.n t.k t.benchlen rise inv
  let x3 := chordX3 t.n t.k t.benchlen slope accX run
  let y3 := chordY3 t.n t.k t.benchlen slope (fieldSub t.n accX x3) accY
  have hpos : 0 < t.n := hOk.n_pos
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hpos sat.mul_span
  have hfitN : FitsLen t.n := FitsLen.of_le hMove (by
    unfold liveMoveRoom
    omega)
  have hM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t)) :=
    FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  have hS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t)) :=
    FitsLen.of_le hSlide (by unfold liveSlideRoom; omega)
  have hO : FitsLen (fr.opsCap + tierR t * (rowRoom t + 3)) :=
    FitsLen.of_le hOps (by unfold liveOpsRoom; omega)
  have hTailM : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen) :=
    FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  have hTailS : FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t) +
      2 * t.n) :=
    FitsLen.of_le hSlide (by unfold liveSlideRoom; omega)
  have hCheck : FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
      pegCount (fieldSub t.n baseX accX) +
      tierR t * rungCharge t.n t.benchlen (rowRoom t) +
      pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
      3 * (t.benchlen - t.n) + 2 * t.n) :=
    FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  have hCtrlC : FitsLen ((fr.ctrl + 1) + (tierR t + 1) * (3 * rowRoom t + 5)) :=
    FitsLen.of_le hCtrl (by unfold liveCtrlRoom; omega)
  obtain ⟨bA, hcopy, hflag, lay, bud, hmatch, hmov, hslay, hctrl, hcops, hops,
      hmark, hmx, hside1, hflag1, hside4, hflag4, hside0, hflag0, _hbase, _hflag3⟩ :=
    copy_add_open b t baseX accX fr hOk sat hM hS hO hTailM hTailS hCheck hCtrlC
  have hmkA : bA.sudo_5Board_9marker_on = true := hflag.trans hmk
  have hrunL : run.length = t.n := fieldSub_length t.n baseX accX
  have htriR : allTritList run := fieldSub_trits t.n baseX accX
  have hinvL : inv.length = t.n := inv_len t run inv sat hpos hacc
  have htriI : allTritList inv :=
    inv_trits t run inv sat hsh hpos hrunL htriR hacc
  have hriseL : rise = fieldSub t.n (if red then mirrorTrits baseY else baseY) accY := rfl
  have hriseN : rise.length = t.n := fieldSub_length t.n _ accY
  have htriRise : allTritList rise := fieldSub_trits t.n _ accY
  have htriX : allTritList accX := fr.triA
  have hChord : FitsLen (checkMoveCap bud + tailMoveCap bud.n bud.bench) := by
    have hEq : checkMoveCap bud + tailMoveCap bud.n bud.bench =
        liveMoveRoom t fr.moves baseX accX := by
      unfold checkMoveCap liveMoveRoom
      rw [hmatch.moves0, hmov, hmatch.n, hmatch.bench, hmatch.R, hmatch.mMax]
    rw [hEq]
    exact hMove
  have hChordS : FitsLen (checkSlideCap bud + tailSlideCap bud.n) := by
    have hEq : checkSlideCap bud + tailSlideCap bud.n = liveSlideRoom t fr.slides := by
      unfold checkSlideCap liveSlideRoom
      rw [hmatch.slides0, hslay, hmatch.n, hmatch.R, hmatch.mMax]
    rw [hEq]
    exact hSlide
  have hCtrlP : FitsLen (checkCtrlCap bud + 6) := by
    apply FitsLen.of_le hCtrl
    unfold checkCtrlCap liveCtrlRoom
    rw [hmatch.ctrl0, hctrl, hmatch.R, hmatch.mMax]
    have hsplit : (tierR t + 1) * (3 * rowRoom t + 5) =
        tierR t * (3 * rowRoom t + 5) + (3 * rowRoom t + 5) := by
      rw [Nat.succ_mul]
    rw [hsplit]
    omega
  have hOpsP : FitsLen (checkOpsCap bud + 3) := by
    have hEq : checkOpsCap bud + 3 = liveOpsRoom t fr.opsCap := by
      unfold checkOpsCap liveOpsRoom
      rw [hmatch.ops0, hops, hmatch.R, hmatch.mMax]
    rw [hEq]
    exact hOps
  have hMarkL : lay.mark + 3 < t.script := by rw [hmark]; exact hMark
  have hMarkL' : FitsLen (lay.mark + 4) := by rw [hmark]; exact hMarkF
  have hf4' : lay.flag4 = true := hflag4.trans hf4
  have hf1' : lay.flag1 = true := hflag1.trans hf1
  have hside4' : baseY = lay.side4 := hY.symm.trans hside4.symm
  have hside1' : accY = lay.side1 := hA.symm.trans hside1.symm
  have hside0' : accX = lay.side0 := hside0.symm
  obtain ⟨_, _, _, _, _, _, _, _, hand⟩ :=
    chord_add_point bA red t baseY accY accX run inv rise lay bud hmatch
      hOk sat hR hsh hacc hside4' hside1' hside0' hf4' hf1' hflag0
      hyB hyA hpos htriY htriUp hmkA hriseL fr.lenA hyA hrunL hinvL hriseN
      htriX htriUp htriR htriI htriRise hfitN sat.mul_span
      hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsh.small hsh.n_small
      hChord hChordS hMarkL hMarkL' hCtrlP hOpsP
  obtain ⟨_, b', htail, hx0, hy1, hwater, _hpack⟩ := hand
  have h2H : 2 < bA.sudo_5Board_4home.size := by
    have hsz : ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4home.size =
        bA.sudo_5Board_4home.size := rfl
    rw [← hsz, lay.szH]
    decide
  have h2D : 2 < bA.sudo_5Board_4held.size := by
    have hsz : ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4held.size =
        bA.sudo_5Board_4held.size := rfl
    rw [← hsz, lay.szD]
    decide
  have hhome2 : bA.sudo_5Board_4home[2]'h2H = embed run := by
    have hEq : bA.sudo_5Board_4home =
        ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4home := rfl
    exact cell_eq_of hEq lay.home2
  have hheld2 : bA.sudo_5Board_4held[2]'h2D = true := by
    have hEq : bA.sudo_5Board_4held =
        ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4held := rfl
    exact cell_eq_of hEq lay.held2
  have hnA : bA.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    have hEq : bA.sudo_5Board_1t =
        ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_1t := rfl
    rw [hEq, lay.tier]
    simp [embTier, ofNat_eq_natCast]
  have hne : run ≠ List.replicate t.n 0 := by
    intro hz
    have hnone := specInv_zero t.n t.k t.benchlen hpos hnb
    have hsome : specInv t.n t.k t.benchlen run = some inv := by
      rw [specInv_eq]
      exact hacc
    rw [hz] at hsome
    cases hnone.symm.trans hsome
  rw [chord_add_eq]
  unfold chordAddGo
  rw [hcopy, ok_bind]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
    is_zero_embed bA 2 t.n run h2D h2H hheld2 hhome2 hnA hrunL hfitN, ok_bind]
  rw [decide_eq_false hne]
  simp only [Bool.false_eq_true, if_false]
  obtain ⟨high, hhi, hge⟩ := hwater
  refine ⟨b', ?_, hx0, hy1, ?_, ⟨high, hhi, hge⟩⟩
  · rw [htail]
  · have hspec : specInv t.n t.k t.benchlen
        (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen preX)) = some inv := by
      rw [specInv_eq, ← hpreX]
      exact hacc
    have hstep := walkStep_live_chord t.n t.k t.benchlen baseX baseY preX preY c inv hc hspec
    rcases hc with rfl | rfl
    · simpa [red, run, y, rise, slope, x3, y3, hpreX, hpreY] using hstep
    · simpa [red, run, y, rise, slope, x3, y3, hpreX, hpreY] using hstep


end EcbsLink2.Link2
