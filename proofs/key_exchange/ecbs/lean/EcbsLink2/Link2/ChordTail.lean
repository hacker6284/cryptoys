/-
  After `invert_checked`, `chordAddTail` restores the marker and runs the rise,
  then `chord_tail`. The spare is `fieldSub`. The inverse itself is a hypothesis:
  this file does not claim `invert_checked` on a walk board.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordIf
import EcbsLink2.Link2.ChordRise

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Put the marker flag back. Homes, held flags, and the cost record stay. -/
def restoreMarker (b : Ecbs.Board) (on : Bool) : Ecbs.Board :=
  { b with sudo_5Board_9marker_on := on }

/-- The nonempty chord, once the inverse has returned. The rise is `chord_rise`
    on the board with the marker flag restored, and what remains is `chord_tail`. -/
theorem chord_tail_after_inv (b : Ecbs.Board) (red : Bool) (bI : Ecbs.Board)
    (baseY accY : List Nat) (n moves peak : Nat)
    (hinv : Ecbs.invert_checked { b with sudo_5Board_9marker_on := false } Ecbs.bottom = .ok bI)
    (hszH : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home.size = 8)
    (hszD : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held.size = 8)
    (hyB : baseY.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hn : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves : Int))
    (hpeak : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h6e : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[6]'(by
      rw [hszD]; decide) = false)
    (h4t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[4]'(by
      rw [hszD]; decide) = true)
    (h4a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[4]'(by
      rw [hszH]; decide) = embed baseY)
    (h1t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[1]'(by
      rw [hszD]; decide) = true)
    (h1a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[1]'(by
      rw [hszH]; decide) = embed accY) :
    ∃ bR,
      chordAddTail b red =
        (do
          let b ← Ecbs.chord_tail bR Ecbs.across Ecbs.up
          pure (true, b)) ∧
      (∀ h : 6 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[6] =
          embed (fieldSub n (if red then mirrorTrits baseY else baseY) accY)) ∧
      (∀ h : 6 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[4] = true) ∧
      bR.sudo_5Board_4held.size = 8 ∧
      bR.sudo_5Board_4home.size = 8 ∧
      bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseY + pegCount accY : Nat) : Int) ∧
      bR.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[0]'(by
            rw [hszH]; decide)) ∧
      (∀ h : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[0]'(by
            rw [hszD]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[2]'(by
            rw [hszH]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[2]'(by
            rw [hszD]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[5] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[5]'(by
            rw [hszH]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[5] =
          (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[5]'(by
            rw [hszD]; decide)) ∧
      bR.sudo_5Board_1t = (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t ∧
      bR.sudo_5Board_6marker =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_6marker ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bR.sudo_5Board_4cost.sudo_5Costs_6slides =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bR.sudo_5Board_4cost.sudo_5Costs_3ops =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bR.sudo_5Board_8bench_on =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_8bench_on ∧
      bR.sudo_5Board_5bench =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_5bench ∧
      bR.sudo_5Board_8bench_to =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_8bench_to ∧
      bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      ∃ pk, bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
  let bR0 := restoreMarker bI b.sudo_5Board_9marker_on
  obtain ⟨bR, hrise, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, hmv, hflag,
      h0aR, h0tR, h2aR, h2tR, h5aR, h5tR, htR, hmR, hcR, hxR, hslR, hopR, honR, hbR, htoR,
      hhoR, hstR, ⟨pk, hpk⟩, _hhiR⟩ :=
    chord_rise bR0 red baseY accY n moves peak hszH hszD hyB hyA hpos htriB htriA
      hn hmoves hpeak hfit h6e h4t h4a h1t h1a
  refine ⟨bR, ?_, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, hmv, ?_,
      h0aR, h0tR, h2aR, h2tR, h5aR, h5tR, htR, hmR, hcR, hxR, hslR, hopR, honR, hbR, htoR,
      hhoR, hstR, ⟨pk, hpk⟩⟩
  · unfold chordAddTail
    dsimp only
    rw [hinv, ok_bind]
    have hcont :
        (do
          let b ← Ecbs.copy_band bR0 Ecbs.spare Ecbs.base_up red
          let b ← Ecbs.add b Ecbs.spare Ecbs.up true
          let b ← Ecbs.chord_tail b Ecbs.across Ecbs.up
          pure (true, b)) =
        (do
          let b ← Ecbs.copy_band bR0 Ecbs.spare Ecbs.base_up red
          Ecbs.add b Ecbs.spare Ecbs.up true) >>= fun b =>
            (do
              let b ← Ecbs.chord_tail b Ecbs.across Ecbs.up
              pure (true, b)) := by
      simp only [except_pull]
    change (do
        let b ← Ecbs.copy_band bR0 Ecbs.spare Ecbs.base_up red
        let b ← Ecbs.add b Ecbs.spare Ecbs.up true
        let b ← Ecbs.chord_tail b Ecbs.across Ecbs.up
        pure (true, b)) =
      (do
        let b ← Ecbs.chord_tail bR Ecbs.across Ecbs.up
        pure (true, b))
    rw [hcont, hrise, ok_bind]
  · simpa [bR0, restoreMarker] using hflag

end EcbsLink2.Link2
