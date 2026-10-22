/-
  Clearing a home and moving a band write homes, held flags, and the move,
  slide, and peak counters. The painted ladder, the tally, and the park
  fields stay. That is the frame `ChordAt` reads. Proof-only. Not a security
  claim.
-/
import EcbsLink2.Link2.ChordAt
import EcbsLink2.Link2.ChordUp

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs

theorem frame_clear (b : Board) (t : Spec.Tier) (home : Nat) (xs : List Nat) (moves : Nat)
    (h : PaintFrame b t)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size) :
    PaintFrame
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } } t where
  hlad := by simpa using h.hlad
  hl0 := by simpa using h.hl0
  hnr := by simpa using h.hnr
  hpark := by simpa using h.hpark
  hfrom := by simpa using h.hfrom
  hridx := by simpa using h.hridx
  htally := by simpa using h.htally
  ht0 := by simpa using h.ht0
  hrow := by simpa using h.hrow

private theorem frame_core (b : Board) (t : Spec.Tier) (dst src : Nat)
    (h : PaintFrame b t)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (mv sl : Nat) :
    PaintFrame (moveBandCore b dst src hSrcH hSrcD hDstH hDstD xs mv sl) t := by
  unfold moveBandCore
  dsimp
  exact
    { hlad := by simpa using h.hlad
      hl0 := by simpa using h.hl0
      hnr := by simpa using h.hnr
      hpark := by simpa using h.hpark
      hfrom := by simpa using h.hfrom
      hridx := by simpa using h.hridx
      htally := by simpa using h.htally
      ht0 := by simpa using h.ht0
      hrow := by simpa using h.hrow }

theorem frame_band (b : Board) (t : Spec.Tier) (dst src : Nat)
    (h : PaintFrame b t)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    PaintFrame (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak) t := by
  unfold moveBandBoard
  dsimp
  have hcore := frame_core b t dst src h hSrcH hSrcD hDstH hDstD xs
    (moves + 2 * pegCount xs) (slides + 2 * pegCount xs)
  split
  · exact
      { hlad := by simpa using hcore.hlad
        hl0 := by simpa using hcore.hl0
        hnr := by simpa using hcore.hnr
        hpark := by simpa using hcore.hpark
        hfrom := by simpa using hcore.hfrom
        hridx := by simpa using hcore.hridx
        htally := by simpa using hcore.htally
        ht0 := by simpa using hcore.ht0
        hrow := by simpa using hcore.hrow }
  · exact hcore

end EcbsLink2.Link2
