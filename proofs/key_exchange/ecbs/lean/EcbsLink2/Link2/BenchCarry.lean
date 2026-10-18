/-
  The facts a later F-form multiply reads off the board the previous one
  left. One structure, so they are not a fresh list of hypotheses at each
  gap line. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- Ops cell, empty spare, peak, hole, and the bench lane's zero tail.
    `gap_u2` and the later gap lines read these off the board they settle. -/
structure BenchCarry (b : Ecbs.Board) (lane : List Nat)
    (n cOps peak hole peakS : Nat) : Prop where
  opsSz : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'opsSz = Int.ofNat cOps
  spareSz : 6 < b.sudo_5Board_4held.size
  spare : b.sudo_5Board_4held[6]'spareSz = false
  peak7 : 7 ≤ peak
  peakEq : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)
  strictEq : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  holeEq : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  posL : 0 < lane.length
  nle : n ≤ lane.length
  fitL : FitsLen lane.length
  zero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i]'hi = 0

end EcbsLink2.Link2
