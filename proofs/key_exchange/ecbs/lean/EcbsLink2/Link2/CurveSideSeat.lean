/-
  After `cube`, the cube sits on the bench aimed at the destination.
  `mul` with `onto = false` settles that bench before it squares.
  The destination home becomes the cube, and the bench flag falls.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Settle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The bench prefix is the cube, so settling writes that cube into the home. -/
theorem cube_bench_settles (b : Ecbs.Board) (dst : Nat) (lane x : List Nat)
    (n k bench moves slides peak : Nat)
    (hH : dst < b.sudo_5Board_4home.size)
    (hD : dst < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (dst : Int))
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (htake : lane.take n = fieldCube n k bench x) :
    ∃ bS,
      Ecbs.settle b = .ok bS ∧
        bS.sudo_5Board_8bench_on = false ∧
        bS.sudo_5Board_4held[dst]? = some true ∧
        bS.sudo_5Board_4home[dst]? = some (embed (fieldCube n k bench x)) := by
  have hset := settle_refines b dst lane n moves slides peak hH hD h7 hon hto hempty
    hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let hin : HomeIn b dst := ⟨hH, hD⟩
  let bS := settleBoard b dst hH hD lane n moves slides peak
  have hhome := settle_home_eq b dst hin lane n moves slides peak
  have hheld := settle_held_eq b dst hin lane n moves slides peak
  refine ⟨bS, hset, ?_, ?_, ?_⟩
  · by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hD⟩ true) 7
    · simp [bS, settleBoard, hpk]
    · simp [bS, settleBoard, hpk]
  · rw [hheld, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · rw [hhome, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set, htake]

end EcbsLink2.Link2
