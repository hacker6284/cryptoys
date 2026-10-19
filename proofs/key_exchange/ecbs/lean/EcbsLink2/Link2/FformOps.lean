/-
  Ops slots. `op_mul` is 0 and `op_cube` is 1. `Ecbs.mul` increments slot 0.
  `Ecbs.cube` increments slot 1. The F-form tail is multiplies and one clear,
  so it leaves the cube counter alone. `FformAt` reads slot 1, the cube
  counter the Frobenius advances before that tail. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The tail's cube slot is the cube slot it was given. `FformAt` stores that
    slot as `ops[1]?`. -/
theorem tail_cube_slot (b b' : Ecbs.Board) (cOps : Nat)
    (h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hkeep : b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]?)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps : Int)) :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps : Int) := by
  rw [hkeep, hop]

/-- `cell_on_add` returns that preservation. The ledger stays on slot 1. -/
theorem cell_cube_slot (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat) (red : Bool)
    (x3 yUp : List Nat) (cOps1 : Nat)
    (s : AddAt b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z))
    (h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps1 : Int)) :
    ∃ (b' : Ecbs.Board) (lane' : List Nat),
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps1 : Int) := by
  obtain ⟨b', lane', _hdo, _hcell, hslot, _hmon, _hH0, _hcount⟩ :=
    cell_on_add b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS red x3 yUp s
      hbound hfitM6 hfitC6 hfops6 hf hBig hSlide hw0 hh0 hrR hrP hnE hkLe hgapN
      hsm hnsm hfitB hx hy
  exact ⟨b', lane', tail_cube_slot b b' cOps1 h1 (hslot h1) hop⟩

end EcbsLink2.Link2
