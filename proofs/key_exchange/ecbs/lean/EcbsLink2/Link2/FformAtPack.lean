/-
  `FformAt` from the frame, the projective triple, and `TailCharge`.
  The multiply room is the remaining-cell bound. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFformInd
import EcbsLink2.Link2.FformFrame
import EcbsLink2.Link2.FformCharge

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem fform_at_pack (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py : List Nat) (done : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hpx : px.length = t.n) (hpy : py.length = t.n)
    (hpxT : allTritList px) (hpyT : allTritList py)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hheld0 : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = true)
    (hscript : 2 < t.script)
    (fr : FrameAt b t baseX baseY)
    (hp : ProjOn t b px py)
    (moves slides ctrl mark mx pk peakS hole c1 c0 : Nat)
    (ch : TailCharge b moves slides ctrl mark mx pk peakS hole c0)
    (hops1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int))
    (hctrl : FitsLen (ctrl + 6))
    (hc1 : FitsLen (c1 + 3 * (t.cells - done)))
    (hc0 : FitsLen (c0 + 13 * (t.cells - done)))
    (hmv : FitsLen (moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)))
    (hsl : FitsLen (slides + 2 * t.n + slideCharge t.n))
    (hmvLe : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hslLe : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hcLe : ctrl ≤ done * (cellCtrlCharge t + 4))
    (h5 : b.sudo_5Board_4held[5]? = some false)
    (h6 : b.sudo_5Board_4held[6]? = some false)
    (hopsN : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5) :
    FformAt t b baseX baseY px py done := by
  refine ⟨hmk, fr.tier, hpx, hpy, hpxT, hpyT, hbx, hby, hbxT, hbyT,
      ?_, ?_, fr.home3, fr.home4, fr.held3, fr.held4, hheld0, hscript,
      fr.szH, fr.szD, hp, ?_⟩
  · rw [fr.szH]; decide
  · rw [fr.szD]; decide
  · refine ⟨moves, slides, ctrl, mark, mx, pk, peakS, hole, c1, c0,
      ch.movesEq, ch.slidesEq, ch.ctrlEq, ch.markEq, ch.mxEq, ch.peakEq,
      ch.strictEq, ch.holeEq, hops1, hop1, ?_, hctrl, hc1, hc0, hmv, hsl,
      hmvLe, hslLe, hcLe, h5, h6, hopsN⟩
    rw [Array.getElem?_eq_getElem ch.opsSz]
    exact congrArg some ch.ops0

end EcbsLink2.Link2
