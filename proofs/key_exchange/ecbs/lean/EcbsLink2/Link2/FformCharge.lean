/-
  The counters on the board the nonzero cell leaves, in the shape `FformAt`
  stores. The numbers are `TailCharge`: moves, slides, control, marker, max,
  peak, strict peak, hole, and ops slot 0. Ops slot 1 is the cube counter
  `FformAt` reads; the mul tail writes slot 0.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellStep
import EcbsLink2.Link2.WalkCharge

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- One more cell of room, once the previous index already fit. -/
theorem ledger_next (done bound spent now : Nat)
    (hprev : now ≤ done * bound) (hspent : spent ≤ bound) :
    now + spent ≤ (done + 1) * bound := by
  rw [Nat.succ_mul]
  exact Nat.add_le_add hprev hspent

/-- `TailCharge` is the equality half of `FformAt`'s ledger, apart from ops
    slot 1. Slot 0 is the counter the multiplies bump. -/
theorem cell_charge_eq (b : Ecbs.Board)
    (moves slides ctrl mark mx pk peakS hole cOps : Nat)
    (ch : TailCharge b moves slides ctrl mark mx pk peakS hole cOps) :
    b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
    b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
    b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
    b.sudo_5Board_6marker = Int.ofNat mark ∧
    b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx ∧
    b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
    b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS ∧
    b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
    0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'ch.opsSz = Int.ofNat cOps :=
  ⟨ch.movesEq, ch.slidesEq, ch.ctrlEq, ch.markEq, ch.mxEq, ch.peakEq, ch.strictEq,
    ch.holeEq, ch.opsSz, ch.ops0⟩

/-- The three ledger inequalities at index `done + 1`, from the inequalities
    at `done` and one cell of spend. -/
theorem cell_charge_le (t : Spec.Tier) (done moves slides ctrl
    dMoves dSlides dCtrl : Nat)
    (hMoves : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hSlides : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hCtrl : ctrl ≤ done * (cellCtrlCharge t + 4))
    (hdM : dMoves ≤ walkCharge t + (6 * t.benchlen + 2 * t.n))
    (hdS : dSlides ≤ cellSlideCharge t + slideCharge t.n)
    (hdC : dCtrl ≤ cellCtrlCharge t + 4) :
    moves + dMoves ≤ (done + 1) * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
    slides + dSlides ≤ (done + 1) * (cellSlideCharge t + slideCharge t.n) ∧
    ctrl + dCtrl ≤ (done + 1) * (cellCtrlCharge t + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ledger_next done _ dMoves moves hMoves hdM
  · exact ledger_next done _ dSlides slides hSlides hdS
  · exact ledger_next done _ dCtrl ctrl hCtrl hdC

end EcbsLink2.Link2
