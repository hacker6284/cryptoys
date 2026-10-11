/-
  After the ladder. The climb invariant reserves `2 · n` on the move and slide
  counters while the gap sits on the bench. That reservation is the settle
  inside the final `cube` of the gap. Unpark does not touch those counters.
-/
import EcbsLink2.Link2.ClimbStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- At the end of a bench-on climb, `mv + 2 · n` is inside `moves0 + R · rungCharge`,
    so `mv + 2 · pegs` fits whenever `pegs ≤ n`. -/
theorem pending_move_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (mv : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      FitsLen (mv + 2 * pegs) := by
  obtain ⟨mv, heq, hle⟩ := h.moves
  have hres : mv + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon] using hle
  have hfitN : FitsLen (mv + 2 * base.n) := by
    apply FitsLen.of_le base.fitM
    exact Nat.le_trans hres
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  refine ⟨mv, heq, ?_⟩
  apply FitsLen.of_le hfitN
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpegs) mv

/-- The same reservation on the slide counter. -/
theorem pending_slide_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (sl : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      FitsLen (sl + 2 * pegs) := by
  obtain ⟨sl, heq, hle⟩ := h.slides
  have hres : sl + 2 * base.n ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    simpa [hon] using hle
  have hfitN : FitsLen (sl + 2 * base.n) := by
    apply FitsLen.of_le base.fitS
    exact Nat.le_trans hres
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  refine ⟨sl, heq, ?_⟩
  apply FitsLen.of_le hfitN
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpegs) sl

/-- Unpark leaves the move counter alone, so the reserved settle still fits
    on the board the final cube reads. -/
theorem pending_move_fit_unpark
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (bU : Ecbs.Board) (mv : Nat),
      Ecbs.unpark_rung b = .ok bU ∧
      bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bU.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bU.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bU.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      FitsLen (mv + 2 * pegs) := by
  obtain ⟨bU, hun, _, _, _, _, hbon, _, hbench, hmvU, hslU, _, _, _, _, _⟩ :=
    unpark_after_climb h hge
  obtain ⟨mv, hmv, hfit⟩ := pending_move_fit h hon hk pegs hpegs
  refine ⟨bU, mv, hun, hmvU.trans hmv, hslU, hbon, hbench, hfit⟩

end EcbsLink2.Link2
