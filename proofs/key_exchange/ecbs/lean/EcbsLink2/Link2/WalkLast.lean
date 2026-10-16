/-
  The last live cell of `walk_chord`. Nothing after it reads a `RunFrame`, so
  the step is `chord_add_live`: one move charge and one control charge.
  `chord_add_live_frame` is the earlier cells, where the next index is the
  extra cell of fuel.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLive
import EcbsLink2.Link2.WalkCharge
import EcbsLink2.Link2.WalkLive

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Last live cell. `i = toN`, so the loop breaks. The rooms are one charge. -/
theorem chordStep_live_last (cells : List Nat) (i toN c : Nat)
    (b0 b bF : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat)
    (fr : RunFrame bF t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : bF.sudo_5Board_9marker_on = true)
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
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hi : i = toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ bA, chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      .ok (SudoRt.Flow.brk (Int.ofNat i, (bA, true))) := by
  obtain ⟨bA, hdemo, _⟩ :=
    chord_add_live bF t baseX accX baseY accY preX preY inv c fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hMove hSlide hCtrl hOps hMark hMarkF
  have hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, bA) := by
    have hflag : SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
      rcases hc with rfl | rfl <;> decide
    rw [hflag]
    exact hdemo
  have hstep := chordStep_open cells i toN c b0 b bF bA (by omega) hlen hcAt hc0 hc2
    hml hfrob hadd hfiti
  exact ⟨bA, by simpa [hi] using hstep⟩

/-- The last index's one charge is `cellsLeft = 1` of the suffix envelope. -/
theorem last_rooms_of_left (t : Spec.Tier) (moves slides ctrl ops : Nat)
    (baseX accX : List Nat) (hx : baseX.length = t.n) (hy : accX.length = t.n)
    (hM : FitsLen (moves + 1 * walkCharge t))
    (hS : FitsLen (slides + 1 * cellSlideCharge t))
    (hC : FitsLen (ctrl + 1 * cellCtrlCharge t))
    (hO : FitsLen (ops + 1 * cellOpsCharge t)) :
    FitsLen (liveMoveRoom t moves baseX accX) ∧
      FitsLen (liveSlideRoom t slides) ∧
      FitsLen (liveCtrlRoom t ctrl) ∧
      FitsLen (liveOpsRoom t ops) := by
  refine ⟨live_move_of_walk t moves baseX accX hx hy (by simpa using hM),
    live_slide_of_cell t slides (by simpa using hS),
    live_ctrl_of_cell t ctrl (by simpa using hC),
    live_ops_of_cell t ops (by simpa using hO)⟩

end EcbsLink2.Link2
