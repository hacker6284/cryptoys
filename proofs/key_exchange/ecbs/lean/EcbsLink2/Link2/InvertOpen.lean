/-
  The ladder array on the tally board is climb order. `Ecbs.invert` is opened
  at `unfold`, and the inlined white scan is `whiteStep`.
-/
import EcbsLink2.Link2.GenRung
import EcbsLink2.Link2.EntryRung

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem gap_ladder (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf,
    tierClimb]

theorem tally_ladder (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [tallyBoard, gap_ladder]

theorem tierR_fit (t : Spec.Tier) (h : BoardOk t) : FitsLen (tierR t) := by
  apply FitsLen.of_le (fits_of h.fits_control)
  unfold tierR
  have hL := h.ladder
  omega

theorem entry_atL (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (i : Nat) (hi : i < tierR t) :
    SudoRt.atL (tallyBoard t xs sat hR).sudo_5Board_6ladder (Int.ofNat i) =
      .ok ((tierClimb t)[i]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hi) : Int) := by
  rw [tally_ladder t xs sat hR]
  exact atL_embed (tierClimb t) i (by
    unfold tierClimb
    rw [List.length_reverse]
    simpa [tierR] using hi)

/-- The white scan inside `Ecbs.invert`, ascription included, is `whiteStep`. -/
theorem white_ascribed (b : Ecbs.Board) (toV : Int) :
    (fun (σ : Int) =>
      (do
        if σ > toV then
          pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
        else
          match ← (do
            let ix ← SudoRt.addI b.sudo_5Board_6tally0 σ
            let c ← SudoRt.atL b.sudo_5Board_3row ix
            SudoRt.sudoAssertEq c (1 : Int) 703
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
          | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
          | .cont _ =>
              if (σ == toV) = true then
                pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
              else do
                let i' ← SudoRt.addI σ (1 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) i'))) =
      whiteStep b toV := by
  unfold whiteStep
  rfl

end EcbsLink2.Link2
