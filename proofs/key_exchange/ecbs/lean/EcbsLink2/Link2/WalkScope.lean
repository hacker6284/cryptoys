/-
  Where `walk_fform` is stated. One live cell is three cubes and twelve
  multiplies. From a lifted marker those steps seat markers `0` through `14`,
  and `marker_step` asserts `marker < script` (sudo line 321). Toy, Hobby, and
  Serious have script 15. Demo's script is 5; `DEMO_SCRIPT.md` records the
  assert on cells `[1, 1]`. No `walk_fform` success theorem is stated for Demo.
  On a demo tier, `walk_and_finish` is `walk_chord`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFform

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- One live F-form cell fits in the script row. -/
def fformScript : Nat := 14

theorem toy_script_fform : fformScript < Spec.toy.script := by decide

theorem hobby_script_fform : fformScript < Spec.hobby.script := by decide

theorem serious_script_fform : fformScript < Spec.serious.script := by decide

/-- Demo is outside the `walk_fform` statements. See `DEMO_SCRIPT.md`. -/
theorem demo_not_fform : ¬ (fformScript < Spec.demo.script) := by decide

/-- A finished cell leaves a seated marker. The next cell's `marker_lift`
    sets that index back to `-1` (`marker_lift_refines`). A marker that is
    already `-1` stays there (`marker_lift_down`). The fifteen steps of one
    live cell therefore start from `-1` again; `fformScript < script` is not
    a sum across cells. -/
theorem cell_marker_low (b : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1)) :
    ∃ b', Ecbs.marker_lift b = .ok b' ∧ b'.sudo_5Board_6marker = -1 := by
  refine ⟨{ b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } },
    marker_lift_refines b marker ctrl hm hc hfit, rfl⟩

/-- A demo board takes `walk_chord`. `finish` is not called. -/
theorem walk_and_finish_demo (b : Ecbs.Board) (cells : Array Int)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = true) :
    Ecbs.walk_and_finish b cells =
      (do
        let r ← Ecbs.walk_chord b cells
        let live := r.1.1
        let ok := r.1.2
        let b := r.2
        let flag ← (if live then pure ok else pure false)
        pure (flag, b)) := by
  unfold Ecbs.walk_and_finish
  simp [hdemo]

/-- Any other tier takes `walk_fform`, and `finish` runs only when that walk
    is live and ok. -/
theorem walk_and_finish_fform (b : Ecbs.Board) (cells : Array Int)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = false) :
    Ecbs.walk_and_finish b cells =
      (do
        let r ← Ecbs.walk_fform b cells
        let live := r.1.1
        let ok := r.1.2
        let b := r.2
        let flag ← (if live then pure ok else pure false)
        if !flag then
          pure (false, b)
        else
          do
            let b ← Ecbs.finish b
            pure (true, b)) := by
  unfold Ecbs.walk_and_finish
  simp [hdemo]

end EcbsLink2.Link2
