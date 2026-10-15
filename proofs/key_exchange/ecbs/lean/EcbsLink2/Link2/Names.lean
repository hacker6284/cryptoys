/-
  ECBS Link 2: `tier`, `phase_names`, `op_names`, `with_script`. Proof-only.
-/
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem beq_demo : SudoRt.SEq.beq (embed demoName) (#[68, 101, 109, 111] : Array Int) = true := by
  decide!

private theorem beq_toy : SudoRt.SEq.beq (embed toyName) (#[84, 111, 121] : Array Int) = true := by
  decide!

private theorem beq_hobby :
    SudoRt.SEq.beq (embed hobbyName) (#[72, 111, 98, 98, 121] : Array Int) = true := by
  decide!

private theorem beq_serious :
    SudoRt.SEq.beq (embed seriousName) (#[83, 101, 114, 105, 111, 117, 115] : Array Int) = true := by
  decide!

private theorem beq_toy_demo :
    SudoRt.SEq.beq (embed toyName) (#[68, 101, 109, 111] : Array Int) = false := by decide!

private theorem beq_hobby_demo :
    SudoRt.SEq.beq (embed hobbyName) (#[68, 101, 109, 111] : Array Int) = false := by decide!

private theorem beq_hobby_toy :
    SudoRt.SEq.beq (embed hobbyName) (#[84, 111, 121] : Array Int) = false := by decide!

private theorem beq_serious_demo :
    SudoRt.SEq.beq (embed seriousName) (#[68, 101, 109, 111] : Array Int) = false := by decide!

private theorem beq_serious_toy :
    SudoRt.SEq.beq (embed seriousName) (#[84, 111, 121] : Array Int) = false := by decide!

private theorem beq_serious_hobby :
    SudoRt.SEq.beq (embed seriousName) (#[72, 111, 98, 98, 121] : Array Int) = false := by decide!

/-- §1. `tier "Demo"` is the model's Demo tier. -/
theorem tier_demo_refines : Ecbs.tier (embed demoName) = .ok (embTier Spec.demo) := by
  unfold Ecbs.tier
  simp only [beq_demo, pure_eq_ok]
  rw [if_pos trivial, demo_emb]

/-- §1. `tier "Toy"` is the model's Toy tier. -/
theorem tier_toy_refines : Ecbs.tier (embed toyName) = .ok (embTier Spec.toy) := by
  unfold Ecbs.tier
  rw [beq_toy_demo]
  simp only [Bool.false_eq_true, if_false, beq_toy, pure_eq_ok]
  rw [if_pos trivial, toy_emb]

/-- §1. `tier "Hobby"` is the model's Hobby tier. -/
theorem tier_hobby_refines : Ecbs.tier (embed hobbyName) = .ok (embTier Spec.hobby) := by
  unfold Ecbs.tier
  rw [beq_hobby_demo, beq_hobby_toy]
  simp only [Bool.false_eq_true, if_false, beq_hobby, pure_eq_ok]
  rw [if_pos trivial, hobby_emb]

/-- §1. `tier "Serious"` is the model's Serious tier. Any other name hits the assert. -/
theorem tier_serious_refines : Ecbs.tier (embed seriousName) = .ok (embTier Spec.serious) := by
  unfold Ecbs.tier
  rw [beq_serious_demo, beq_serious_toy, beq_serious_hobby]
  simp only [Bool.false_eq_true, if_false, sudoAssertEq_of_beq beq_serious, pure_eq_ok, ok_bind,
    serious_emb]

/-- §1. A name that is none of the four tiers traps with `AssertFailed`. The detail
    carries the sudo line; the kind does not. -/
theorem tier_rejects (name : Array Int)
    (h1 : SudoRt.SEq.beq name (#[68, 101, 109, 111] : Array Int) = false)
    (h2 : SudoRt.SEq.beq name (#[84, 111, 121] : Array Int) = false)
    (h3 : SudoRt.SEq.beq name (#[72, 111, 98, 98, 121] : Array Int) = false)
    (h4 : SudoRt.SEq.beq name (#[83, 101, 114, 105, 111, 117, 115] : Array Int) = false) :
    ∃ e, Ecbs.tier name = .error e ∧ e.kind = "AssertFailed" := by
  unfold Ecbs.tier
  rw [h1]
  simp only [Bool.false_eq_true, if_false]
  rw [h2]
  simp only [Bool.false_eq_true, if_false]
  rw [h3]
  simp only [Bool.false_eq_true, if_false]
  unfold SudoRt.sudoAssertEq
  rw [h4]
  exact ⟨_, rfl, rfl⟩

/-- The eight phase names, in index order. -/
theorem phase_names_refines : Ecbs.phase_names = .ok (embNames phaseNames) := by
  unfold Ecbs.phase_names embNames phaseNames
  rfl

/-- The five operation names, in index order. -/
theorem op_names_refines : Ecbs.op_names = .ok (embNames opNames) := by
  unfold Ecbs.op_names embNames opNames
  rfl

/-- `with_script` replaces the script-marker length and leaves the rest of the tier. -/
theorem with_script_refines (t : Spec.Tier) (script : Nat) :
    Ecbs.with_script (embTier t) (Int.ofNat script) = .ok (embTier (t.withScript script)) := by
  unfold Ecbs.with_script Spec.Tier.withScript embTier
  rfl

end EcbsLink2.Link2
