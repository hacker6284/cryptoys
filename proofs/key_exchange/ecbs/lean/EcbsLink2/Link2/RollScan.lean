/-
  The innermost `roll_key` loop: skip blank faces until a face in `1 .. 9`,
  or run off the end of the stream. That is `Spec.readFace`. A face outside
  `0 .. 9` is the assert at sudo line 1216 and is outside this statement.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Keypad
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- One step of the face scan. `1216` is the range assert. -/
def faceBody (faces : Array Int) (f : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Option Ecbs.Rolled)) := do
  let face ← SudoRt.atL faces f
  let next ← SudoRt.addI f (1 : Int)
  let ge ← (if decide (face ≥ 0) then pure (decide (face ≤ 9)) else pure false)
  let _ ← SudoRt.sudoAssert ge 1216
  if face != 0 then
    pure (SudoRt.Flow.brk (face, next))
  else
    pure (SudoRt.Flow.cont (face, next))

def faceStep (faces : Array Int) (toV : Int) (σ : Int × (Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Int × Int)) (Option Ecbs.Rolled)) := do
  let f := σ.1
  let face := σ.2.1
  let next := σ.2.2
  if f > toV then
    pure (SudoRt.Flow.brk (f, (face, next)))
  else
    match ← faceBody faces f with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (f, fs))
    | .cont fs => do
        if f == toV then
          pure (SudoRt.Flow.brk (f, fs))
        else
          let f' ← SudoRt.addI f (1 : Int)
          pure (SudoRt.Flow.cont (f', fs))

private theorem face_in_range (n : Nat) (h : n ≤ 9) :
    (decide ((Int.ofNat n) ≥ 0) = true) ∧ decide (Int.ofNat n ≤ 9) = true := by
  constructor
  · exact decide_eq_true (by
      rw [ofNat_eq_natCast]
      omega)
  · exact decide_eq_true (by
      rw [ofNat_eq_natCast]
      have : (n : Int) ≤ 9 := by omega
      exact this)

private theorem faceBody_zero (faces : List Nat) (f : Nat)
    (hf : f < faces.length) (hz : faces[f] = 0)
    (hfit : FitsLen (f + 1)) :
    faceBody (embed faces) (Int.ofNat f) =
      .ok (SudoRt.Flow.cont (Int.ofNat 0, Int.ofNat (f + 1))) := by
  unfold faceBody
  rw [atL_embed faces f hf, ok_bind, hz, addI_ofNat_one f hfit, ok_bind]
  have hr := face_in_range 0 (by decide)
  rw [if_pos hr.1, hr.2, pure_eq_ok, ok_bind, sudoAssert_bool 1216 rfl, ok_bind]
  rw [show (Int.ofNat 0 != (0 : Int)) = false from by decide]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), pure_eq_ok]

private theorem faceBody_pos (faces : List Nat) (f : Nat)
    (hf : f < faces.length) (h9 : faces[f] ≤ 9) (hnz : faces[f] ≠ 0)
    (hfit : FitsLen (f + 1)) :
    faceBody (embed faces) (Int.ofNat f) =
      .ok (SudoRt.Flow.brk (Int.ofNat (faces[f]), Int.ofNat (f + 1))) := by
  unfold faceBody
  rw [atL_embed faces f hf, ok_bind, addI_ofNat_one f hfit, ok_bind]
  have hr := face_in_range (faces[f]) h9
  rw [if_pos hr.1, hr.2, pure_eq_ok, ok_bind, sudoAssert_bool 1216 rfl, ok_bind]
  have hne : (Int.ofNat (faces[f]) != (0 : Int)) = true := by
    simp [bne]
    intro h
    exact hnz (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h))
  rw [hne, if_pos rfl, pure_eq_ok]

/-- From index `i` through the last face, the scan stops on the first
    non-zero face, or on a zero face at the end of the stream. -/
theorem scan_face (faces : List Nat) (i : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hi : i < faces.length) (hfit : FitsLen faces.length) :
    (do
        let toV ← SudoRt.subI (Int.ofNat faces.length) (1 : Int)
        let fuel := if Int.ofNat i > toV then 1 else (toV - Int.ofNat i).natAbs + 1
        SudoRt.runLoopOn (Int.ofNat i, ((0 : Int), Int.ofNat i)) fuel
          (faceStep (embed faces) toV)
          (fun σ => pure σ.2)
          (fun _ => pure ((0 : Int), (0 : Int)))) =
      .ok (match readFace faces i with
        | none => (0, Int.ofNat faces.length)
        | some (f, n) => (Int.ofNat f, Int.ofNat n)) := by
  have hle : i ≤ faces.length - 1 := by omega
  rw [subI_ofNat_one _ (by omega) hfit, ok_bind, fuelRange_eq]
  refine asc_brk_goal
      (fun k st =>
        st = ((0 : Int), Int.ofNat k) ∧ readFace faces i = readFace faces k)
      (fun k st =>
        ∃ f, f ≠ 0 ∧ st = (Int.ofNat f, Int.ofNat (k + 1)) ∧
          readFace faces i = some (f, k + 1))
      hle ?_ ?_ ?_
  · exact ⟨rfl, rfl⟩
  · intro k st _ hk2 hI
    obtain ⟨hst, hread⟩ := hI
    have hkf : k < faces.length := by omega
    have hfk : FitsLen (k + 1) := FitsLen.of_le hfit (by omega)
    rw [hst]
    by_cases hz : faces[k] = 0
    · have hbody := faceBody_zero faces k hkf hz hfk
      refine Or.inl ⟨(0, Int.ofNat (k + 1)), ?_, ?_⟩
      · exact ⟨rfl, by rw [hread, readFace_zero hkf hz]⟩
      · unfold faceStep
        conv => lhs; zeta
        have hng : ¬ Int.ofNat k > Int.ofNat (faces.length - 1) := by
          rw [ofNat_eq_natCast, ofNat_eq_natCast]
          omega
        rw [if_neg hng, hbody, ok_bind]
        simpa using asc_tail (faces.length - 1) k hfk (0, Int.ofNat (k + 1))
    · have hbody := faceBody_pos faces k hkf (h9 k hkf) hz hfk
      refine Or.inr ⟨(Int.ofNat (faces[k]), Int.ofNat (k + 1)), ?_, ?_⟩
      · exact ⟨faces[k], hz, rfl, by rw [hread, readFace_pos hkf hz]⟩
      · unfold faceStep
        conv => lhs; zeta
        have hng : ¬ Int.ofNat k > Int.ofNat (faces.length - 1) := by
          rw [ofNat_eq_natCast, ofNat_eq_natCast]
          omega
        rw [if_neg hng, hbody, ok_bind]
        simp [pure_eq_ok]
  · intro j st _ _ hdone
    cases hdone with
    | inl hI =>
      obtain ⟨hst, hread⟩ := hI
      have hk : faces.length - 1 + 1 = faces.length := by omega
      rw [pure_eq_ok, hst, hread, hk, readFace_ge (Nat.le_refl _)]
    | inr hD =>
      obtain ⟨f, hnz, hst, hread⟩ := hD
      rw [pure_eq_ok, hst, hread]

end EcbsLink2.Link2
