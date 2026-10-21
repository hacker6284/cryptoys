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

private theorem embed_set (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    (embed xs).set ⟨i, by rw [size_embed]; exact h⟩ (Int.ofNat v) = embed (xs.set i v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro j _ _
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem set_irrel {α : Type} (a : Array α) (i : Nat) (h₁ h₂ : i < a.size) (v : α) :
    a.set ⟨i, h₁⟩ v = a.set ⟨i, h₂⟩ v := by
  have : (⟨i, h₁⟩ : Fin a.size) = ⟨i, h₂⟩ := Fin.ext rfl
  simp [this]

/-- One die, faces `1 .. 9`, written into the pair of cells. -/
theorem lay_die (cells : Nat) (acc : List Nat) (pair face : Nat)
    (h1 : 1 ≤ face) (h9 : face ≤ 9) (hlen : acc.length = cells)
    (hix : 2 * pair < cells) (hfit : FitsLen (2 * pair + 1)) :
    (do
        let ix ← SudoRt.mulI (Int.ofNat 2) (Int.ofNat pair)
        let d ← Ecbs.keypad_first (Int.ofNat face)
        let acc ← SudoRt.putL (embed acc) ix d
        let j ← SudoRt.addI ix (1 : Int)
        if decide (j < Int.ofNat cells) then
          let d2 ← Ecbs.keypad_second (Int.ofNat face)
          SudoRt.putL acc j d2
        else
          pure acc) =
      .ok (embed (writePair cells acc pair face)) := by
  have hmul : FitsLen (2 * pair) := FitsLen.of_le hfit (Nat.le_succ _)
  rw [mulI_ofNat 2 pair hmul, ok_bind]
  rw [show Int.ofNat face = (face : Int) from by rw [ofNat_eq_natCast]]
  rw [keypad_first_refines face h1 h9, ok_bind]
  have hjA : 2 * pair < (embed acc).size := by rw [size_embed, hlen]; exact hix
  rw [putL_ofNat _ _ _ hjA, set_irrel _ _ _ (by rw [size_embed, hlen]; exact hix)]
  rw [embed_set acc (2 * pair) (keypadFirst face) (by rw [hlen]; exact hix)]
  rw [ok_bind, addI_ofNat_one (2 * pair) hfit, ok_bind]
  by_cases h2 : 2 * pair + 1 < cells
  · have hdec : decide (Int.ofNat (2 * pair + 1) < Int.ofNat cells) = true :=
      decide_eq_true (Int.ofNat_lt.mpr h2)
    rw [if_pos hdec, keypad_second_refines face h1 h9, ok_bind]
    have hj2 : 2 * pair + 1 < (embed (acc.set (2 * pair) (keypadFirst face))).size := by
      rw [size_embed, List.length_set, hlen]; exact h2
    rw [putL_ofNat _ _ _ hj2, set_irrel _ _ _ hj2]
    rw [embed_set (acc.set (2 * pair) (keypadFirst face)) (2 * pair + 1)
      (keypadSecond face) (by rw [List.length_set, hlen]; exact h2)]
    unfold writePair
    rw [if_pos h2]
  · have hdec : decide (Int.ofNat (2 * pair + 1) < Int.ofNat cells) = false :=
      decide_eq_false (fun h => h2 (Int.ofNat_lt.mp h))
    rw [if_neg (by rw [hdec]; decide : ¬ (decide
        (Int.ofNat (2 * pair + 1) < Int.ofNat cells) = true))]
    rw [pure_eq_ok]
    unfold writePair
    rw [if_neg h2]

/-- After the scan: a blank face is `none`; a real face is `writePair`. -/
def faceLayAfter (cells : Nat) (acc : List Nat) (pair : Nat)
    (σ : Int × (Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Option Ecbs.Rolled)) := do
  let face := σ.2.1
  let next := σ.2.2
  if SudoRt.SEq.beq face (0 : Int) then
    pure (SudoRt.Flow.ret (none : Option Ecbs.Rolled))
  else
    let arr ← (do
      let ix ← SudoRt.mulI (Int.ofNat 2) (Int.ofNat pair)
      let d ← Ecbs.keypad_first face
      let acc ← SudoRt.putL (embed acc) ix d
      let j ← SudoRt.addI ix (1 : Int)
      if decide (j < Int.ofNat cells) then
        let d2 ← Ecbs.keypad_second face
        SudoRt.putL acc j d2
      else
        pure acc)
    pure (SudoRt.Flow.cont (next, arr))

private theorem face_lay_step (faces : List Nat) (i k : Nat)
    (hpos : 0 < faces.length) (hk : k ≤ faces.length - 1)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hfit : FitsLen faces.length)
    (st : Int × Int) (hst : st = (0, Int.ofNat k))
    (hread : readFace faces i = readFace faces k) :
    (∃ st', st' = (0, Int.ofNat (k + 1)) ∧
        readFace faces i = readFace faces (k + 1) ∧
        faceStep (embed faces) (Int.ofNat (faces.length - 1)) (Int.ofNat k, st) =
          if k = faces.length - 1 then
            .ok (SudoRt.Flow.brk (Int.ofNat k, st'))
          else
            .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), st'))) ∨
    (∃ f st', f ≠ 0 ∧ f ≤ 9 ∧ st' = (Int.ofNat f, Int.ofNat (k + 1)) ∧
        readFace faces i = some (f, k + 1) ∧
        faceStep (embed faces) (Int.ofNat (faces.length - 1)) (Int.ofNat k, st) =
          .ok (SudoRt.Flow.brk (Int.ofNat k, st'))) := by
  have hkf : k < faces.length := by
    simpa [Nat.sub_add_cancel hpos] using Nat.lt_succ_of_le hk
  have hfk : FitsLen (k + 1) := FitsLen.of_le hfit (Nat.succ_le_of_lt hkf)
  rw [hst]
  by_cases hz : faces[k] = 0
  · have hbody := faceBody_zero faces k hkf hz hfk
    refine Or.inl ⟨(0, Int.ofNat (k + 1)), rfl, ?_, ?_⟩
    · rw [hread, readFace_zero hkf hz]
    · unfold faceStep
      conv => lhs; zeta
      have hng : ¬ Int.ofNat k > Int.ofNat (faces.length - 1) := by
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        omega
      rw [if_neg hng, hbody, ok_bind]
      simpa using asc_tail (faces.length - 1) k hfk (0, Int.ofNat (k + 1))
  · have hbody := faceBody_pos faces k hkf (h9 k hkf) hz hfk
    refine Or.inr ⟨faces[k], (Int.ofNat (faces[k]), Int.ofNat (k + 1)), hz,
      h9 k hkf, rfl, ?_, ?_⟩
    · rw [hread, readFace_pos hkf hz]
    · unfold faceStep
      conv => lhs; zeta
      have hng : ¬ Int.ofNat k > Int.ofNat (faces.length - 1) := by
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        omega
      rw [if_neg hng, hbody, ok_bind]
      simp [pure_eq_ok]

theorem face_lay (faces : List Nat) (cells : Nat) (acc : List Nat) (pair i : Nat)
    (h9 : ∀ j (hj : j < faces.length), faces[j] ≤ 9)
    (hlen : acc.length = cells) (hix : 2 * pair < cells)
    (hfit2 : FitsLen (2 * pair + 1)) (hfit : FitsLen faces.length)
    (hi : i < faces.length) :
    (do
        let toV ← SudoRt.subI (Int.ofNat faces.length) (1 : Int)
        let fuel := if Int.ofNat i > toV then 1 else (toV - Int.ofNat i).natAbs + 1
        let r ← SudoRt.runLoopOn (Int.ofNat i, ((0 : Int), Int.ofNat i)) fuel
          (faceStep (embed faces) toV) (faceLayAfter cells acc pair)
          (fun r => pure (SudoRt.Flow.ret r))
        pure r) =
      match readFace faces i with
      | none => .ok (SudoRt.Flow.ret (none : Option Ecbs.Rolled))
      | some (f, n) =>
        .ok (SudoRt.Flow.cont (Int.ofNat n, embed (writePair cells acc pair f))) := by
  simp only [bind_pure]
  have hle : i ≤ faces.length - 1 := by omega
  rw [subI_ofNat_one _ (by omega : 0 < faces.length) hfit, ok_bind, fuelRange_eq]
  refine asc_brk_goal
      (fun k st => st = ((0 : Int), Int.ofNat k) ∧ readFace faces i = readFace faces k)
      (fun k st => ∃ f, f ≠ 0 ∧ f ≤ 9 ∧ st = (Int.ofNat f, Int.ofNat (k + 1)) ∧
        readFace faces i = some (f, k + 1))
      hle ⟨rfl, rfl⟩ ?_ ?_
  · intro k st _ hk hI
    obtain ⟨hst, hread⟩ := hI
    rcases face_lay_step faces i k (Nat.lt_of_le_of_lt (Nat.zero_le i) hi) hk h9 hfit
      st hst hread with
      ⟨st', hst', hread', hstep⟩ | ⟨f, st', hnz, h9f, hst', hread', hstep⟩
    · exact Or.inl ⟨st', ⟨hst', hread'⟩, hstep⟩
    · exact Or.inr ⟨st', ⟨f, hnz, h9f, hst', hread'⟩, hstep⟩
  · intro j st _ _ hdone
    cases hdone with
    | inl hI =>
      obtain ⟨hst, hread⟩ := hI
      have hk : faces.length - 1 + 1 = faces.length := by omega
      unfold faceLayAfter
      conv => lhs; zeta
      rw [hst]
      dsimp
      rw [sEq_int, decide_eq_true (by rfl : (0 : Int) = 0), if_pos rfl, pure_eq_ok,
        hread, hk, readFace_ge (Nat.le_refl _)]
    | inr hD =>
      obtain ⟨f, hnz, h9f, hst, hread⟩ := hD
      have h1 : 1 ≤ f := by omega
      unfold faceLayAfter
      conv => lhs; zeta
      rw [hst]
      have hbeq : SudoRt.SEq.beq (Int.ofNat f) (0 : Int) = false := by
        rw [sEq_int]
        exact decide_eq_false (by
          intro h
          exact hnz (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)))
      rw [if_neg (by rw [hbeq]; decide : ¬ (SudoRt.SEq.beq (Int.ofNat f) 0 = true))]
      rw [lay_die cells acc pair f h1 h9f hlen hix hfit2, ok_bind, pure_eq_ok, hread]

end EcbsLink2.Link2
