/-
  Reading aids for Em.lean against SPEC v3 §5, so the model can be checked without reading
  the sudo's search code. Facts about the model only; Link 2 (MegaDreifachV3.Link2) proves the
  emitted code equals the model, and nothing here relates either to the SPEC prose formally.
  - `edgeFaceOf_spec`, `cornerFaceOf_spec`: a successful piece search returns a face of the
    slot that holds the named piece, and that face shows the asked-for colour `x`.
  - `countUp` is SPEC §5.1's "count up from face X by rank r" (r steps up the 12-cycle of
    colours, after Q comes A). `turnedFace_countUp` / `turnedFace_king`: the first turn of a
    card step counts up from the base face, or takes the opposite face for a King (§5.3).
    `echoColour_countUp`: the echo colour counts up from X by Y (§5.4).
  - `cardStep_g_last`, `echoStep_g_last`, `dealFold_g_last`, `echoRun_g_last` and
    `emBlock_any_counters`: the counters never affect `g` or `last`, so `emBlock` is the same
    for any starting counter values (§5.6 costs are bookkeeping only).
-/
import MegaDreifachV3.Link2.FaceOf

namespace MegaDreifachV3.Em
open MegaDreifach MegaDreifach.Em MegaDreifachV3.Link2

/-! ## The piece searches -/

theorem edgeFaceOf_spec (g : Position) (a b x y : Fin 12) (h : edgeFaceOf? g a b x = some y) :
    ∃ slot : Fin 30, g.ep slot = edgeSlot a b ∧
      ((y = edgeFace slot.val 0 ∧ (edgeColoursAt g (edgeFace slot.val 0) (edgeFace slot.val 1)).1 = x) ∨
       (y = edgeFace slot.val 1 ∧ (edgeColoursAt g (edgeFace slot.val 0) (edgeFace slot.val 1)).2 = x)) := by
  unfold edgeFaceOf? at h
  dsimp only at h
  cases hl : lastIdx 30 (fun s => decide ((g.ep ⟨s % 30, Nat.mod_lt _ (by decide)⟩) = edgeSlot a b)) with
  | none => rw [hl] at h; cases h
  | some s =>
    rw [hl] at h
    have hs := lastIdx_lt _ _ _ hl
    have hp := lastIdx_spec _ _ _ hl
    simp only [decide_eq_true_eq, Nat.mod_eq_of_lt hs] at hp
    refine ⟨⟨s, hs⟩, hp, ?_⟩
    dsimp only at h
    split at h
    · cases h; exact Or.inl ⟨rfl, by assumption⟩
    · split at h
      · cases h; exact Or.inr ⟨rfl, by assumption⟩
      · cases h

theorem cornerFaceOf_spec (g : Position) (a b c x y : Fin 12)
    (h : cornerFaceOf? g a b c x = some y) :
    ∃ slot : Fin 20, g.cp slot = cornerSlot a b c ∧ ∃ j < 3, y = cornerFace slot.val j ∧
      colourOn y (cornerFace slot.val 1) (cornerFace slot.val 2)
        (cornerFace (cornerSlot a b c).val 0) (cornerFace (cornerSlot a b c).val 1)
        (cornerFace (cornerSlot a b c).val 2) (g.co slot) = x := by
  unfold cornerFaceOf? at h
  dsimp only at h
  cases hl : lastIdx 20 (fun s => decide ((g.cp ⟨s % 20, Nat.mod_lt _ (by decide)⟩) = cornerSlot a b c)) with
  | none => rw [hl] at h; cases h
  | some s =>
    rw [hl] at h
    have hs := lastIdx_lt _ _ _ hl
    have hp := lastIdx_spec _ _ _ hl
    simp only [decide_eq_true_eq, Nat.mod_eq_of_lt hs] at hp
    refine ⟨⟨s, hs⟩, hp, ?_⟩
    dsimp only at h
    simp only [Nat.mod_eq_of_lt hs] at h
    split at h
    · cases h; exact ⟨2, by decide, rfl, by assumption⟩
    · split at h
      · cases h; exact ⟨1, by decide, rfl, by assumption⟩
      · split at h
        · cases h; exact ⟨0, by decide, rfl, by assumption⟩
        · cases h

/-! ## Counting up (SPEC §5.1) -/

/-- One step up the 12-cycle of colours (after Q comes A). -/
def nextColour (f : Fin 12) : Fin 12 := ⟨(f.val + 1) % 12, Nat.mod_lt _ (by decide)⟩

/-- "Count up from face X by rank r": `r` steps up the colour cycle. -/
def countUp (x : Fin 12) : Nat → Fin 12
  | 0 => x
  | r + 1 => nextColour (countUp x r)

theorem countUp_val (x : Fin 12) (r : Nat) : (countUp x r).val = (x.val + r) % 12 := by
  induction r with
  | zero => simp [countUp, Nat.mod_eq_of_lt x.isLt]
  | succ r ih => simp only [countUp, nextColour, ih]; omega

theorem turnedFace_countUp (base : Fin 12) (rank : Nat) (h : rank < 12) :
    turnedFace base rank = countUp base rank := by
  apply Fin.ext
  rw [countUp_val]
  simp [turnedFace, h]

theorem turnedFace_king (base : Fin 12) : turnedFace base 12 = opp base := by
  simp [turnedFace]

theorem echoColour_countUp (g : Position) (held : Nat) :
    echoColour g held =
      let c := cardColour held
      let n := (suitNbrs c (held % 4 + 1)).1
      let n2 := (suitNbrs c (held % 4 + 1)).2
      countUp (edgeFaceOf g c n n) (cornerFaceOf g c n n2 n).val := by
  apply Fin.ext
  simp only [echoColour]
  rw [countUp_val]

/-! ## The counters never affect `g` or `last` -/

/-- A card step reads only `g` (its base face is an argument). -/
theorem cardStep_g_last (r r' : Run) (hg : r.g = r'.g)
    (base : Fin 12) (rank k : Nat) (c : Fin 12) :
    (cardStep r base rank k c).g = (cardStep r' base rank k c).g ∧
      (cardStep r base rank k c).last = (cardStep r' base rank k c).last := by
  simp [cardStep, turnRun, countFind, countRelook, hg]

theorem dealFold_g_last (l : List Nat) (r r' : Run) (hg : r.g = r'.g) (hl : r.last = r'.last) :
    (l.foldl dealStep r).g = (l.foldl dealStep r').g ∧
      (l.foldl dealStep r).last = (l.foldl dealStep r').last := by
  induction l generalizing r r' with
  | nil => exact ⟨hg, hl⟩
  | cons a l ih =>
    apply ih
    · unfold dealStep; rw [hl]; exact (cardStep_g_last r r' hg _ _ _ _).1
    · unfold dealStep; rw [hl]; exact (cardStep_g_last r r' hg _ _ _ _).2

theorem echoStep_g_last (held : Nat) (r r' : Run) (hg : r.g = r'.g) :
    (echoStep held r).g = (echoStep held r').g ∧
      (echoStep held r).last = (echoStep held r').last := by
  unfold echoStep
  dsimp only
  rw [hg]
  exact cardStep_g_last (countRegisterLooks r) (countRegisterLooks r') hg _ _ _ _

theorem echoRun_g_last (held n : Nat) (r r' : Run) (hg : r.g = r'.g) (hl : r.last = r'.last) :
    (echoRun held n r).g = (echoRun held n r').g ∧
      (echoRun held n r).last = (echoRun held n r').last := by
  induction n generalizing r r' with
  | zero => exact ⟨hg, hl⟩
  | succ n ih =>
    have h1 := echoStep_g_last held r r' hg
    exact ih _ _ h1.1 h1.2

/-- `E_m` from any starting counters: the same position as `emBlock` (which starts at 0). -/
theorem emBlock_any_counters (h : Position) (deal : List Nat) (r0 : Run) (hg : r0.g = h)
    (hl : r0.last = 0) :
    (echoRun (deal.getD 51 0) echoCount ((deal.take 52).foldl dealStep r0)).g = emBlock h deal := by
  have h1 := dealFold_g_last (deal.take 52) r0 (startRun h) hg hl
  exact (echoRun_g_last _ _ _ _ h1.1 h1.2).1

end MegaDreifachV3.Em
