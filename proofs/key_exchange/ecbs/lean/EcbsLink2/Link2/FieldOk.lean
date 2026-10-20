/-
  `FieldOk t`: every nonzero trit list of length `t.n` has `fieldInv ≠ none`.
  That is the zero-home statement. It empties `RunNonUnit` for such a run.
  Demo is the kernel check of the `3^7` lists, in chunks. Toy is `3^23`
  and is not decided here.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OneField
import EcbsLink2.Link2.School
import EcbsLink2.Link2.WalkFformCase
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The zero home: `n` zeros. -/
abbrev zeroHome (n : Nat) : List Nat := zeroPeg n

/-- Every nonzero home of length `n`, written in trits, inverts. -/
def FieldOk (t : Spec.Tier) : Prop :=
  ∀ x, allTritList x → x.length = t.n → x ≠ zeroHome t.n →
    fieldInv t.n t.k t.benchlen x ≠ none

private theorem and3 (a b c : Bool) (h : ((a && b) && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c
  all_goals try exact ⟨rfl, rfl, rfl⟩
  all_goals simp at h

private theorem list_beq_decide (xs ys : List Nat) :
    (xs == ys) = decide (xs = ys) := by
  by_cases h : xs = ys <;> simp [h]

private theorem check_sound (n k bench : Nat) (x : List Nat)
    (h : ((x == zeroHome n) || (specInv n k bench x).isSome) = true)
    (hne : x ≠ zeroHome n) :
    fieldInv n k bench x ≠ none := by
  have hbf : (x == zeroHome n) = false := by
    rw [list_beq_decide, decide_eq_false_iff_not]
    exact hne
  rw [hbf, Bool.false_or] at h
  intro hnone
  rw [← specInv_eq] at hnone
  rw [hnone] at h
  simp [Option.isSome] at h

/-- Every length-`left` trit extension of `pref`. The leaf is `fieldInv`. -/
def allTrit (left n k bench : Nat) (pref : List Nat) : Bool :=
  match left with
  | 0 => (pref == zeroHome n) || (specInv n k bench pref).isSome
  | left + 1 =>
      allTrit left n k bench (pref ++ [0]) &&
      allTrit left n k bench (pref ++ [1]) &&
      allTrit left n k bench (pref ++ [2])

theorem allTrit_sound (left n k bench : Nat) (pref : List Nat)
    (h : allTrit left n k bench pref = true) :
    ∀ suf, suf.length = left → allTritList suf →
      pref ++ suf ≠ zeroHome n →
      fieldInv n k bench (pref ++ suf) ≠ none := by
  induction left generalizing pref with
  | zero =>
    intro suf hlen _ht hne
    cases suf with
    | nil =>
      simp only [List.append_nil] at hne ⊢
      have hck : ((pref == zeroHome n) || (specInv n k bench pref).isSome) = true := by
        simpa [allTrit] using h
      exact check_sound n k bench pref hck hne
    | cons _ _ => simp at hlen
  | succ left ih =>
    intro suf hlen ht hne
    cases suf with
    | nil => simp at hlen
    | cons d rest =>
      have hd : d ≤ 2 := ht d (List.mem_cons_self _ _)
      have hrest : allTritList rest := by
        intro a ha
        exact ht a (List.mem_cons_of_mem _ ha)
      have hlen' : rest.length = left := by
        simp at hlen
        exact hlen
      have hjoin : (pref ++ [d]) ++ rest = pref ++ (d :: rest) := by
        simp [List.append_assoc]
      unfold allTrit at h
      obtain ⟨ha, hb, hc⟩ := and3 _ _ _ h
      have hdig : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hdig with rfl | rfl | rfl
      · have hne' : (pref ++ [0]) ++ rest ≠ zeroHome n := by
          simpa [hjoin] using hne
        have hs := ih (pref ++ [0]) ha rest hlen' hrest hne'
        simpa [hjoin] using hs
      · have hne' : (pref ++ [1]) ++ rest ≠ zeroHome n := by
          simpa [hjoin] using hne
        have hs := ih (pref ++ [1]) hb rest hlen' hrest hne'
        simpa [hjoin] using hs
      · have hne' : (pref ++ [2]) ++ rest ≠ zeroHome n := by
          simpa [hjoin] using hne
        have hs := ih (pref ++ [2]) hc rest hlen' hrest hne'
        simpa [hjoin] using hs

/-- A trit run of length `n` is not the open `RunNonUnit` cell. -/
theorem runNonUnit_field (t : Spec.Tier) (hF : FieldOk t) (baseX px : List Nat)
    (ht : allTritList (affineRun t.n t.k t.benchlen baseX px))
    (hlen : (affineRun t.n t.k t.benchlen baseX px).length = t.n) :
    ¬ RunNonUnit t.n t.k t.benchlen baseX px := by
  intro hbad
  have hne : affineRun t.n t.k t.benchlen baseX px ≠ zeroHome t.n := by
    intro hz
    exact hbad.1 (by simpa [zeroHome, zeroPeg] using hz)
  exact hF _ ht hlen hne hbad.2

/-- Under `FieldOk`, the run is zero or it inverts. -/
theorem cell_run_field (t : Spec.Tier) (hF : FieldOk t) (baseX px : List Nat)
    (ht : allTritList (affineRun t.n t.k t.benchlen baseX px))
    (hlen : (affineRun t.n t.k t.benchlen baseX px).length = t.n) :
    affineRun t.n t.k t.benchlen baseX px = zeroHome t.n ∨
      ∃ g, fieldInv t.n t.k t.benchlen (affineRun t.n t.k t.benchlen baseX px) = some g := by
  have hnot := runNonUnit_field t hF baseX px ht hlen
  rcases cell_run_split t.n t.k t.benchlen baseX px with h0 | hsome | hbad
  · left
    simpa [zeroHome, zeroPeg] using h0
  · exact Or.inr hsome
  · exact absurd hbad hnot

theorem demo_rungs_6 : specRungs 6 = [1, 2] := by
  decide

/-- The Demo climb is two rungs. A white hole-0 product keeps the gap. -/
theorem specInv_white_7 (x g1 g2 g : List Nat)
    (h1 : invRung 7 5 20 x x 1 2 false = (g1, 3))
    (h2 : invRung 7 5 20 x g1 3 1 true = (g2, 3))
    (hg : fieldCube 7 5 20 g2 = g)
    (hv : fieldMul 7 5 20 g x = whiteHole0 7) :
    specInv 7 5 20 x = some g := by
  unfold specInv invGapOf
  rw [show (7 - 1) = 6 by decide, demo_rungs_6]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h1]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h2]
  unfold invClimb
  rw [hg, hv, if_pos rfl]

/-- A red hole-0 product mirrors the gap. -/
theorem specInv_mirror_7 (x g1 g2 g ans : List Nat)
    (h1 : invRung 7 5 20 x x 1 2 false = (g1, 3))
    (h2 : invRung 7 5 20 x g1 3 1 true = (g2, 3))
    (hg : fieldCube 7 5 20 g2 = g)
    (hv : fieldMul 7 5 20 g x = 2 :: List.replicate 6 0)
    (hm : mirrorTrits g = ans) :
    specInv 7 5 20 x = some ans := by
  unfold specInv invGapOf
  rw [show (7 - 1) = 6 by decide, demo_rungs_6]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h1]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h2]
  unfold invClimb
  rw [hg]
  have hnot : ¬ (2 :: List.replicate 6 0 = whiteHole0 7) := by decide
  rw [hv, if_neg hnot, if_pos rfl, hm]

theorem field_of_spec (x g : List Nat) (h : specInv 7 5 20 x = some g) :
    fieldInv 7 5 20 x ≠ none := by
  rw [← specInv_eq]
  intro hnone
  rw [hnone] at h
  cases h

theorem cons7 (x : List Nat) (h : x.length = 7) :
    ∃ a b c d e f g, x = a :: b :: c :: d :: e :: f :: g :: [] := by
  cases x with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => simp at h
          | cons e xs =>
            cases xs with
            | nil => simp at h
            | cons f xs =>
              cases xs with
              | nil => simp at h
              | cons g xs =>
                cases xs with
                | nil => exact ⟨a, b, c, d, e, f, g, rfl⟩
                | cons _ _ => simp at h

theorem demo_inv_onepeg : specInv 7 5 20 [1, 0, 0, 0, 0, 0, 0] = some [1, 0, 0, 0, 0, 0, 0] := by
  have h1 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] 1 2 false =
      ([1, 0, 0, 0, 0, 0, 0], 3) := by decide
  have h2 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] 3 1 true =
      ([1, 0, 0, 0, 0, 0, 0], 3) := by decide
  have hg : fieldCube 7 5 20 [1, 0, 0, 0, 0, 0, 0] = [1, 0, 0, 0, 0, 0, 0] := by decide
  have hv : fieldMul 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] = whiteHole0 7 := by
    decide
  exact specInv_white_7 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0]
    [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] h1 h2 hg hv

end EcbsLink2.Link2
