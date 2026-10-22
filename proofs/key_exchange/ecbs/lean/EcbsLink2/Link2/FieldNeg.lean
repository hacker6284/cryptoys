/-
  Negation in this trit basis. `mirrorTrits` is addition of the colour flip,
  `2 · a = −a`, and `3 · a = 0`. Multiplication on the left distributes
  because the schoolbook does not care which factor is laid.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldLin
import EcbsLink2.Link2.FieldComm
import EcbsLink2.Link2.OneField

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem trit_add_flip (a : Nat) (ha : a ≤ 2) : tritAdd a (flipTrit a) = 0 := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritAdd, flipTrit]

theorem trit_double (a : Nat) (ha : a ≤ 2) : tritAdd a a = flipTrit a := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritAdd, flipTrit]

private theorem coeff_le_local {xs : List Nat} (h : allTritList xs) (i : Nat) : coeff xs i ≤ 2 := by
  by_cases hi : i < xs.length
  · rw [coeff_eq_get xs i hi]
    exact h _ (List.getElem_mem hi)
  · unfold coeff
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp

private theorem coeff_ge_local (xs : List Nat) (t : Nat) (h : xs.length ≤ t) : coeff xs t = 0 := by
  unfold coeff
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp

theorem mirror_coeff (xs : List Nat) (t : Nat) :
    coeff (mirrorTrits xs) t = flipTrit (coeff xs t) := by
  rw [mirrorTrits_map]
  by_cases ht : t < xs.length
  · rw [coeff_eq_get _ t (by simp; exact ht), List.getElem_map, coeff_eq_get xs t ht]
  · rw [coeff_ge_local _ t (by simp; exact Nat.le_of_not_gt ht),
      coeff_ge_local xs t (Nat.le_of_not_gt ht), flipTrit]
    simp

theorem fieldAdd_trits (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
  intro x hx
  simp only [fieldAdd, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

theorem mirror_trits (xs : List Nat) : allTritList (mirrorTrits xs) := by
  intro a ha
  rw [mirrorTrits_map, List.mem_map] at ha
  rcases ha with ⟨c, _, rfl⟩
  exact flipTrit_le c

/-- A trit list plus its colour flip is the zero home. -/
theorem fieldAdd_mirror (n : Nat) (xs : List Nat) (ht : allTritList xs) :
    fieldAdd n xs (mirrorTrits xs) = zeroPeg n := by
  apply List.ext_getElem
  · simp [fieldAdd, zeroPeg, List.length_map, List.length_range, List.length_replicate]
  · intro i hi _
    simp only [fieldAdd, zeroPeg, List.getElem_map, List.getElem_range, List.getElem_replicate]
    rw [mirror_coeff]
    exact trit_add_flip _ (coeff_le_local ht i)

/-- Twice a trit list is its colour flip. In this basis `2 = −1`. -/
theorem fieldAdd_double (n : Nat) (xs : List Nat) (ht : allTritList xs)
    (hlen : xs.length = n) :
    fieldAdd n xs xs = mirrorTrits xs := by
  apply List.ext_getElem
  · simp [fieldAdd, mirrorTrits, List.length_map, List.length_range, hlen]
  · intro i hi _
    simp only [fieldAdd, mirrorTrits_map, List.getElem_map, List.getElem_range]
    have hi0 : i < xs.length := by
      rw [hlen]
      simpa [fieldAdd, List.length_map, List.length_range] using hi
    rw [coeff_eq_get xs i hi0]
    exact trit_double _ (ht _ (List.getElem_mem hi0))

/-- Three copies of a trit list sum to zero. -/
theorem fieldAdd_triple (n : Nat) (xs : List Nat) (ht : allTritList xs)
    (hlen : xs.length = n) :
    fieldAdd n (fieldAdd n xs xs) xs = zeroPeg n := by
  rw [fieldAdd_double n xs ht hlen, fieldAdd_comm, fieldAdd_mirror n xs ht]

/-- Left distributivity. `fieldMul` does not care which factor is laid. -/
theorem fieldMul_left_add (n k bench : Nat) (x y z : List Nat)
    (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) (hn : n ≤ bench) :
    fieldMul n k bench (fieldAdd n y z) x =
      fieldAdd n (fieldMul n k bench y x) (fieldMul n k bench z x) := by
  rw [fieldMul_comm n k bench (fieldAdd n y z) x (fieldAdd_trits n y z) hx,
    fieldMul_right_add n k bench x y z hx hy hz hn,
    fieldMul_comm n k bench x y hx hy, fieldMul_comm n k bench x z hx hz]

/-- Negating the second factor negates the product. -/
theorem fieldMul_mirror_right (n k bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    fieldMul n k bench x (mirrorTrits y) = mirrorTrits (fieldMul n k bench x y) := by
  rw [fieldMul_comm n k bench x (mirrorTrits y) hx (mirror_trits y),
    fieldMul_mirror_left n k bench y x hy hx,
    fieldMul_comm n k bench y x hy hx]

end EcbsLink2.Link2
