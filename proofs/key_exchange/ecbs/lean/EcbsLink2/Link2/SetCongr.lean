/-
  `Array.set` along an array equality. The index proof mentions the old size,
  so `rw` on the array will not type-check. `subst` does, because both sides
  are variables.
-/

theorem Array.set_congr_arr {α : Type} {a e : Array α} (h : a = e) {i : Nat}
    (hi : i < a.size) (v : α) :
    a.set ⟨i, hi⟩ v = e.set ⟨i, h ▸ hi⟩ v := by
  subst h
  rfl
