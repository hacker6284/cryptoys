/-
  List left/right rotates and modular cancel lemmas — correctness, zero sorry.
  Used by ShiftRows and SumRanks.
-/
namespace DoubleDeal

/-- Left rotate by `n` (mod length). Empty list is fixed. -/
def rotL (xs : List α) (n : Nat) : List α :=
  if xs.length = 0 then xs
  else xs.drop (n % xs.length) ++ xs.take (n % xs.length)

/-- Right rotate by `n` (mod length). Empty list is fixed. -/
def rotR (xs : List α) (n : Nat) : List α :=
  if xs.length = 0 then xs
  else xs.drop (xs.length - n % xs.length) ++ xs.take (xs.length - n % xs.length)

def sumNats : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNats xs

theorem sumNats_append (xs ys : List Nat) :
    sumNats (xs ++ ys) = sumNats xs + sumNats ys := by
  induction xs <;> simp [sumNats, *]; omega

theorem sumNats_rotL (xs : List Nat) (n : Nat) :
    sumNats (rotL xs n) = sumNats xs := by
  unfold rotL; split
  · rfl
  · rw [sumNats_append, Nat.add_comm, ← sumNats_append, List.take_append_drop]

theorem sumNats_rotR (xs : List Nat) (n : Nat) :
    sumNats (rotR xs n) = sumNats xs := by
  unfold rotR; split
  · rfl
  · rw [sumNats_append, Nat.add_comm, ← sumNats_append, List.take_append_drop]

theorem length_rotL (xs : List α) (n : Nat) : (rotL xs n).length = xs.length := by
  unfold rotL; split
  · rfl
  · next hne =>
    rw [List.length_append, List.length_drop, List.length_take]
    have : n % xs.length < xs.length := Nat.mod_lt _ (Nat.pos_of_ne_zero hne)
    omega

theorem length_rotR (xs : List α) (n : Nat) : (rotR xs n).length = xs.length := by
  unfold rotR; split
  · rfl
  · next hne =>
    rw [List.length_append, List.length_drop, List.length_take]
    omega

private theorem drop_append_exact (xs : List α) (k : Nat) (_hk : k ≤ xs.length) :
    List.drop (xs.length - k) (xs.drop k ++ xs.take k) = xs.take k := by
  have hlen : (xs.drop k).length = xs.length - k := List.length_drop k xs
  have hle : xs.length - k ≤ (xs.drop k).length := by omega
  rw [List.drop_append_of_le_length hle]
  have hempty : List.drop (xs.length - k) (xs.drop k) = [] := by
    rw [← List.length_eq_zero, List.length_drop, hlen, Nat.sub_self]
  rw [hempty, List.nil_append]

private theorem take_append_exact (xs : List α) (k : Nat) (_hk : k ≤ xs.length) :
    List.take (xs.length - k) (xs.drop k ++ xs.take k) = xs.drop k := by
  have hlen : (xs.drop k).length = xs.length - k := List.length_drop k xs
  have hle : xs.length - k ≤ (xs.drop k).length := by omega
  rw [List.take_append_of_le_length hle]
  exact List.take_of_length_le (by omega)

theorem rotR_rotL (xs : List α) (n : Nat) : rotR (rotL xs n) n = xs := by
  by_cases h0 : xs.length = 0
  · unfold rotL rotR; simp [h0]
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
    have hkle : n % xs.length ≤ xs.length := Nat.le_of_lt (Nat.mod_lt _ hpos)
    unfold rotL; simp only [h0, ↓reduceIte]
    unfold rotR
    have hlenEq : (xs.drop (n % xs.length) ++ xs.take (n % xs.length)).length = xs.length := by
      rw [List.length_append, List.length_drop, List.length_take]; omega
    simp only [hlenEq, h0, ↓reduceIte]
    rw [drop_append_exact xs (n % xs.length) hkle,
        take_append_exact xs (n % xs.length) hkle,
        List.take_append_drop]

theorem rotL_rotR (xs : List α) (n : Nat) : rotL (rotR xs n) n = xs := by
  by_cases h0 : xs.length = 0
  · unfold rotL rotR; simp [h0]
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
    unfold rotR; simp only [h0, ↓reduceIte]
    unfold rotL
    have hlenEq : (xs.drop (xs.length - n % xs.length) ++
        xs.take (xs.length - n % xs.length)).length = xs.length := by
      rw [List.length_append, List.length_drop, List.length_take]; omega
    simp only [hlenEq, h0, ↓reduceIte]
    have hdm : (xs.drop (xs.length - n % xs.length)).length = n % xs.length := by
      rw [List.length_drop]
      have hk : n % xs.length ≤ xs.length := Nat.le_of_lt (Nat.mod_lt _ hpos)
      exact Nat.sub_sub_self hk
    have hle' : n % xs.length ≤ (xs.drop (xs.length - n % xs.length)).length := by omega
    rw [List.drop_append_of_le_length hle', List.take_append_of_le_length hle']
    have hempty : List.drop (n % xs.length) (xs.drop (xs.length - n % xs.length)) = [] := by
      rw [← List.length_eq_zero, List.length_drop, hdm, Nat.sub_self]
    have ht : List.take (n % xs.length) (xs.drop (xs.length - n % xs.length)) =
              xs.drop (xs.length - n % xs.length) :=
      List.take_of_length_le (by omega)
    rw [hempty, List.nil_append, ht]
    exact List.take_append_drop (xs.length - n % xs.length) xs

/-- Modular cancel: `(c + n) % n = c` when `c < n`. -/
theorem add_n_mod (c n : Nat) (hc : c < n) : (c + n) % n = c := by
  have := Nat.add_mul_mod_self_right c 1 n
  rw [Nat.one_mul] at this
  rw [this, Nat.mod_eq_of_lt hc]

theorem rotate_left_right_cancel (c s n : Nat) (hc : c < n) (hn : 0 < n) :
    ((c + s % n) % n + (n - s % n)) % n = c := by
  let s' := s % n
  have : s' < n := Nat.mod_lt _ hn
  calc ((c + s') % n + (n - s')) % n
      = (c + s' + (n - s')) % n := Nat.mod_add_mod _ _ _
    _ = (c + n) % n := by rw [show c + s' + (n - s') = c + n from by omega]
    _ = c := add_n_mod c n hc

theorem rotate_right_left_cancel (c s n : Nat) (hc : c < n) (hn : 0 < n) :
    ((c + (n - s % n)) % n + s % n) % n = c := by
  let s' := s % n
  have : s' < n := Nat.mod_lt _ hn
  calc ((c + (n - s')) % n + s') % n
      = (c + (n - s') + s') % n := Nat.mod_add_mod _ _ _
    _ = (c + n) % n := by rw [show c + (n - s') + s' = c + n from by omega]
    _ = c := add_n_mod c n hc

/-- Rank-sum of a list under `rank`. -/
def rankSum (rank : α → Nat) (xs : List α) : Nat :=
  sumNats (xs.map rank)

theorem map_rotL (f : α → β) (xs : List α) (n : Nat) :
    (rotL xs n).map f = rotL (xs.map f) n := by
  unfold rotL
  by_cases h : xs.length = 0
  · simp [h, List.length_map]
  · have hm : (xs.map f).length = xs.length := by simp [List.length_map]
    have h' : (xs.map f).length ≠ 0 := by simp [hm, h]
    simp only [h, hm, h', ↓reduceIte, List.map_append, List.map_drop, List.map_take]

theorem map_rotR (f : α → β) (xs : List α) (n : Nat) :
    (rotR xs n).map f = rotR (xs.map f) n := by
  unfold rotR
  by_cases h : xs.length = 0
  · simp [h, List.length_map]
  · have hm : (xs.map f).length = xs.length := by simp [List.length_map]
    simp only [h, hm, ↓reduceIte, List.map_append, List.map_drop, List.map_take]

theorem rankSum_rotL (rank : α → Nat) (xs : List α) (n : Nat) :
    rankSum rank (rotL xs n) = rankSum rank xs := by
  unfold rankSum
  rw [map_rotL, sumNats_rotL]

theorem rankSum_rotR (rank : α → Nat) (xs : List α) (n : Nat) :
    rankSum rank (rotR xs n) = rankSum rank xs := by
  unfold rankSum
  rw [map_rotR, sumNats_rotR]

theorem rotL_perm (xs : List α) (n : Nat) : List.Perm (rotL xs n) xs := by
  unfold rotL; split
  · exact List.Perm.refl _
  · have p : List.Perm (xs.drop (n % xs.length) ++ xs.take (n % xs.length))
                       (xs.take (n % xs.length) ++ xs.drop (n % xs.length)) :=
      List.perm_append_comm
    exact p.trans (List.Perm.of_eq (List.take_append_drop _ _))

theorem rotR_perm (xs : List α) (n : Nat) : List.Perm (rotR xs n) xs := by
  unfold rotR; split
  · exact List.Perm.refl _
  · have p : List.Perm (xs.drop (xs.length - n % xs.length) ++ xs.take (xs.length - n % xs.length))
                       (xs.take (xs.length - n % xs.length) ++ xs.drop (xs.length - n % xs.length)) :=
      List.perm_append_comm
    exact p.trans (List.Perm.of_eq (List.take_append_drop _ _))

end DoubleDeal
