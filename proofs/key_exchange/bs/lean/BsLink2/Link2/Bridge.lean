/-
  BS Link 2: the bridge between the model (`BsLink2.Spec`, `Nat` registers) and the emitted
  code (`Array Int`): `embed`, `val`, `Trits`, and the uniqueness of a register with a given
  value. Proof-only.
-/
import BsLink2.Spec
import BsLink2.Link2.Basic

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- The emitted `Field` of a model field. -/
def emb (F : Spec.Field) : Bs.Field :=
  { sudo_5Field_1n := Int.ofNat F.n, sudo_5Field_4toll := embed F.toll }

theorem valL_map_ofNat (xs : List Nat) : valL (xs.map Int.ofNat) = (Spec.value xs : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, valL, ih, Spec.value]
    simp [Int.ofNat_add, Int.ofNat_mul]

theorem val_embed (xs : List Nat) : val (embed xs) = (Spec.value xs : Int) := by
  unfold val; rw [toList_embed]; exact valL_map_ofNat xs

theorem trits_embed {xs : List Nat} (h : ∀ t ∈ xs, t ≤ 2) : Trits (embed xs) := by
  unfold Trits TritsL; rw [toList_embed]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have := h t ht
  constructor
  · exact Int.ofNat_zero_le t
  · show (t : Int) ≤ ((2 : Nat) : Int); exact Int.ofNat_le.mpr this

theorem nonneg_of_trits {a : Array Int} (h : Trits a) : Nonneg a := by
  intro i hi; exact (trits_get h i hi).1

theorem decode_trits {a : Array Int} (h : Trits a) : ∀ t ∈ decode a, t ≤ 2 := by
  intro t ht
  unfold decode at ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  have := h x hx
  omega

/-- A register is determined by its value: `toReg n (value xs) = xs` for `n` trits. -/
theorem toReg_value (xs : List Nat) (h : ∀ t ∈ xs, t ≤ 2) :
    Spec.toReg xs.length (Spec.value xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≤ 2 := h x (List.mem_cons_self _ _)
    have ht : ∀ t ∈ xs, t ≤ 2 := fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp only [List.length_cons, Spec.toReg, Spec.value]
    have h1 : (x + 3 * Spec.value xs) % 3 = x := by omega
    have h2 : (x + 3 * Spec.value xs) / 3 = Spec.value xs := by omega
    rw [h1, h2, ih ht]

/-- An emitted trit array of `n` holes whose value is `v` is `embed (toReg n v)`. -/
theorem eq_embed_toReg {a : Array Int} (h : Trits a) {n v : Nat} (hn : a.size = n)
    (hv : val a = (v : Int)) : a = embed (Spec.toReg n v) := by
  have he := embed_decode a (nonneg_of_trits h)
  have hval : Spec.value (decode a) = v := by
    have := val_embed (decode a)
    rw [he, hv] at this
    exact (Int.ofNat.inj this).symm
  have hlen : (decode a).length = n := by simp [decode, hn]
  rw [← he, ← hval, ← hlen, toReg_value _ (decode_trits h)]

theorem isReg_toReg (n v : Nat) : Spec.IsReg n (Spec.toReg n v) := by
  induction n generalizing v with
  | zero => exact ⟨rfl, by simp [Spec.toReg]⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (v / 3)
    refine ⟨by simp [Spec.toReg, h1], ?_⟩
    intro t ht
    simp only [Spec.toReg, List.mem_cons] at ht
    rcases ht with rfl | ht
    · omega
    · exact h2 t ht

theorem value_lt (xs : List Nat) (h : ∀ t ∈ xs, t ≤ 2) : Spec.value xs < 3 ^ xs.length := by
  induction xs with
  | nil => simp [Spec.value]
  | cons x xs ih =>
    have hx : x ≤ 2 := h x (List.mem_cons_self _ _)
    have := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [Spec.value, List.length_cons, Nat.pow_succ]
    omega

/-- The model's `p` as the integer the Link 2 lemmas use. -/
theorem p_cast (F : Spec.Field) (hF : F.Wf) :
    ((F.p : Nat) : Int) = pw F.n - val (embed F.toll) := by
  rw [val_embed, pw_natCast]
  have hc : F.c ≤ 3 ^ F.n := by
    have := value_lt F.toll hF.toll_trits
    have := Nat.pow_le_pow_right (show 0 < 3 by decide) (Nat.le_of_lt hF.toll_lt)
    unfold Spec.Field.c; omega
  unfold Spec.Field.p
  rw [Int.ofNat_sub hc]
  rfl

/-- A well-formed field's toll, embedded, is what the emitted `pay_toll`/`tidy` lemmas ask
    for: a non-empty trit array of fewer than `n` trits. Use as `hF.embed_parts`. -/
theorem _root_.BsLink2.Spec.Field.Wf.embed_parts {F : Spec.Field} (hF : F.Wf) :
    Trits (embed F.toll) ∧ 0 < (embed F.toll).size ∧ (embed F.toll).size < F.n := by
  refine ⟨trits_embed hF.toll_trits, ?_, ?_⟩ <;> rw [size_embed]
  · exact hF.toll_pos
  · exact hF.toll_lt

/-! ### Passing asserts without naming the sudo line

The emitted asserts carry the sudo source line as an argument. These lemmas leave it
free, so a proof that rewrites with them keeps working when `bs.sudo` moves a line. -/

/-- `assert_eq` passes when the emitted equality test holds. -/
theorem sudoAssertEq_of_beq {α : Type} [SudoRt.SEq α] [SudoRt.Canon α] {a b : α}
    (h : SudoRt.SEq.beq a b = true) (line : Nat) : SudoRt.sudoAssertEq a b line = .ok () := by
  unfold SudoRt.sudoAssertEq; rw [h]; rfl

/-- `assert_eq` on integers passes when they are equal. -/
theorem sudoAssertEq_int {a b : Int} (h : a = b) (line : Nat) :
    SudoRt.sudoAssertEq a b line = .ok () :=
  sudoAssertEq_of_beq (by rw [sEq_int, h]; exact decide_eq_true rfl) line

/-- `assert_eq x x` on integers passes. -/
theorem sudoAssertEq_self (a : Int) (line : Nat) : SudoRt.sudoAssertEq a a line = .ok () :=
  sudoAssertEq_int rfl line

/-- `assert !false` passes. -/
theorem sudoAssert_not_false (line : Nat) : SudoRt.sudoAssert (!false) line = .ok () := rfl

/-! ### Small-number helpers (the Scramble package has its own `fits_small`; see #162) -/

/-- A small natural fits `i64`. -/
theorem fits_small {n : Nat} (h : n ≤ 1000) : FitsLen n := by
  unfold FitsLen i64MaxNat; omega

theorem dec_ofNat_ge0 (n : Nat) : decide (Int.ofNat n ≥ 0) = true :=
  decide_eq_true (Int.ofNat_zero_le n)

theorem dec_ofNat_lt_ten (n : Nat) (h : n < 10) : decide (Int.ofNat n < 10) = true :=
  decide_eq_true ((ofNat_lt_iff n 10).mpr h)

theorem dec_ofNat_le_ten (n : Nat) (h : n ≤ 10) : decide (Int.ofNat n ≤ 10) = true :=
  decide_eq_true ((ofNat_le_iff n 10).mpr h)

theorem mulI_ten (a : Nat) (h : a < 100) : SudoRt.mulI (Int.ofNat a) 10 = .ok (Int.ofNat (a * 10)) :=
  mulI_ofNat a 10 (fits_small (by omega))

theorem mulI_one (a : Nat) (h : a < 1000) : SudoRt.mulI (Int.ofNat a) 1 = .ok (Int.ofNat (a * 1)) :=
  mulI_ofNat a 1 (fits_small (by omega))

theorem length_flatMap_le {α β} (l : List α) (f : α → List β) (k : Nat)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have h1 := h a (List.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem embed_set (l : List Nat) (k x : Nat) (h : k < (embed l).size) :
    (embed l).set ⟨k, h⟩ (Int.ofNat x) = embed (l.set k x) := by
  simp [embed, Array.set, List.map_set]

theorem embed_getElem? (l : List Nat) (i : Nat) : (embed l)[i]? = (l[i]?).map Int.ofNat := by
  simp [embed]

end BsLink2.Link2
