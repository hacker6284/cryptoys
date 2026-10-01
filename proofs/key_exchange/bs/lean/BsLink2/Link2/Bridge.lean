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

end BsLink2.Link2
