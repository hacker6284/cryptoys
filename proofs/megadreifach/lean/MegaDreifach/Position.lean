/-
  M1 — Megaminx position model and legality predicates.
  Matches SPEC.md: even cp, corner-ori sum ≡ 0 (mod 3),
  even ep, edge-ori sum ≡ 0 (mod 2). Zero sorry. No native_decide.
-/
import MegaDreifach.Basic
import MegaDreifach.NatUtil

namespace MegaDreifach

/-- Cubie-wise megaminx position (fixed centres). -/
structure Position where
  cp : Fin 20 → Fin 20
  co : Fin 20 → Fin 3
  ep : Fin 30 → Fin 30
  eo : Fin 30 → Fin 2

theorem Position.ext {a b : Position}
    (hcp : a.cp = b.cp) (hco : a.co = b.co)
    (hep : a.ep = b.ep) (heo : a.eo = b.eo) : a = b := by
  cases a; cases b; simp_all

def identity : Position where
  cp := id
  co := fun _ => 0
  ep := id
  eo := fun _ => 0

def listOf {n : Nat} (f : Fin n → Fin n) : List Nat :=
  (List.range n).map (fun i => if h : i < n then (f ⟨i, h⟩).val else 0)

def listOfOri {n m : Nat} (f : Fin n → Fin m) : List Nat :=
  (List.range n).map (fun i => if h : i < n then (f ⟨i, h⟩).val else 0)

theorem listOf_length {n : Nat} (f : Fin n → Fin n) : (listOf f).length = n := by
  simp [listOf]

theorem listOfOri_length {n m : Nat} (f : Fin n → Fin m) : (listOfOri f).length = n := by
  simp [listOfOri]

/-- Inversion count (pairs `i < j` with `p[i] > p[j]`). Parity is the sign. -/
def inversions : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter (fun y => decide (x > y))).length + inversions xs

def permParity (p : List Nat) : Nat := inversions p % 2

@[simp] theorem inversions_nil : inversions [] = 0 := rfl
@[simp] theorem permParity_nil : permParity [] = 0 := rfl

/-- Appending a strictly-larger last element adds no inversions. -/
theorem inversions_snoc (xs : List Nat) (z : Nat) (h : ∀ x ∈ xs, x < z) :
    inversions (xs ++ [z]) = inversions xs := by
  induction xs with
  | nil => simp [inversions]
  | cons x xs ih =>
      have hx : x < z := h x (List.mem_cons_self x xs)
      have hxs : ∀ y ∈ xs, y < z := fun y hy => h y (List.mem_cons_of_mem x hy)
      have hfilz : List.filter (fun y => decide (x > y)) [z] = [] := by
        have : decide (x > z) = false :=
          decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt hx))
        simp [this]
      have hfilter :
          (List.filter (fun y => decide (x > y)) (xs ++ [z])).length =
            (List.filter (fun y => decide (x > y)) xs).length := by
        rw [List.filter_append, hfilz, List.append_nil]
      rw [List.cons_append, inversions, hfilter, ih hxs]
      rfl

/-- `range n` is strictly increasing, so it has no inversions. -/
theorem inversions_range (n : Nat) : inversions (List.range n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ]
      have hmem : ∀ x ∈ List.range n, x < n := fun x hx => List.mem_range.mp hx
      rw [inversions_snoc (List.range n) n hmem, ih]

theorem inversions_range_20 : inversions (List.range 20) = 0 := inversions_range 20
theorem inversions_range_30 : inversions (List.range 30) = 0 := inversions_range 30

/-- M1 legality: even corner/edge perms and orientation parities. -/
def isLegal (p : Position) : Prop :=
  Injective p.cp ∧ Injective p.ep ∧
  permParity (listOf p.cp) = 0 ∧ permParity (listOf p.ep) = 0 ∧
  sumNats (listOfOri p.co) % 3 = 0 ∧ sumNats (listOfOri p.eo) % 2 = 0

theorem listOf_id (n : Nat) : listOf (id : Fin n → Fin n) = List.range n := by
  apply List.ext_getElem
  · simp [listOf]
  · intro i h1 h2
    have hi : i < n := by simp [listOf] at h1; exact h1
    simp [listOf, List.getElem_map, List.getElem_range, hi]

theorem listOfOri_const_zero (n m : Nat) (hm : 0 < m) :
    listOfOri (fun _ : Fin n => (⟨0, hm⟩ : Fin m)) = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [listOfOri]
  · intro i h1 h2
    have hi : i < n := by simp [listOfOri] at h1; exact h1
    simp [listOfOri, List.getElem_map, List.getElem_range, List.getElem_replicate, hi]

/-- M1: the solved position is legal. -/
theorem identity_isLegal : isLegal identity := by
  refine ⟨id_injective, id_injective, ?_, ?_, ?_, ?_⟩
  · have : listOf (identity.cp) = List.range 20 := listOf_id 20
    simp [permParity, this, inversions_range_20]
  · have : listOf (identity.ep) = List.range 30 := listOf_id 30
    simp [permParity, this, inversions_range_30]
  · have : listOfOri (identity.co) = List.replicate 20 0 := listOfOri_const_zero 20 3 (by decide)
    simp [this, sumNats_replicate_zero]
  · have : listOfOri (identity.eo) = List.replicate 30 0 := listOfOri_const_zero 30 2 (by decide)
    simp [this, sumNats_replicate_zero]

theorem legal_even_cp {p : Position} (h : isLegal p) : permParity (listOf p.cp) = 0 :=
  h.2.2.1
theorem legal_even_ep {p : Position} (h : isLegal p) : permParity (listOf p.ep) = 0 :=
  h.2.2.2.1
theorem legal_co_parity {p : Position} (h : isLegal p) : sumNats (listOfOri p.co) % 3 = 0 :=
  h.2.2.2.2.1
theorem legal_eo_parity {p : Position} (h : isLegal p) : sumNats (listOfOri p.eo) % 2 = 0 :=
  h.2.2.2.2.2

/-- `listOf` recovers each `f s`, so equal lists imply equal functions. -/
theorem listOf_get {n : Nat} (f : Fin n → Fin n) (s : Fin n) :
    (listOf f)[s.val]?.getD 0 = (f s).val := by
  simp [listOf, s.isLt]

theorem listOf_inj {n : Nat} (f g : Fin n → Fin n)
    (h : listOf f = listOf g) : f = g := by
  funext s
  have : (f s).val = (g s).val := by
    have hf := listOf_get f s
    have hg := listOf_get g s
    rw [← hf, ← hg, h]
  exact Fin.ext this

theorem listOfOri_get {n m : Nat} (f : Fin n → Fin m) (s : Fin n) :
    (listOfOri f)[s.val]?.getD 0 = (f s).val := by
  simp [listOfOri, s.isLt]

theorem listOfOri_inj {n m : Nat} (f g : Fin n → Fin m)
    (h : listOfOri f = listOfOri g) : f = g := by
  funext s
  have : (f s).val = (g s).val := by
    have hf := listOfOri_get f s
    have hg := listOfOri_get g s
    rw [← hf, ← hg, h]
  exact Fin.ext this

end MegaDreifach
