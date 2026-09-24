/-
  M2 — Group law on positions: compose is associative; inverse round-trip.
  Software convention matches SPEC.md: `compose g h` = apply `h` then `g`.
  Zero sorry. No native_decide.
-/
import MegaDreifach.Position

namespace MegaDreifach

/-- Modular negation on `Fin 3` (Lean 4.14 has no `Neg (Fin n)`). -/
def neg3 (x : Fin 3) : Fin 3 :=
  ⟨(3 - x.val) % 3, Nat.mod_lt _ (by decide)⟩

def neg2 (x : Fin 2) : Fin 2 :=
  ⟨(2 - x.val) % 2, Nat.mod_lt _ (by decide)⟩

theorem fin_val_add {n : Nat} (a b : Fin n) :
    (a + b).val = (a.val + b.val) % n :=
  Fin.val_add a b

/-- `(x % n + y) % n = (x + y) % n` from `Nat.add_mod`. -/
private theorem add_mod_left' (x y n : Nat) :
    (x % n + y) % n = (x + y) % n := by
  have h1 : (x + y) % n = (x % n + y % n) % n := Nat.add_mod x y n
  have h2 : (x % n + y) % n = (x % n % n + y % n) % n := Nat.add_mod (x % n) y n
  have h3 : x % n % n = x % n := Nat.mod_mod x n
  rw [h1, h2, h3]

/-- `(x + y % n) % n = (x + y) % n`. -/
private theorem add_mod_right' (x y n : Nat) :
    (x + y % n) % n = (x + y) % n := by
  have h1 : (x + y) % n = (x % n + y % n) % n := Nat.add_mod x y n
  have h2 : (x + y % n) % n = (x % n + y % n % n) % n := Nat.add_mod x (y % n) n
  have h3 : y % n % n = y % n := Nat.mod_mod y n
  rw [h1, h2, h3]

theorem fin_add_assoc {n : Nat} (a b c : Fin n) :
    a + b + c = a + (b + c) := by
  apply Fin.ext
  have h1 : (a + b + c).val = ((a.val + b.val) % n + c.val) % n := by
    simp [fin_val_add]
  have h2 : (a + (b + c)).val = (a.val + (b.val + c.val) % n) % n := by
    simp [fin_val_add]
  rw [h1, h2]
  have hL : ((a.val + b.val) % n + c.val) % n = (a.val + b.val + c.val) % n :=
    add_mod_left' (a.val + b.val) c.val n
  have hR : (a.val + (b.val + c.val) % n) % n = (a.val + (b.val + c.val)) % n :=
    add_mod_right' a.val (b.val + c.val) n
  rw [hL, hR, Nat.add_assoc]

private theorem fin3_val (x : Fin 3) : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
  have := x.isLt; omega

private theorem fin2_val (x : Fin 2) : x.val = 0 ∨ x.val = 1 := by
  have := x.isLt; omega

theorem neg3_add (x : Fin 3) : neg3 x + x = 0 := by
  apply Fin.ext
  rcases fin3_val x with h | h | h <;> simp [neg3, fin_val_add, h]

theorem add_neg3 (x : Fin 3) : x + neg3 x = 0 := by
  apply Fin.ext
  rcases fin3_val x with h | h | h <;> simp [neg3, fin_val_add, h]

theorem neg2_add (x : Fin 2) : neg2 x + x = 0 := by
  apply Fin.ext
  rcases fin2_val x with h | h <;> simp [neg2, fin_val_add, h]

theorem add_neg2 (x : Fin 2) : x + neg2 x = 0 := by
  apply Fin.ext
  rcases fin2_val x with h | h <;> simp [neg2, fin_val_add, h]

theorem fin3_add_left_cancel (a b c : Fin 3) (h : a + b = a + c) : b = c := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have hv : (a.val + b.val) % 3 = (a.val + c.val) % 3 := by
    simpa [Fin.ext_iff, fin_val_add] using h
  omega

theorem fin2_add_left_cancel (a b c : Fin 2) (h : a + b = a + c) : b = c := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have hv : (a.val + b.val) % 2 = (a.val + c.val) % 2 := by
    simpa [Fin.ext_iff, fin_val_add] using h
  omega

/-- `compose g h` = apply `h` first, then `g` (function composition / left action). -/
def compose (g h : Position) : Position where
  cp := h.cp ∘ g.cp
  co := fun s => h.co (g.cp s) + g.co s
  ep := h.ep ∘ g.ep
  eo := fun s => h.eo (g.ep s) + g.eo s

/-- Inverse given explicit permutation inverses (DoubleDeal-style hypotheses). -/
def inverseWith (g : Position) (icp : Fin 20 → Fin 20) (iep : Fin 30 → Fin 30) : Position where
  cp := icp
  co := fun s => neg3 (g.co (icp s))
  ep := iep
  eo := fun s => neg2 (g.eo (iep s))

@[simp] theorem compose_id_right (g : Position) : compose g identity = g := by
  apply Position.ext
  · funext s; rfl
  · funext s; simp [compose, identity]
  · funext s; rfl
  · funext s; simp [compose, identity]

@[simp] theorem compose_id_left (g : Position) : compose identity g = g := by
  apply Position.ext
  · funext s; rfl
  · funext s; simp [compose, identity]
  · funext s; rfl
  · funext s; simp [compose, identity]

/-- M2: compose is associative. -/
theorem compose_assoc (a b c : Position) :
    compose (compose a b) c = compose a (compose b c) := by
  apply Position.ext
  · funext s; rfl
  · funext s
    simp [compose]
    exact (fin_add_assoc _ _ _).symm
  · funext s; rfl
  · funext s
    simp [compose]
    exact (fin_add_assoc _ _ _).symm

/-- M2: left inverse of `g`. -/
theorem compose_left_inv (g : Position) (icp : Fin 20 → Fin 20) (iep : Fin 30 → Fin 30)
    (hcpL : ∀ s, icp (g.cp s) = s) (hepL : ∀ s, iep (g.ep s) = s) :
    compose g (inverseWith g icp iep) = identity := by
  apply Position.ext
  · funext s; simp [compose, inverseWith, identity, Function.comp, hcpL]
  · funext s
    simp [compose, inverseWith, identity, hcpL, neg3_add]
  · funext s; simp [compose, inverseWith, identity, Function.comp, hepL]
  · funext s
    simp [compose, inverseWith, identity, hepL, neg2_add]

/-- M2: right inverse of `g`. -/
theorem compose_right_inv (g : Position) (icp : Fin 20 → Fin 20) (iep : Fin 30 → Fin 30)
    (hcpR : ∀ s, g.cp (icp s) = s) (hepR : ∀ s, g.ep (iep s) = s) :
    compose (inverseWith g icp iep) g = identity := by
  apply Position.ext
  · funext s; simp [compose, inverseWith, identity, Function.comp, hcpR]
  · funext s
    simp [compose, inverseWith, identity, hcpR, add_neg3]
  · funext s; simp [compose, inverseWith, identity, Function.comp, hepR]
  · funext s
    simp [compose, inverseWith, identity, hepR, add_neg2]

/-- M2: inverse round-trip in both orders. -/
theorem compose_inverse_rt (g : Position) (icp : Fin 20 → Fin 20) (iep : Fin 30 → Fin 30)
    (hcpL : ∀ s, icp (g.cp s) = s) (hcpR : ∀ s, g.cp (icp s) = s)
    (hepL : ∀ s, iep (g.ep s) = s) (hepR : ∀ s, g.ep (iep s) = s) :
    compose g (inverseWith g icp iep) = identity ∧
    compose (inverseWith g icp iep) g = identity :=
  ⟨compose_left_inv g icp iep hcpL hepL, compose_right_inv g icp iep hcpR hepR⟩

/-- Left multiplication `T · g`. Face turns act this way. -/
def leftMul (T g : Position) : Position := compose T g

theorem leftMul_eq_compose (T g : Position) : leftMul T g = compose T g := rfl

/-- Left cancellation when `g.cp` / `g.ep` are injective. -/
theorem leftMul_cancel (T T' g : Position)
    (hcp : Injective g.cp) (hep : Injective g.ep)
    (heq : leftMul T g = leftMul T' g) : T = T' := by
  have hcpEq : g.cp ∘ T.cp = g.cp ∘ T'.cp := by
    have := congrArg Position.cp heq
    simpa [leftMul, compose] using this
  have hepEq : g.ep ∘ T.ep = g.ep ∘ T'.ep := by
    have := congrArg Position.ep heq
    simpa [leftMul, compose] using this
  have hTcp : T.cp = T'.cp := by
    funext s
    exact hcp (congrFun hcpEq s)
  have hTep : T.ep = T'.ep := by
    funext s
    exact hep (congrFun hepEq s)
  have hcoEq : (fun s => g.co (T.cp s) + T.co s) = (fun s => g.co (T'.cp s) + T'.co s) := by
    have := congrArg Position.co heq
    simpa [leftMul, compose] using this
  have heoEq : (fun s => g.eo (T.ep s) + T.eo s) = (fun s => g.eo (T'.ep s) + T'.eo s) := by
    have := congrArg Position.eo heq
    simpa [leftMul, compose] using this
  apply Position.ext hTcp ?_ hTep ?_
  · funext s
    have : g.co (T.cp s) + T.co s = g.co (T'.cp s) + T'.co s := congrFun hcoEq s
    rw [hTcp] at this
    exact fin3_add_left_cancel _ _ _ this
  · funext s
    have : g.eo (T.ep s) + T.eo s = g.eo (T'.ep s) + T'.eo s := congrFun heoEq s
    rw [hTep] at this
    exact fin2_add_left_cancel _ _ _ this

end MegaDreifach
