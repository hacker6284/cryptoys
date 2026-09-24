/-
  Compose / InverseCompose as reindexing by a fixed bijection on Fin n.
  Correctness: mutual inverses, and CTR nonce-reuse keystream uniqueness
  at the Compose layer (SPEC §6 S1 / S11). Not a bit-security claim.
-/
namespace TwoDeck

def composeVec (n : Nat) (α : Type _) (M : Fin n → α) (pos : Fin n → Fin n) :
    Fin n → α :=
  fun j => M (pos j)

theorem compose_mutual_inverses (n : Nat) (α : Type _)
    (M : Fin n → α) (pos invPos : Fin n → Fin n)
    (hL : ∀ j, invPos (pos j) = j) (hR : ∀ i, pos (invPos i) = i) :
    composeVec n α (fun i => M (invPos i)) pos = M ∧
    (fun i => composeVec n α M pos (invPos i)) = M := by
  constructor
  · funext j; simp [composeVec, hL]
  · funext i; simp [composeVec, hR]

theorem compose_mutual_inverses_52 (α : Type _)
    (M : Fin 52 → α) (pos invPos : Fin 52 → Fin 52)
    (hL : ∀ j, invPos (pos j) = j) (hR : ∀ i, pos (invPos i) = i) :
    composeVec 52 α (fun i => M (invPos i)) pos = M ∧
    (fun i => composeVec 52 α M pos (invPos i)) = M :=
  compose_mutual_inverses 52 α M pos invPos hL hR

/-- CTR nonce-reuse KP lemma (Compose layer): if `C = composeVec M pos` and `M` is
injective, then `pos j` is the unique index `i` with `M i = C j`. -/
theorem compose_kp_unique (n : Nat) (α : Type _)
    (M : Fin n → α) (pos : Fin n → Fin n) (C : Fin n → α)
    (hC : C = composeVec n α M pos)
    (hInj : ∀ i j : Fin n, M i = M j → i = j) :
    ∀ (j i : Fin n), M i = C j → i = pos j := by
  intro j i hi
  have : M i = M (pos j) := by
    rw [hi, hC]; rfl
  exact hInj i (pos j) this

theorem compose_kp_unique_52 (α : Type _)
    (M : Fin 52 → α) (pos : Fin 52 → Fin 52) (C : Fin 52 → α)
    (hC : C = composeVec 52 α M pos)
    (hInj : ∀ i j : Fin 52, M i = M j → i = j) :
    ∀ (j i : Fin 52), M i = C j → i = pos j :=
  compose_kp_unique 52 α M pos C hC hInj

end TwoDeck
