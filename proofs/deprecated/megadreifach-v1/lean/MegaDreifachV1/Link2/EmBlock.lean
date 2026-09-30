/-
  LINK 2. `Generated.em_block` refines `Em.emBlock` on every deal array of
  length at least 52 (entries are arbitrary naturals), and every starting
  position. No other hypothesis: the `recipe_a` side conditions are
  discharged by the `GripOk` invariant (`EmInv.lean`).

  Algebraic Link 2 only. Not `v_Hash` (the DM chaining + padding + unranking
  composition is not stated here).
-/
import MegaDreifachV1.Link2.EmInv
import MegaDreifachV1.Link2.RequirePerm
import MegaDreifachV1.Link2.PosBytes

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

/-- State after the first `i` G2 steps. -/
def g2Pre (h : Position) (deal : List Nat) (i : Nat) : Position × Grip :=
  (deal.take i).foldl g2Step (h, gripId)

theorem g2Pre_succ (h : Position) (deal : List Nat) (i : Nat) (hi : i < deal.length) :
    g2Pre h deal (i + 1) = g2Step (g2Pre h deal i) deal[i] := by
  unfold g2Pre
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [List.foldl_append]

theorem gripOk_g2Pre (h : Position) (deal : List Nat) (i : Nat) :
    GripOk (g2Pre h deal i).2 := by
  unfold g2Pre
  generalize deal.take i = xs
  suffices ∀ st : Position × Grip, GripOk st.2 → GripOk (xs.foldl g2Step st).2 from
    this _ gripOk_id
  induction xs with
  | nil => intro st hs; exact hs
  | cons x xs ih => intro st hs; exact ih _ (gripOk_g2Step st x hs)

theorem f3Iter_succ' (n : Nat) (st : Position × Grip) :
    f3Iter (n + 1) st = f3Step (f3Iter n st) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => rw [f3Iter, ih, f3Iter]

theorem gripOk_f3Iter (n : Nat) (st : Position × Grip) (hs : GripOk st.2) :
    GripOk (f3Iter n st).2 := by
  induction n generalizing st with
  | zero => exact hs
  | succ n ih => rw [f3Iter]; exact ih _ (gripOk_f3Step st hs)

theorem embedGrip_id : embedGrip gripId = embed (List.range 12) := by
  unfold embedGrip; congr 1

/-- `loopTailR` with a larger bound on `toN`. -/
theorem loopTailBig {α ρ : Type} (i toN : Nat) (hi : i ≤ toN) (htoN : toN ≤ 1000) (st : α) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := ρ) (Int.ofNat i, st)) : Except SudoRt.Trap _)
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', st))) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  by_cases heq : i = toN
  · subst heq; simp [beq_int_iff]; rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    have hf : FitsLen (i + 1) :=
      FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 1001) (by omega)
    rw [ite_int_beq, if_neg hneI, addI_ofNat_one i hf, ok_bind, if_neg heq]
    rfl

/-- `Generated.em_block` refines `Em.emBlock`. -/
theorem em_block_refines (h : Position) (deal : List Nat) (hlen : 52 ≤ deal.length) :
    Megadreifach.em_block (embedPos h) (embed deal) = .ok (embedPos (emBlock h deal)) := by
  unfold Megadreifach.em_block
  rw [show (12 : Int) = Int.ofNat 12 from rfl,
    range_list_refines 12 (by decide)
      (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 12) (Nat.le_refl _)),
    ok_bind, ← embedGrip_id]
  dsimp only
  rw [except_bind_pure]
  apply chain_loop (f := fun i => (embedPos (g2Pre h deal i).1, embedGrip (g2Pre h deal i).2))
    (fromN := 0) (toN := 51) (hle := by decide)
  · intro i _ hi
    dsimp only
    rw [show (51 : Int) = Int.ofNat 51 from rfl, if_neg (ofNat_not_gt hi),
      atL_embed deal i (by omega), ok_bind,
      g2_step_refines' _ _ _ (gripOk_g2Pre h deal i), ok_bind]
    dsimp only
    rw [pure_bind, ← g2Pre_succ h deal i (by omega)]
    exact loopTailBig i 51 hi (by omega) _
  · dsimp only
    rw [show Megadreifach.f3_t = Int.ofNat 12 from rfl]
    rw [except_bind_pure]
    apply chain_loop
      (f := fun t => (embedPos (f3Iter (t - 1) (g2Pre h deal 52)).1,
        embedGrip (f3Iter (t - 1) (g2Pre h deal 52)).2))
      (fromN := 1) (toN := 12) (hle := by decide)
    · intro t ht1 ht
      dsimp only
      rw [if_neg (ofNat_not_gt ht),
        f3_step_refines' _ _ (gripOk_f3Iter _ _ (gripOk_g2Pre h deal 52)), ok_bind]
      dsimp only
      rw [pure_bind, show t + 1 - 1 = (t - 1) + 1 by omega, f3Iter_succ']
      exact loopTailBig t 12 ht (by omega) _
    · dsimp only
      rfl

/-- Davies–Meyer step: `em_block` then `compose h`. -/
theorem dm_step_refines (h : Position) (deal : List Nat) (hlen : 52 ≤ deal.length) :
    (Megadreifach.em_block (embedPos h) (embed deal) >>= fun e => Megadreifach.compose (embedPos h) e) =
      .ok (embedPos (dmStep h deal)) := by
  rw [em_block_refines h deal hlen, ok_bind, compose_refines]
  rfl

/-- `body_from` reduces to `position_to_bytes` of the algebraic DM step on every
    52-permutation deal. -/
theorem body_from_refines (h : Position) (deal : List Nat) (hp : isPermutation52 deal) :
    Megadreifach.body_from (embed deal) (embedPos h) =
      Megadreifach.position_to_bytes (embedPos (dmStep h deal)) := by
  unfold Megadreifach.body_from
  rw [(require_permutation_refines deal hp).1, ok_bind]
  dsimp only
  rw [em_block_refines h deal (by rw [hp.1]; exact Nat.le_refl _), ok_bind]
  try dsimp only
  rw [compose_refines, ok_bind, except_bind_pure]
  rfl

end MegaDreifachV1.Link2
