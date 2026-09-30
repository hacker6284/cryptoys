/-
  LINK 2. `Generated.em_block` refines `Em.emBlock` on every deal array of
  length at least 52 (entries are arbitrary naturals), and every starting
  position. No other hypothesis: the `read_grip` side conditions are
  discharged by the `GripOk` invariant (`EmInv.lean`). v2: the G2 loop passes
  the 1-based deal position `i + 1` and the F3 loop (`f3_t = 36` rounds) the
  round number `t` to the steps.

  Algebraic Link 2 only. Not `v_Hash` (the DM chaining + padding + unranking
  composition is not stated here).
-/
import MegaDreifach.Link2.EmInv
import MegaDreifach.Link2.RequirePerm
import MegaDreifach.Link2.PosBytes

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- `g2Run` over an appended card. -/
theorem g2Run_append (x : Nat) : ∀ (xs : List Nat) (p : Nat) (st : Position × Grip),
    g2Run p (xs ++ [x]) st = g2Step (g2Run p xs st) x (p + xs.length)
  | [], p, st => rfl
  | y :: ys, p, st => by
      show g2Run (p + 1) (ys ++ [x]) (g2Step st y p) =
        g2Step (g2Run (p + 1) ys (g2Step st y p)) x (p + (ys.length + 1))
      rw [g2Run_append x ys (p + 1) (g2Step st y p)]
      congr 1
      omega

/-- State after the first `i` G2 steps (deal positions `1..i`). -/
def g2Pre (h : Position) (deal : List Nat) (i : Nat) : Position × Grip :=
  g2Run 1 (deal.take i) (h, gripId)

theorem g2Pre_succ (h : Position) (deal : List Nat) (i : Nat) (hi : i < deal.length) :
    g2Pre h deal (i + 1) = g2Step (g2Pre h deal i) deal[i] (i + 1) := by
  unfold g2Pre
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp only [Option.toList]
  rw [g2Run_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), Nat.add_comm]

theorem gripOk_g2Run : ∀ (xs : List Nat) (p : Nat) (st : Position × Grip), GripOk st.2 →
    GripOk (g2Run p xs st).2
  | [], _, _, hs => hs
  | x :: xs, p, st, hs => gripOk_g2Run xs (p + 1) _ (gripOk_g2Step st x p hs)

theorem gripOk_g2Pre (h : Position) (deal : List Nat) (i : Nat) :
    GripOk (g2Pre h deal i).2 :=
  gripOk_g2Run _ _ _ gripOk_id

/-- One more F3 round at the end. -/
theorem f3Run_succ' : ∀ (n r : Nat) (st : Position × Grip),
    f3Run r (n + 1) st = f3Step (f3Run r n st) (r + n)
  | 0, r, st => rfl
  | n + 1, r, st => by
      rw [f3Run, f3Run_succ' n (r + 1) (f3Step st r), f3Run]
      congr 1
      omega

theorem gripOk_f3Run : ∀ (n r : Nat) (st : Position × Grip), GripOk st.2 →
    GripOk (f3Run r n st).2
  | 0, _, _, hs => hs
  | n + 1, r, st, hs => gripOk_f3Run n (r + 1) _ (gripOk_f3Step st r hs)

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

/-- The loop tail once the index increment `addI i 1` has been evaluated. -/
theorem loopTailOk {α ρ : Type} (i toN : Nat) (st : α) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := ρ) (Int.ofNat i, st)) : Except SudoRt.Trap _)
      else do
        let i' ← (Except.ok (Int.ofNat (i + 1)) : Except SudoRt.Trap Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', st))) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  by_cases heq : i = toN
  · subst heq; simp [beq_int_iff]; rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    rw [ite_int_beq, if_neg hneI, ok_bind, if_neg heq]
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
      addI_ofNat_one i (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 52) (by omega)),
      ok_bind, g2_step_refines' _ _ _ _ (gripOk_g2Pre h deal i), ok_bind]
    dsimp only
    rw [pure_bind, ← g2Pre_succ h deal i (by omega)]
    exact loopTailOk i 51 _
  · dsimp only
    rw [show Megadreifach.f3_t = Int.ofNat 36 from rfl]
    rw [except_bind_pure]
    apply chain_loop
      (f := fun t => (embedPos (f3Run 1 (t - 1) (g2Pre h deal 52)).1,
        embedGrip (f3Run 1 (t - 1) (g2Pre h deal 52)).2))
      (fromN := 1) (toN := 36) (hle := by decide)
    · intro t ht1 ht
      dsimp only
      rw [if_neg (ofNat_not_gt ht),
        f3_step_refines' _ _ _ (gripOk_f3Run _ _ _ (gripOk_g2Pre h deal 52)), ok_bind]
      dsimp only
      rw [pure_bind, show t + 1 - 1 = (t - 1) + 1 by omega, f3Run_succ',
        show 1 + (t - 1) = t by omega]
      exact loopTailBig t 36 ht (by omega) _
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

end MegaDreifach.Link2
