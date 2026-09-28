/-
  LINK 2. `Generated.face_move` / `Generated.face_turn` refine the algebraic
  `Em.faceMove` / `Em.faceTurn`.

  `face_move f` returns the four verbatim `ft_*_f` tables; on `f : Fin 12`
  that is `embedPos (faceMove f)` (closed per face by kernel `rfl`).
  `face_turn g f a` reduces `a mod 5`, returns `g` on `0`, and otherwise runs
  `out := compose(face_move f, out)` for `i = 1 .. a`; each step is
  `compose_refines`, driven by `chain_loop`.

  Domain: any algebraic position `g` (so `PosWf (embedPos g)`), face
  `f : Fin 12`, amount any `Nat` that fits in an i64. Every call in E_m has a
  face `o[·] ∈ 0..11` and an amount in `0..4`.

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.Compose
import MegaDreifach.Em

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-! ## `face_move` -/

set_option maxRecDepth 10000 in
/-- `Generated.face_move` on a face id `0..11` is the embedded algebraic
    `faceMove`. -/
theorem face_move_refines (f : Fin 12) :
    Megadreifach.face_move (Int.ofNat f.val) = .ok (embedPos (faceMove f)) := by
  match f with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl
  | ⟨11, _⟩ => rfl

/-! ## `face_turn` loop -/

/-- Emitted `face_turn` loop body (`out := compose(t, out)`), with `toV = a`. -/
def faceTurnStep (t : Megadreifach.Position) (toV : Int)
    (σ : Int × Megadreifach.Position) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Megadreifach.Position) Megadreifach.Position) :=
  let i := σ.1
  let out := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (i, out))
    else
      match ← ((do
        let _t138 ← Megadreifach.compose t out
        let out := _t138
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) out)) :
          Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.Position)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.Position) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (i, _fs))
      | .cont _fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (i, _fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', _fs))

/-- Loop state on entry to index `i` (`i ≥ 1`): `i - 1` turns done. -/
def turnState (T g : Position) (i : Nat) : Megadreifach.Position :=
  embedPos (leftIter T (i - 1) g)

private theorem fits5 (a : Nat) (ha : a < 5) : FitsLen a :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 5) (Nat.le_of_lt ha)

theorem faceTurnStep_hit (T g : Position) (a i : Nat) (ha : a < 5)
    (hi1 : 1 ≤ i) (hi : i ≤ a) :
    faceTurnStep (embedPos T) (Int.ofNat a) (Int.ofNat i, turnState T g i) =
      if i = a then
        .ok (SudoRt.Flow.brk (Int.ofNat i, turnState T g (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), turnState T g (i + 1))) := by
  unfold faceTurnStep turnState
  dsimp only
  rw [if_neg (ofNat_not_gt hi), compose_refines, ok_bind, pure_bind]
  have hsucc : leftIter T (i + 1 - 1) g = compose T (leftIter T (i - 1) g) := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rfl
  rw [hsucc]
  by_cases heq : i = a
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat a) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (fits5 (i + 1) (by omega) |>.of_le (Nat.le_refl _))
    dsimp only
    rw [ite_int_beq, if_neg hneI, hadd, ok_bind, if_neg heq]
    rfl

/-- The emitted loop `for i = 1 to a: out = compose(t, out)` from `out = g`. -/
theorem faceTurn_loop (T g : Position) (a : Nat) (ha : a < 5) (ha0 : 0 < a) :
    SudoRt.runLoopOn (ρ := Megadreifach.Position) ((1 : Int), embedPos g)
      (fuelRange (1 : Int) (Int.ofNat a))
      (faceTurnStep (embedPos T) (Int.ofNat a))
      (fun σ => let out := σ.2; do pure out) (fun r => pure r) =
    .ok (embedPos (leftIter T a g)) := by
  have h1 : ((1 : Int), embedPos g) = (Int.ofNat 1, turnState T g 1) := by
    simp [turnState, leftIter]
  rw [h1, show (1 : Int) = Int.ofNat 1 from rfl]
  apply chain_loop (f := turnState T g) (fromN := 1) (toN := a) (hle := ha0)
  · intro i hi1 hi
    exact faceTurnStep_hit T g a i ha hi1 hi
  · simp [turnState]
    rfl

/-! ## `face_turn` -/

private theorem sEq_ofNat (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

/-- `Generated.face_turn` refines `Em.faceTurn` on every algebraic position,
    face `f : Fin 12`, and amount `amount` (reduced `mod 5`). -/
theorem face_turn_refines (g : Position) (f : Fin 12) (amount : Nat) :
    Megadreifach.face_turn (embedPos g) (Int.ofNat f.val) (Int.ofNat amount) =
      .ok (embedPos (faceTurn g f amount)) := by
  unfold Megadreifach.face_turn
  rw [show (5 : Int) = Int.ofNat 5 from rfl, modI_ofNat amount (by decide : (5 : Nat) ≠ 0),
    ok_bind]
  dsimp only
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat]
  by_cases h0 : amount % 5 = 0
  · rw [decide_eq_true h0]
    simp [faceTurn, h0, leftIter]
    rfl
  · rw [decide_eq_false h0]
    simp only [Bool.false_eq_true, ite_false]
    rw [face_move_refines, ok_bind]
    rw [except_bind_pure, fuelRange_eq]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := faceTurnStep (embedPos (faceMove f))
        (Int.ofNat (amount % 5)))
      intro σ
      rfl
    · exact faceTurn_loop (faceMove f) g (amount % 5) (Nat.mod_lt _ (by decide))
        (Nat.pos_of_ne_zero h0)

end MegaDreifach.Link2
