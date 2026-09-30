/-
  LINK 2. `Generated.read_grip` refines `Em.readGrip` (the v2 read).

  `read_grip g phys noon pos` = `pos mod 2`, then on odd `pos`
  `corner_after_noon` (`corner_after_noon_refines`) and `colours_at`
  (`colours_at_refines`), on even `pos` `edge_colours_at`
  (`edge_colours_at_refines`), then `abs_reorient` (`abs_reorient_refines`).

  Domain: any algebraic position, faces `phys`, `noon` and position `pos`, plus
  the side conditions that keep the emitted `assert` branches unreachable:
  `noon` is a neighbour of `phys`, the corner and edge lookups succeed, and the
  read colours are adjacent (`absReorient? c1 c2 = some r`).  `ReadOk` packages
  them.  (`loopTailR` also lives here; later loop proofs use it.)

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.EmEdge

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- Close the inclusive-loop tail at index `i ≤ toN` (any result type `ρ`). -/
theorem loopTailR {α ρ : Type} (i toN : Nat) (hi : i ≤ toN) (htoN : toN ≤ 30) (st : α) :
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
      FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 31) (by omega)
    rw [ite_int_beq, if_neg hneI, addI_ofNat_one i hf, ok_bind, if_neg heq]
    rfl

/-- Side conditions under which `read_grip` does not hit an `assert`. -/
structure ReadOk (g : Position) (phys noon : Fin 12) (pos : Nat) : Prop where
  nbr : noon ∈ nbrs phys
  cslot : (cornerSlot? phys noon (cornerAfterNoon phys noon)).isSome
  eslot : (edgeSlot? phys noon).isSome
  rot : (absReorient? (readColours g phys noon pos).1 (readColours g phys noon pos).2).isSome

private theorem sEq_ofNat2 (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

/-- `Generated.read_grip` refines `Em.readGrip` on `ReadOk`. -/
theorem read_grip_refines (g : Position) (phys noon : Fin 12) (pos : Nat)
    (h : ReadOk g phys noon pos) :
    Megadreifach.read_grip (embedPos g) (Int.ofNat phys.val) (Int.ofNat noon.val) (Int.ofNat pos) =
      .ok (embedGrip (readGrip g phys noon pos)) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.rot
  have hrA : readGrip g phys noon pos = r := by
    rw [readGrip_eq]; unfold absReorient; rw [hr]; rfl
  rw [hrA]
  unfold Megadreifach.read_grip
  rw [show (2 : Int) = Int.ofNat 2 from rfl, modI_ofNat _ (by decide : (2 : Nat) ≠ 0), ok_bind,
    show (1 : Int) = Int.ofNat 1 from rfl, sEq_ofNat2]
  by_cases hp : pos % 2 = 1
  · have hc : readColours g phys noon pos = coloursAt g phys noon (cornerAfterNoon phys noon) := by
      unfold readColours; rw [if_pos hp]
    rw [hc] at hr
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h.cslot
    rw [decide_eq_true hp, if_pos rfl, corner_after_noon_refines _ _ h.nbr, ok_bind,
      colours_at_refines g phys noon _ s hs, ok_bind]
    dsimp only
    rw [abs_reorient_refines _ _ r hr]
    rfl
  · have hc : readColours g phys noon pos = edgeColoursAt g phys noon := by
      unfold readColours; rw [if_neg hp]
    rw [hc] at hr
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h.eslot
    rw [decide_eq_false hp]
    simp only [Bool.false_eq_true, ite_false]
    rw [edge_colours_at_refines g phys noon s hs, ok_bind]
    dsimp only
    rw [abs_reorient_refines _ _ r hr]
    rfl

end MegaDreifach.Link2
