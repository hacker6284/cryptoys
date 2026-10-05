/-
  SECURITY. Same-`h` cancellation for Davies–Meyer in MegaDreifach v3.
  Not a collision-resistance claim and not a PRF claim. A green build of this file is
  not a security claim.

  `compose g h` is `g` then `h` (`MegaDreifach.Group`). `emBlock h deal` is the board
  `E_m = W·h` (`Em.emBlock`, the sudo's `em_block`). So
  `Em.dmStep h deal = compose h (emBlock h deal)` is `h·W·h`, the hand 3-solve
  (v3 SPEC §5.7; v2 `daviesMeyer` is the same `compose h e`). Software and the hand
  schedule are this one product.

  What is proved: cancelling the outer `h`, a same-`h` DM collision is the same thing
  as a same-board `emBlock` collision. The hypothesis is `InjPos h`
  (`Injective h.cp ∧ Injective h.ep`, `Link2/PosBytesGen.lean`). It is not assumed
  for a bare `Position`. `isLegal` adds even permutations and orientation parities,
  which this lemma does not use.

  `injPos_ivCook12` gives `InjPos` at the IV. `dmStep_inj` (`EmRun.lean`) preserves it
  through one step. `injPos_chainPre` (`VHash.lean`) gives it for every MD chaining
  value `chainPre xs k`, and `dmStep_same_h_iff_chainPre` applies the iff there.
  Nothing is said when the two chaining values differ.

  Left cancellation is `MegaDreifach.Link2.compose_left_cancel` (`Link2/InjPos.lean`).
  `Group.leftMul_cancel` is the other cancellation: a shared injective right factor.

  Zero sorry. No native_decide.
-/
import MegaDreifach.Link2.InjPos
import MegaDreifachV3.Link2.VHash

namespace MegaDreifachV3.Security

open MegaDreifach MegaDreifach.Link2

/-- `dmStep h b = leftMul h (emBlock h b)`, and `leftMul` is `compose`, so this is
    `compose h (emBlock h b)`. The board is `W·h`, so the product is `h·W·h`. -/
private theorem dmStep_leftMul (h : Position) (b : List Nat) :
    Em.dmStep h b = leftMul h (Em.emBlock h b) := by
  rw [Em.dmStep, ← leftMul_eq_compose]

/-- Same-h cancellation for Davies–Meyer.
    `dmStep h b = dmStep h b'` iff `emBlock h b = emBlock h b'`, for `InjPos h`.
    Cancelling the outer `h`, a same-`h` DM collision is a same-board `emBlock` collision.
    `dmStep` is `h·W·h`, the hand 3-solve.
    Says nothing when the chaining values differ.
    Not a collision-resistance claim and not a PRF claim.
    A green build is not a security claim. -/
theorem dmStep_same_h_iff (h : Position) (hh : InjPos h) (b b' : List Nat) :
    Em.dmStep h b = Em.dmStep h b' ↔ Em.emBlock h b = Em.emBlock h b' := by
  constructor
  · intro hstep
    rw [dmStep_leftMul] at hstep
    rw [leftMul_eq_compose] at hstep
    exact compose_left_cancel h (Em.emBlock h b) (Em.emBlock h b') hh hstep
  · intro hW
    -- `rw` rewrites the first occurrence, so unfold both sides, then the board.
    rw [Em.dmStep, Em.dmStep, hW]

/-- The contentful direction of `dmStep_same_h_iff`: a same-`h` DM collision is an
    `emBlock` collision. The other direction is congruence and needs no hypothesis on `h`.
    Not a collision-resistance claim and not a PRF claim. -/
theorem emBlock_eq_of_dmStep_eq (h : Position) (hh : InjPos h) (b b' : List Nat)
    (hstep : Em.dmStep h b = Em.dmStep h b') :
    Em.emBlock h b = Em.emBlock h b' :=
  (dmStep_same_h_iff h hh b b').mp hstep

/-- `dmStep_same_h_iff` at the MD chaining value `chainPre xs k`.
    `injPos_chainPre` is the `InjPos` hypothesis. Not a collision-resistance claim
    and not a PRF claim. -/
theorem dmStep_same_h_iff_chainPre (xs : List Nat) (k : Nat) (b b' : List Nat) :
    Em.dmStep (MegaDreifachV3.Link2.chainPre xs k) b =
        Em.dmStep (MegaDreifachV3.Link2.chainPre xs k) b' ↔
      Em.emBlock (MegaDreifachV3.Link2.chainPre xs k) b =
        Em.emBlock (MegaDreifachV3.Link2.chainPre xs k) b' :=
  dmStep_same_h_iff _ (MegaDreifachV3.Link2.injPos_chainPre xs k) b b'

end MegaDreifachV3.Security
