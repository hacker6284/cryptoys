/-
  `base_point_of` and `Spec.basePoint`. A positive hole is the point in the
  base homes. A non-positive hole is assert 1527. An error from `base_point`
  (assert 963 when the search misses, assert 972 or 975 when the cofactor
  walk fails) is the same error. Demo's spec point is the published pair,
  and a demo board walks by `walk_chord`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkScope
import EcbsLink2.Link2.DemoPoint
import EcbsLink2.Link2.Basic
import EcbsLink2.Link2.Board

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem point_of_eq (b : Ecbs.Board) (xh yh : Int) (vx vy : Array Int)
    (hx : Ecbs.value b xh = .ok vx) (hy : Ecbs.value b yh = .ok vy) :
    Ecbs.point_of b xh yh =
      .ok { sudo_5Point_1x := vx, sudo_5Point_1y := vy } := by
  unfold Ecbs.point_of
  rw [hx, ok_bind, hy, ok_bind, pure_eq_ok]

private theorem of_gt (j : Int) (hj : 0 < j) :
    decide (j > (0 : Int)) = true :=
  decide_eq_true hj

/-- The cofactor colours are white, red, white, red. -/
theorem cofactor_colour_cells : cofactorCells = [1, 2, 1, 2] := rfl

/-- Those four cells, as the array `base_point` hands to the walk. -/
theorem cofactor_colour_embed :
    (#[(1 : Int), (2 : Int), (1 : Int), (2 : Int)] : Array Int) = embed cofactorCells := by
  rw [cofactor_colour_cells]
  rfl

/-- A positive hole. `base_point_of` is `point_of` of the base homes. -/
theorem base_point_of_point (t : Ecbs.Tier) (b0 b : Ecbs.Board) (j : Int)
    (vx vy : Array Int)
    (hN : Ecbs.new_board t = .ok b0)
    (hB : Ecbs.base_point b0 = .ok (j, b))
    (hj : 0 < j)
    (hx : Ecbs.value b Ecbs.base_across = .ok vx)
    (hy : Ecbs.value b Ecbs.base_up = .ok vy) :
    Ecbs.base_point_of t =
      .ok { sudo_5Point_1x := vx, sudo_5Point_1y := vy } := by
  unfold Ecbs.base_point_of
  conv => lhs; zeta
  rw [hN, ok_bind, hB, ok_bind]
  dsimp only
  rw [show decide (j > (0 : Int)) = true from of_gt j hj]
  rw [sudoAssert_bool 1527 rfl, ok_bind]
  rw [point_of_eq b Ecbs.base_across Ecbs.base_up vx vy hx hy, ok_bind, pure_eq_ok]

/-- The same point on both sides. Homes 3 and 4 are the seated point, so
    `value` is not a premise. -/
theorem base_point_of_spec (t : Spec.Tier) (b0 b : Ecbs.Board) (j : Int)
    (x y : List Nat)
    (hN : Ecbs.new_board (embTier t) = .ok b0)
    (hB : Ecbs.base_point b0 = .ok (j, b))
    (hj : 0 < j)
    (h3H : 3 < b.sudo_5Board_4home.size) (h4H : 4 < b.sudo_5Board_4home.size)
    (h3D : 3 < b.sudo_5Board_4held.size) (h4D : 4 < b.sudo_5Board_4held.size)
    (h3 : b.sudo_5Board_4home[3] = embed x) (h4 : b.sudo_5Board_4home[4] = embed y)
    (hd3 : b.sudo_5Board_4held[3] = true) (hd4 : b.sudo_5Board_4held[4] = true)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n)
    (hxlen : x.length = t.n) (hylen : y.length = t.n) (hf : FitsLen t.n)
    (hspec : basePoint t = some (x, y)) :
    Ecbs.base_point_of (embTier t) =
        .ok { sudo_5Point_1x := embed x, sudo_5Point_1y := embed y } ∧
      basePoint t = some (x, y) := by
  obtain ⟨hx, hy⟩ := seated_homes b x y t.n h3H h4H h3D h4D h3 h4 hd3 hd4 hn
    hxlen hylen hf
  exact ⟨base_point_of_point (embTier t) b0 b j (embed x) (embed y)
    hN hB hj hx hy, hspec⟩

/-- A non-positive hole is assert 1527. -/
theorem base_point_of_refuse (t : Ecbs.Tier) (b0 b : Ecbs.Board) (j : Int)
    (hN : Ecbs.new_board t = .ok b0)
    (hB : Ecbs.base_point b0 = .ok (j, b))
    (hj : ¬ 0 < j) :
    Ecbs.base_point_of t =
      .error { kind := "AssertFailed", detail := s!"line {1527}" } := by
  unfold Ecbs.base_point_of
  conv => lhs; zeta
  rw [hN, ok_bind, hB, ok_bind]
  dsimp only
  have hdec : decide (j > (0 : Int)) = false := decide_eq_false hj
  rw [hdec]
  unfold SudoRt.sudoAssert SudoRt.fail
  have hne : ¬ ((false : Bool) = true) := by decide
  rw [if_neg hne, error_bind]

/-- An error from `base_point`, including assert 963 and the cofactor asserts,
    is the error `base_point_of` returns. -/
theorem base_point_of_error (t : Ecbs.Tier) (b0 : Ecbs.Board) (e : SudoRt.Trap)
    (hN : Ecbs.new_board t = .ok b0)
    (hB : Ecbs.base_point b0 = .error e) :
    Ecbs.base_point_of t = .error e := by
  unfold Ecbs.base_point_of
  conv => lhs; zeta
  rw [hN, ok_bind, hB]
  simp only [error_bind]

/-- Demo's base point is the published pair, and a demo board takes `walk_chord`. -/
theorem demo_base_through_chord (b : Ecbs.Board) (cells : Array Int)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = true) :
    basePoint demo = some ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2]) ∧
      Ecbs.walk_and_finish b cells =
        (do
          let r ← Ecbs.walk_chord b cells
          let live := r.1.1
          let ok := r.1.2
          let b := r.2
          let flag ← (if live then pure ok else pure false)
          pure (flag, b)) :=
  ⟨demo_basePoint, walk_and_finish_demo b cells hdemo⟩

end EcbsLink2.Link2
