/-
  The branch after the cofactor walk. Demo skips `finish` and moves the
  point back. Every other tier runs `finish` first: invert the bottom, multiply
  across and up by the gap, settle, then clear the gap and the bottom. The
  clear and the two `move_band`s are the same block on both arms.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CofactorTail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The clear and the two moves, packaged with the search hole `base_point`
    returns beside the board. -/
def pointBackPair (b : Board) (found : Int) : Except SudoRt.Trap (Int × Board) :=
  (do
    let b ← clear b base_across
    let b ← clear b base_up
    let b ← move_band b base_across across
    move_band b base_up up) >>= fun b => pure (found, b)

/-- `finish`, then that same block. -/
def finishBackPair (b : Board) (found : Int) : Except SudoRt.Trap (Int × Board) :=
  finish b >>= fun b => pointBackPair b found

/-- The `if` `base_point` writes after either walk. -/
def afterWalk (b : Board) (found : Int) : Except SudoRt.Trap (Int × Board) :=
  if !(b.sudo_5Board_1t.sudo_4Tier_4demo) then
    finishBackPair b found
  else
    pointBackPair b found

/-- Demo does not call `finish`. -/
theorem demo_skips_finish (b : Board) (found : Int)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = true) :
    afterWalk b found = pointBackPair b found := by
  unfold afterWalk
  rw [hdemo]
  simp [Bool.not_true]

/-- Toy, Hobby, and Serious run `finish`, then the same clear and move. -/
theorem tier_runs_finish (b : Board) (found : Int)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = false) :
    afterWalk b found = finishBackPair b found := by
  unfold afterWalk
  rw [hdemo]
  simp [Bool.not_false]

/-- `finish` is the six steps on the projective board: invert the bottom,
    multiply across and up by the gap, settle, then clear the gap and the
    bottom. -/
theorem finish_steps (b : Board) :
    finish b =
      (do
        let b ← invert_checked b bottom
        let b ← mul b across gap across false false false
        let b ← mul b up gap up false false false
        let b ← settle b
        let b ← clear b gap
        let b ← clear b bottom
        pure b) := by
  unfold finish
  rfl

private theorem pair_ok (b b' : Board) (found : Int)
    (h : (do
        let b ← clear b base_across
        let b ← clear b base_up
        let b ← move_band b base_across across
        move_band b base_up up) = .ok b') :
    pointBackPair b found = .ok (found, b') := by
  unfold pointBackPair
  rw [h, ok_bind, pure_eq_ok]

/-- Demo's arm is `point_back`. Homes 3 and 4 are the point. -/
theorem demo_point_back (t : Spec.Tier) (b : Board) (px py baseX baseY : List Nat)
    (mv0 sl0 : Nat) (found : Int)
    (lay : LastLay b baseX baseY (suffixMoveCap t mv0 (cofactorSpan - 1))
      (suffixSlideCap t sl0 (cofactorSpan - 1)))
    (h0a : b.sudo_5Board_4home[0]'(by rw [lay.szH]; decide) = embed px)
    (h1a : b.sudo_5Board_4home[1]'(by rw [lay.szH]; decide) = embed py)
    (hdemo : b.sudo_5Board_1t.sudo_4Tier_4demo = true)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpx : px.length = t.n) (hpy : py.length = t.n)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hmv0 : mv0 ≤ perHole t.n t.benchlen * t.n + 5 * t.n)
    (hsl0 : sl0 ≤ perSlide t.n * t.n + 2 * t.n) :
    ∃ b',
      afterWalk b found = .ok (found, b') ∧
      (∀ h : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3] = embed px) ∧
      (∀ h : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4] = embed py) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = (#[] : Array Int)) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = (#[] : Array Int)) := by
  rw [demo_skips_finish b found hdemo]
  obtain ⟨b', hdo, h3, h4, h0, h1⟩ :=
    point_back_of_lay t b px py baseX baseY mv0 sl0 lay h0a h1a hship
      hpx hpy hbx hby hmv0 hsl0
  exact ⟨b', pair_ok b b' found hdo, h3, h4, h0, h1⟩

end EcbsLink2.Link2
