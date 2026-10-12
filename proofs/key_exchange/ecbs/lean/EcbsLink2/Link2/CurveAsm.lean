/-
  `curve_test` is `new_board`, the two puts, and `on_curve`.
  The pieces are the curve lemmas; this file only chains them.
-/
import EcbsLink2.Link2.CurveTest

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem curve_decide_onCurve (n k bench : Nat) (x y : List Nat) :
    decide (fieldMul n k bench y y =
        fieldAdd n
          (fieldAdd n (fieldCube n k bench x) (mirrorTrits (fieldMul n k bench x x)))
          (1 :: List.replicate (n - 1) 0)) =
      onCurve n k bench x y := by
  unfold onCurve
  rfl

/-- From the board that already holds `x³`, `x²`, and `y²`, the rest of `on_curve`
    is the spec predicate. -/
theorem curve_suffix (b : Ecbs.Board) (x y x3 x2 y2 : List Nat) (n k bench moves : Nat)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hheld2 : b.sudo_5Board_4held[2] = true)
    (harr2 : b.sudo_5Board_4home[2] = embed x3)
    (hheld5 : b.sudo_5Board_4held[5] = true)
    (harr5 : b.sudo_5Board_4home[5] = embed y2)
    (hheld6 : b.sudo_5Board_4held[6] = true)
    (harr6 : b.sudo_5Board_4home[6] = embed x2)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx3 : x3.length = n) (hx2 : x2.length = n) (hy2 : y2.length = n) (hpos : 0 < n)
    (ht3 : allTritList x3) (ht2 : allTritList x2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hf : FitsLen n)
    (hfitC : FitsLen (moves + pegCount x2 + pegCount x2))
    (hfitW : FitsLen (moves + pegCount x2 + pegCount x2 + 1))
    (hfitG : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2))
    (hfitBot : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2 + n))
    (hx3f : x3 = fieldCube n k bench x) (hx2f : x2 = fieldMul n k bench x x)
    (hy2f : y2 = fieldMul n k bench y y) :
    ∃ bF,
      (Ecbs.add b Ecbs.bottom Ecbs.spare true >>= fun b1 =>
        Ecbs.clear b1 Ecbs.spare >>= fun b2 =>
        Ecbs.white0 b2 Ecbs.bottom >>= fun b3 =>
        Ecbs.value b3 Ecbs.gap >>= fun g =>
        Ecbs.value b3 Ecbs.bottom >>= fun bot =>
        Ecbs.clear b3 Ecbs.gap >>= fun b4 =>
        Ecbs.clear b4 Ecbs.bottom >>= fun b5 =>
        pure (SudoRt.SEq.beq g bot, b5)) =
        .ok (onCurve n k bench x y, bF) := by
  obtain ⟨bF, h⟩ := curve_white_beq b x3 x2 y2 n moves h2H h2D h5H h5D h6H h6D
    hheld2 harr2 hheld5 harr5 hheld6 harr6 hn hx3 hx2 hy2 hpos ht3 ht2 hm hfit hf
    hfitC hfitW hfitG hfitBot
  refine ⟨bF, ?_⟩
  rw [h, hx3f, hx2f, hy2f, curve_decide_onCurve]

end EcbsLink2.Link2
