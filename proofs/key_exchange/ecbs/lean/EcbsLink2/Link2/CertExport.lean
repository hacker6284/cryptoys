/-
  `certificate` is the card's chord. An empty bottom returns false and does
  not invert. The other arm calls `invert_checked` and then the chord.
  `make_certificate` is a fresh board, the two puts, and that call: none when
  the certificate is empty, otherwise the point in the across and the up.
  `FieldOk` is not a hypothesis. The inverse stays inside `invert_checked`.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

open Ecbs

/-- The chord op counter, then the certificate. -/
def certificateCard (b : Board) (xh yh : Int) :
    Except SudoRt.Trap (Bool × Board) :=
  do
    let n ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_chord
    let n ← SudoRt.addI n (1 : Int)
    let ops ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_chord n
    let b ← copy_band
      { b with sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } }
      bottom xh false
    let b ← cube b bottom bottom
    let b ← settle b
    let b ← mirror b bottom
    let b ← add b bottom xh false
    let z ← is_zero b bottom
    if z then
      do
        let b ← clear b bottom
        pure (false, b)
    else
      do
        let b ← invert_checked b bottom
        let b ← copy_band b spare yh false
        let b ← cube b spare spare
        let b ← settle b
        let b ← add b spare yh false
        let b ← mirror b spare
        let b ← mul b gap gap spare false false false
        let b ← clear b gap
        let b ← settle b
        let b ← cube b xh xh
        let b ← cube b yh yh
        let b ← settle b
        let b ← mul b bottom gap gap true false false
        let b ← bench_white0 b
        let b ← bench_add b xh false
        let b ← bench_add b bottom true
        let b ← clear b bottom
        let b ← settle b
        let b ← add b xh bottom true
        let b ← mirror b yh
        let b ← mul b yh gap xh false true false
        let b ← clear b gap
        let b ← settle b
        let b ← move_band b xh bottom
        pure (true, b)

theorem certificate_card (b : Board) (xh yh : Int) :
    certificate b xh yh = certificateCard b xh yh := by
  unfold certificate certificateCard
  conv =>
    lhs
    zeta

/-- A fresh board, the across and the up, then `certificate`. -/
def makeCertificateCard (t : Tier) (c : Point) :
    Except SudoRt.Trap (Option Point) :=
  do
    let b ← new_board t
    let b ← put b across c.sudo_5Point_1x
    let b ← put b up c.sudo_5Point_1y
    let ⟨ok, b⟩ ← certificate b across up
    if !ok then
      pure (none : Option Point)
    else
      do
        let p ← point_of b across up
        pure (some p)

theorem make_certificate_card (t : Tier) (c : Point) :
    make_certificate t c = makeCertificateCard t c := by
  unfold make_certificate makeCertificateCard
  conv =>
    lhs
    zeta

/-- The same export, with the empty arm and the `invert_checked` arm written out. -/
theorem make_certificate_steps (t : Tier) (c : Point) :
    make_certificate t c =
      (do
        let b ← new_board t
        let b ← put b across c.sudo_5Point_1x
        let b ← put b up c.sudo_5Point_1y
        let ⟨ok, b⟩ ← certificateCard b across up
        if !ok then
          pure (none : Option Point)
        else
          do
            let p ← point_of b across up
            pure (some p)) := by
  rw [make_certificate_card]
  simp only [makeCertificateCard, certificate_card]

end EcbsLink2.Link2
