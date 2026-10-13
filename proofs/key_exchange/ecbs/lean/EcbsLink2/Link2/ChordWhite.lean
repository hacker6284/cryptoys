/-
  `bench_white0` writes `(peg + 1) mod 3` into hole 0 of the bench and
  charges one move. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerCopyEq

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem modI_three (a : Nat) :
    SudoRt.modI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a % 3)) :=
  modI_ofNat a (by decide)

/-- `bench_white0` writes `(peg + 1) mod 3` into hole 0 and charges one move. -/
theorem bench_white0_step (b : Ecbs.Board) (xs : List Nat) (moves : Nat)
    (hpos : 0 < xs.length)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hc : xs[0] ≤ 2)
    (hfitM : FitsLen (moves + 1)) :
    Ecbs.bench_white0 b =
      .ok { { b with sudo_5Board_5bench := embed (xs.set 0 ((xs[0] + 1) % 3)) }
          with sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 1) } } := by
  have hfit : FitsLen (xs[0] + 1) := by
    have hle : xs[0] + 1 ≤ 3 := by omega
    have h3 : FitsLen 3 := by unfold FitsLen i64MaxNat; omega
    exact FitsLen.of_le h3 hle
  unfold Ecbs.bench_white0
  rw [hbench, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed xs 0 hpos, ok_bind,
    addI_ofNat_one (xs[0]) hfit, ok_bind, modI_three (xs[0] + 1), ok_bind]
  have hsz : 0 < (embed xs).size := by rw [size_embed]; exact hpos
  rw [putL_ofNat (embed xs) 0 (Int.ofNat ((xs[0] + 1) % 3)) hsz, ok_bind,
    embed_set xs 0 ((xs[0] + 1) % 3) hpos]
  conv =>
    lhs
    zeta
  rw [hmoves, ← ofNat_eq_natCast moves, addI_ofNat_one moves hfitM]
  simp only [ok_bind, pure_eq_ok]

end EcbsLink2.Link2
