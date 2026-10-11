/-
  The ladder loop carries the rung read. `ClimbInvL` is `ClimbInvK` plus the
  ladder array, a positive tally length, and the i64 fit of that length.
  `runLoop_drop_inv` asks for the step only on boards in this predicate.
-/
import EcbsLink2.Link2.InvertOpen
import EcbsLink2.Link2.TailLen

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `ClimbInvK` at list index `k`, with the ladder and the tally length the
    step reads. `m` is `s.tally`, which starts at 1 and then follows `tallyAfter`,
    not `k + 1`. `FitsLen m` is `m ≤ control` against `ClimbBudget.fitControl`. -/
structure ClimbInvL (L : List Nat) (k : Nat) (b : Ecbs.Board) (base : ClimbBudget) where
  done : List Nat
  rest : List Nat
  s : ClimbModel
  split : L = done ++ rest
  k_eq : k = done.length
  inv : ClimbInvK done rest b s base
  ladder : b.sudo_5Board_6ladder = embed L
  m_pos : 0 < s.tally
  m_le : s.tally ≤ base.control
  m_len : b.sudo_5Board_9tally_len = Int.ofNat s.tally

/-- The predicate `runLoop_drop_inv` carries. -/
def ClimbP (L : List Nat) (base : ClimbBudget) (k : Nat) (b : Ecbs.Board) : Prop :=
  Nonempty (ClimbInvL L k b base)

theorem ClimbInvL.m_fit {L : List Nat} {k : Nat} {b : Ecbs.Board} {base : ClimbBudget}
    (h : ClimbInvL L k b base) : FitsLen h.s.tally :=
  FitsLen.of_le base.fitControl (Nat.le_trans h.m_le (Nat.le_succ base.control))

/-- The three reads, for any board that still holds `L` and a natural length. -/
theorem inv_named_step
    (b : Ecbs.Board) (L : List Nat) (x : Int) (i m : Nat)
    (hi : i < L.length) (hpos : 0 < L.length) (hfitL : FitsLen L.length)
    (hL : b.sudo_5Board_6ladder = embed L)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m) :
    let rung := (L[i]'hi)
    let last := (L.drop (i + 1)).isEmpty
    (do
      let t0 ← SudoRt.subI (SudoRt.listLen b.sudo_5Board_6ladder) (1 : Int)
      let lastB := SudoRt.SEq.beq (Int.ofNat i) t0
      let rv ← SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i)
      let b ← Ecbs.park_rung b rv
      let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
      let m0 := b.sudo_5Board_9tally_len
      let toW ← SudoRt.subI m0 (1 : Int)
      let fromW := (0 : Int)
      let fuelW : Nat := if fromW > toW then 1 else (toW - fromW).natAbs + 1
      SudoRt.runLoopOn fromW fuelW (whiteStep b toW)
        (fun _ => rungAfterNamed x rv lastB b m0)
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
      (do
        let b ← climbRung b rung last x m
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  intro rung last
  have hsub : SudoRt.subI (Int.ofNat L.length) (1 : Int) =
      .ok (Int.ofNat (L.length - 1)) :=
    subI_ofNat_one L.length hpos hfitL
  have hlast : SudoRt.SEq.beq (Int.ofNat i) (Int.ofNat (L.length - 1)) = last := by
    simpa [last] using last_flag L i hi
  have hat : SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i) = .ok (rung : Int) := by
    rw [hL]
    simpa [rung] using atL_embed L i hi
  rw [show SudoRt.listLen b.sudo_5Board_6ladder = Int.ofNat L.length by
    rw [hL, listLen_embed]]
  exact named_rung_step b x (Int.ofNat i) (Int.ofNat L.length)
    (Int.ofNat (L.length - 1)) rung last m hm hfit hlen hsub hlast hat

end EcbsLink2.Link2
