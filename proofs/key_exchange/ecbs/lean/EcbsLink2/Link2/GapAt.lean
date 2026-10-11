/-
  Where a rung reads the gap.

  `copy_band` reads its source through `value` → `get_number` → `where_bench`.
  Home 5 held: the array in that home (the first rung, bench off).
  Home 5 empty and the bench aimed at it: the bench (every later rung).
  `clear` of a held home 5 leaves the bench on, so the next rung starts there.

  The first cube of the peg loop then calls `settle`, which slides that bench
  into home 5 before the cube reads the spare. The gap mul reads `first` from
  the home, after that settle. `modelRung` leaves `onBench` true, which is
  this post-clear bench.
-/
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The working gap is on the bench exactly when the model says so. -/
def gapAtBench (s : ClimbModel) : Bool := s.onBench

theorem modelRung_onBench (s : ClimbModel) (x : List Nat) (rung hole : Nat) (last : Bool) :
    (modelRung s x rung hole last).onBench = true := by
  simp [modelRung]

/-- `value` of home 5 is the gap prefix. Held: the home array. Empty and aimed:
    the bench. -/
theorem gap_value_refines {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    {done rest : List Nat}
    (h : ClimbInvK done rest b s base) (hf : FitsLen s.n) :
    Ecbs.value b ((5 : Nat) : Int) = .ok (embed s.gap) := by
  have hlenG : s.gap.length = s.n := h.shape.gapLen
  by_cases hB : s.onBench = true
  · have hg := h.inv.gapBench hB
    have hheld : b.sudo_5Board_4held[5]'(Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7) =
        false := h.shape.gapClear hB
    have h5 : 5 < b.sudo_5Board_4held.size :=
      Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7
    let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
    have hxs : b.sudo_5Board_5bench = embed xs := by
      simpa [xs] using hg.2.2.1
    have hnle : s.n ≤ s.benchlen := by
      have hsp := h.shape.peg.span
      omega
    have htake : xs.take s.n = s.gap := by
      have hpre : (s.gap.take s.n).length = s.n := by
        rw [List.length_take, hlenG, Nat.min_self]
      have hleft : xs.take (s.gap.take s.n).length = s.gap.take s.n := by
        simpa [xs] using List.take_left (s.gap.take s.n)
          (List.replicate (s.benchlen - s.n) 0)
      rw [hpre] at hleft
      rw [hleft, ← hlenG, List.take_length]
    have hv := value_bench_refines b 5 xs s.n h5 hheld hg.1 hg.2.1 hxs
      h.shape.tierN (by rw [show xs.length = s.benchlen by
        simp [xs, List.length_take, List.length_replicate, hlenG]; omega]; exact hnle)
      hf
    simpa [htake] using hv
  · have hBf : s.onBench = false := eq_false_of_ne_true hB
    have hg := h.inv.gapHome hBf
    have h5h : 5 < b.sudo_5Board_4home.size := h.inv.hG
    have h5d : 5 < b.sudo_5Board_4held.size := h.inv.hGs
    have hv := value_held_refines b 5 s.gap s.n h5d h5h hg.1 hg.2
      h.shape.tierN (Nat.le_of_eq hlenG.symm) hf
    rw [← hlenG, List.take_length] at hv
    exact hv

end EcbsLink2.Link2
