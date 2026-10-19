/-
  The power loop as one digit at a time. `PowAt` is the board with `ds`
  digits still to run. Each counter keeps a remaining budget
  `FitsLen (c + perDigit * ds.length)`, the same shape as `FformAt`.
  A digit spends at most one unit of that budget. The marker seated by a
  digit is 0 or 1, and every shipped script is at least 2, so the
  `marker < script` assert does not fail on Demo.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowFold
import EcbsLink2.Link2.CheckTail
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.ClimbEmit

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

def powUp : Nat := 1
def powBottom : Nat := 2
def powGap : Nat := 5
def powSpare : Nat := 6

/-- Moves one root digit can add: the cube, the copy, the schoolbook, and the settles. -/
def powMove (n bench : Nat) : Nat := n * n + 6 * n + 6 * bench

/-- Slides one root digit can add: two settles, two pegs each. -/
def powSlide (n : Nat) : Nat := 4 * n

/-- Control one root digit can add: lift, cube feed, and the multiply's seat. -/
def powCtrl : Nat := 4

theorem room_move (moves spend n bench k : Nat)
    (h : FitsLen (moves + powMove n bench * (k + 1)))
    (hs : spend ≤ powMove n bench) :
    FitsLen (moves + spend) ∧
      FitsLen (moves + spend + powMove n bench * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powMove n bench ≤ powMove n bench * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powMove n bench * (k + 1) = powMove n bench + powMove n bench * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_slide (slides spend n k : Nat)
    (h : FitsLen (slides + powSlide n * (k + 1)))
    (hs : spend ≤ powSlide n) :
    FitsLen (slides + spend) ∧
      FitsLen (slides + spend + powSlide n * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powSlide n ≤ powSlide n * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powSlide n * (k + 1) = powSlide n + powSlide n * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_ctrl (ctrl spend k : Nat)
    (h : FitsLen (ctrl + powCtrl * (k + 1)))
    (hs : spend ≤ powCtrl) :
    FitsLen (ctrl + spend) ∧
      FitsLen (ctrl + spend + powCtrl * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powCtrl ≤ powCtrl * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powCtrl * (k + 1) = powCtrl + powCtrl * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_ops (c k : Nat) (h : FitsLen (c + (k + 1))) :
    FitsLen (c + 1) ∧ FitsLen ((c + 1) + k) := by
  refine ⟨FitsLen.of_le h (by omega), ?_⟩
  have hsum : c + (k + 1) = (c + 1) + k := by omega
  simpa [hsum] using h

theorem room_ops_keep (c k : Nat) (h : FitsLen (c + (k + 1))) :
    FitsLen (c + k) :=
  FitsLen.of_le h (by omega)

/-- `2 ≤ script` is `1 < script`. The power loop's assert is `1 < script`. -/
theorem script_one (t : Spec.Tier) (h : TierShape t) : 1 < t.script := by
  have h2 := h.script_ge
  omega

theorem demo_pow_script : 1 < demo.script := by decide
theorem toy_pow_script : 1 < toy.script := by decide
theorem hobby_pow_script : 1 < hobby.script := by decide
theorem serious_pow_script : 1 < serious.script := by decide

theorem powStep_trits (n k bench : Nat) (rhs acc : List Nat) (d : Nat)
    (ht : allTritList acc) (hk : k ≤ n) (hspan : 3 * (n - 1) < bench)
    (hn : n ≤ bench) (hr : rhs.length = n) :
    allTritList (powStep n k bench rhs acc d) := by
  rw [powStep_branch]
  have hcube := fieldCube_trits n k bench acc ht hspan hk
  have htakeR : rhs.take n = rhs := by rw [← hr, List.take_length]
  have hrhs : allTritList (fieldMul n k bench (fieldCube n k bench acc) rhs) := by
    simpa [htakeR] using fieldMul_trits n k bench (fieldCube n k bench acc) rhs hspan hn
  have hsq : allTritList (fieldMul n k bench rhs rhs) := by
    simpa [htakeR] using fieldMul_trits n k bench rhs rhs hspan hn
  have hsqLen : (fieldMul n k bench rhs rhs).length = n := fieldMul_length n k bench rhs rhs hn
  have htakeS : (fieldMul n k bench rhs rhs).take n = fieldMul n k bench rhs rhs := by
    have h := List.take_length (fieldMul n k bench rhs rhs)
    rwa [hsqLen] at h
  have hboth : allTritList (fieldMul n k bench (fieldCube n k bench acc)
      (fieldMul n k bench rhs rhs)) := by
    simpa [htakeS] using
      fieldMul_trits n k bench (fieldCube n k bench acc) (fieldMul n k bench rhs rhs) hspan hn
  by_cases h2 : d = 2
  · simpa [h2] using hboth
  · by_cases h1 : d = 1
    · simpa [h2, h1] using hrhs
    · simpa [h2, h1] using hcube

/-- One digit of the emitted power loop. Digit 0 settles the cube.
    Any other digit copies `src` into the spare and multiplies. -/
def powDigitRun (b : Ecbs.Board) (d src : Nat) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.marker_lift b
    let b ← Ecbs.cube b ((powUp : Nat) : Int) ((powUp : Nat) : Int)
    if d = 0 then
      Ecbs.settle b
    else
      do
        let b ← Ecbs.copy_band b ((powSpare : Nat) : Int) ((src : Nat) : Int) false
        let b ← Ecbs.mul b ((powUp : Nat) : Int) ((powUp : Nat) : Int)
            ((powSpare : Nat) : Int) false false false
        let b ← Ecbs.clear b ((powUp : Nat) : Int)
        Ecbs.settle b

/-- The power loop while `ds` digits remain. Counters carry
    `FitsLen (c + perDigit * ds.length)`. -/
structure PowAt (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat) (ds : List Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  shape : TierShape t
  sat : TierSat t
  markerOn : b.sudo_5Board_9marker_on = true
  benchOff : b.sudo_5Board_8bench_on = false
  accLen : acc.length = t.n
  rhsLen : rhs.length = t.n
  accT : allTritList acc
  rhsT : allTritList rhs
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  upHome : b.sudo_5Board_4home[powUp]'(by rw [szH]; decide) = embed acc
  upHeld : b.sudo_5Board_4held[powUp]'(by rw [szD]; decide) = true
  botHome : b.sudo_5Board_4home[powBottom]'(by rw [szH]; decide) = embed rhs
  botHeld : b.sudo_5Board_4held[powBottom]'(by rw [szD]; decide) = true
  gapHome : b.sudo_5Board_4home[powGap]'(by rw [szH]; decide) =
    embed (fieldMul t.n t.k t.benchlen rhs rhs)
  gapHeld : b.sudo_5Board_4held[powGap]'(by rw [szD]; decide) = true
  spareOff : b.sudo_5Board_4held[powSpare]'(by rw [szD]; decide) = false
  pack :
    ∃ (moves slides ctrl mark mx pk ps hole c0 c1 : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_6marker = Int.ofNat mark ∧
      mark ≤ 1 ∧
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps ∧
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) ∧
      FitsLen (moves + powMove t.n t.benchlen * ds.length) ∧
      FitsLen (slides + powSlide t.n * ds.length) ∧
      FitsLen (ctrl + powCtrl * ds.length) ∧
      FitsLen (c0 + ds.length) ∧
      FitsLen (c1 + ds.length)

end EcbsLink2.Link2
