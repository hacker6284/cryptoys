/-
  A nocopy multiply with the script marker on is the marker-off multiply on the
  board `marker_step` leaves, with the marker flag put back.
  The schoolbook is `school_loop_refines`. The lane fold is `lane_fold_refines`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Put the script-marker flag on. Every other field stays. -/
def markerOn (b : Ecbs.Board) : Ecbs.Board :=
  { b with sudo_5Board_9marker_on := true }

@[simp] theorem markerOn_flag (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_9marker_on = true := rfl

@[simp] theorem markerOn_tier (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_1t = b.sudo_5Board_1t := rfl

@[simp] theorem markerOn_held (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4held = b.sudo_5Board_4held := rfl

@[simp] theorem markerOn_home (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4home = b.sudo_5Board_4home := rfl

@[simp] theorem markerOn_row (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_3row = b.sudo_5Board_3row := rfl

@[simp] theorem markerOn_moves (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

@[simp] theorem markerOn_peak (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

@[simp] theorem markerOn_strict (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

@[simp] theorem markerOn_hole (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl

@[simp] theorem markerOn_on (b : Ecbs.Board) :
    (markerOn b).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := rfl

theorem markerOn_def (b : Ecbs.Board) :
    markerOn b = { b with sudo_5Board_9marker_on := true } := rfl

theorem markerOn_clear (b : Ecbs.Board) (h : b.sudo_5Board_9marker_on = false) :
    { markerOn b with sudo_5Board_9marker_on := false } = b := by
  unfold markerOn
  exact clear_flag b h

/-- The bench write and the marker flag touch different fields. -/
theorem bench_markerOn (b : Ecbs.Board) (strip : Array Int) :
    { { b with sudo_5Board_9marker_on := true } with sudo_5Board_5bench := strip } =
      { { b with sudo_5Board_5bench := strip } with sudo_5Board_9marker_on := true } := by
  apply board_ext <;> rfl

theorem noteBench_marker (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
  unfold noteBench withMoves withHole
  split <;> rfl

@[simp] theorem moves_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

@[simp] theorem tier_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold withMoves
  rfl

@[simp] theorem held_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold withMoves
  rfl

@[simp] theorem hole_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold withMoves
  rfl

@[simp] theorem peak_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := by
  unfold withMoves
  rfl

@[simp] theorem marker_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
  unfold withMoves
  rfl

theorem withMoves_markerOn (b : Ecbs.Board) (m : Int) :
    withMoves (markerOn b) m = markerOn (withMoves b m) := by
  unfold withMoves markerOn
  rfl

/-- The op-count bump and the seated marker frame touch different fields. -/
theorem mul_down_bump (b : Ecbs.Board) (ctrl mx cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hmk : b.sudo_5Board_9marker_on = true) :
    { bumpOp (markerDownFeed b ctrl mx) 0 cOps (by simpa [markerDownFeed] using hops) with
        sudo_5Board_9marker_on := true } =
      { bumpOp b 0 cOps hops with
        sudo_5Board_6marker := 0
        sudo_5Board_4cost := { (bumpOp b 0 cOps hops).sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx 1) } } := by
  unfold bumpOp markerDownFeed
  simp [hmk]

theorem mul_up_bump (b : Ecbs.Board) (m ctrl mx cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hmk : b.sudo_5Board_9marker_on = true) :
    { bumpOp (markerUpFeed b m ctrl mx) 0 cOps (by simpa [markerUpFeed] using hops) with
        sudo_5Board_9marker_on := true } =
      { bumpOp b 0 cOps hops with
        sudo_5Board_6marker := Int.ofNat (m + 1)
        sudo_5Board_4cost := { (bumpOp b 0 cOps hops).sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx (m + 2)) } } := by
  unfold bumpOp markerUpFeed
  simp [hmk]

/-- Lane fold, then the bench write, then `note_peak`. The school loop's `after`. -/
def mulAfter (σ : Int × (Ecbs.Board × Array Int)) : Except SudoRt.Trap Ecbs.Board :=
  do
    let folded ← Ecbs.lane_fold σ.2.1 σ.2.2
    let out ← Ecbs.note_peak { folded.1 with sudo_5Board_5bench := folded.2 }
    pure out

/-- Fresh strip aimed at `dst`. -/
def mulAimed (b : Ecbs.Board) (dst : Int) (strip : Array Int) : Ecbs.Board :=
  { b with
    sudo_5Board_8bench_on := true
    sudo_5Board_8bench_to := dst
    sudo_5Board_5bench := strip }

@[simp] theorem mulAimed_held (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    (mulAimed b dst strip).sudo_5Board_4held = b.sudo_5Board_4held := rfl

@[simp] theorem mulAimed_home (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    (mulAimed b dst strip).sudo_5Board_4home = b.sudo_5Board_4home := rfl

@[simp] theorem mulAimed_tier (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    (mulAimed b dst strip).sudo_5Board_1t = b.sudo_5Board_1t := rfl

@[simp] theorem mulAimed_moves (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    (mulAimed b dst strip).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

@[simp] theorem mulAimed_strict (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    (mulAimed b dst strip).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

@[simp] theorem strict_held (b : Ecbs.Board) (peakS : Nat) :
    (strictBoard b peakS).sudo_5Board_4held = b.sudo_5Board_4held := rfl

@[simp] theorem strict_home (b : Ecbs.Board) (peakS : Nat) :
    (strictBoard b peakS).sudo_5Board_4home = b.sudo_5Board_4home := rfl

@[simp] theorem strict_moves (b : Ecbs.Board) (peakS : Nat) :
    (strictBoard b peakS).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

/-- `note_strict`, then the second home is cleared. The school loop starts here. -/
def mulPrep (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) : Ecbs.Board :=
  { strictBoard (mulAimed b dst strip) peakS with
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨second, hS⟩ false
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨second, hHome⟩ #[] }

@[simp] theorem mulPrep_marker (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  unfold mulPrep mulAimed strictBoard
  rfl

@[simp] theorem mulPrep_tier (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold mulPrep mulAimed strictBoard
  rfl

@[simp] theorem mulPrep_moves (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := by
  unfold mulPrep mulAimed strictBoard
  rfl

@[simp] theorem mulPrep_peak (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := by
  unfold mulPrep mulAimed strictBoard
  rfl

@[simp] theorem mulPrep_hole (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold mulPrep mulAimed strictBoard
  rfl

theorem mulPrep_held_size (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat) (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold mulPrep mulAimed strictBoard
  simp

theorem mulPrep_markerOn (b : Ecbs.Board) (dst : Int) (strip : Array Int)
    (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size)
    (hS' : second < (markerOn b).sudo_5Board_4held.size)
    (hHome' : second < (markerOn b).sudo_5Board_4home.size) :
    mulPrep (markerOn b) dst strip second peakS hS' hHome' =
      markerOn (mulPrep b dst strip second peakS hS hHome) := by
  unfold mulPrep mulAimed strictBoard markerOn
  apply board_ext
  case hheld =>
    have hfin : (⟨second, hS'⟩ : Fin _) = ⟨second, hS⟩ := Fin.ext rfl
    simp [hfin]
  case hhome =>
    have hfin : (⟨second, hHome'⟩ : Fin _) = ⟨second, hHome⟩ := Fin.ext rfl
    simp [hfin]
  all_goals rfl

/-- Nocopy body after `settle`: fresh strip, schoolbook, lane fold.
    `n` is the length `log_op` captured before the slide. -/
def mulNoTail (n : Int) (b : Ecbs.Board) (dst first second : Int) :
    Except SudoRt.Trap Ecbs.Board :=
  do
    let strip ← SudoRt.filledL b.sudo_5Board_1t.sudo_4Tier_8benchlen (0 : Int)
    let held ← SudoRt.atL b.sudo_5Board_4held first
    SudoRt.sudoAssert held 568
    let a ← SudoRt.atL b.sudo_5Board_4home first
    let src := second
    SudoRt.sudoAssert (!(SudoRt.SEq.beq src first)) 575
    let b ← Ecbs.note_strict (mulAimed b dst strip)
    let held2 ← SudoRt.atL b.sudo_5Board_4held src
    SudoRt.sudoAssert held2 577
    let s ← SudoRt.atL b.sudo_5Board_4home src
    let heldA ← SudoRt.putL b.sudo_5Board_4held src false
    let b := { b with sudo_5Board_4held := heldA }
    let homeA ← SudoRt.putL b.sudo_5Board_4home src (#[] : Array Int)
    let b := { b with sudo_5Board_4home := homeA }
    let fromV ← SudoRt.subI n (1 : Int)
    let toV : Int := 0
    let fuel : Nat := if fromV < toV then 1 else (fromV - toV).natAbs + 1
    SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, (b, strip)) fuel
      (mulSchoolStep a s false n toV) mulAfter (fun r => pure r)

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

private theorem nat_beq_false (a b : Nat) (h : a ≠ b) :
    SudoRt.SEq.beq (a : Int) (b : Int) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b] at hEq
    exact hEq))

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

/-- The lane fold does not read the marker flag. The arithmetic is `lane_fold_refines`. -/
theorem mulAfter_flag (b : Ecbs.Board) (sch : List Nat)
    (w h r n k mv hole bench peak : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hfit : FitsLen sch.length)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hs : allTritList sch)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfm : FitsLen (mv + 3 * (sch.length - n)))
    (hlen : sch.length ≤ bench) (hpos : 0 < bench) :
    mulAfter (Int.ofNat 0, (markerOn b, embed sch)) =
      (do
        let r ← mulAfter (Int.ofNat 0, (b, embed sch))
        pure { r with sudo_5Board_9marker_on := true }) := by
  unfold mulAfter
  have hwM : (markerOn b).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [markerOn_tier]; exact hw
  have hhM : (markerOn b).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [markerOn_tier]; exact hh
  have hrM : (markerOn b).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [markerOn_tier]; exact hr
  have hnM : (markerOn b).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    rw [markerOn_tier]; exact hn
  have hkM : (markerOn b).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [markerOn_tier]; exact hk
  have hblM : (markerOn b).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [markerOn_tier]; exact hbl
  have hmM : (markerOn b).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    rw [markerOn_moves]; exact hm
  have hholeM : (markerOn b).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat hole := by
    rw [markerOn_hole]; exact hhole
  rw [lane_fold_eq sch w h r n k bench (markerOn b) hfit hwM hhM hrM hnM hkM hblM]
  rw [lane_fold_eq sch w h r n k bench b hfit hw hh hr hn hk hbl]
  rw [lane_fold_refines sch w h r n k mv hole bench (markerOn b)
      hw0 hh0 hrR hrP hnE hkLe hgap hs hmM hholeM hsm hnsm hfm hfit hlen hpos]
  rw [lane_fold_refines sch w h r n k mv hole bench b
      hw0 hh0 hrR hrP hnE hkLe hgap hs hm hhole hsm hnsm hfm hfit hlen hpos]
  simp only [ok_bind, pure_eq_ok, Prod.fst, Prod.snd]
  let top := Int.ofNat (topIdx sch)
  let mvF := Int.ofNat (mv + foldCharge n (n - k) sch)
  let folded := embed (laneFold n (n - k) sch)
  have hnb : noteBench (markerOn b) top mvF =
      { noteBench b top mvF with sudo_5Board_9marker_on := true } := by
    rw [noteBench_flag (markerOn b) top mvF (markerOn_flag b), markerOn_clear b hflag]
  let nOn := { noteBench (markerOn b) top mvF with sudo_5Board_5bench := folded }
  let nOff := { noteBench b top mvF with sudo_5Board_5bench := folded }
  have hbenchNB : noteBench (markerOn b) top mvF = markerOn (noteBench b top mvF) := by
    rw [hnb]
    exact (markerOn_def (noteBench b top mvF)).symm
  have hnN : nOn = markerOn nOff := by
    unfold nOn nOff
    rw [hbenchNB, markerOn_def, markerOn_def]
  have h7N : 7 ≤ nOn.sudo_5Board_4held.size := by
    simp only [nOn, noteBench_held, markerOn_held]
    exact h7
  have hpN : nOn.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [show nOn.sudo_5Board_4cost.sudo_5Costs_4peak =
        (noteBench (markerOn b) top mvF).sudo_5Board_4cost.sudo_5Costs_4peak from rfl,
      noteBench_peak, markerOn_peak]
    exact hpeak
  have h7F : 7 ≤ nOff.sudo_5Board_4held.size := by
    simp only [nOff, noteBench_held]
    exact h7
  have hpF : nOff.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [show nOff.sudo_5Board_4cost.sudo_5Costs_4peak =
        (noteBench b top mvF).sudo_5Board_4cost.sudo_5Costs_4peak from rfl,
      noteBench_peak]
    exact hpeak
  conv =>
    lhs
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak nOn
  conv =>
    rhs
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak nOff
  rw [note_peak_eq nOn peak h7N hpN, note_peak_eq nOff peak h7F hpF]
  simp only [ok_bind, pure_eq_ok]
  have hoffN : nOff.sudo_5Board_9marker_on = false := by
    have hproj : nOff.sudo_5Board_9marker_on =
        (noteBench b top mvF).sudo_5Board_9marker_on := rfl
    rw [hproj, noteBench_marker, hflag]
  rw [hnN]
  rw [peakBoard_flag (markerOn nOff) peak (markerOn_flag nOff)]
  rw [markerOn_clear nOff hoffN]

/-- Lane fold of one strip, then `note_peak`. The bench is `laneFold`. -/
def ontoFoldBoard (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) : Ecbs.Board :=
  peakBoard
    { noteBench b (Int.ofNat (topIdx sch))
        (Int.ofNat (mv + foldCharge n (n - k) sch)) with
      sudo_5Board_5bench := embed (laneFold n (n - k) sch) }
    peak

theorem ontoFoldBoard_bench (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_5bench =
      embed (laneFold n (n - k) sch) := rfl

theorem ontoFoldBoard_high (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem ontoFoldBoard_row (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_3row = b.sudo_5Board_3row := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

/-- `mulAfter` on a marker-off board is that fold. -/
theorem mulAfter_ok (b : Ecbs.Board) (sch : List Nat)
    (w h r n k mv hole bench peak : Nat)
    (hfit : FitsLen sch.length)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hs : allTritList sch)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfm : FitsLen (mv + 3 * (sch.length - n)))
    (hlen : sch.length ≤ bench) (hpos : 0 < bench) :
    mulAfter (Int.ofNat 0, (b, embed sch)) =
      .ok (ontoFoldBoard b sch n k mv peak) := by
  unfold mulAfter ontoFoldBoard
  rw [lane_fold_eq sch w h r n k bench b hfit hw hh hr hn hk hbl]
  rw [lane_fold_refines sch w h r n k mv hole bench b
      hw0 hh0 hrR hrP hnE hkLe hgap hs hm hhole hsm hnsm hfm hfit hlen hpos]
  simp only [ok_bind, pure_eq_ok, Prod.fst, Prod.snd]
  let top := Int.ofNat (topIdx sch)
  let mvF := Int.ofNat (mv + foldCharge n (n - k) sch)
  let folded := embed (laneFold n (n - k) sch)
  let nOff := { noteBench b top mvF with sudo_5Board_5bench := folded }
  have h7F : 7 ≤ nOff.sudo_5Board_4held.size := by
    simp only [nOff, noteBench_held]
    exact h7
  have hpF : nOff.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [show nOff.sudo_5Board_4cost.sudo_5Costs_4peak =
        (noteBench b top mvF).sudo_5Board_4cost.sudo_5Costs_4peak from rfl,
      noteBench_peak]
    exact hpeak
  conv =>
    lhs
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak nOff
  rw [note_peak_eq nOff peak h7F hpF]
  simp only [ok_bind]

/-- From the settled board through the schoolbook. The lane fold stays inside `mulAfter`. -/
theorem mul_tail_eq (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peakS : Nat)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    mulNoTail ((n : Nat) : Int) b ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep b ((dst : Nat) : Int) (embed (List.replicate bench 0))
              second peakS hS hHomeS)
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold mulNoTail
  rw [hbl, filledL_ofNat, ok_bind]
  rw [← embed_replicate_zero]
  rw [← ofNat_eq_natCast first]
  rw [atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ first hHome, hArr, ok_bind]
  have hbf : SudoRt.SEq.beq (↑second) (Int.ofNat first) = false := by
    rw [ofNat_eq_natCast first]
    exact nat_beq_false second first hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b ((dst : Nat) : Int) strip
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by simpa [bA, mulAimed] using h7
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bA, mulAimed] using hpeakS
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bA peakS
  have hheldS : bS.sudo_5Board_4held = bA.sudo_5Board_4held := rfl
  have hhomeS : bS.sudo_5Board_4home = bA.sudo_5Board_4home := rfl
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves =
      bA.sudo_5Board_4cost.sudo_5Costs_5moves := rfl
  have hSs : second < bS.sudo_5Board_4held.size := by
    rw [hheldS]; simpa [bA, mulAimed] using hS
  have hHs : second < bS.sudo_5Board_4home.size := by
    rw [hhomeS]; simpa [bA, mulAimed] using hHomeS
  have hHeld2 : bS.sudo_5Board_4held[second] = true := by
    simp [bS, strictBoard, bA, mulAimed, hHS]
  have hHome2 : bS.sudo_5Board_4home[second] = embed ys := by
    simp [bS, strictBoard, bA, mulAimed, hYs]
  rw [← ofNat_eq_natCast second, atL_ofNat _ second hSs, hHeld2]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ second hHs, hHome2, ok_bind]
  rw [putL_ofNat _ second false hSs, ok_bind]
  rw [putL_ofNat _ second (#[] : Array Int) hHs, ok_bind]
  rw [show ((n : Nat) : Int) = Int.ofNat n from (ofNat_eq_natCast n).symm]
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bL := mulPrep b ((dst : Nat) : Int) strip second peakS hS hHomeS
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [show bL.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves from by simp [bL, mulPrep_moves]]
    simpa [ofNat_eq_natCast] using hmoves
  rw [mulSchool_step]
  conv =>
    pattern (rowStep _ _ _ _ _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) moves n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [size_embed, List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]

/-- The settled nocopy tail does not read the marker flag. -/
theorem mul_tail_flag (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    mulNoTail ((n : Nat) : Int) (markerOn b) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) =
      (do
        let r ← mulNoTail ((n : Nat) : Int) b ((dst : Nat) : Int) ((first : Nat) : Int)
          ((second : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  have hS' : second < (markerOn b).sudo_5Board_4held.size := by simpa using hS
  have hHome' : second < (markerOn b).sudo_5Board_4home.size := by simpa using hHomeS
  have hF' : first < (markerOn b).sudo_5Board_4held.size := by simpa using hF
  have hHomeF' : first < (markerOn b).sudo_5Board_4home.size := by simpa using hHome
  have hHF' : (markerOn b).sudo_5Board_4held[first] = true := by simpa using hHF
  have hArr' : (markerOn b).sudo_5Board_4home[first] = embed xs := by simpa using hArr
  have hHS' : (markerOn b).sudo_5Board_4held[second] = true := by simpa using hHS
  have hYs' : (markerOn b).sudo_5Board_4home[second] = embed ys := by simpa using hYs
  have h7' : 7 ≤ (markerOn b).sudo_5Board_4held.size := by simpa using h7
  have hbl' : (markerOn b).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simpa using hbl
  have hmoves' : (markerOn b).sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa using hmoves
  have hpeakS' : (markerOn b).sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa using hpeakS
  rw [mul_tail_eq (markerOn b) dst first second xs ys n moves bench peakS
      hbl' hF' hHomeF' hHF' hArr' hS' hHome' hHS' hYs' h7' hne hn0 hlenx hleny hf
      hmoves' hpeakS' hspan hxsT hfi hfm]
  rw [mul_tail_eq b dst first second xs ys n moves bench peakS
      hbl hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0 hlenx hleny hf
      hmoves hpeakS hspan hxsT hfi hfm]
  rw [mulPrep_markerOn b ((dst : Nat) : Int) (embed (List.replicate bench 0)) second peakS
      hS hHomeS hS' hHome', withMoves_markerOn]
  let sch := school n xs ys (List.replicate bench 0) false
  let mvW := moves + schoolMoves xs ys n n
  let bW := withMoves (mulPrep b ((dst : Nat) : Int) (embed (List.replicate bench 0))
      second peakS hS hHomeS) (Int.ofNat mvW)
  have hflagW : bW.sudo_5Board_9marker_on = false := by
    simp [bW, mulPrep_marker, hflag]
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length xs ys (List.replicate bench 0) false n
  have hfit : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have hnW : bW.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bW, mulPrep_tier, hn, ofNat_eq_natCast]
  have hwW : bW.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bW, mulPrep_tier, hw]
  have hhW : bW.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bW, mulPrep_tier, hh]
  have hrW : bW.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bW, mulPrep_tier, hr]
  have hkW : bW.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bW, mulPrep_tier, hk]
  have hblW : bW.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bW, mulPrep_tier, hbl]
  have hmW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvW := by
    simp [bW]
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bW, mulPrep_hole, hhole]
  have hpeakW : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bW, mulPrep_peak, hpeak]
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by
    simpa [bW, mulPrep_held_size] using h7
  have htri : allTritList sch := by
    simpa [sch] using school_trits xs ys (List.replicate bench 0) false n (replicate_trits _)
      (fun i hi => by
        rw [List.length_replicate]
        have : i + (n - 1) ≤ 2 * (n - 1) := by omega
        exact Nat.lt_of_le_of_lt this hspan)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hpos : 0 < bench := by omega
  have hfitF : FitsLen (mvW + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by
      have := schoolMoves_bound xs ys n
      omega)
  exact mulAfter_flag bW sch w h r n k mvW hole bench peak hflagW hfit hwW hhW hrW hnW hkW
    hblW hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hpos

/-- Marker off, bench off. The emitted nocopy `mul` is `mulAfter` of the schoolbook. -/
theorem mul_off_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep (bumpOp b 0 cOps hops) ((dst : Nat) : Int)
              (embed (List.replicate bench 0)) second peakS hS hHomeS)
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_off (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  simp only [ok_bind]
  rw [settle_off (bumpOp b 0 cOps hops) (by simp [bumpOp, hoff])]
  simp only [ok_bind, pure_eq_ok]
  let b0 := bumpOp b 0 cOps hops
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, bumpOp, hbl]
  rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  rw [bumpOp_held, bumpOp_home]
  rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ first hHome, hArr, ok_bind]
  have hbf : SudoRt.SEq.beq (↑second) (Int.ofNat first) = false := by
    rw [ofNat_eq_natCast first]
    exact nat_beq_false second first hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by simpa [bA, mulAimed, b0, bumpOp] using h7
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bA, mulAimed, b0, bumpOp] using hpeakS
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bA peakS
  have hheldS : bS.sudo_5Board_4held = b.sudo_5Board_4held := by
    simp [bS, strictBoard, bA, mulAimed, b0, bumpOp]
  have hhomeS : bS.sudo_5Board_4home = b.sudo_5Board_4home := by
    simp [bS, strictBoard, bA, mulAimed, b0, bumpOp]
  have hSs : second < bS.sudo_5Board_4held.size := by rw [hheldS]; exact hS
  have hHs : second < bS.sudo_5Board_4home.size := by rw [hhomeS]; exact hHomeS
  have hHeld2 : bS.sudo_5Board_4held[second] = true := by
    simp [bS, strictBoard, bA, mulAimed, b0, bumpOp, hHS]
  have hHome2 : bS.sudo_5Board_4home[second] = embed ys := by
    simp [bS, strictBoard, bA, mulAimed, b0, bumpOp, hYs]
  rw [← ofNat_eq_natCast second, atL_ofNat _ second hSs, hHeld2]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ second hHs, hHome2, ok_bind]
  rw [putL_ofNat _ second false hSs, ok_bind]
  rw [putL_ofNat _ second (#[] : Array Int) hHs, ok_bind]
  rw [show (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
    simp [bumpOp, hn, ofNat_eq_natCast]]
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bL := mulPrep b0 ((dst : Nat) : Int) strip second peakS hS hHomeS
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [bL, mulPrep_moves, b0, bumpOp, hmoves, ofNat_eq_natCast]
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) moves n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [size_embed, List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]

/-- Marker on and lifted, bench off. The emitted nocopy `mul` is `mulAfter`
    on the board `marker_step` leaves. -/
theorem mul_down_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peakS cOps ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitC : FitsLen (ctrl + 1))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep { bumpOp (markerDownFeed b ctrl mx) 0 cOps
                (by simpa [markerDownFeed] using hops) with
                sudo_5Board_9marker_on := true }
              ((dst : Nat) : Int) (embed (List.replicate bench 0)) second peakS
              (by simpa [markerDownFeed, bumpOp] using hS)
              (by simpa [markerDownFeed, bumpOp] using hHomeS))
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker < 0 := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hscript
  rw [marker_step_down (bumpOp b 0 cOps hops) ctrl mx script hmB hcB hxB hsB hpos hfitC]
  rw [← mul_down_bump b ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let feed := markerDownFeed b ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerDownFeed] using hops
  let b0 := { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true }
  rw [settle_off b0 (by simp [b0, bumpOp, feed, markerDownFeed, hoff])]
  simp only [ok_bind, pure_eq_ok]
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, bumpOp, feed, markerDownFeed, hbl]
  have hheld0 : b0.sudo_5Board_4held = b.sudo_5Board_4held := by
    simp [b0, bumpOp, feed, markerDownFeed]
  have hhome0 : b0.sudo_5Board_4home = b.sudo_5Board_4home := by
    simp [b0, bumpOp, feed, markerDownFeed]
  conv =>
    lhs
    rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [hheld0, hhome0]
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ first hHome, hArr, ok_bind]
  have hbf : SudoRt.SEq.beq (↑second) (Int.ofNat first) = false := by
    rw [ofNat_eq_natCast first]
    exact nat_beq_false second first hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by simpa [bA, mulAimed, hheld0] using h7
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bA, mulAimed, b0, bumpOp, feed, markerDownFeed] using hpeakS
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bA peakS
  have hheldStep : bS.sudo_5Board_4held = b0.sudo_5Board_4held := by
    simp [bS, strictBoard, bA, mulAimed]
  have hhomeStep : bS.sudo_5Board_4home = b0.sudo_5Board_4home := by
    simp [bS, strictBoard, bA, mulAimed]
  have hheldS : bS.sudo_5Board_4held = b.sudo_5Board_4held := hheldStep.trans hheld0
  have hhomeS : bS.sudo_5Board_4home = b.sudo_5Board_4home := hhomeStep.trans hhome0
  have hSs : second < bS.sudo_5Board_4held.size := by rw [hheldS]; exact hS
  have hHs : second < bS.sudo_5Board_4home.size := by rw [hhomeS]; exact hHomeS
  conv =>
    lhs
    pattern (SudoRt.atL bS.sudo_5Board_4held _)
    rw [hheldS]
  conv =>
    lhs
    pattern (SudoRt.atL bS.sudo_5Board_4home _)
    rw [hhomeS]
  rw [← ofNat_eq_natCast second, atL_ofNat _ second hS, hHS]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ second hHomeS, hYs, ok_bind]
  rw [putL_ofNat _ second false hSs, ok_bind]
  rw [putL_ofNat _ second (#[] : Array Int) hHs, ok_bind]
  rw [show b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
    simp [b0, bumpOp, feed, markerDownFeed, hn, ofNat_eq_natCast]]
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bL := mulPrep b0 ((dst : Nat) : Int) strip second peakS
    (by simpa [b0, bumpOp, feed, markerDownFeed] using hS)
    (by simpa [b0, bumpOp, feed, markerDownFeed] using hHomeS)
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [bL, mulPrep_moves, b0, bumpOp, feed, markerDownFeed, hmoves, ofNat_eq_natCast]
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) moves n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [size_embed, List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]

/-- A nocopy multiply with the marker lifted is `mulNoOffBoard` of the board
    `marker_step` leaves, with the flag put back. Arithmetic is `mul_no_eq`. -/
theorem mul_down_eq (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS cOps ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitC : FitsLen (ctrl + 1))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false false =
      .ok { mulNoOffBoard (markerDownFeed b ctrl mx) dst second xs ys n k moves hole bench
          peak peakS cOps hops hS hHomeS with
        sudo_5Board_9marker_on := true } := by
  let feed := markerDownFeed b ctrl mx
  have hflagF : feed.sudo_5Board_9marker_on = false := by simp [feed, markerDownFeed]
  have hoffF : feed.sudo_5Board_8bench_on = false := by simp [feed, markerDownFeed, hoff]
  have hOff := mul_off_after feed dst first second xs ys n moves bench peakS cOps
    hflagF hoffF hops (by simpa [feed, markerDownFeed] using hop0) hfops
    (by simpa [feed, markerDownFeed] using hbl)
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0
    (by simpa [feed, markerDownFeed] using hn) hlenx hleny hf
    (by simpa [feed, markerDownFeed] using hmoves)
    (by simpa [feed, markerDownFeed] using hpeakS) hspan hxsT hfi hfm
  have hCard := mul_no_eq feed dst first second xs ys w h r n k moves hole bench peak peakS cOps
    hflagF hoffF hops (by simpa [feed, markerDownFeed] using hop0) hfops
    (by simpa [feed, markerDownFeed] using hbl)
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0
    (by simpa [feed, markerDownFeed] using hn) hlenx hleny hf
    (by simpa [feed, markerDownFeed] using hmoves)
    (by simpa [feed, markerDownFeed] using hpeak)
    (by simpa [feed, markerDownFeed] using hpeakS) hspan hxsT hfi hfm
    ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩
    (by simpa [feed, markerDownFeed] using hw)
    (by simpa [feed, markerDownFeed] using hh)
    (by simpa [feed, markerDownFeed] using hr)
    (by simpa [feed, markerDownFeed] using hk)
    (by simpa [feed, markerDownFeed] using hhole)
    hsm hnsm hfitB hfold
  have hOn := mul_down_after b dst first second xs ys n moves bench peakS cOps ctrl mx script
    hmk hoff hm hc hx hscript hpos hfitC hops hop0 hfops hbl hF hHome hHF hArr hS hHomeS hHS hYs
    h7 hne hn0 hn hlenx hleny hf hmoves hpeakS hspan hxsT hfi hfm
  rw [hOn]
  let sch := school n xs ys (List.replicate bench 0) false
  let mvW := moves + schoolMoves xs ys n n
  let strip := embed (List.replicate bench 0)
  let bFeed := bumpOp feed 0 cOps hops
  let bPrep := mulPrep bFeed ((dst : Nat) : Int) strip second peakS hS hHomeS
  let bW := withMoves bPrep (Int.ofNat mvW)
  have hprep : mulPrep { bFeed with sudo_5Board_9marker_on := true }
      ((dst : Nat) : Int) strip second peakS
      (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hS)
      (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hHomeS) =
      markerOn bPrep := by
    simpa [bFeed, markerOn_def] using
      mulPrep_markerOn bFeed ((dst : Nat) : Int) strip second peakS hS hHomeS
        (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hS)
        (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hHomeS)
  have hmove : withMoves (mulPrep { bFeed with sudo_5Board_9marker_on := true }
      ((dst : Nat) : Int) strip second peakS
      (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hS)
      (by simpa [bFeed, bumpOp, feed, markerDownFeed] using hHomeS)) (Int.ofNat mvW) =
      markerOn bW := by
    rw [hprep, withMoves_markerOn]
  rw [hmove]
  have hflagW : bW.sudo_5Board_9marker_on = false := by
    simp [bW, bPrep, mulPrep_marker, bFeed, bumpOp, feed, markerDownFeed]
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length xs ys (List.replicate bench 0) false n
  have hfit : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have hnW : bW.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hn, ofNat_eq_natCast]
  have hwW : bW.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hw]
  have hhW : bW.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hh]
  have hrW : bW.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hr]
  have hkW : bW.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hk]
  have hblW : bW.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerDownFeed, hbl]
  have hmW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvW := by simp [bW]
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bW, bPrep, mulPrep_hole, bFeed, bumpOp, feed, markerDownFeed, hhole]
  have hpeakW : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bW, bPrep, mulPrep_peak, bFeed, bumpOp, feed, markerDownFeed, hpeak]
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by
    simpa [bW, bPrep, mulPrep_held_size, bFeed, bumpOp, feed, markerDownFeed] using h7
  have htri : allTritList sch := by
    simpa [sch] using school_trits xs ys (List.replicate bench 0) false n (replicate_trits _)
      (fun i hi => by
        rw [List.length_replicate]
        have : i + (n - 1) ≤ 2 * (n - 1) := by omega
        exact Nat.lt_of_le_of_lt this hspan)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hposB : 0 < bench := by omega
  have hfitF : FitsLen (mvW + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by
      have := schoolMoves_bound xs ys n
      omega)
  rw [mulAfter_flag bW sch w h r n k mvW hole bench peak hflagW hfit hwW hhW hrW hnW hkW hblW
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hposB]
  have hAfter : mulAfter (Int.ofNat 0, (bW, embed sch)) =
      .ok (mulNoOffBoard feed dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS) := by
    simpa [bW, bPrep, bFeed, strip, sch, mvW, feed] using hOff.symm.trans hCard
  rw [hAfter]
  simp only [ok_bind, pure_eq_ok]

/-- Marker on and already seated, bench off. The emitted nocopy `mul` is `mulAfter`
    on the board `marker_step` leaves. -/
theorem mul_up_after (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (n moves bench peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep { bumpOp (markerUpFeed b m ctrl mx) 0 cOps
                (by simpa [markerUpFeed] using hops) with
                sudo_5Board_9marker_on := true }
              ((dst : Nat) : Int) (embed (List.replicate bench 0)) second peakS
              (by simpa [markerUpFeed, bumpOp] using hS)
              (by simpa [markerUpFeed, bumpOp] using hHomeS))
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys (List.replicate bench 0) false))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hscript
  rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitM hfitC hfit2]
  rw [← mul_up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let b0 := { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true }
  rw [settle_off b0 (by simp [b0, bumpOp, feed, markerUpFeed, hoff])]
  simp only [ok_bind, pure_eq_ok]
  have hbl0 : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, bumpOp, feed, markerUpFeed, hbl]
  have hheld0 : b0.sudo_5Board_4held = b.sudo_5Board_4held := by
    simp [b0, bumpOp, feed, markerUpFeed]
  have hhome0 : b0.sudo_5Board_4home = b.sudo_5Board_4home := by
    simp [b0, bumpOp, feed, markerUpFeed]
  conv =>
    lhs
    rw [hbl0, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [hheld0, hhome0]
  conv =>
    lhs
    rw [← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ first hHome, hArr, ok_bind]
  have hbf : SudoRt.SEq.beq (↑second) (Int.ofNat first) = false := by
    rw [ofNat_eq_natCast first]
    exact nat_beq_false second first hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let strip := embed (List.replicate bench 0)
  let bA := mulAimed b0 ((dst : Nat) : Int) strip
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by simpa [bA, mulAimed, hheld0] using h7
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bA, mulAimed, b0, bumpOp, feed, markerUpFeed] using hpeakS
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bA peakS
  have hheldStep : bS.sudo_5Board_4held = b0.sudo_5Board_4held := by
    simp [bS, strictBoard, bA, mulAimed]
  have hhomeStep : bS.sudo_5Board_4home = b0.sudo_5Board_4home := by
    simp [bS, strictBoard, bA, mulAimed]
  have hheldS : bS.sudo_5Board_4held = b.sudo_5Board_4held := hheldStep.trans hheld0
  have hhomeS : bS.sudo_5Board_4home = b.sudo_5Board_4home := hhomeStep.trans hhome0
  have hSs : second < bS.sudo_5Board_4held.size := by rw [hheldS]; exact hS
  have hHs : second < bS.sudo_5Board_4home.size := by rw [hhomeS]; exact hHomeS
  conv =>
    lhs
    pattern (SudoRt.atL bS.sudo_5Board_4held _)
    rw [hheldS]
  conv =>
    lhs
    pattern (SudoRt.atL bS.sudo_5Board_4home _)
    rw [hhomeS]
  rw [← ofNat_eq_natCast second, atL_ofNat _ second hS, hHS]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ second hHomeS, hYs, ok_bind]
  rw [putL_ofNat _ second false hSs, ok_bind]
  rw [putL_ofNat _ second (#[] : Array Int) hHs, ok_bind]
  rw [show b0.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n from by
    simp [b0, bumpOp, feed, markerUpFeed, hn, ofNat_eq_natCast]]
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bL := mulPrep b0 ((dst : Nat) : Int) strip second peakS
    (by simpa [b0, bumpOp, feed, markerUpFeed] using hS)
    (by simpa [b0, bumpOp, feed, markerUpFeed] using hHomeS)
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [bL, mulPrep_moves, b0, bumpOp, feed, markerUpFeed, hmoves, ofNat_eq_natCast]
  simp only [strip]
  rw [school_loop_refines xs ys (List.replicate bench 0) moves n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hleny]; exact Nat.le_refl _)
      (by simp [size_embed, List.length_replicate]; exact hspan)
      hxsT (replicate_trits _) hmL hf hfi hfm]
  rw [bind_ok_id]

/-- A nocopy multiply with the marker already seated is `mulNoOffBoard` of the board
    `marker_step` leaves, with the flag put back. Arithmetic is `mul_no_eq`. -/
theorem mul_up_eq (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false false =
      .ok { mulNoOffBoard (markerUpFeed b m ctrl mx) dst second xs ys n k moves hole bench
          peak peakS cOps hops hS hHomeS with
        sudo_5Board_9marker_on := true } := by
  let feed := markerUpFeed b m ctrl mx
  have hflagF : feed.sudo_5Board_9marker_on = false := by simp [feed, markerUpFeed]
  have hoffF : feed.sudo_5Board_8bench_on = false := by simp [feed, markerUpFeed, hoff]
  have hOff := mul_off_after feed dst first second xs ys n moves bench peakS cOps
    hflagF hoffF hops (by simpa [feed, markerUpFeed] using hop0) hfops
    (by simpa [feed, markerUpFeed] using hbl)
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0
    (by simpa [feed, markerUpFeed] using hn) hlenx hleny hf
    (by simpa [feed, markerUpFeed] using hmoves)
    (by simpa [feed, markerUpFeed] using hpeakS) hspan hxsT hfi hfm
  have hCard := mul_no_eq feed dst first second xs ys w h r n k moves hole bench peak peakS cOps
    hflagF hoffF hops (by simpa [feed, markerUpFeed] using hop0) hfops
    (by simpa [feed, markerUpFeed] using hbl)
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0
    (by simpa [feed, markerUpFeed] using hn) hlenx hleny hf
    (by simpa [feed, markerUpFeed] using hmoves)
    (by simpa [feed, markerUpFeed] using hpeak)
    (by simpa [feed, markerUpFeed] using hpeakS) hspan hxsT hfi hfm
    ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩
    (by simpa [feed, markerUpFeed] using hw)
    (by simpa [feed, markerUpFeed] using hh)
    (by simpa [feed, markerUpFeed] using hr)
    (by simpa [feed, markerUpFeed] using hk)
    (by simpa [feed, markerUpFeed] using hhole)
    hsm hnsm hfitB hfold
  have hOn := mul_up_after b dst first second xs ys n moves bench peakS cOps m ctrl mx script
    hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hops hop0 hfops hbl hF hHome hHF hArr
    hS hHomeS hHS hYs h7 hne hn0 hn hlenx hleny hf hmoves hpeakS hspan hxsT hfi hfm
  rw [hOn]
  let sch := school n xs ys (List.replicate bench 0) false
  let mvW := moves + schoolMoves xs ys n n
  let strip := embed (List.replicate bench 0)
  let bFeed := bumpOp feed 0 cOps hops
  let bPrep := mulPrep bFeed ((dst : Nat) : Int) strip second peakS hS hHomeS
  let bW := withMoves bPrep (Int.ofNat mvW)
  have hprep : mulPrep { bFeed with sudo_5Board_9marker_on := true }
      ((dst : Nat) : Int) strip second peakS
      (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hS)
      (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hHomeS) =
      markerOn bPrep := by
    simpa [bFeed, markerOn_def] using
      mulPrep_markerOn bFeed ((dst : Nat) : Int) strip second peakS hS hHomeS
        (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hS)
        (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hHomeS)
  have hmove : withMoves (mulPrep { bFeed with sudo_5Board_9marker_on := true }
      ((dst : Nat) : Int) strip second peakS
      (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hS)
      (by simpa [bFeed, bumpOp, feed, markerUpFeed] using hHomeS)) (Int.ofNat mvW) =
      markerOn bW := by
    rw [hprep, withMoves_markerOn]
  rw [hmove]
  have hflagW : bW.sudo_5Board_9marker_on = false := by
    simp [bW, bPrep, mulPrep_marker, bFeed, bumpOp, feed, markerUpFeed]
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length xs ys (List.replicate bench 0) false n
  have hfit : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have hnW : bW.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hn, ofNat_eq_natCast]
  have hwW : bW.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hw]
  have hhW : bW.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hh]
  have hrW : bW.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hr]
  have hkW : bW.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hk]
  have hblW : bW.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bW, bPrep, mulPrep_tier, bFeed, bumpOp, feed, markerUpFeed, hbl]
  have hmW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvW := by simp [bW]
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bW, bPrep, mulPrep_hole, bFeed, bumpOp, feed, markerUpFeed, hhole]
  have hpeakW : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bW, bPrep, mulPrep_peak, bFeed, bumpOp, feed, markerUpFeed, hpeak]
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by
    simpa [bW, bPrep, mulPrep_held_size, bFeed, bumpOp, feed, markerUpFeed] using h7
  have htri : allTritList sch := by
    simpa [sch] using school_trits xs ys (List.replicate bench 0) false n (replicate_trits _)
      (fun i hi => by
        rw [List.length_replicate]
        have : i + (n - 1) ≤ 2 * (n - 1) := by omega
        exact Nat.lt_of_le_of_lt this hspan)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hposB : 0 < bench := by omega
  have hfitF : FitsLen (mvW + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by
      have := schoolMoves_bound xs ys n
      omega)
  rw [mulAfter_flag bW sch w h r n k mvW hole bench peak hflagW hfit hwW hhW hrW hnW hkW hblW
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hposB]
  have hAfter : mulAfter (Int.ofNat 0, (bW, embed sch)) =
      .ok (mulNoOffBoard feed dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS) := by
    simpa [bW, bPrep, bFeed, strip, sch, mvW, feed] using hOff.symm.trans hCard
  rw [hAfter]
  simp only [ok_bind, pure_eq_ok]

end EcbsLink2.Link2
