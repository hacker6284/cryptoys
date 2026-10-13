/-
  A live zero cell of `walk_chord`. The Frobenius hypothesis of `chordStep_cube`
  is `frobenius_affine_len`: the settle `FitsLen` checks follow from the home
  length, and the cell invariant carries that room.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkLoop
import EcbsLink2.Link2.FrobeniusRead
import EcbsLink2.Link2.ChordIf

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A live zero cell cubes the accumulator and stays live. -/
theorem walkStep_live_zero (n k bench : Nat) (x y : List Nat) :
    walkStep n k bench (x, y) true (x, y) 0 =
      some (true, (fieldCube n k bench x, fieldCube n k bench y)) := by
  unfold walkStep pointCube
  simp

/-- Room for `k` further Frobenius charges, after this cell spends one.
    `FitsLen n` is the home length. The settle checks are `FitsLen.of_le` of the
    move and slide conjuncts, because a length-`n` home has at most `n` pegs. -/
theorem cellFit_consume (n bench moves slides moves' slides' k : Nat)
    (hm : moves' ≤ moves + cubeCharge n bench)
    (hs : slides' ≤ slides + slideCharge n)
    (hMv : FitsLen (moves + (k + 1) * cubeCharge n bench))
    (hSl : FitsLen (slides + (k + 1) * slideCharge n)) :
    FitsLen (moves' + k * cubeCharge n bench) ∧
      FitsLen (slides' + k * slideCharge n) := by
  have hMc : (k + 1) * cubeCharge n bench = k * cubeCharge n bench + cubeCharge n bench := by
    rw [Nat.succ_mul]
  have hSc : (k + 1) * slideCharge n = k * slideCharge n + slideCharge n := by
    rw [Nat.succ_mul]
  refine ⟨?_, ?_⟩
  · apply FitsLen.of_le hMv
    rw [hMc]
    omega
  · apply FitsLen.of_le hSl
    rw [hSc]
    omega

/-- The counters the closing settle writes still fit when the cell invariant
    had room for this cube and `k` later ones. -/
theorem live_zero_fit
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (fuel : Nat)
    (hMv : FitsLen (moves + (fuel + 1) * cubeCharge n bench))
    (hSl : FitsLen (slides + (fuel + 1) * slideCharge n)) :
    let pegs := pegCount ((upLane n k bench y).take n)
    FitsLen (2 * pegs) ∧
      FitsLen (upMv2 a + 2 * pegs) ∧
      FitsLen (upSl a + 2 * pegs) ∧
      FitsLen ((upMv2 a + 2 * pegs) + fuel * cubeCharge n bench) ∧
      FitsLen ((upSl a + 2 * pegs) + fuel * slideCharge n) := by
  have hroomM : FitsLen (moves + cubeCharge n bench) := by
    apply FitsLen.of_le hMv
    have : moves + cubeCharge n bench ≤ moves + (fuel + 1) * cubeCharge n bench := by
      have hc : cubeCharge n bench ≤ (fuel + 1) * cubeCharge n bench :=
        Nat.le_mul_of_pos_left (cubeCharge n bench) (Nat.succ_pos fuel)
      omega
    exact this
  have hroomS : FitsLen (slides + slideCharge n) := by
    apply FitsLen.of_le hSl
    have : slides + slideCharge n ≤ slides + (fuel + 1) * slideCharge n := by
      have hc : slideCharge n ≤ (fuel + 1) * slideCharge n :=
        Nat.le_mul_of_pos_left (slideCharge n) (Nat.succ_pos fuel)
      omega
    exact this
  have hfit := up_settle_fit a hroomM hroomS
  obtain ⟨hpt, hOle, hSle⟩ := up_out_le a
  have hleft := cellFit_consume n bench moves slides
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (upSl a + 2 * pegCount ((upLane n k bench y).take n)) fuel hOle hSle hMv hSl
  exact ⟨hfit.1, hfit.2.1, hfit.2.2, hleft.1, hleft.2⟩

/-- A live zero cell. `marker_lift` then `frobenius_affine_len`. The three settle
    `FitsLen` checks are `live_zero_fit`, not hypotheses. -/
theorem chordStep_live_zero
    {b b0 : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (cells : List Nat) (i toN : Nat)
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hs1 : 1 < script) (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hnbL : n ≤ a.laneX.length) (hnb : n ≤ bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hmv : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n)
    (hsl : slides ≤ 2 * n)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = 0)
    (hfiti : FitsLen (i + 1)) :
    ∃ bF,
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bF, true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bF, true)))) ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube n k bench x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube n k bench y)) ∧
      walkStep n k bench (x, y) true (x, y) 0 =
        some (true, (fieldCube n k bench x, fieldCube n k bench y)) := by
  obtain ⟨bF, hfrob, hflag, hbench, hx0, hy1⟩ :=
    frobenius_affine_len a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit
      hnbL hnb hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm hmv hsl
  refine ⟨bF, ?_, hflag, hbench, hx0, hy1, walkStep_live_zero n k bench x y⟩
  exact chordStep_cube cells i toN b0 b bF hi hlen hz hml hfrob hfiti

/-- A live white or red cell whose chord add returns the reroll flag.
    The emitted step returns `(live, false)` and turns the marker off.
    It does not advance to the next cell. -/
theorem chordStep_reroll (cells : List Nat) (i toN c : Nat)
    (b0 b bF bA : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hc : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (false, bA)) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      .ok (SudoRt.Flow.ret ((true, false),
        { bA with sudo_5Board_9marker_on := false })) := by
  unfold chordStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold chordBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hc]
  have hge : decide (Int.ofNat c ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg c
  have hle : decide (Int.ofNat c ≤ (2 : Int)) = true := by
    rw [decide_eq_true_eq, show (2 : Int) = Int.ofNat 2 from rfl, ofNat_le_iff]
    exact hc2
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  simp only [if_true]
  rw [hfrob, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat c 0, decide_eq_false hc0]
  simp only [Bool.not_false, if_true, Bool.not_true]
  rw [if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [hadd, ok_bind]
  dsimp only [Prod.fst, Prod.snd]
  simp only [Bool.not_false, if_true]
  rw [pure_eq_ok, ok_bind]
  dsimp only
  rw [pure_eq_ok]

/-- A live white or red cell whose run is the zero home. The emitted step is
    the reroll return `(live, false)` with the marker turned off, and `walkStep`
    is `none`. -/
theorem chordStep_empty_run
    (cells : List Nat) (i toN c : Nat) (b0 b bF : Ecbs.Board)
    (n k bench moves peak cOps : Nat)
    (base acc : List Nat × List Nat)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc : c = 1 ∨ c = 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hszH : bF.sudo_5Board_4home.size = 8) (hszD : bF.sudo_5Board_4held.size = 8)
    (hops : 3 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : bF.sudo_5Board_4cost.sudo_5Costs_3ops[3]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hx : base.1.length = n)
    (htriB : allTritList base.1) (htriA : allTritList (fieldCube n k bench acc.1))
    (hn : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h2e : bF.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h0t : bF.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (h0a : bF.sudo_5Board_4home[0]'(by rw [hszH]; decide) =
      embed (fieldCube n k bench acc.1))
    (h3t : bF.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : bF.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed base.1)
    (hzero : fieldSub n base.1 (fieldCube n k bench acc.1) = List.replicate n 0)
    (hn0 : 0 < n) (hnb : n ≤ bench) :
    ∃ bA : Ecbs.Board,
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
        .ok (SudoRt.Flow.ret ((true, false),
          { bA with sudo_5Board_9marker_on := false })) ∧
      walkStep n k bench base true acc c = none := by
  have hc0 : c ≠ 0 := by cases hc <;> omega
  have hc2 : c ≤ 2 := by cases hc <;> omega
  have hy : (fieldCube n k bench acc.1).length = n := fieldCube_length n k bench acc.1 hnb
  obtain ⟨bA, hadd, _, _, _, _, _, _⟩ :=
    chord_add_empty bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int))
      base.1 (fieldCube n k bench acc.1) n moves peak cOps
      hszH hszD hops hop hfops hx hy hn0 htriB htriA hn hmoves hpeak hfit
      h2e h0t h0a h3t h3a hzero
  refine ⟨bA, ?_, ?_⟩
  · exact chordStep_reroll cells i toN c b0 b bF bA hi hlen hcAt hc0 hc2 hml hfrob hadd
  · exact walkStep_empty_run n k bench base acc c hc hzero hn0 hnb

end EcbsLink2.Link2
