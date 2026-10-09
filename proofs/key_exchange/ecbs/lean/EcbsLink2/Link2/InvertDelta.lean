/-
  Relative counter changes for one climb rung. Each sub-step states how much
  it adds to the move counter, the slide counter, and each ops slot. The sum of
  those amounts is at most `rungCharge` / `rungSlideCharge` / `rungOpCharge`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves added by copying a length-`n` home: at most `n` nonzero pegs. -/
def copyMoves (n : Nat) : Nat := n

/-- Moves added by `m` cube-pegs. -/
def pegMoves (n bench m : Nat) : Nat := m * pegCharge n bench

/-- Moves added by one live nocopy mul. -/
def mulStepMoves (n bench : Nat) : Nat := mulCharge n bench

/-- Moves added by clearing a length-`n` home. -/
def clearMoves (n : Nat) : Nat := n

/-- Slides added by one live cube or one live mul: two per nonzero peg, at most `2 · n`. -/
def liveSlides (n : Nat) : Nat := 2 * n

theorem copy_moves_le (xs : List Nat) (n : Nat) (hlen : xs.length = n) :
    pegCount xs ≤ copyMoves n := by
  rw [← hlen]
  exact pegCount_le xs

theorem place_moves_delta (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_slides_delta (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_ops_delta (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem clear_moves_delta (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount xs) := rfl

theorem clear_slides_delta (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := rfl

theorem clear_ops_delta (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem peg_loop_moves (c : PegCtx) :
    (pegPack c c.m c.hm (Nat.le_refl _)).moves ≤
      c.moves0 + pegMoves c.n c.bench c.m :=
  (pegPack c c.m c.hm (Nat.le_refl _)).hmovB

theorem peg_loop_slides (c : PegCtx) :
    (pegPack c c.m c.hm (Nat.le_refl _)).slides ≤
      c.slides0 + c.m * (2 * c.n) :=
  (pegPack c c.m c.hm (Nat.le_refl _)).hsldB

theorem peg_loop_op1 (c : PegCtx) :
    (pegPack c c.m c.hm (Nat.le_refl _)).cOps = c.cOps0 + c.m :=
  (pegPack c c.m c.hm (Nat.le_refl _)).hcOps

theorem cube_moves_delta (moves : Nat) (xs : List Nat) (n k bench : Nat) :
    cubeMoves (moves + 2 * pegCount (xs.take n)) (xs.take n) n k bench ≤
      moves + pegCharge n bench :=
  liveCubeMoves_le moves xs n k bench

theorem cube_slides_delta (slides n : Nat) (ys : List Nat) (hlen : ys.length ≤ n) :
    slides + 2 * pegCount ys ≤ slides + liveSlides n := by
  unfold liveSlides
  have hp := pegCount_le ys
  omega

theorem mul_moves_delta (moves n k bench : Nat) (xs ys : List Nat) (hn : n ≤ bench) :
    mulMovesNo (moves + 2 * pegCount (ys.take n)) xs (ys.take n) n k bench ≤
      moves + mulStepMoves n bench := by
  unfold mulStepMoves
  exact Nat.le_trans (mulMovesNo_bound moves n k bench xs ys hn)
    (mulCharge_ge n bench moves xs ys k hn (pegCount_take_le ys n))

/-- A live cube writes ops slot 1 and leaves every other slot alone. -/
theorem cube_live_ops_ne (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (j : Nat) (hne : j ≠ 1) (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops[j]'(by
        rw [cube_live_ops b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
          Array.size_set]; exact hj) =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have hOps := cube_live_ops b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hlt : j <
      (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOps, Array.size_set]; exact hj
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget hOps j hlt, Array.getElem_set, if_neg (Ne.symm hne)]

/-- A live nocopy mul writes ops slot 0 and leaves every other slot alone. -/
theorem mul_live_ops_ne (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (j : Nat) (hne : j ≠ 0) (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops[j]'(by
        have h := mul_live_ops b dst second xs ys n k moves slides hole bench peak peakS cOps
          hH hD hops
        rw [h, Array.size_set, settle_ops b second hH hD ys n moves slides peak]; exact hj) =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have h := mul_live_ops b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops
  have hsz : j <
      (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [h, Array.size_set, settle_ops b second hH hD ys n moves slides peak]; exact hj
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget h j hsz, Array.getElem_set, if_neg (Ne.symm hne)]
  have hs := settle_ops b second hH hD ys n moves slides peak
  have hszS : j < (settleBoard b second hH hD ys n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [h, Array.size_set] at hsz
    exact hsz
  exact hget hs j hszS

theorem pegStep_ops (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4cost.sudo_5Costs_3ops =
      bC.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem pegStep_moves (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4cost.sudo_5Costs_5moves =
      bC.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

theorem pegStep_slides (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4cost.sudo_5Costs_6slides =
      bC.sudo_5Board_4cost.sudo_5Costs_6slides := rfl

/-- Doubling changes the tally fields and leaves moves, slides, and ops alone. -/
theorem withTally_counters (b : Ecbs.Board) (row : Array Int) (len ctrl high tmax : Int) :
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    (withTally b row len ctrl high tmax).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp [withTally]

/-- The extra white peg changes the tally fields and leaves moves, slides, and ops alone. -/
theorem add_one_counters (b : Ecbs.Board) (i : Nat) (hi : i < b.sudo_5Board_3row.size)
    (len high ctrl tmax : Int) :
    let b' := { b with
      sudo_5Board_3row := b.sudo_5Board_3row.set ⟨i, hi⟩ (1 : Int)
      sudo_5Board_9tally_len := len
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_15control_highest := high
        sudo_5Costs_4ctrl := ctrl
        sudo_5Costs_9tally_max := tmax } }
    b'.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
    b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp

/-- Every ops slot stays a natural when a step replaces the array by one that
    agrees with it off slots 0 and 1 and writes a natural into those two. -/
theorem opsNat_set (ops : Array Int) (slot : Nat) (hslot : slot < ops.size) (v : Nat)
    (h : ∀ i (hi : i < ops.size), ∃ c : Nat, ops[i] = (c : Int))
    (i : Nat) (hi : i < (ops.set ⟨slot, hslot⟩ (Int.ofNat v)).size) :
    ∃ c : Nat, (ops.set ⟨slot, hslot⟩ (Int.ofNat v))[i] = (c : Int) := by
  rw [Array.size_set] at hi
  by_cases hie : i = slot
  · refine ⟨v, ?_⟩
    simp [Array.getElem_set, hie, ofNat_eq_natCast]
  · obtain ⟨c, hc⟩ := h i hi
    refine ⟨c, ?_⟩
    rw [Array.getElem_set, if_neg (Ne.symm hie), hc]

/-- Copy, the `m` cube-pegs, the gap mul, the clear, the red cube, and the red
    mul. Doubling and `tally_add_one` add no moves. The sum is at most one
    `rungCharge`. -/
theorem rung_move_sum (n bench m : Nat) :
    copyMoves n + pegMoves n bench m + mulStepMoves n bench + clearMoves n +
        pegCharge n bench + mulStepMoves n bench ≤
      rungCharge n bench m := by
  simpa [copyMoves, pegMoves, mulStepMoves, clearMoves] using charge_final_red n bench m

/-- Slides: `2 · n` for each cube-peg, the gap mul, the red cube, and the red mul. -/
theorem rung_slide_sum (n m : Nat) :
    m * liveSlides n + liveSlides n + liveSlides n + liveSlides n ≤
      rungSlideCharge n m := by
  simpa [liveSlides] using slide_open_red n m

/-- Ops: the cube slot grows by `m + 1`, the mul slot by `2`. Every other slot
    is unchanged, so the largest growth is `m + 3`. -/
theorem rung_op_sum (m : Nat) : m + 1 + 2 ≤ rungOpCharge m :=
  op_open_red m

/-- Park writes the control row and the counter. Moves, slides, and ops stay. -/
theorem park_counters (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp [parkKeepBoard]

/-! The i64 fits of a non-final double are not free hypotheses.
    `fitControl` is the tier's `fits_control`. `fitCtrl` bounds the counter by
    one `rungCtrl` step per rung. Both hold for the four shipped tiers with
    `ctrl0` equal to the control-row length and `mMax` equal to that length
    (at least the row-room cap). -/

theorem demo_control_fit : FitsLen (Spec.demo.control + 1) :=
  fits_of demo_board.fits_control

theorem toy_control_fit : FitsLen (Spec.toy.control + 1) :=
  fits_of toy_board.fits_control

theorem hobby_control_fit : FitsLen (Spec.hobby.control + 1) :=
  fits_of hobby_board.fits_control

theorem serious_control_fit : FitsLen (Spec.serious.control + 1) :=
  fits_of serious_board.fits_control

theorem demo_ctrl_fit :
    FitsLen (Spec.demo.control +
      ((rungList (Spec.demo.n - 1)).length + 1) * (3 * Spec.demo.control + 5)) := by
  unfold FitsLen i64MaxNat
  decide!

theorem toy_ctrl_fit :
    FitsLen (Spec.toy.control +
      ((rungList (Spec.toy.n - 1)).length + 1) * (3 * Spec.toy.control + 5)) := by
  unfold FitsLen i64MaxNat
  decide!

theorem hobby_ctrl_fit :
    FitsLen (Spec.hobby.control +
      ((rungList (Spec.hobby.n - 1)).length + 1) * (3 * Spec.hobby.control + 5)) := by
  unfold FitsLen i64MaxNat
  decide!

set_option maxRecDepth 4000 in
theorem serious_ctrl_fit :
    FitsLen (Spec.serious.control +
      ((rungList (Spec.serious.n - 1)).length + 1) * (3 * Spec.serious.control + 5)) := by
  unfold FitsLen i64MaxNat
  decide!

end EcbsLink2.Link2
