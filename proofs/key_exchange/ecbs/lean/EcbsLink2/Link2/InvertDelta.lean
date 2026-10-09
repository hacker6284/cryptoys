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

/-- Setting the same ops index twice keeps the later value. -/
theorem ops_set_set (a : Array Int) (i : Nat) (h : i < a.size) (u v : Int)
    (h' : i < (a.set ⟨i, h⟩ u).size) :
    (a.set ⟨i, h⟩ u).set ⟨i, h'⟩ v = a.set ⟨i, h⟩ v := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j hj1 hj2
    simp only [Array.getElem_set]
    split <;> rfl

/-- A one-slot write transports along an array equality. -/
theorem ops_set_transport {a b : Array Int} (h : a = b) (i : Nat)
    (ha : i < a.size) (hb : i < b.size) (v v' : Int) (hv : v = v') :
    a.set ⟨i, ha⟩ v = b.set ⟨i, hb⟩ v' := by
  subst h
  subst hv
  rfl

/-- The first peg is the bench-off cube: ops slot 1 becomes the incoming count plus one. -/
theorem offPeg_ops (c : PegCtx) :
    (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
        (Int.ofNat (c.cOps0 + 1)) := by
  unfold offPeg pegStep
  rw [cube_off_ops]

/-- Each later peg is the live cube of the board the previous peg left.
    Ops slot 1 becomes that board's cube count plus one. -/
theorem livePeg_ops (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m) :
    (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops =
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, d.hops⟩
        (Int.ofNat (d.cOps + 1)) := by
  unfold livePegBoard pegStep
  rw [cube_live_ops]

/-- After `k` cube-pegs the ops array is the input with slot 1 replaced by
    `cOps0 + k`. The first peg uses `cube_off_ops`; every later peg uses
    `cube_live_ops` on the board the previous peg left. -/
theorem pegPack_ops_eq (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m) :
    (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
        (Int.ofNat (c.cOps0 + k)) := by
  revert h0 hle
  induction k with
  | zero =>
    intro h0
    exact absurd h0 (Nat.not_lt_zero 0)
  | succ k ih =>
    intro h0 hle
    by_cases hk : k = 0
    · subst hk
      have hp : pegPack c 1 h0 hle = pegFromOff c := rfl
      rw [hp, pegFromOff]
      exact offPeg_ops c
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hle1 : j + 1 ≤ c.m := Nat.le_of_succ_le hle
      have hiLt : j + 1 < c.m := Nat.lt_of_succ_le hle
      let d := pegPack c (j + 1) (Nat.succ_pos j) hle1
      have hp : pegPack c (Nat.succ (j + 1)) h0 hle = pegNext c d hiLt := rfl
      rw [hp]
      rw [show (pegNext c d hiLt).b = livePegBoard c d hiLt from rfl]
      rw [livePeg_ops c d hiLt]
      have hih := ih (Nat.succ_pos j) hle1
      have hv : Int.ofNat (d.cOps + 1) = Int.ofNat (c.cOps0 + Nat.succ (j + 1)) := by
        have hc := d.hcOps
        apply congrArg Int.ofNat
        omega
      have hb : 1 <
          (c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
            (Int.ofNat (c.cOps0 + (j + 1)))).size := by
        rw [Array.size_set]
        exact c.hops0
      rw [ops_set_transport hih 1 d.hops hb (Int.ofNat (d.cOps + 1))
        (Int.ofNat (c.cOps0 + Nat.succ (j + 1))) hv]
      exact ops_set_set c.b0.sudo_5Board_4cost.sudo_5Costs_3ops 1 c.hops0
        (Int.ofNat (c.cOps0 + (j + 1)))
        (Int.ofNat (c.cOps0 + Nat.succ (j + 1))) hb

/-- A slot other than 1 is the value the peg loop was given. -/
theorem pegPack_ops_ne (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m)
    (j : Nat) (hne : j ≠ 1)
    (hj : j < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'(by
      rw [pegPack_ops_eq c k h0 hle, Array.size_set]; exact hj) =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have hOps := pegPack_ops_eq c k h0 hle
  have hlt : j < (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOps, Array.size_set]; exact hj
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget hOps j hlt, Array.getElem_set, if_neg (Ne.symm hne)]

/-- Ops slot 1 is the incoming cube count plus the number of pegs. -/
theorem pegPack_ops_one (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m) :
    (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'
      ((pegPack c k h0 hle).hops) = ((c.cOps0 + k : Nat) : Int) := by
  have hOps := pegPack_ops_eq c k h0 hle
  have hlt : 1 < (pegPack c k h0 hle).b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    (pegPack c k h0 hle).hops
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget hOps 1 hlt, Array.getElem_set, if_pos rfl, ofNat_eq_natCast]

end EcbsLink2.Link2
