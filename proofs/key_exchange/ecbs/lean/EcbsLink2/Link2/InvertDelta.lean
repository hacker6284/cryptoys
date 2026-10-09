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

theorem natCast_inj {a b : Nat} (h : (a : Int) = (b : Int)) : a = b :=
  Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)

/-- `place` raises peak against the held-count of homes `0 .. 6`, at most seven. -/
theorem place_peak_delta (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak
        (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7)) := by
  unfold placeBoard raisedPeak
  dsimp only
  split
  · next hlt => simp [hlt, ofNat_eq_natCast]
  · next hnk =>
      simp [hnk]
      rw [hpeak]

/-- Every peg's peak stays at most `max(P, 7)` when the copy that starts the
    loop is already under that cap. The bound is the one stored on `LivePeg`. -/
theorem pegPack_peak_le (c : PegCtx) (k : Nat) (h0 : 0 < k) (hle : k ≤ c.m)
    (P : Nat) (hP : c.peak0 ≤ max P 7) :
    (pegPack c k h0 hle).peak ≤ max P 7 :=
  peak_carry P c.peak0 _ hP (pegPack c k h0 hle).hpeakB

/-- One `raisedPeak` against at most seven homes, then another, stays under the same cap. -/
theorem peak_two_raise (P pk : Nat) (h : pk ≤ max P 7) (occ1 occ2 : Nat)
    (h1 : occ1 ≤ 7) (h2 : occ2 ≤ 7) :
    raisedPeak (raisedPeak pk occ1) occ2 ≤ max P 7 := by
  exact peak_carry P _ _ (peak_carry P pk _ h (raisedPeak_carry pk occ1 h1))
    (raisedPeak_carry _ occ2 h2)

/-- The cube-peg loop, read off the rung entry. The copy adds the gap's nonzero
    count. The `m` pegs add at most one peg charge and `2 · n` slides each, and
    they write ops only at slot 1. Peak stays under `max` of the entry peak and 7. -/
theorem peg_entry_pack
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (mv sl pk : Nat) (c : PegCtx),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
      c.moves0 = mv + pegCount s.gap ∧
      c.slides0 = sl ∧
      c.m = s.tally ∧
      c.n = s.n ∧
      c.bench = s.benchlen ∧
      c.src = 6 ∧
      c.g = s.gap ∧
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      c.b0 = placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk ∧
      c.peak0 ≤ max pk 7 ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((pegPack c c.m c.hm (Nat.le_refl _)).moves : Int) ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).moves ≤
        mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_6slides =
        ((pegPack c c.m c.hm (Nat.le_refl _)).slides : Int) ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).slides ≤
        sl + s.tally * (2 * s.n) ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).peak ≤ max pk 7 ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_4peak =
        ((pegPack c c.m c.hm (Nat.le_refl _)).peak : Int) ∧
      (pegPack c c.m c.hm (Nat.le_refl _)).b.sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
          (Int.ofNat (c.cOps0 + c.m)) := by
  obtain ⟨mv, pk, sl, c, hrest⟩ := peg_of_shape h hm hT hhome
  obtain ⟨hmv, hpk, hsl, _hmvLe, _hslLe, hb0, _hcopy, hsrc, hg, hmEq, _hrow,
      hn, _hk, hbch, hmv0, hsl0, _ht0, _hctrl0, _hhigh, _hcontrol, _hlen0, _hmax0⟩ := hrest
  have hOps0 : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hb0]
    exact place_ops_delta b 6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hpkB := place_peak_delta b 6 h.shape.spareH h.shape.spareD s.gap mv pk hpk
  have hpkEq : (c.peak0 : Int) =
      Int.ofNat (raisedPeak pk
        (countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7)) := by
    rw [← c.hpeak0, hb0]
    exact hpkB
  have hpk0 : c.peak0 =
      raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7) :=
    natCast_inj (hpkEq.trans (ofNat_eq_natCast _))
  have hpkLe : c.peak0 ≤ max pk 7 := by
    rw [hpk0]
    exact raisedPeak_carry pk _ (countHeld_seven _)
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hmovRhs : c.moves0 + c.m * pegCharge c.n c.bench =
      mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen := by
    rw [hmv0, hmEq, hn, hbch]
  have hmov : d.moves ≤ mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen :=
    Nat.le_trans d.hmovB (Nat.le_of_eq hmovRhs)
  have hsldRhs : c.slides0 + c.m * (2 * c.n) = sl + s.tally * (2 * s.n) := by
    rw [hsl0, hmEq, hn]
  have hsld : d.slides ≤ sl + s.tally * (2 * s.n) :=
    Nat.le_trans d.hsldB (Nat.le_of_eq hsldRhs)
  have hpeak : d.peak ≤ max pk 7 := pegPack_peak_le c c.m c.hm (Nat.le_refl _) pk hpkLe
  refine ⟨mv, sl, pk, c, hmv, hsl, hpk, hmv0, hsl0, hmEq, hn, hbch, hsrc, hg,
    hOps0, hb0, hpkLe, ?_, hmov, ?_, hsld, hpeak, ?_, ?_⟩
  · simpa [d] using d.hmoves
  · simpa [d] using d.hslides
  · simpa [d] using d.hpeak
  · simpa [d] using pegPack_ops_eq c c.m c.hm (Nat.le_refl _)

/-- Copy plus the cube-peg loop is one `RungDelta`. Later sub-steps only add
    more of the same charge, so this is the prefix of the full rung. -/
theorem rung_delta_peg
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ c : PegCtx,
      c.m = s.tally ∧
      RungDelta b (pegPack c c.m c.hm (Nat.le_refl _)).b base s.tally := by
  obtain ⟨mv, sl, pk, c, hmv, hsl, hpk, _hmv0, _hsl0, hmEq, hn, hbch, _hsrc, _hg,
      hOps0, _hb0, _hpkLe, hmoves, hmovN, hslides, hsldN, hpeakN, hpeak, hOps⟩ :=
    peg_entry_pack h hm hT hhome
  have hnB : s.n = base.n := h.hn
  have hbB : s.benchlen = base.bench := h.hbench
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, hnB] at h1
    exact h1
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hsize : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
          (Int.ofNat (c.cOps0 + c.m)) from hOps, Array.size_set, hOps0]
  refine ⟨c, hmEq, ?_⟩
  refine
    { moves := ?_
      slides := ?_
      opsSize := hsize
      ops := ?_
      peak := ?_ }
  · refine ⟨mv, d.moves, hmv, ?_, ?_⟩
    · simpa [d] using hmoves
    · have hmovN' : d.moves ≤
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
        rw [hnB, hbB] at hmovN
        exact hmovN
      have hpiece : pegCount s.gap + s.tally * pegCharge base.n base.bench ≤
          rungCharge base.n base.bench s.tally := by
        have hwhite := charge_final_white base.n base.bench s.tally
        exact Nat.le_trans (Nat.add_le_add hpegN (Nat.le_refl _))
          (Nat.le_trans (Nat.le_add_right _ (mulCharge base.n base.bench))
            (Nat.le_trans (Nat.le_add_right _ base.n) hwhite))
      have hflat : mv + pegCount s.gap + s.tally * pegCharge base.n base.bench =
          mv + (pegCount s.gap + s.tally * pegCharge base.n base.bench) := by
        rw [Nat.add_assoc]
      exact Nat.le_trans (Nat.le_trans hmovN' (Nat.le_of_eq hflat))
        (Nat.add_le_add_left hpiece mv)
  · refine ⟨sl, d.slides, hsl, ?_, ?_⟩
    · simpa [d] using hslides
    · have hsldN' : d.slides ≤ sl + s.tally * (2 * base.n) := by
        rw [hnB] at hsldN
        exact hsldN
      have hpiece : s.tally * (2 * base.n) ≤ rungSlideCharge base.n s.tally := by
        unfold rungSlideCharge
        have hmul : s.tally * (2 * base.n) ≤ (s.tally + 3) * (2 * base.n) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        exact hmul
      exact Nat.le_trans hsldN' (Nat.add_le_add_left hpiece sl)
  · intro i hi
    have hsz1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hOps0]; exact c.hops0
    have hArr : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hsz1⟩
          (Int.ofNat (c.cOps0 + c.m)) := by
      have htr := ops_set_transport hOps0 1 c.hops0 hsz1
        (Int.ofNat (c.cOps0 + c.m)) (Int.ofNat (c.cOps0 + c.m)) rfl
      exact hOps.trans htr
    obtain ⟨c0, hc0, _⟩ := h.ops i hi
    have hget {a c : Array Int} (eq : a = c) (j : Nat) (ha : j < a.size) :
        a[j] = c[j]'(eq ▸ ha) := by subst eq; rfl
    have hi' : i < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsize]; exact hi
    by_cases hie : i = 1
    · have hslot : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (c.cOps0 : Int) := by
        have h1 := hget hOps0 1 (by rw [hOps0]; exact hsz1)
        exact h1.symm.trans c.hop10
      have hc0at : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (c0 : Int) := by
        subst hie
        exact hc0
      have hcEq : c0 = c.cOps0 := natCast_inj (hc0at.symm.trans hslot)
      refine ⟨c0, c.cOps0 + c.m, hc0, ?_, ?_⟩
      · rw [hget hArr i hi', Array.getElem_set, if_pos hie.symm, ofNat_eq_natCast]
      · rw [hcEq, hmEq]
        have hm3 : s.tally ≤ base.mMax + 3 := Nat.le_trans hT (Nat.le_add_right _ _)
        omega
    · refine ⟨c0, c0, hc0, ?_, Nat.le_add_right _ _⟩
      rw [hget hArr i hi', Array.getElem_set, if_neg (Ne.symm hie), hc0]
  · refine ⟨pk, d.peak, hpk, ?_, hpeakN⟩
    simpa [d] using hpeak

/-- Gap mul then clear, on the peg-loop board. Moves gain one mul charge and at
    most `n`. Slides gain at most `2 · n`. Ops slot 0 grows by one. This is the
    white rung; a red rung only adds another cube and another mul on top. -/
theorem rung_delta_clear
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (c : PegCtx) (bClear : Ecbs.Board),
      c.m = s.tally ∧
      RungDelta b bClear base s.tally := by
  obtain ⟨mv, sl, pk, c, hmv, hsl, hpk, _hmv0, _hsl0, hmEq, hn, hbch, hsrc, hg,
      hOps0, hb0, _hpkLe, _hmoves, hmovN, _hslides, hsldN, hpeakN, _hpeak, hOps⟩ :=
    peg_entry_pack h hm hT hhome
  have hnB : s.n = base.n := h.hn
  have hbB : s.benchlen = base.bench := h.hbench
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hops0 : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) d.hops
  have hH6 : 6 < d.b.sudo_5Board_4home.size := by
    rw [show (6 : Nat) = c.src from hsrc.symm]
    exact d.hH
  have hD6 : 6 < d.b.sudo_5Board_4held.size := by
    rw [show (6 : Nat) = c.src from hsrc.symm]
    exact d.hD
  have hsz0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [← hOps0]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) c.hops0
  obtain ⟨c0, hc0, _⟩ := h.ops 0 hsz0
  have hget {a c : Array Int} (eq : a = c) (j : Nat) (ha : j < a.size) :
      a[j] = c[j]'(eq ▸ ha) := by subst eq; rfl
  have hArr : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, by rw [← hOps0]; exact c.hops0⟩
        (Int.ofNat (c.cOps0 + c.m)) := by
    have hsz1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hOps0]; exact c.hops0
    exact (hOps.trans (ops_set_transport hOps0 1 c.hops0 hsz1
      (Int.ofNat (c.cOps0 + c.m)) (Int.ofNat (c.cOps0 + c.m)) rfl))
  have hslot0 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (c0 : Int) := by
    have h0lt : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hops0
    rw [hget hArr 0 h0lt, Array.getElem_set, if_neg (by decide : (1 : Nat) ≠ 0)]
    exact hc0
  let bMul := mulNoLiveBoard d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
    d.peak d.peakS c0 hH6 hD6 hops0
  have hmvM : bMul.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mulMovesNo (d.moves + 2 * pegCount (d.xs.take c.n)) c.g (d.xs.take c.n)
        c.n c.k c.bench) := by
    simpa [bMul] using
      mul_live_moves d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hmvMle : mulMovesNo (d.moves + 2 * pegCount (d.xs.take c.n)) c.g (d.xs.take c.n)
      c.n c.k c.bench ≤ d.moves + mulCharge c.n c.bench := by
    have hstep := mul_moves_delta d.moves c.n c.k c.bench c.g d.xs c.n_le
    exact hstep
  have hslM : bMul.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (d.slides + 2 * pegCount (d.xs.take c.n)) := by
    simpa [bMul] using
      mul_live_slides d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hslMle : d.slides + 2 * pegCount (d.xs.take c.n) ≤ d.slides + 2 * c.n := by
    have hp := pegCount_take_le d.xs c.n
    omega
  obtain ⟨_hb, _hp, _hi, _hl, _ht0, _hph, _hhi, hhomeSz, hheldSz⟩ :=
    pegPack_board c c.m c.hm (Nat.le_refl _)
  have hplaceH : c.b0.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    rw [hb0]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.size_set]
  have hplaceD : c.b0.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
    rw [hb0]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.size_set]
  have h5H : 5 < bMul.sudo_5Board_4home.size := by
    have hsz : bMul.sudo_5Board_4home.size = d.b.sudo_5Board_4home.size := by
      rw [show bMul.sudo_5Board_4home =
          d.b.sudo_5Board_4home.set ⟨6, hH6⟩ #[] from
        mul_live_home d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0, Array.size_set]
    rw [hsz, hhomeSz, hplaceH]
    exact h.inv.hG
  have h5D : 5 < bMul.sudo_5Board_4held.size := by
    have hsz : bMul.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [mul_live_held d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak, Array.size_set]
    rw [hsz, hheldSz, hplaceD]
    exact h.inv.hGs
  let mvM := mulMovesNo (d.moves + 2 * pegCount (d.xs.take c.n)) c.g (d.xs.take c.n)
    c.n c.k c.bench
  let bClear := clearHeldBoard bMul 5 c.g mvM h5H h5D
  have hmvC : bClear.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mvM + pegCount c.g) := by
    simpa [bClear, mvM] using clear_moves_delta bMul 5 c.g mvM h5H h5D
  have hpegG : pegCount c.g ≤ c.n := by
    rw [← c.hlenx]
    exact pegCount_le c.g
  have hslC : bClear.sudo_5Board_4cost.sudo_5Costs_6slides =
      bMul.sudo_5Board_4cost.sudo_5Costs_6slides := by
    simpa [bClear] using clear_slides_delta bMul 5 c.g mvM h5H h5D
  have hopsC : bClear.sudo_5Board_4cost.sudo_5Costs_3ops =
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simpa [bClear] using clear_ops_delta bMul 5 c.g mvM h5H h5D
  have hpkM : bMul.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
        (countHeld ((settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.set
          ⟨6, settle_held_lt d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak⟩ false) 7)) := by
    simpa [bMul, ofNat_eq_natCast] using
      mul_live_peak d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hpkC : bClear.sudo_5Board_4cost.sudo_5Costs_4peak =
      bMul.sudo_5Board_4cost.sudo_5Costs_4peak := by
    simp [bClear, clearHeldBoard]
  refine ⟨c, bClear, hmEq, ?_⟩
  refine
    { moves := ?_
      slides := ?_
      opsSize := ?_
      ops := ?_
      peak := ?_ }
  · refine ⟨mv, mvM + pegCount c.g, hmv, ?_, ?_⟩
    · rw [hmvC, ofNat_eq_natCast]
    · have h1 : mvM + pegCount c.g ≤ d.moves + mulCharge c.n c.bench + c.n := by
        have := Nat.add_le_add hmvMle hpegG
        simpa [mvM, Nat.add_assoc] using this
      have h2 : d.moves + mulCharge base.n base.bench + base.n ≤
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench +
            mulCharge base.n base.bench + base.n := by
        have hmov' : d.moves ≤ mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
          rw [hnB, hbB] at hmovN
          exact hmovN
        have hc : c.n = base.n := hn.trans hnB
        have hbench : c.bench = base.bench := hbch.trans hbB
        rw [hc, hbench] at h1
        exact Nat.add_le_add_right (Nat.add_le_add_right hmov' _) _
      have hpiece : pegCount s.gap + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n ≤ rungCharge base.n base.bench s.tally := by
        have hwhite := charge_final_white base.n base.bench s.tally
        have hpeg : pegCount s.gap ≤ base.n := by
          have hlen : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
          rw [h.shape.gapLen, hnB] at hlen
          exact hlen
        omega
      have hflat : mv + pegCount s.gap + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n =
          mv + (pegCount s.gap + s.tally * pegCharge base.n base.bench +
            mulCharge base.n base.bench + base.n) := by
        omega
      exact Nat.le_trans (by rw [hn.trans hnB, hbch.trans hbB] at h1; exact h1)
        (Nat.le_trans h2 (Nat.le_trans (Nat.le_of_eq hflat) (Nat.add_le_add_left hpiece mv)))
  · refine ⟨sl, d.slides + 2 * pegCount (d.xs.take c.n), hsl, ?_, ?_⟩
    · rw [hslC, hslM, ofNat_eq_natCast]
    · have h1 : d.slides + 2 * pegCount (d.xs.take c.n) ≤
          sl + s.tally * (2 * base.n) + 2 * base.n := by
        have hs : d.slides ≤ sl + s.tally * (2 * s.n) := hsldN
        have hc : c.n = base.n := hn.trans hnB
        have hsn : s.n = base.n := hnB
        have hsl' : d.slides + 2 * pegCount (d.xs.take c.n) ≤
            d.slides + 2 * base.n := by
          simpa [hc] using hslMle
        have hs' : d.slides ≤ sl + s.tally * (2 * base.n) := by
          simpa [hsn] using hs
        exact Nat.le_trans hsl' (Nat.add_le_add_right hs' _)
      have hpiece : s.tally * (2 * base.n) + 2 * base.n ≤ rungSlideCharge base.n s.tally := by
        unfold rungSlideCharge
        have hsplit : (s.tally + 3) * (2 * base.n) =
            s.tally * (2 * base.n) + 3 * (2 * base.n) := by rw [Nat.add_mul]
        omega
      have hflat : sl + s.tally * (2 * base.n) + 2 * base.n =
          sl + (s.tally * (2 * base.n) + 2 * base.n) := by rw [Nat.add_assoc]
      exact Nat.le_trans (Nat.le_trans h1 (Nat.le_of_eq hflat))
        (Nat.add_le_add_left hpiece sl)
  · rw [hopsC]
    have hmulOps := mul_live_ops d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS c0 hH6 hD6 hops0
    have hset := settle_ops d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak
    rw [hmulOps, Array.size_set, hset, hArr, Array.size_set]
  · intro i hi
    obtain ⟨cOld, hcOld, _⟩ := h.ops i hi
    have hmulOps := mul_live_ops d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS c0 hH6 hD6 hops0
    have hset := settle_ops d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak
    have hiC : i < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsC, hmulOps, Array.size_set, hset, hArr, Array.size_set]
      exact hi
    have hiM : i < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsC ▸ hiC
    have hMulHere := hget hmulOps i hiM
    have hiS : i <
        (settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hsz := congrArg Array.size hmulOps
      rw [Array.size_set] at hsz
      exact hsz ▸ hiM
    by_cases h0i : i = 0
    · have hcEq : cOld = c0 := by
        have hc0at : b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cOld : Int) := by
          subst h0i
          exact hcOld
        exact natCast_inj (hc0at.symm.trans hc0)
      refine ⟨cOld, c0 + 1, hcOld, ?_, by omega⟩
      · rw [hget hopsC i hiC, hMulHere, Array.getElem_set, if_pos h0i.symm, ofNat_eq_natCast]
    · by_cases h1i : i = 1
      · have hcEq : cOld = c.cOps0 := by
          have hsz1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [← hOps0]; exact c.hops0
          have hslot := (hget hOps0 1 (by rw [hOps0]; exact hsz1)).symm.trans c.hop10
          have hc1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOld : Int) := by
            subst h1i
            exact hcOld
          exact natCast_inj (hc1.symm.trans hslot)
        refine ⟨cOld, c.cOps0 + c.m, hcOld, ?_, ?_⟩
        · rw [hget hopsC i hiC, hMulHere, Array.getElem_set,
            if_neg (Ne.symm h0i)]
          rw [hget hset i hiS, hget hArr i (hset ▸ hiS),
            Array.getElem_set, if_pos h1i.symm, ofNat_eq_natCast]
        · rw [hcEq, hmEq]
          exact Nat.add_le_add_left (Nat.le_trans hT (Nat.le_add_right _ _)) _
      · refine ⟨cOld, cOld, hcOld, ?_, Nat.le_add_right _ _⟩
        rw [hget hopsC i hiC, hMulHere, Array.getElem_set, if_neg (Ne.symm h0i)]
        rw [hget hset i hiS, hget hArr i (hset ▸ hiS),
          Array.getElem_set, if_neg (Ne.symm h1i), hcOld]
  · have hpkLe : raisedPeak
        (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
        (countHeld ((settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.set
          ⟨6, settle_held_lt d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak⟩ false) 7) ≤
        max pk 7 :=
      peak_two_raise pk d.peak hpeakN _ _ (countHeld_seven _) (countHeld_seven _)
    refine ⟨pk, _, hpk, ?_, hpkLe⟩
    rw [hpkC, hpkM, ofNat_eq_natCast]

end EcbsLink2.Link2
