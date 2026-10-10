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

/-- A live cube writes `(cOps + 1)` into ops slot 1. -/
theorem cube_live_ops_one (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by
        rw [cube_live_ops b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
          Array.size_set]; exact hops) =
      ((cOps + 1 : Nat) : Int) := by
  have hOps := cube_live_ops b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hlt : 1 <
      (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOps, Array.size_set]; exact hops
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget hOps 1 hlt, Array.getElem_set, if_pos rfl, ofNat_eq_natCast]

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

/-- A live nocopy mul writes `(cOps + 1)` into ops slot 0. -/
theorem mul_live_ops_zero (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
        have h := mul_live_ops b dst second xs ys n k moves slides hole bench peak peakS cOps
          hH hD hops
        rw [h, Array.size_set, settle_ops b second hH hD ys n moves slides peak]; exact hops) =
      ((cOps + 1 : Nat) : Int) := by
  have h := mul_live_ops b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops
  have hsz : 0 <
      (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [h, Array.size_set, settle_ops b second hH hD ys n moves slides peak]; exact hops
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  rw [hget h 0 hsz, Array.getElem_set, if_pos rfl, ofNat_eq_natCast]

/-- The hole a live nocopy mul records. The body writes it and does not read the board. -/
theorem gap_mul_hole (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx
        (school n xs (ys.take n) (List.replicate bench 0) false))) := by
  unfold mulNoLiveBoard mulNoOffBoard
  rfl

/-- A live nocopy mul turns the bench on and aims it at `dst`. -/
theorem gap_mul_aimed (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_on = true ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_to =
      (dst : Int) := by
  unfold mulNoLiveBoard mulNoOffBoard
  exact ⟨rfl, rfl⟩

/-- Slides of the white piece plus the red cube and the red mul.
    Each `peg*` is a `pegCount` of some `take n`, hence at most `n`. -/
theorem red_slides_le (sl n m slides pegD pegG pegZ : Nat)
    (hs : slides ≤ sl + m * (2 * n))
    (hD : pegD ≤ n) (hG : pegG ≤ n) (hZ : pegZ ≤ n) :
    slides + 2 * pegD + 2 * pegG + 2 * pegZ ≤ sl + rungSlideCharge n m := by
  have hpiece := slide_open_red n m
  have h2D : 2 * pegD ≤ 2 * n := Nat.mul_le_mul_left _ hD
  have h2G : 2 * pegG ≤ 2 * n := Nat.mul_le_mul_left _ hG
  have h2Z : 2 * pegZ ≤ 2 * n := Nat.mul_le_mul_left _ hZ
  omega

/-- The cleared board is already within the white piece. One more peg charge and
    one more mul charge still fit in `rungCharge`. -/
theorem reassoc_le (mv n p q r a : Nat) (h : a ≤ mv + n + p + q + r) :
    a ≤ mv + (n + p + q + r) := by
  omega

theorem le_rung_piece (mv piece charge a : Nat) (h : a ≤ mv + piece) (hp : piece ≤ charge) :
    a ≤ mv + charge :=
  Nat.le_trans h (Nat.add_le_add_left hp mv)

theorem clear_move_fit (moves0 R done n bench m mMax mv mvC peg : Nat)
    (hT : m ≤ mMax) (hd : done + 1 ≤ R)
    (hmv : mv ≤ moves0 + done * rungCharge n bench mMax)
    (hC : mvC ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hp : peg ≤ n) :
    2 * peg ≤ moves0 + R * rungCharge n bench mMax ∧
    mvC + 2 * peg ≤ moves0 + R * rungCharge n bench mMax ∧
    mvC + 2 * peg + 2 * n ≤ moves0 + R * rungCharge n bench mMax ∧
    mvC + 2 * peg + 2 * n + 3 * (bench - n) ≤ moves0 + R * rungCharge n bench mMax := by
  have hwhite := charge_final_white n bench m
  have hre := reassoc_le mv n (m * pegCharge n bench) (mulCharge n bench) n mvC hC
  have hpiece := le_rung_piece mv _ _ mvC hre hwhite
  have hmono := rungCharge_mono n bench m mMax hT
  have hmax : mvC ≤ mv + rungCharge n bench mMax :=
    Nat.le_trans hpiece (Nat.add_le_add_left hmono mv)
  have hright := Nat.add_le_add_right hmv (rungCharge n bench mMax)
  have hjoin := Nat.le_trans hmax hright
  have hsucc : moves0 + done * rungCharge n bench mMax + rungCharge n bench mMax =
      moves0 + (done + 1) * rungCharge n bench mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hstep : mvC ≤ moves0 + (done + 1) * rungCharge n bench mMax := by
    rw [← hsucc]; exact hjoin
  have hmul := Nat.mul_le_mul_right (rungCharge n bench mMax) hd
  have hmvR : mvC ≤ moves0 + R * rungCharge n bench mMax :=
    Nat.le_trans hstep (Nat.add_le_add_left hmul moves0)
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have h4 : 2 * n + 2 * n = 4 * n := by
    rw [← Nat.mul_add, ← Nat.two_mul, ← Nat.mul_assoc]
  have hpeg : 2 * peg + 2 * n + 3 * (bench - n) ≤ pegCharge n bench := by
    unfold pegCharge
    exact Nat.add_le_add_right (Nat.le_trans (Nat.add_le_add_right h2 _) (Nat.le_of_eq h4)) _
  have hre2 := reassoc_le mvC (2 * peg) (2 * n) (3 * (bench - n)) 0
    (mvC + 2 * peg + 2 * n + 3 * (bench - n) + 0) (by
      rw [Nat.add_zero]
      exact Nat.le_refl _)
  have hbig : mvC + 2 * peg + 2 * n + 3 * (bench - n) ≤ mvC + pegCharge n bench := by
    have hzero : 2 * peg + 2 * n + 3 * (bench - n) + 0 = 2 * peg + 2 * n + 3 * (bench - n) :=
      Nat.add_zero _
    have hle := Nat.le_trans hre2 (Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq hzero) hpeg) mvC)
    simpa [Nat.add_zero] using hle
  have hadd := Nat.add_le_add_right hre (pegCharge n bench)
  have hdrop : n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench ≤
      rungCharge n bench m :=
    Nat.le_trans (Nat.le_add_right _ (mulCharge n bench)) (charge_final_red n bench m)
  have hEq : mv + (n + m * pegCharge n bench + mulCharge n bench + n) + pegCharge n bench =
      mv + (n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench) :=
    Nat.add_assoc _ _ _
  have hred : mvC + pegCharge n bench ≤ mv + rungCharge n bench m :=
    Nat.le_trans (Nat.le_trans hadd (Nat.le_of_eq hEq)) (Nat.add_le_add_left hdrop mv)
  have hcap : mvC + pegCharge n bench ≤ moves0 + R * rungCharge n bench mMax := by
    have h1 : mvC + pegCharge n bench ≤ mv + rungCharge n bench mMax :=
      Nat.le_trans hred (Nat.add_le_add_left hmono mv)
    have h2 := Nat.le_trans h1 (Nat.add_le_add_right hmv (rungCharge n bench mMax))
    have h2' : mvC + pegCharge n bench ≤ moves0 + (done + 1) * rungCharge n bench mMax := by
      rw [hsucc] at h2
      exact h2
    exact Nat.le_trans h2' (Nat.add_le_add_left hmul moves0)
  have hfold : mvC + 2 * peg + 2 * n + 3 * (bench - n) ≤ moves0 + R * rungCharge n bench mMax :=
    Nat.le_trans hbig hcap
  refine ⟨?_, ?_, ?_, hfold⟩
  · exact Nat.le_trans (Nat.le_add_left (2 * peg) mvC)
      (Nat.le_trans (Nat.le_add_right (mvC + 2 * peg) (2 * n))
        (Nat.le_trans (Nat.le_add_right (mvC + 2 * peg + 2 * n) (3 * (bench - n))) hfold))
  · exact Nat.le_trans (Nat.le_add_right (mvC + 2 * peg) (2 * n))
      (Nat.le_trans (Nat.le_add_right (mvC + 2 * peg + 2 * n) (3 * (bench - n))) hfold)
  · exact Nat.le_trans (Nat.le_add_right (mvC + 2 * peg + 2 * n) (3 * (bench - n))) hfold

theorem clear_slide_fit (slides0 R done n m mMax sl slC peg : Nat)
    (hT : m ≤ mMax) (hd : done + 1 ≤ R)
    (hsl : sl ≤ slides0 + done * rungSlideCharge n mMax)
    (hC : slC ≤ sl + m * (2 * n) + 2 * n) (hp : peg ≤ n) :
    slC + 2 * peg ≤ slides0 + R * rungSlideCharge n mMax := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have hsum : slC + 2 * peg ≤ sl + m * (2 * n) + 2 * n + 2 * n :=
    Nat.add_le_add hC h2
  have hpiece : m * (2 * n) + 2 * n + 2 * n ≤ rungSlideCharge n m :=
    Nat.le_trans (Nat.le_add_right _ _) (slide_open_red n m)
  have hmono := rungSlideCharge_mono n m mMax hT
  have hslR : sl + rungSlideCharge n mMax ≤
      slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax :=
    Nat.add_le_add_right hsl _
  have hsucc : slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax =
      slides0 + (done + 1) * rungSlideCharge n mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hmul := Nat.mul_le_mul_right (rungSlideCharge n mMax) hd
  have hcap : sl + rungSlideCharge n m ≤ slides0 + R * rungSlideCharge n mMax := by
    have h1 : sl + rungSlideCharge n m ≤ sl + rungSlideCharge n mMax :=
      Nat.add_le_add_left hmono sl
    have h2 := Nat.le_trans h1 hslR
    have h2' : sl + rungSlideCharge n m ≤ slides0 + (done + 1) * rungSlideCharge n mMax := by
      rw [hsucc] at h2
      exact h2
    exact Nat.le_trans h2' (Nat.add_le_add_left hmul slides0)
  have hre := reassoc_le sl (m * (2 * n)) (2 * n) (2 * n) 0
    (sl + m * (2 * n) + 2 * n + 2 * n) (Nat.le_of_eq (by rw [Nat.add_zero]))
  exact Nat.le_trans hsum (Nat.le_trans hre (Nat.le_trans (Nat.add_le_add_left hpiece sl) hcap))

theorem clear_ops_fit (ops0 R done mMax cE tally cOps : Nat)
    (hT : tally ≤ mMax) (hd : done + 1 ≤ R)
    (hent : cE ≤ ops0 + done * (mMax + 3))
    (hc : cOps = cE + tally) :
    cOps + 1 ≤ ops0 + R * (mMax + 3) := by
  have h1 : tally + 1 ≤ mMax + 3 := Nat.le_trans (Nat.add_le_add_right hT 1) (Nat.le_add_right _ 2)
  have hgrow : cE + (tally + 1) ≤ cE + (mMax + 3) := Nat.add_le_add_left h1 cE
  have hflat : cE + tally + 1 = cE + (tally + 1) := by rw [Nat.add_assoc]
  have hent' : cE + (mMax + 3) ≤ ops0 + done * (mMax + 3) + (mMax + 3) :=
    Nat.add_le_add_right hent _
  have hsucc : ops0 + done * (mMax + 3) + (mMax + 3) = ops0 + (done + 1) * (mMax + 3) := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hmul := Nat.mul_le_mul_right (mMax + 3) hd
  rw [hc, hflat]
  exact Nat.le_trans hgrow (Nat.le_trans hent' (by
    rw [hsucc]
    exact Nat.add_le_add_left hmul ops0))

theorem lift_to_budget (moves0 R done n bench m mMax mv extra : Nat)
    (hT : m ≤ mMax) (hd : done + 1 ≤ R)
    (hmv : mv ≤ moves0 + done * rungCharge n bench mMax)
    (h : extra ≤ mv + rungCharge n bench m) :
    extra ≤ moves0 + R * rungCharge n bench mMax := by
  have hmono := rungCharge_mono n bench m mMax hT
  have hmax := Nat.le_trans h (Nat.add_le_add_left hmono mv)
  have hright := Nat.add_le_add_right hmv (rungCharge n bench mMax)
  have hjoin := Nat.le_trans hmax hright
  have hsucc : moves0 + done * rungCharge n bench mMax + rungCharge n bench mMax =
      moves0 + (done + 1) * rungCharge n bench mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hstep : extra ≤ moves0 + (done + 1) * rungCharge n bench mMax := by
    rw [← hsucc]; exact hjoin
  exact Nat.le_trans hstep (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) moves0)

/-- One more rung is in the budget once the reversed tail still contains it. -/
theorem step_room (doneLen restLen R : Nat) (h : doneLen + (restLen + 1) ≤ R) :
    doneLen + 1 ≤ R :=
  Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 1 restLen) doneLen) h

/-- The cube's peg charge and the mul charge, on top of the white piece, are one
    `rungCharge`. -/
theorem red_mul_moves_le (mv n bench m mvC mvCube : Nat)
    (hC : mvC ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hCube : mvCube ≤ mvC + pegCharge n bench) :
    mvCube + mulCharge n bench ≤ mv + rungCharge n bench m := by
  let white := n + m * pegCharge n bench + mulCharge n bench + n
  have hWhite := reassoc_le mv n (m * pegCharge n bench) (mulCharge n bench) n mvC hC
  have hsum := Nat.add_le_add_right hCube (mulCharge n bench)
  have hflat : mvC + pegCharge n bench + mulCharge n bench =
      mvC + (pegCharge n bench + mulCharge n bench) :=
    Nat.add_assoc _ _ _
  have hadd := Nat.add_le_add_right hWhite (pegCharge n bench + mulCharge n bench)
  have hjoin := Nat.le_trans (Nat.le_trans hsum (Nat.le_of_eq hflat)) hadd
  have hassoc : mv + white + (pegCharge n bench + mulCharge n bench) =
      mv + (white + (pegCharge n bench + mulCharge n bench)) :=
    Nat.add_assoc _ _ _
  have hwhite : white + (pegCharge n bench + mulCharge n bench) =
      n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
        mulCharge n bench := by
    rw [← Nat.add_assoc]
  have hred := charge_final_red n bench m
  exact Nat.le_trans (Nat.le_trans hjoin (Nat.le_of_eq hassoc))
    (Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq hwhite) hred) mv)

/-- The live mul's four move prefixes, lifted from the cleared board to the rung budget. -/
theorem red_mul_move_fit (moves0 R done n bench m mMax mv mvC mvCube peg : Nat)
    (hT : m ≤ mMax) (hd : done + 1 ≤ R)
    (hmv : mv ≤ moves0 + done * rungCharge n bench mMax)
    (hC : mvC ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hCube : mvCube ≤ mvC + pegCharge n bench)
    (hp : peg ≤ n) :
    2 * peg ≤ moves0 + R * rungCharge n bench mMax ∧
    mvCube + 2 * peg ≤ moves0 + R * rungCharge n bench mMax ∧
    mvCube + 2 * peg + n * (n + 1) ≤ moves0 + R * rungCharge n bench mMax ∧
    mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) ≤
      moves0 + R * rungCharge n bench mMax := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have hpiece : 2 * peg + n * (n + 1) + 3 * (bench - n) ≤ mulCharge n bench := by
    unfold mulCharge
    exact Nat.add_le_add_right (Nat.add_le_add_right h2 (n * (n + 1))) (3 * (bench - n))
  have hre := reassoc_le mvCube (2 * peg) (n * (n + 1)) (3 * (bench - n)) 0
    (mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) + 0) (by
      rw [Nat.add_zero]
      exact Nat.le_refl _)
  have hbig : mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) ≤
      mvCube + mulCharge n bench := by
    have hzero : 2 * peg + n * (n + 1) + 3 * (bench - n) + 0 =
        2 * peg + n * (n + 1) + 3 * (bench - n) := Nat.add_zero _
    have hle := Nat.le_trans hre
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq hzero) hpiece) mvCube)
    simpa [Nat.add_zero] using hle
  have hUp := red_mul_moves_le mv n bench m mvC mvCube hC hCube
  have hfold := lift_to_budget moves0 R done n bench m mMax mv _
    hT hd hmv (Nat.le_trans hbig hUp)
  refine ⟨?_, ?_, ?_, hfold⟩
  · exact Nat.le_trans (Nat.le_add_left (2 * peg) mvCube)
      (Nat.le_trans (Nat.le_add_right (mvCube + 2 * peg) (n * (n + 1)))
        (Nat.le_trans
          (Nat.le_add_right (mvCube + 2 * peg + n * (n + 1)) (3 * (bench - n))) hfold))
  · exact Nat.le_trans (Nat.le_add_right (mvCube + 2 * peg) (n * (n + 1)))
      (Nat.le_trans
        (Nat.le_add_right (mvCube + 2 * peg + n * (n + 1)) (3 * (bench - n))) hfold)
  · exact Nat.le_trans
      (Nat.le_add_right (mvCube + 2 * peg + n * (n + 1)) (3 * (bench - n))) hfold

/-- The red mul bumps ops slot 0 by one. Growth by two from the rung entry always
    fits in `mMax + 3`, with no `mMax > 0` hypothesis. -/
theorem mul_ops_fit (ops0 R done mMax cE cOps : Nat)
    (hd : done + 1 ≤ R)
    (hent : cE ≤ ops0 + done * (mMax + 3))
    (hc : cOps = cE + 1) :
    cOps + 1 ≤ ops0 + R * (mMax + 3) := by
  have h2 : 2 ≤ mMax + 3 :=
    Nat.le_trans (Nat.le_add_left 2 mMax) (Nat.add_le_add_left (Nat.le_succ 2) mMax)
  have hgrow : cE + 2 ≤ cE + (mMax + 3) := Nat.add_le_add_left h2 cE
  have hent' : cE + (mMax + 3) ≤ ops0 + done * (mMax + 3) + (mMax + 3) :=
    Nat.add_le_add_right hent _
  have hsucc : ops0 + done * (mMax + 3) + (mMax + 3) =
      ops0 + (done + 1) * (mMax + 3) := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  rw [hc, Nat.add_assoc]
  exact Nat.le_trans hgrow (Nat.le_trans hent' (by
    rw [hsucc]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) ops0))

theorem red_moves_from_clear (mv n bench m mvC mvCube mvRed : Nat)
    (hC : mvC ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hCube : mvCube ≤ mvC + pegCharge n bench)
    (hRed : mvRed ≤ mvCube + mulCharge n bench) :
    mvRed ≤ mv + rungCharge n bench m := by
  have hfinal := charge_final_red n bench m
  omega

/-- Clear slides are the peg loop plus one `2 · n`. The red cube and the red mul
    add one more `2 · n` each. -/
theorem red_slides_from_clear (sl n m slC pegX pegY : Nat)
    (hs : slC ≤ sl + m * (2 * n) + 2 * n)
    (hX : pegX ≤ n) (hY : pegY ≤ n) :
    slC + 2 * pegX + 2 * pegY ≤ sl + rungSlideCharge n m := by
  have hpiece := slide_open_red n m
  have h2X : 2 * pegX ≤ 2 * n := Nat.mul_le_mul_left _ hX
  have h2Y : 2 * pegY ≤ 2 * n := Nat.mul_le_mul_left _ hY
  omega

/-- Clear slides plus the red cube's pegs and the red mul's pegs, in the rung budget. -/
theorem red_slide_fit (slides0 R done n m mMax sl slC pegX pegY : Nat)
    (hT : m ≤ mMax) (hd : done + 1 ≤ R)
    (hsl : sl ≤ slides0 + done * rungSlideCharge n mMax)
    (hC : slC ≤ sl + m * (2 * n) + 2 * n)
    (hX : pegX ≤ n) (hY : pegY ≤ n) :
    slC + 2 * pegX + 2 * pegY ≤ slides0 + R * rungSlideCharge n mMax := by
  have hpiece := red_slides_from_clear sl n m slC pegX pegY hC hX hY
  have hmono := rungSlideCharge_mono n m mMax hT
  have hslR : sl + rungSlideCharge n mMax ≤
      slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax :=
    Nat.add_le_add_right hsl _
  have hsucc : slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax =
      slides0 + (done + 1) * rungSlideCharge n mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hmul := Nat.mul_le_mul_right (rungSlideCharge n mMax) hd
  have hcap : sl + rungSlideCharge n m ≤ slides0 + R * rungSlideCharge n mMax := by
    have h1 : sl + rungSlideCharge n m ≤ sl + rungSlideCharge n mMax :=
      Nat.add_le_add_left hmono sl
    have h2 := Nat.le_trans h1 hslR
    have h2' : sl + rungSlideCharge n m ≤ slides0 + (done + 1) * rungSlideCharge n mMax := by
      rw [hsucc] at h2
      exact h2
    exact Nat.le_trans h2' (Nat.add_le_add_left hmul slides0)
  exact Nat.le_trans hpiece hcap

/-- Counters of a cube then a mul, read off the boards as variables.
    No live-board term is reduced here. -/
theorem rungDelta_cube_mul
    {b bRed : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    {mv mvRed sl slRed pk pkRed : Nat}
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int))
    (hmvRed : bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvRed : Int))
    (hMov : mvRed ≤ mv + rungCharge base.n base.bench m)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int))
    (hslRed : bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slRed : Int))
    (hSld : slRed ≤ sl + rungSlideCharge base.n m)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int))
    (hpkRed : bRed.sudo_5Board_4cost.sudo_5Costs_4peak = (pkRed : Int))
    (hPk : pkRed ≤ max pk 7)
    (hsz : bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hslots : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hsz ▸ hi) = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3)) :
    RungDelta b bRed base m := by
  refine
    { moves := ⟨mv, mvRed, hmv, hmvRed, hMov⟩
      slides := ⟨sl, slRed, hsl, hslRed, hSld⟩
      opsSize := hsz
      ops := hslots
      peak := ⟨pk, pkRed, hpk, hpkRed, hPk⟩ }

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
      c.k = s.k ∧
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
      hn, hk, hbch, hmv0, hsl0, _ht0, _hctrl0, _hhigh, _hcontrol, _hlen0, _hmax0⟩ := hrest
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
  refine ⟨mv, sl, pk, c, hmv, hsl, hpk, hmv0, hsl0, hmEq, hn, hk, hbch, hsrc, hg,
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
  obtain ⟨mv, sl, pk, c, hmv, hsl, hpk, _hmv0, _hsl0, hmEq, hn, _hk, hbch, _hsrc, _hg,
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

theorem take_n_bench (n n' bench bench' k m : Nat) (g xs : List Nat)
    (hn : n = n') (hb : bench = bench')
    (h : xs.take n = cubeTimes n k bench g m) :
    xs.take n' = cubeTimes n' k bench' g m := by
  subst hn hb
  exact h

theorem sub_pos_cast (n n' k : Nat) (hn : n = n') (h : 0 < n - k) : 0 < n' - k := by
  subst hn
  exact h

theorem le_cast (n n' b b' : Nat) (hn : n = n') (hb : b = b') (h : n ≤ b) : n' ≤ b' := by
  subst hn hb
  exact h

/-- The gap mul's bench list is `fieldMul` of the gap by `cubeTimes`, then zeros. -/
theorem take_of_pad (a : List Nat) (n bench : Nat) (hn : n ≤ bench)
    (hlen : (a ++ List.replicate (bench - n) 0).length = bench) :
    (a ++ List.replicate (bench - n) 0).take n = a := by
  have hsum : a.length + (bench - n) = bench := by
    simpa [List.length_append, List.length_replicate] using hlen
  have hsplit : n + (bench - n) = bench := Nat.add_sub_of_le hn
  have hlenA : a.length = n := Nat.add_right_cancel (hsum.trans hsplit.symm)
  rw [List.take_append_of_le_length (Nat.le_of_eq hlenA.symm)]
  rw [← hlenA]
  exact List.take_length a

theorem take_eq_of_eq (xs pad a : List Nat) (n : Nat) (hxs : xs = pad) (ht : pad.take n = a) :
    xs.take n = a := by
  rw [hxs, ht]

theorem prefix_cube (n k k' bench : Nat) (xs a : List Nat) (hk : k = k') (ht : xs.take n = a) :
    (cubeBench n k bench xs).take n = fieldCube n k' bench a := by
  rw [hk]
  have h := cubeBench_prefix n k' bench xs
  rw [ht] at h
  exact h

theorem embed_mul_cast (n k k' bench : Nat) (x p p' : List Nat) (hk : k = k') (hp : p = p') :
    embed (fieldMul n k bench x p ++ List.replicate (bench - n) 0) =
      embed (fieldMul n k' bench x p' ++ List.replicate (bench - n) 0) := by
  rw [hk, hp]

theorem gap_list_cast (n k k' bench : Nat) (g g' : List Nat) (m m' : Nat) (xs : List Nat)
    (hk : k = k') (hg : g = g') (hm : m = m')
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench)
    (hxs : xs.take n = cubeTimes n k bench g m) :
    laneFold n (n - k) (school n g (xs.take n) (List.replicate bench 0) false) =
      fieldMul n k' bench g' (cubeTimes n k' bench g' m') ++
        List.replicate (bench - n) 0 := by
  subst hk hg hm
  have hL := mul_bench_gap n k bench g xs hn0 hgap0 hn
  dsimp only at hL
  rw [hxs] at hL
  rw [hxs]
  exact hL

/-- Gap mul then clear, on the peg-loop board. Moves gain one mul charge and at
    most `n`. Slides gain at most `2 · n`. Ops slot 0 grows by one. This is the
    white rung. The same package carries the reads the red cube uses: the bench
    list, the hole, the strict peak, and the ops-slot increments. -/
theorem rung_delta_clear
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (bClear : Ecbs.Board) (k mv sl pk mvC slC pkC hole peakS : Nat) (xs : List Nat),
      k = s.k ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_4peak = (pkC : Int) ∧
      pkC ≤ max pk 7 ∧
      mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n ∧
      slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n ∧
      5 < bClear.sudo_5Board_4home.size ∧
      5 < bClear.sudo_5Board_4held.size ∧
      6 < bClear.sudo_5Board_4home.size ∧
      6 < bClear.sudo_5Board_4held.size ∧
      1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hiC : i < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        ∃ cE cC : Nat,
          b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (cE : Int) ∧
          bClear.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (cC : Int) ∧
          (i = 0 → cC = cE + 1) ∧
          (i = 1 → cC = cE + s.tally) ∧
          (i ≠ 0 → i ≠ 1 → cC = cE)) ∧
      bClear.sudo_5Board_5bench = embed xs ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hole : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) ∧
      base.n ≤ base.bench ∧
      bClear.sudo_5Board_9marker_on = false ∧
      bClear.sudo_5Board_8bench_on = true ∧
      bClear.sudo_5Board_8bench_to = (5 : Int) ∧
      7 ≤ bClear.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bClear.sudo_5Board_4held.size, bClear.sudo_5Board_4held[5] = false) ∧
      bClear.sudo_5Board_1t = b.sudo_5Board_1t ∧
      xs.length = base.bench ∧
      (∀ i, base.n ≤ i → ∀ hi : i < xs.length, xs[i] = 0) ∧
      allTritList (xs.take base.n) ∧
      xs = fieldMul base.n s.k base.bench s.gap
        (cubeTimes base.n s.k base.bench s.gap s.tally) ++
        List.replicate (base.bench - base.n) 0 ∧
      (∀ h6 : 6 < bClear.sudo_5Board_4held.size, bClear.sudo_5Board_4held[6] = false) ∧
      CellKeep bClear base.xHome base.x ∧
      RungDelta b bClear base s.tally := by
  obtain ⟨mv, sl, pk, c, hmv, hsl, hpk, _hmv0, _hsl0, hmEq, hn, hk, hbch, hsrc, hg,
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
  have hδ : RungDelta b bClear base s.tally := by
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
  have hcN : c.n = base.n := hn.trans hnB
  have hcbN : c.bench = base.bench := hbch.trans hbB
  let mvCN := mvM + pegCount c.g
  have hmvCN : bClear.sudo_5Board_4cost.sudo_5Costs_5moves = (mvCN : Int) := by
    rw [hmvC, ofNat_eq_natCast]
  let slCN := d.slides + 2 * pegCount (d.xs.take c.n)
  have hslCN : bClear.sudo_5Board_4cost.sudo_5Costs_6slides = (slCN : Int) := by
    rw [hslC, hslM, ofNat_eq_natCast]
  let pkCN := raisedPeak
    (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
    (countHeld ((settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.set
      ⟨6, settle_held_lt d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak⟩ false) 7)
  have hpkCN : bClear.sudo_5Board_4cost.sudo_5Costs_4peak = (pkCN : Int) := by
    rw [hpkC, hpkM, ofNat_eq_natCast]
  have hpkLeN : pkCN ≤ max pk 7 :=
    peak_two_raise pk d.peak hpeakN _ _ (countHeld_seven _) (countHeld_seven _)
  have hpegBase : pegCount s.gap ≤ base.n := by
    have hlen : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, hnB] at hlen
    exact hlen
  have hMovW : mvCN ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
      mulCharge base.n base.bench + base.n := by
    have hmov' : d.moves ≤ mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
      rw [hnB, hbB] at hmovN
      exact hmovN
    have hmul' : mvM ≤ d.moves + mulCharge base.n base.bench := by
      have hchg : mulCharge c.n c.bench = mulCharge base.n base.bench := by
        rw [hcN, hcbN]
      exact Nat.le_trans hmvMle (Nat.add_le_add_left (Nat.le_of_eq hchg) _)
    have hclear' : mvCN ≤ mvM + base.n := by
      have hpeg' : pegCount c.g ≤ base.n := by rw [← hcN]; exact hpegG
      simpa [mvCN] using Nat.add_le_add_left hpeg' mvM
    have hgap' : pegCount s.gap ≤ base.n := hpegBase
    omega
  have hSldW : slCN ≤ sl + s.tally * (2 * base.n) + 2 * base.n := by
    have hs : d.slides ≤ sl + s.tally * (2 * base.n) := by
      rw [hnB] at hsldN
      exact hsldN
    have hp : 2 * pegCount (d.xs.take c.n) ≤ 2 * base.n := by
      exact Nat.le_trans (Nat.mul_le_mul_left 2 (pegCount_take_le d.xs c.n))
        (Nat.mul_le_mul_left 2 (Nat.le_of_eq hcN))
    simpa [slCN] using Nat.add_le_add hs hp
  have h5Hc : 5 < bClear.sudo_5Board_4home.size := by
    have hsz : bClear.sudo_5Board_4home.size = bMul.sudo_5Board_4home.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hsz]
    exact h5H
  have h5Dc : 5 < bClear.sudo_5Board_4held.size := by
    have hsz : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hsz]
    exact h5D
  have h6Hc : 6 < bClear.sudo_5Board_4home.size := by
    have hszM : bMul.sudo_5Board_4home.size = d.b.sudo_5Board_4home.size := by
      rw [show bMul.sudo_5Board_4home =
          d.b.sudo_5Board_4home.set ⟨6, hH6⟩ #[] from
        mul_live_home d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0, Array.size_set]
    have hszC : bClear.sudo_5Board_4home.size = bMul.sudo_5Board_4home.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC, hszM]
    exact hH6
  have h6Dc : 6 < bClear.sudo_5Board_4held.size := by
    have hszM : bMul.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [mul_live_held d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak, Array.size_set]
    have hszC : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC, hszM]
    exact hD6
  have hmulOps := mul_live_ops d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
    d.peak d.peakS c0 hH6 hD6 hops0
  have hset := settle_ops d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak
  have hopsSz : bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsC, hmulOps, Array.size_set, hset, hArr, Array.size_set]
  have hops1c : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsSz, ← hOps0]
    exact c.hops0
  let xsC := laneFold base.n (base.n - c.k)
    (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false)
  have hbenchM : bMul.sudo_5Board_5bench =
      embed (laneFold c.n (c.n - c.k)
        (school c.n c.g (d.xs.take c.n) (List.replicate c.bench 0) false)) := by
    simpa [bMul] using
      mul_live_bench d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hbenchC : bClear.sudo_5Board_5bench = embed xsC := by
    have hbc : bClear.sudo_5Board_5bench = bMul.sudo_5Board_5bench := by
      simp [bClear, clearHeldBoard]
    rw [hbc, hbenchM, hcN, hcbN]
  let holeN := raisedHole d.hole (topIdx
    (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false))
  have hholeM : bMul.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole d.hole (topIdx
        (school c.n c.g (d.xs.take c.n) (List.replicate c.bench 0) false))) := by
    simpa [bMul] using
      gap_mul_hole d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hholeC : bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    have hbc : bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bMul.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      simp [bClear, clearHeldBoard]
    rw [hbc, hholeM, hcN, hcbN, ofNat_eq_natCast]
  let peakSN := raisedPeak d.peakS
    (countHeld (settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held 7)
  have hstrictM : bMul.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakSN := by
    simpa [bMul, peakSN] using
      mul_live_strict d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hstrictC : bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSN : Int) := by
    have hbc : bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bMul.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      simp [bClear, clearHeldBoard]
    rw [hbc, hstrictM, ofNat_eq_natCast]
  have hnle : base.n ≤ base.bench := by
    rw [← hcN, ← hcbN]
    exact c.n_le
  have hmkM : bMul.sudo_5Board_9marker_on = false := by
    simpa [bMul] using
      mul_live_marker d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have hmkC : bClear.sudo_5Board_9marker_on = false := by
    simp [bClear, clearHeldBoard, hmkM]
  have haimed : bMul.sudo_5Board_8bench_on = true ∧
      bMul.sudo_5Board_8bench_to = (5 : Int) := by
    simpa [bMul] using
      gap_mul_aimed d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have honC : bClear.sudo_5Board_8bench_on = true := by
    simp [bClear, clearHeldBoard, haimed.1]
  have htoC : bClear.sudo_5Board_8bench_to = (5 : Int) := by
    simp [bClear, clearHeldBoard, haimed.2]
  have h7c : 7 ≤ bClear.sudo_5Board_4held.size := by
    have hszC : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    have hszM : bMul.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [mul_live_held d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak, Array.size_set]
    rw [hszC, hszM]
    exact d.h7
  have hgetB {a c : Array Bool} (eq : a = c) (j : Nat) (ha : j < a.size) :
      a[j] = c[j]'(eq ▸ ha) := by subst eq; rfl
  have hemptyC : ∀ h5 : 5 < bClear.sudo_5Board_4held.size,
      bClear.sudo_5Board_4held[5] = false := by
    intro h5
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, h5D⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [hgetB hEq 5 h5]
    simp [Array.getElem_set]
  have htierP : c.b0.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [hb0]
    unfold placeBoard
    dsimp only
    split <;> rfl
  have htierM : bMul.sudo_5Board_1t = d.b.sudo_5Board_1t := by
    simpa [bMul] using
      mul_live_tier d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS c0 hH6 hD6 hops0
  have htierC : bClear.sudo_5Board_1t = b.sudo_5Board_1t := by
    have hbc : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [hbc, htierM, d.tier, htierP]
  have hlenX : xsC.length = base.bench := by
    have hsch : (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false).length =
        base.bench := by
      simpa [List.length_replicate] using
        school_length c.g (d.xs.take base.n) (List.replicate base.bench 0) false base.n
    simpa [xsC, hsch] using
      laneFold_length base.n (base.n - c.k)
        (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false)
        (by rw [hsch]; exact hnle)
  have hzeroX : ∀ i, base.n ≤ i → ∀ hi : i < xsC.length, xsC[i] = 0 := by
    intro i hlo hi
    have hcoeff := mul_no_high c.g (d.xs.take base.n) base.n c.k base.bench
      (by rw [← hcN]; exact c.hn0) (by rw [← hcN]; exact c.gap_pos) i hlo (hlenX ▸ hi)
    exact (coeff_eq_get xsC i hi).symm.trans hcoeff
  have htriX : allTritList (xsC.take base.n) := by
    have hrep : allTritList (List.replicate base.bench 0) := by
      intro x hx
      simp [List.mem_replicate] at hx
      rcases hx with ⟨_, rfl⟩
      decide
    have hwide : ∀ i, i < base.n → i + (base.n - 1) < (List.replicate base.bench 0).length := by
      intro i hi
      rw [List.length_replicate]
      have h2 : 2 * (base.n - 1) < base.bench := by
        have h3 : 3 * (base.n - 1) < base.bench := by
          rw [← hcN, ← hcbN]
          exact c.span3
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : 2 ≤ 3)) h3
      omega
    have hschT := school_trits c.g (d.xs.take base.n) (List.replicate base.bench 0) false base.n
      hrep hwide
    have hfoldT := laneFold_trits base.n (base.n - c.k)
      (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false)
      hschT (Nat.sub_le _ _) (by
        rw [show (school base.n c.g (d.xs.take base.n) (List.replicate base.bench 0) false).length =
          base.bench by
          simpa [List.length_replicate] using
            school_length c.g (d.xs.take base.n) (List.replicate base.bench 0) false base.n]
        exact hnle)
    exact allTritList_take hfoldT base.n
  have hslots : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hiC : i < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ cE cC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (cE : Int) ∧
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (cC : Int) ∧
        (i = 0 → cC = cE + 1) ∧
        (i = 1 → cC = cE + s.tally) ∧
        (i ≠ 0 → i ≠ 1 → cC = cE) := by
    intro i hi hiC
    obtain ⟨cOld, hcOld, _⟩ := h.ops i hi
    have hiM : i < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsC ▸ hiC
    have hMulHere := hget hmulOps i hiM
    have hiS : i <
        (settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hszS := congrArg Array.size hmulOps
      rw [Array.size_set] at hszS
      exact hszS ▸ hiM
    by_cases h0i : i = 0
    · have hcEq : cOld = c0 := by
        have hc0at : b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cOld : Int) := by
          subst h0i
          exact hcOld
        exact natCast_inj (hc0at.symm.trans hc0)
      refine ⟨cOld, cOld + 1, hcOld, ?_, ?_, ?_, ?_⟩
      · rw [hget hopsC i hiC, hMulHere, Array.getElem_set, if_pos h0i.symm,
          ofNat_eq_natCast, ← hcEq]
      · intro _; rfl
      · intro h1
        exact absurd (h0i.symm.trans h1) (by decide : (0 : Nat) ≠ 1)
      · intro hne _
        exact absurd h0i hne
    · by_cases h1i : i = 1
      · have hcEq : cOld = c.cOps0 := by
          have hsz1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [← hOps0]; exact c.hops0
          have hslot := (hget hOps0 1 (by rw [hOps0]; exact hsz1)).symm.trans c.hop10
          have hc1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOld : Int) := by
            subst h1i
            exact hcOld
          exact natCast_inj (hc1.symm.trans hslot)
        refine ⟨cOld, cOld + s.tally, hcOld, ?_, ?_, ?_, ?_⟩
        · rw [hget hopsC i hiC, hMulHere, Array.getElem_set, if_neg (Ne.symm h0i)]
          rw [hget hset i hiS, hget hArr i (hset ▸ hiS),
            Array.getElem_set, if_pos h1i.symm, ofNat_eq_natCast, ← hcEq, hmEq]
        · intro h0
          exact absurd h0 h0i
        · intro _; rfl
        · intro _ hne
          exact absurd h1i hne
      · refine ⟨cOld, cOld, hcOld, ?_, ?_, ?_, ?_⟩
        · rw [hget hopsC i hiC, hMulHere, Array.getElem_set, if_neg (Ne.symm h0i)]
          rw [hget hset i hiS, hget hArr i (hset ▸ hiS),
            Array.getElem_set, if_neg (Ne.symm h1i), hcOld]
        · intro h0
          exact absurd h0 h0i
        · intro h1
          exact absurd h1 h1i
        · intro _ _; rfl
  have hempty6M : ∀ h6 : 6 < bMul.sudo_5Board_4held.size,
      bMul.sudo_5Board_4held[6] = false := by
    intro h6
    have hHeld := mul_live_held d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS c0 hH6 hD6 hops0
    rw [show bMul.sudo_5Board_4held =
        (mulNoLiveBoard d.b 5 6 c.g d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS c0 hH6 hD6 hops0).sudo_5Board_4held from rfl] at h6
    have hget6 := hgetB hHeld 6 h6
    rw [hget6]
    simp [Array.getElem_set]
  have hempty6C : ∀ h6 : 6 < bClear.sudo_5Board_4held.size,
      bClear.sudo_5Board_4held[6] = false := by
    intro h6
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, h5D⟩ false := by
      simp [bClear, clearHeldBoard]
    have h6M : 6 < bMul.sudo_5Board_4held.size := by
      have hsz : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
        simp [bClear, clearHeldBoard, Array.size_set]
      exact hsz ▸ h6
    rw [hgetB hEq 6 h6, Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    exact hempty6M h6M
  have hopsZ : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOps0]; exact hsz0
  have hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (c0 : Int) := by
    have h0 : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsZ
    exact (hget hOps0 0 h0).trans hc0
  have hXFD0 : base.xHome < c.b0.sudo_5Board_4held.size := by
    rw [hb0]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.size_set]
    all_goals exact h.shape.xD
  have hXFH0 : base.xHome < c.b0.sudo_5Board_4home.size := by
    rw [hb0]
    unfold placeBoard
    dsimp only
    split <;> simp [Array.size_set]
    all_goals exact h.shape.xH
  have hXHeld0 : c.b0.sudo_5Board_4held[base.xHome] = true := by
    have hEq : c.b0.sudo_5Board_4held =
        (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held := by
      rw [hb0]
    have hF : base.xHome <
        (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held.size :=
      hEq ▸ hXFD0
    have hP := (place_held_other b 6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk
      (Ne.symm h.shape.xNe6) h.shape.xD hF).trans h.shape.xHeld
    exact (hgetB hEq base.xHome hXFD0).trans hP
  have hXArr0 : c.b0.sudo_5Board_4home[base.xHome] = embed base.x := by
    have hEq : c.b0.sudo_5Board_4home =
        (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home := by
      rw [hb0]
    have hF : base.xHome <
        (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home.size :=
      hEq ▸ hXFH0
    have hP := (place_home_other b 6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk
      (Ne.symm h.shape.xNe6) h.shape.xH hF).trans h.shape.xArr
    simp only [hb0]
    exact hP
  have hXkeep := pegPack_keep c base.xHome base.x c0 c.m c.hm (Nat.le_refl _)
    hXFD0 hXFH0 (by rw [hsrc]; exact h.shape.xNe6) hXHeld0 hXArr0 hopsZ hopZ
  have hXmul := mulLive_keep d.b 5 6 base.xHome c.g d.xs c.n c.k d.moves d.slides d.hole
    c.bench d.peak d.peakS c0 base.x hH6 hD6 hops0 h.shape.xNe6
    hXkeep.heldLt hXkeep.homeLt hXkeep.held hXkeep.arr
  have hXclear : CellKeep bClear base.xHome base.x :=
    clearCell_keep bMul 5 base.xHome c.g mvM base.x h5H h5D (Ne.symm h.shape.xNe5)
      { heldLt := hXmul.heldLt
        held := hXmul.held
        homeLt := hXmul.homeLt
        arr := hXmul.arr }
  have hpreX := gap_list_cast base.n c.k s.k base.bench c.g s.gap c.m s.tally d.xs
    hk hg hmEq
    ((hn.trans hnB) ▸ c.hn0)
    (sub_pos_cast c.n base.n c.k (hn.trans hnB) c.gap_pos)
    (le_cast c.n base.n c.bench base.bench (hn.trans hnB) (hbch.trans hbB) c.n_le)
    (take_n_bench c.n base.n c.bench base.bench c.k c.m c.g d.xs
      (hn.trans hnB) (hbch.trans hbB) (pegPack_times c))
  exact ⟨bClear, c.k, mv, sl, pk, mvCN, slCN, pkCN, holeN, peakSN, xsC,
    hk, hmv, hsl, hpk, hmvCN, hslCN, hpkCN, hpkLeN, hMovW, hSldW,
    h5Hc, h5Dc, h6Hc, h6Dc, hops1c, hopsSz, hslots, hbenchC, hholeC, hstrictC, hnle,
    hmkC, honC, htoC, h7c, hemptyC, htierC, hlenX, hzeroX, htriX, hpreX, hempty6C, hXclear, hδ⟩

/-- Same moves, slides, ops, and peak: a `RungDelta` carries from one board to the other. -/
theorem rungDelta_eq {b b1 b2 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m)
    (hmoves : b2.sudo_5Board_4cost.sudo_5Costs_5moves = b1.sudo_5Board_4cost.sudo_5Costs_5moves)
    (hslides : b2.sudo_5Board_4cost.sudo_5Costs_6slides = b1.sudo_5Board_4cost.sudo_5Costs_6slides)
    (hops : b2.sudo_5Board_4cost.sudo_5Costs_3ops = b1.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hpeak : b2.sudo_5Board_4cost.sudo_5Costs_4peak = b1.sudo_5Board_4cost.sudo_5Costs_4peak) :
    RungDelta b b2 base m := by
  refine
    { moves := ?_
      slides := ?_
      opsSize := ?_
      ops := ?_
      peak := ?_ }
  · obtain ⟨mv, mv', hb, hb', hle⟩ := hδ.moves
    exact ⟨mv, mv', hb, hmoves.trans hb', hle⟩
  · obtain ⟨sl, sl', hb, hb', hle⟩ := hδ.slides
    exact ⟨sl, sl', hb, hslides.trans hb', hle⟩
  · rw [hops, hδ.opsSize]
  · intro i hi
    obtain ⟨c, c', hc, hc', hle⟩ := hδ.ops i hi
    have hget {a c : Array Int} (eq : a = c) (j : Nat) (ha : j < a.size) :
        a[j] = c[j]'(eq ▸ ha) := by subst eq; rfl
    have hi1 : i < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ.opsSize ▸ hi
    have hi2 : i < b2.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      congrArg Array.size hops ▸ hi1
    exact ⟨c, c', hc, (hget hops i hi2).trans hc', hle⟩
  · obtain ⟨pk, pk', hb, hb', hle⟩ := hδ.peak
    exact ⟨pk, pk', hb, hpeak.trans hb', hle⟩

/-- Doubling replaces the tally fields and leaves the four `RungDelta` counters. -/
theorem rungDelta_withTally {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m) (row : Array Int) (len ctrl high tmax : Int) :
    RungDelta b (withTally b1 row len ctrl high tmax) base m := by
  have h3 := withTally_counters b1 row len ctrl high tmax
  apply rungDelta_eq hδ h3.1 h3.2.1 h3.2.2
  simp [withTally]

/-- The extra white peg replaces the tally fields and leaves the four counters. -/
theorem rungDelta_add_one {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m) (i : Nat) (hi : i < b1.sudo_5Board_3row.size)
    (len high ctrl tmax : Int) :
    RungDelta b ({ b1 with
      sudo_5Board_3row := b1.sudo_5Board_3row.set ⟨i, hi⟩ (1 : Int)
      sudo_5Board_9tally_len := len
      sudo_5Board_4cost := { b1.sudo_5Board_4cost with
        sudo_5Costs_15control_highest := high
        sudo_5Costs_4ctrl := ctrl
        sudo_5Costs_9tally_max := tmax } }) base m := by
  have h3 := add_one_counters b1 i hi len high ctrl tmax
  apply rungDelta_eq hδ h3.1 h3.2.1 h3.2.2
  rfl

/-- Ops size through a live cube and a live mul, for an arbitrary incoming board.
    Both steps only `set` one slot, so the length is the incoming length. -/
theorem cube_mul_ops_size (b : Ecbs.Board) (dst src second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps cOps' : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (h6H : second <
      (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4home.size)
    (h6D : second <
      (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4held.size)
    (hops0 : 0 <
      (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard
        (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops)
        dst second xs ys n k moves slides hole bench peak peakS cOps' h6H h6D hops0).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [mul_live_ops, Array.size_set,
    settle_ops, cube_live_ops, Array.size_set]

theorem cube_live_home_size (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  rw [cube_live_home, Array.size_set]

theorem cube_live_held_size (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  rw [cube_live_held, Array.size_set, settle_held_eq, Array.size_set]

theorem cube_live_ops_size (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [cube_live_ops, Array.size_set]

theorem mul_live_ops_size (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [mul_live_ops, Array.size_set, settle_ops]

/-- The red cube and the red mul add one peg charge and one mul charge on top
    of the white piece. That is still one `rungCharge`. -/
theorem red_extends_white (mv n bench m pegG mvPeg mvMul pegGap mvClear mvCube mvRed : Nat)
    (hG : pegG ≤ n) (hPeg : mvPeg ≤ mv + pegG + m * pegCharge n bench)
    (hMul : mvMul ≤ mvPeg + mulCharge n bench) (hGap : pegGap ≤ n)
    (hClear : mvClear ≤ mvMul + pegGap) (hCube : mvCube ≤ mvClear + pegCharge n bench)
    (hRed : mvRed ≤ mvCube + mulCharge n bench) :
    mvRed ≤ mv + rungCharge n bench m := by
  have hfinal := charge_final_red n bench m
  have h1 : mvClear ≤ mv + pegG + m * pegCharge n bench + mulCharge n bench + n := by
    omega
  have h2 : mvRed ≤ mv + pegG + m * pegCharge n bench + mulCharge n bench + n +
      pegCharge n bench + mulCharge n bench := by
    omega
  omega

attribute [local irreducible] cubeLiveBoard mulNoLiveBoard

/-- The red cube and the red mul, read off the cleared board.
    `bClear` is the witness of `rung_delta_clear`, so it does not reduce, and the
    live-board definitions are irreducible: the counters are the projection lemmas. -/
theorem rung_delta_red
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ bRed : Ecbs.Board, RungDelta b bRed base s.tally := by
  obtain ⟨bClear, k, mv, sl, pk, mvC, slC, pkC, hole, peakS, xs, hk, hmv, hsl, hpk,
      hmvC, hslC, hpkC, hpkLe, hMovW, hSldW, h5H, h5D, h6H, h6D, hops1, hopsSz, hslots,
      hbench, hhole, hstrict, hnle, _hmk, _hon, _hto, _h7, _hempty, _htier, _hlen,
      _hzero, _htri, _hpre, _hempty6, _hX, hδ⟩ :=
    rung_delta_clear h hm hT hhome
  have _hk : k = s.k := hk
  have _bench : bClear.sudo_5Board_5bench = embed xs := hbench
  have _hole : bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hole : Int) := hhole
  have _strict : bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := hstrict
  have htwo : ∀ c : Nat, c + 2 ≤ c + (base.mMax + 3) := by
    intro c
    exact Nat.add_le_add_left (by omega : (2 : Nat) ≤ base.mMax + 3) c
  have hsucc : ∀ c : Nat, c + (s.tally + 1) ≤ c + (base.mMax + 3) := by
    intro c
    exact Nat.add_le_add_left (by omega : s.tally + 1 ≤ base.mMax + 3) c
  have hpegX : pegCount (xs.take base.n) ≤ base.n := pegCount_take_le xs base.n
  let ys := cubeBench base.n k base.bench xs
  have hpegY : pegCount (ys.take base.n) ≤ base.n := pegCount_take_le ys base.n
  let mvCube := cubeMoves (mvC + 2 * pegCount (xs.take base.n)) (xs.take base.n)
    base.n k base.bench
  have hCubeLe : mvCube ≤ mvC + pegCharge base.n base.bench := by
    simpa [mvCube] using cube_moves_delta mvC xs base.n k base.bench
  let mvRedN := mulMovesNo (mvCube + 2 * pegCount (ys.take base.n)) base.x
    (ys.take base.n) base.n k base.bench
  have hMulLe : mvRedN ≤ mvCube + mulCharge base.n base.bench := by
    have hstep := mul_moves_delta mvCube base.n k base.bench base.x ys hnle
    simpa [mvRedN, mulStepMoves] using hstep
  have hMov : mvRedN ≤ mv + rungCharge base.n base.bench s.tally :=
    red_moves_from_clear mv base.n base.bench s.tally mvC mvCube mvRedN hMovW hCubeLe hMulLe
  let slCube := slC + 2 * pegCount (xs.take base.n)
  let slRedN := slCube + 2 * pegCount (ys.take base.n)
  have hSld : slRedN ≤ sl + rungSlideCharge base.n s.tally := by
    simpa [slRedN, slCube] using
      red_slides_from_clear sl base.n s.tally slC (pegCount (xs.take base.n))
        (pegCount (ys.take base.n)) hSldW hpegX hpegY
  have hops0 : 0 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) hops1
  have hi0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsSz ▸ hops0
  have hi1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsSz ▸ hops1
  obtain ⟨cE0, cOps0, hcE0, _hcC0, h0eq, _, _⟩ := hslots 0 hi0 (hopsSz ▸ hi0)
  obtain ⟨cE1, cOps1, hcE1, _hcC1, _, h1eq, _⟩ := hslots 1 hi1 hops1
  have hc0 : cOps0 = cE0 + 1 := h0eq rfl
  have hc1 : cOps1 = cE1 + s.tally := h1eq rfl
  let pkCube := raisedPeak
    (raisedPeak pkC (countHeld (bClear.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7))
    (countHeld
      ((settleBoard bClear 5 h5H h5D xs base.n mvC slC pkC).sudo_5Board_4held.set
        ⟨5, settle_held_lt bClear 5 h5H h5D xs base.n mvC slC pkC⟩ false) 7)
  have hpkCube : pkCube ≤ max pk 7 :=
    peak_two_raise pk pkC hpkLe _ _ (countHeld_seven _) (countHeld_seven _)
  let holeRed := raisedHole hole (topIdx (combStrip base.n base.bench (xs.take base.n)))
  let peakSRed := raisedPeak peakS
    (countHeld (settleBoard bClear 5 h5H h5D xs base.n mvC slC pkC).sudo_5Board_4held 7)
  let bCube := cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
    cOps1 h5H h5D hops1
  have h6 : 6 < bCube.sudo_5Board_4home.size :=
    (cube_live_home_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ h6H
  have hD6 : 6 < bCube.sudo_5Board_4held.size :=
    (cube_live_held_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ h6D
  have h0c : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    (cube_live_ops_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ hops0
  let bRed := mulNoLiveBoard bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
    pkCube peakSRed cOps0 h6 hD6 h0c
  let pkRed := raisedPeak
    (raisedPeak pkCube (countHeld (bCube.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
    (countHeld
      ((settleBoard bCube 6 h6 hD6 ys base.n mvCube slCube pkCube).sudo_5Board_4held.set
        ⟨6, settle_held_lt bCube 6 h6 hD6 ys base.n mvCube slCube pkCube⟩ false) 7)
  have hpkRedLe : pkRed ≤ max pk 7 :=
    peak_two_raise pk pkCube hpkCube _ _ (countHeld_seven _) (countHeld_seven _)
  have hmvRed : bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvRedN : Int) :=
    mul_live_moves bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 h0c
  have hslRed : bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slRedN : Int) :=
    mul_live_slides bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 h0c
  have hpkRed : bRed.sudo_5Board_4cost.sudo_5Costs_4peak = (pkRed : Int) :=
    mul_live_peak bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 h0c
  have hszM : bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    mul_live_ops_size bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 h0c
  have hszC : bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    cube_live_ops_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  have hsz : bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    hszM.trans (hszC.trans hopsSz)
  have hget {a c : Array Int} (eq : a = c) (i : Nat) (ha : i < a.size) :
      a[i] = c[i]'(eq ▸ ha) := by subst eq; rfl
  have hMulOps := mul_live_ops bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
    pkCube peakSRed cOps0 h6 hD6 h0c
  have hSettle := settle_ops bCube 6 h6 hD6 ys base.n mvCube slCube pkCube
  have hCubeOps := cube_live_ops bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
    cOps1 h5H h5D hops1
  have hslotsR : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hsz ▸ hi) = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3) := by
    intro i hi
    have hiC : i < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsSz ▸ hi
    obtain ⟨cE, cC, hcE, hcC, h0i, h1i, hrest⟩ := hslots i hi hiC
    have hiR : i < bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size := hsz ▸ hi
    have hiM : i < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size := hszM ▸ hiR
    have hHere := hget hMulOps i hiR
    have hiS : i <
        (settleBoard bCube 6 h6 hD6 ys base.n mvCube slCube pkCube).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hszS := congrArg Array.size hMulOps
      rw [Array.size_set] at hszS
      exact hszS ▸ hiR
    by_cases hzero : i = 0
    · have hcC0 : cC = cE + 1 := h0i hzero
      have hcEeq : cE = cE0 := by
        have hcAt : b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cE : Int) := by
          subst hzero
          exact hcE
        exact natCast_inj (hcAt.symm.trans hcE0)
      refine ⟨cE, cE + 2, hcE, ?_, htwo cE⟩
      rw [hHere, Array.getElem_set, if_pos hzero.symm, ofNat_eq_natCast, hc0, hcEeq]
    · have hCubeHere := hget hCubeOps i hiM
      by_cases hone : i = 1
      · have hcEeq : cE = cE1 := by
          have hcAt : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cE : Int) := by
            subst hone
            exact hcE
          exact natCast_inj (hcAt.symm.trans hcE1)
        refine ⟨cE, cE + s.tally + 1, hcE, ?_, ?_⟩
        · rw [hHere, Array.getElem_set, if_neg (Ne.symm hzero), hget hSettle i hiS,
            hCubeHere, Array.getElem_set, if_pos hone.symm, ofNat_eq_natCast, hc1, hcEeq]
        · rw [← Nat.add_assoc]
          exact hsucc cE
      · have hcEq : cC = cE := hrest hzero hone
        refine ⟨cE, cE, hcE, ?_, Nat.le_add_right _ _⟩
        rw [hHere, Array.getElem_set, if_neg (Ne.symm hzero), hget hSettle i hiS,
          hCubeHere, Array.getElem_set, if_neg (Ne.symm hone), hcC, hcEq]
  refine ⟨bRed, rungDelta_cube_mul hmv hmvRed hMov hsl hslRed hSld hpk hpkRed hpkRedLe hsz hslotsR⟩

/-- A non-final white rung doubles the tally and leaves the four counters. -/
theorem rung_delta_white_open
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false)
    (row : Array Int) (len ctrl high tmax : Int) :
    ∃ bW : Ecbs.Board, RungDelta b bW base s.tally := by
  obtain ⟨bClear, _k, _mv, _sl, _pk, _mvC, _slC, _pkC, _hole, _peakS, _xs, _hk, _hmv, _hsl,
      _hpk, _hmvC, _hslC, _hpkC, _hpkLe, _hMovW, _hSldW, _h5H, _h5D, _h6H, _h6D, _hops1,
      _hopsSz, _hslots, _hbench, _hhole, _hstrict, _hnle, _hmk, _hon, _hto, _h7,
      _hempty, _htier, _hlen, _hzero, _htri, _hpre, _hempty6, _hX, hδ⟩ :=
    rung_delta_clear h hm hT hhome
  exact ⟨withTally bClear row len ctrl high tmax,
    rungDelta_withTally hδ row len ctrl high tmax⟩

/-- A double, then the extra white peg, leaves the four counters of any rung delta.
    The row and the index are the ones `tally_double` and `tally_add_one` write. -/
theorem rung_delta_double_add
    {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m)
    (row : Array Int) (len ctrl high tmax : Int)
    (i : Nat) (hi : i < row.size)
    (len1 high1 ctrl1 tmax1 : Int) :
    RungDelta b
      ({ withTally b1 row len ctrl high tmax with
          sudo_5Board_3row :=
            (withTally b1 row len ctrl high tmax).sudo_5Board_3row.set
              ⟨i, withTally_row b1 row len ctrl high tmax ▸ hi⟩ (1 : Int)
          sudo_5Board_9tally_len := len1
          sudo_5Board_4cost :=
            { (withTally b1 row len ctrl high tmax).sudo_5Board_4cost with
                sudo_5Costs_15control_highest := high1
                sudo_5Costs_4ctrl := ctrl1
                sudo_5Costs_9tally_max := tmax1 } })
      base m :=
  rungDelta_add_one (rungDelta_withTally hδ row len ctrl high tmax) i
    (withTally_row b1 row len ctrl high tmax ▸ hi) len1 high1 ctrl1 tmax1

/-- Non-final red rung: the red cube and mul, then the double's row and the extra peg. -/
theorem rung_delta_red_open
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false)
    (row : Array Int) (len ctrl high tmax : Int)
    (i : Nat) (hi : i < row.size)
    (len1 high1 ctrl1 tmax1 : Int) :
    ∃ bA : Ecbs.Board, RungDelta b bA base s.tally := by
  obtain ⟨bRed, hδ⟩ := rung_delta_red h hm hT hhome
  exact ⟨_, rung_delta_double_add hδ row len ctrl high tmax i hi len1 high1 ctrl1 tmax1⟩

/-- The emitted cube of the cleared gap board is the live cube used for the red delta. -/
theorem red_cube_emit
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (bClear bCube : Ecbs.Board) (xs : List Nat),
      Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      xs = fieldMul base.n s.k base.bench s.gap
        (cubeTimes base.n s.k base.bench s.gap s.tally) ++
        List.replicate (base.bench - base.n) 0 ∧
      bCube.sudo_5Board_5bench = embed (cubeBench base.n s.k base.bench xs) ∧
      (cubeBench base.n s.k base.bench xs).take base.n =
        fieldCube base.n s.k base.bench (xs.take base.n) := by
  obtain ⟨bClear, k, mv, sl, pk, mvC, slC, pkC, hole, peakS, xs, hk, hmv, hsl, hpk,
      hmvC, hslC, hpkC, _hpkLe, hMovW, hSldW, h5H, h5D, _h6H, _h6D, hops1, hopsSz, hslots,
      hbench, hhole, hstrict, hnle, hmk, hon, hto, h7, hempty, htier, hlen, hzero, htri,
      hpre, _hempty6, _hX, _hδ⟩ :=
    rung_delta_clear h hm hT hhome
  have hi1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsSz ▸ hops1
  obtain ⟨cE, cOps, hcE, hcOps, _, hplus1, _⟩ := hslots 1 hi1 hops1
  obtain ⟨mv0, hmv0, hle0⟩ := h.moves
  have hmvEq : mv = mv0 := natCast_inj (hmv.symm.trans hmv0)
  have hmvLe : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    rw [hmvEq]; exact hle0
  have hstepR : done.length + 1 ≤ base.R := by
    have hkL := h.kLe
    rw [List.length_append, List.length_cons] at hkL
    omega
  have hpegTake : pegCount (xs.take base.n) ≤ base.n := pegCount_take_le xs base.n
  have hfitM := clear_move_fit base.moves0 base.R done.length base.n base.bench s.tally
    base.mMax mv mvC (pegCount (xs.take base.n)) hT hstepR hmvLe hMovW hpegTake
  obtain ⟨sl0, hsl0, hsle⟩ := h.slides
  have hslEq : sl = sl0 := natCast_inj (hsl.symm.trans hsl0)
  have hslLe : sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    rw [hslEq]; exact hsle
  have hfitS := clear_slide_fit base.slides0 base.R done.length base.n s.tally base.mMax
    sl slC (pegCount (xs.take base.n)) hT hstepR hslLe hSldW hpegTake
  obtain ⟨cSlot, hcSlot, hcLe⟩ := h.ops 1 hi1
  have hcEeq : cE = cSlot := natCast_inj (hcE.symm.trans hcSlot)
  have hent : cE ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [hcEeq]; exact hcLe
  have hcOpsLe := clear_ops_fit base.ops0 base.R done.length base.mMax cE s.tally cOps
    hT hstepR hent (hplus1 rfl)
  have hcube : Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) =
      .ok (cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
        cOps h5H h5D hops1) := by
    apply cube_eq_live bClear 6 5 xs base.w base.h base.r base.n k mvC slC hole base.bench
      pkC peakS cOps base.cg
    · exact hmk
    · exact hon
    · exact hto
    · exact h7
    · exact hempty h5D
    · exact hbench
    · rw [htier, h.shape.tierN, h.hn]
    · rw [← h.hn]; exact h.shape.peg.n_pos
    · rw [hlen]; exact Nat.lt_of_lt_of_le (by rw [← h.hn]; exact h.shape.peg.n_pos) hnle
    · rw [hlen]; exact hnle
    · exact hzero
    · rw [← h.hn]; exact h.shape.peg.fitN
    · rw [hlen, ← h.hbench]; exact h.shape.peg.fitBn
    · exact hmvC
    · exact hslC
    · exact hpkC
    · exact FitsLen.of_le base.fitM hfitM.1
    · exact FitsLen.of_le base.fitM hfitM.2.1
    · exact FitsLen.of_le base.fitS hfitS
    · exact hcOps
    · exact FitsLen.of_le base.fitO hcOpsLe
    · rw [htier, h.shape.tierB, h.hbench]; exact (ofNat_eq_natCast _).symm
    · rw [htier, h.shape.tierCg]; exact (ofNat_eq_natCast _).symm
    · rw [← h.hn, ← h.hbench]; exact h.shape.peg.span
    · exact htri
    · rw [← h.hn]; exact h.shape.peg.fit3
    · exact FitsLen.of_le base.fitM hfitM.2.2.1
    · exact h.shape.w0
    · exact h.shape.h0
    · exact h.shape.rlt
    · exact h.shape.r0
    · rw [← h.hn]; exact h.shape.n_eq
    · rw [hk, ← h.hn]; exact h.shape.k_le
    · rw [hk, ← h.hn]; exact h.shape.gap_eq
    · rw [htier, h.shape.tierW]; exact (ofNat_eq_natCast _).symm
    · rw [htier, h.shape.tierH]; exact (ofNat_eq_natCast _).symm
    · rw [htier, h.shape.tierR]; exact (ofNat_eq_natCast _).symm
    · rw [htier, h.shape.tierK, hk]; exact (ofNat_eq_natCast _).symm
    · exact hhole
    · exact hstrict
    · exact ⟨h.shape.peg.small.1, h.shape.peg.small.2.1, h.shape.peg.small.2.2.1,
        h.hbench ▸ h.shape.peg.small.2.2.2⟩
    · rw [← h.hn]; exact h.shape.peg.n_small
    · rw [← h.hbench]; exact h.shape.peg.fitBn
    · exact FitsLen.of_le base.fitM hfitM.2.2.2

  have hBench : (cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
      cOps h5H h5D hops1).sudo_5Board_5bench =
      embed (cubeBench base.n s.k base.bench xs) := by
    have hB : (cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
        cOps h5H h5D hops1).sudo_5Board_5bench =
        embed (cubeBench base.n k base.bench xs) := by
      have hraw := cube_live_bench bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
        cOps h5H h5D hops1
      dsimp only at hraw
      exact hraw
    have hck : cubeBench base.n k base.bench xs = cubeBench base.n s.k base.bench xs := by
      rw [hk]
    exact hB.trans (congrArg embed hck)
  have hTake : (cubeBench base.n s.k base.bench xs).take base.n =
      fieldCube base.n s.k base.bench (xs.take base.n) := by
    rw [← hk]
    exact cubeBench_prefix base.n k base.bench xs
  exact ⟨bClear, cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
      cOps h5H h5D hops1, xs, hcube, hpre, hBench, hTake⟩

/-- The emitted mul after the red cube is the live nocopy mul.
    `bCube` is named so the projection lemmas apply without unfolding it. -/
theorem red_mul_emit
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bCube bRed : Ecbs.Board),
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul base.n s.k base.bench base.x
          (fieldCube base.n s.k base.bench
            (fieldMul base.n s.k base.bench s.gap
              (cubeTimes base.n s.k base.bench s.gap s.tally))) ++
          List.replicate (base.bench - base.n) 0) := by
  obtain ⟨bClear, k, mv, sl, pk, mvC, slC, pkC, hole, peakS, xs, hk, hmv, hsl, hpk,
      hmvC, hslC, hpkC, _hpkLe, hMovW, hSldW, h5H, h5D, h6H, h6D, hops1, _hopsSz, hslots,
      _hbench, hhole, hstrict, hnle, _hmk, _hon, _hto, h7, _hempty, htier, hlen, hzero, htri,
      hpre, hempty6, hX, _hδ⟩ :=
    rung_delta_clear h hm hT hhome
  have hi0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have h0c : 0 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      Nat.lt_trans (by decide : (0 : Nat) < 1) hops1
    exact _hopsSz ▸ h0c
  obtain ⟨cE0, cOps0, hcE0, hcOps0, h0eq, _, _⟩ := hslots 0 hi0
    (Nat.lt_trans (by decide : (0 : Nat) < 1) hops1)
  have hc0 : cOps0 = cE0 + 1 := h0eq rfl
  have hi1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := _hopsSz ▸ hops1
  obtain ⟨cE1, cOps1, hcE1, _hc1, _, h1eq, _⟩ := hslots 1 hi1 hops1
  let ys := cubeBench base.n k base.bench xs
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hgap0 : 0 < base.n - k := by
    rw [hk, ← h.hn, h.shape.gap_eq]
    exact Nat.mul_pos h.shape.w0 h.shape.r0
  have hysLen : ys.length = base.bench := cubeBench_length base.n k base.bench xs hnle
  have hysZero := cubeBench_zero base.n k base.bench xs hn0 hgap0 hnle
  have hspan3 : 3 * (base.n - 1) < base.bench := by
    rw [← h.hn, ← h.hbench]
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) h.shape.peg.span
  have hysT : allTritList (ys.take base.n) :=
    allTritList_take (cubeBench_trits base.n k base.bench xs htri hspan3 hnle) base.n
  have hpegY : pegCount (ys.take base.n) ≤ base.n := pegCount_take_le ys base.n
  let mvCube := cubeMoves (mvC + 2 * pegCount (xs.take base.n)) (xs.take base.n)
    base.n k base.bench
  let slCube := slC + 2 * pegCount (xs.take base.n)
  let pkCube := raisedPeak
    (raisedPeak pkC (countHeld (bClear.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7))
    (countHeld ((settleBoard bClear 5 h5H h5D xs base.n mvC slC pkC).sudo_5Board_4held.set
      ⟨5, settle_held_lt bClear 5 h5H h5D xs base.n mvC slC pkC⟩ false) 7)
  let holeRed := raisedHole hole (topIdx (combStrip base.n base.bench (xs.take base.n)))
  let peakSRed := raisedPeak peakS
    (countHeld (settleBoard bClear 5 h5H h5D xs base.n mvC slC pkC).sudo_5Board_4held 7)
  let bCube := cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
    cOps1 h5H h5D hops1
  have hC : bCube = cubeLiveBoard bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS
      cOps1 h5H h5D hops1 := rfl
  have h6 : 6 < bCube.sudo_5Board_4home.size :=
    (cube_live_home_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ h6H
  have hD6 : 6 < bCube.sudo_5Board_4held.size :=
    (cube_live_held_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ h6D
  have hops0 : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    (cube_live_ops_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ Nat.lt_trans (by decide : (0 : Nat) < 1) hops1
  have h7b : 7 ≤ bCube.sudo_5Board_4held.size :=
    (cube_live_held_size bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1).symm ▸ h7
  have hXcube := cubeLive_keep bClear 6 5 base.xHome xs base.n k mvC slC hole base.bench
    pkC peakS cOps1 base.x h5H h5D hops1 h.shape.xNe5 hX.heldLt hX.homeLt hX.held hX.arr
  have hheld6 := cube_live_held_other bClear bCube 6 5 6 xs base.n k mvC slC hole base.bench
    pkC peakS cOps1 h5H h5D hops1 hC (by decide) h6D hD6
  obtain ⟨mv0, hmv0, hle0⟩ := h.moves
  have hmvLe : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    rw [natCast_inj (hmv.symm.trans hmv0)]; exact hle0
  have hstepR : done.length + 1 ≤ base.R := by
    have hkL := h.kLe
    rw [List.length_append, List.length_cons] at hkL
    exact step_room _ _ _ hkL
  have hCubeLe : mvCube ≤ mvC + pegCharge base.n base.bench :=
    cube_moves_delta mvC xs base.n k base.bench
  have hMulFit := red_mul_move_fit base.moves0 base.R done.length base.n base.bench s.tally
    base.mMax mv mvC mvCube (pegCount (ys.take base.n)) hT hstepR hmvLe hMovW hCubeLe hpegY
  obtain ⟨sl0, hsl0, hsle⟩ := h.slides
  have hslLe : sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    rw [natCast_inj (hsl.symm.trans hsl0)]; exact hsle
  have hSlideFit : slCube + 2 * pegCount (ys.take base.n) ≤
      base.slides0 + base.R * rungSlideCharge base.n base.mMax :=
    red_slide_fit base.slides0 base.R done.length base.n s.tally base.mMax sl slC
      (pegCount (xs.take base.n)) (pegCount (ys.take base.n)) hT hstepR hslLe hSldW
      (pegCount_take_le xs base.n) hpegY
  obtain ⟨cSlot0, hcSlot0, hcLe0⟩ := h.ops 0 hi0
  have hent0 : cE0 ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [natCast_inj (hcE0.symm.trans hcSlot0)]; exact hcLe0
  have hOpsFit : cOps0 + 1 ≤ base.ops0 + base.R * (base.mMax + 3) :=
    mul_ops_fit base.ops0 base.R done.length base.mMax cE0 cOps0 hstepR hent0 hc0
  let gapA := fieldMul base.n s.k base.bench s.gap
    (cubeTimes base.n s.k base.bench s.gap s.tally)
  have hpad := take_of_pad gapA base.n base.bench hnle (hpre ▸ hlen)
  have hxsTake := take_eq_of_eq xs _ gapA base.n hpre hpad
  have hysTake := prefix_cube base.n k s.k base.bench xs gapA hk hxsTake
  have hraw := mul_live_bench_gap bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
    pkCube peakSRed cOps0 h6 hD6 hops0 hn0 hgap0 hnle
  have hRed : (mulNoLiveBoard bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 hops0).sudo_5Board_5bench =
      embed (fieldMul base.n s.k base.bench base.x
        (fieldCube base.n s.k base.bench gapA) ++
        List.replicate (base.bench - base.n) 0) :=
    hraw.trans (embed_mul_cast base.n k s.k base.bench base.x (ys.take base.n)
      (fieldCube base.n s.k base.bench gapA) hk hysTake)
  have hAim := gap_mul_aimed bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
    pkCube peakSRed cOps0 h6 hD6 hops0
  refine ⟨bCube, mulNoLiveBoard bCube 5 6 base.x ys base.n k mvCube slCube holeRed base.bench
      pkCube peakSRed cOps0 h6 hD6 hops0, ?_, hAim.1, hAim.2, hRed⟩
  apply mul_eq_live bCube 5 base.xHome 6 base.x ys base.w base.h base.r base.n k mvCube slCube
    holeRed base.bench pkCube peakSRed cOps0
  · exact cube_live_marker bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact cube_live_on bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact cube_live_to bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact h7b
  · exact (hheld6.trans (hempty6 h6D))
  · exact cube_live_bench bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierN, h.hn]
  · exact hn0
  · rw [hysLen]; exact Nat.lt_of_lt_of_le hn0 hnle
  · rw [hysLen]; exact hnle
  · exact hysZero
  · rw [← h.hn]; exact h.shape.peg.fitN
  · rw [hysLen, ← h.hbench]; exact h.shape.peg.fitBn
  · exact cube_live_moves bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact cube_live_slides bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact cube_live_peak bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact FitsLen.of_le base.fitM hMulFit.1
  · exact FitsLen.of_le base.fitM hMulFit.2.1
  · exact FitsLen.of_le base.fitS hSlideFit
  · exact (cube_live_op0 bClear bCube 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1 hC hops0).trans hcOps0
  · exact FitsLen.of_le base.fitO hOpsFit
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierB, h.hbench]; exact (ofNat_eq_natCast _).symm
  · exact hXcube.held
  · exact hXcube.arr
  · exact h.shape.xNe6
  · exact hxLen
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)) hspan3
  · exact hxT
  · exact FitsLen.of_le (by rw [← h.hn]; exact h.shape.peg.fit3)
      (Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3))
  · exact FitsLen.of_le base.fitM hMulFit.2.2.1
  · exact h.shape.w0
  · exact h.shape.h0
  · exact h.shape.rlt
  · exact h.shape.r0
  · rw [← h.hn]; exact h.shape.n_eq
  · rw [hk, ← h.hn]; exact h.shape.k_le
  · rw [hk, ← h.hn]; exact h.shape.gap_eq
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierW]; exact (ofNat_eq_natCast _).symm
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierH]; exact (ofNat_eq_natCast _).symm
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierR]; exact (ofNat_eq_natCast _).symm
  · rw [hC, cube_live_tier bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1, htier, h.shape.tierK, hk]; exact (ofNat_eq_natCast _).symm
  · exact cube_live_hole bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact cube_live_strict bClear 6 5 xs base.n k mvC slC hole base.bench pkC peakS cOps1
      h5H h5D hops1
  · exact ⟨h.shape.peg.small.1, h.shape.peg.small.2.1, h.shape.peg.small.2.2.1,
      h.hbench ▸ h.shape.peg.small.2.2.2⟩
  · rw [← h.hn]; exact h.shape.peg.n_small
  · rw [← h.hbench]; exact h.shape.peg.fitBn
  · exact FitsLen.of_le base.fitM hMulFit.2.2.2

/-- Nothing parked: `afterPark` writes the rung colour into the parking hole and
    clears the climb hole. -/
theorem afterPark_idle (row : List Nat) (park hole colour : Nat) :
    afterPark row (-1) park hole colour = (row.set park colour).set hole 0 := by
  simp [afterPark]

/-- A final red rung, nothing parked yet. The gap is the product of the input by
    the cube of the gap product. The tally length stays. The counter is the park
    write plus one per tally peg. The row is that park write, then the red tally.
    The parked-from hole is the climb hole and the rung index advances by one. -/
theorem model_final_red (s : ClimbModel) (x : List Nat) (hole : Nat)
    (hFrom : s.fromHole < 0) :
    (modelRung s x 2 hole true).gap =
      fieldMul s.n s.k s.benchlen x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ∧
    (modelRung s x 2 hole true).tally = s.tally ∧
    (modelRung s x 2 hole true).onBench = true ∧
    (modelRung s x 2 hole true).work =
      fieldMul s.n s.k s.benchlen x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ∧
    (modelRung s x 2 hole true).ctrl = s.ctrl + 2 + s.tally ∧
    (modelRung s x 2 hole true).high = s.high ∧
    (modelRung s x 2 hole true).row =
      paintRed (afterPark s.row s.fromHole s.parkAt hole 2) s.t0 s.tally ∧
    (modelRung s x 2 hole true).fromHole = (hole : Int) ∧
    (modelRung s x 2 hole true).ridx = s.ridx + 1 ∧
    (modelRung s x 2 hole true).t0 = s.t0 ∧
    (modelRung s x 2 hole true).parkAt = s.parkAt := by
  have hpark : decide (0 ≤ s.fromHole) = false := by
    rw [decide_eq_false_iff_not]
    omega
  simp [modelRung, invRung, rungCtrl, rungHigh, rungRow, afterTally, hpark]

/-- The keep-park board: the row is `afterPark`, the counter grows by two, the
    parked-from hole is the climb hole, the rung index advances, and the tally
    length is unchanged. -/
theorem parkKeep_fields (b : Ecbs.Board) (xs : List Nat)
    (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size)
    (hrow : b.sudo_5Board_3row = embed xs) (hp : park < xs.length) (hh : hole < xs.length) :
    let bP := parkKeepBoard b hole park rung i ctrl hRowP hRowH
    bP.sudo_5Board_3row = embed (afterPark xs (-1) park hole rung) ∧
    bP.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((ctrl + 2 : Nat) : Int) ∧
    bP.sudo_5Board_11parked_from = (hole : Int) ∧
    bP.sudo_5Board_8rung_idx = ((i + 1 : Nat) : Int) ∧
    bP.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [parkKeep_row b xs hole park rung i ctrl hRowP hRowH hrow hp hh, afterPark_idle]

/-- Emitted keep-park, from `ClimbInvK` with nothing parked. The row is `afterPark`,
    the counter has grown by two, the parked-from hole is the climb hole, the rung
    index has advanced, and the tally length is the model's. -/
theorem parked_fields
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) :
    ∃ bPark : Ecbs.Board,
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bPark.sudo_5Board_3row =
        embed (afterPark s.row (-1) s.parkAt (climbAt base.ladder0 base.R s.ridx) r) ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 : Nat) : Int) ∧
      bPark.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bPark.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bPark.sudo_5Board_9tally_len = (s.tally : Int) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bPark, hpark, hfrom, hridx, hkeep⟩ := park_of_shape h
  obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
  have hp : s.parkAt < s.row.length := h.shape.park.parkLt
  have hh : hole < s.row.length := h.shape.park.holeLt
  have hfields := parkKeep_fields b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH h.inv.row hp hh
  have hlen : b.sudo_5Board_9tally_len = (s.tally : Int) := h.inv.len
  refine ⟨bPark, hpark, ?_, ?_, hfrom, hridx, ?_⟩
  · rw [hEq]
    exact hfields.1
  · rw [hEq]
    exact hfields.2.1
  · rw [hEq, hfields.2.2.2.2, hlen]

/-- After the cube-peg loop the row is the start row painted red, the counter has
    grown by the peg count, and the park, rung index, and tally length are the
    ones the loop started with. -/
theorem peg_loop_book (c : PegCtx) (hm : 0 < c.m) :
    let d := pegPack c c.m hm (Nat.le_refl _)
    d.b.sudo_5Board_3row = embed (paintRed c.row0 c.t0 c.m) ∧
    d.b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((c.ctrl0 + c.m : Nat) : Int) ∧
    d.b.sudo_5Board_11parked_from = c.b0.sudo_5Board_11parked_from ∧
    d.b.sudo_5Board_8rung_idx = c.b0.sudo_5Board_8rung_idx ∧
    d.b.sudo_5Board_9tally_len = c.b0.sudo_5Board_9tally_len := by
  let d := pegPack c c.m hm (Nat.le_refl _)
  have hB := pegPack_board c c.m hm (Nat.le_refl _)
  refine ⟨d.hrow, ?_, hB.2.1, hB.2.2.1, hB.2.2.2.1⟩
  rw [d.hctrl, d.hctrlN]

theorem afterPark_neg (row : List Nat) (f : Int) (park hole colour : Nat) (hf : f < 0) :
    afterPark row f park hole colour = afterPark row (-1) park hole colour := by
  simp [afterPark, hf]

/-- The peg-loop board of a context that started on the keep-park board has the
    final red rung's row, counter, parked-from hole, rung index, and tally length. -/
theorem peg_is_final_red (s : ClimbModel) (x : List Nat) (hole : Nat)
    (hFrom : s.fromHole < 0) (c : PegCtx) (hm : 0 < c.m)
    (hrow0 : c.row0 = afterPark s.row s.fromHole s.parkAt hole 2)
    (hctrl0 : c.ctrl0 = s.ctrl + 2) (hmT : c.m = s.tally) (ht0 : c.t0 = s.t0)
    (hfrom : c.b0.sudo_5Board_11parked_from = (hole : Int))
    (hridx : c.b0.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int))
    (hlen : c.b0.sudo_5Board_9tally_len = (s.tally : Int)) :
    let d := pegPack c c.m hm (Nat.le_refl _)
    let st := modelRung s x 2 hole true
    d.b.sudo_5Board_3row = embed st.row ∧
    d.b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (st.ctrl : Int) ∧
    d.b.sudo_5Board_11parked_from = st.fromHole ∧
    d.b.sudo_5Board_8rung_idx = (st.ridx : Int) ∧
    d.b.sudo_5Board_9tally_len = (st.tally : Int) := by
  have hM := model_final_red s x hole hFrom
  have hP := peg_loop_book c hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hP.1, hrow0, ht0, hmT, hM.2.2.2.2.2.2.1]
  · rw [hP.2.1, hctrl0, hmT, hM.2.2.2.2.1]
  · rw [hP.2.2.1, hfrom, hM.2.2.2.2.2.2.2.1]
  · rw [hP.2.2.2.1, hridx, hM.2.2.2.2.2.2.2.2.1]
  · rw [hP.2.2.2.2, hlen, hM.2.1]

/-- `clear` of one home leaves the row, the counter, the park, the rung index,
    and the tally length. -/
theorem clear_keeps (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_3row = b.sudo_5Board_3row ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len := by
  unfold clearHeldBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A live cube leaves the row, the counter, the park, the rung index, and the
    tally length. -/
theorem cube_keeps (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_3row =
      b.sudo_5Board_3row ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len := by
  have hC := cubeLive_carries b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  exact ⟨cube_live_row b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
    cube_live_ctrl b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
    hC.1, hC.2.1, hC.2.2⟩

/-- A final red rung stores the product of the input by the cube of the gap product.
    The tally length does not change. The polynomial sits on the bench. -/
theorem model_red_gap (s : ClimbModel) (x : List Nat) (hole : Nat) :
    (modelRung s x 2 hole true).gap =
      fieldMul s.n s.k s.benchlen x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ∧
    (modelRung s x 2 hole true).onBench = true ∧
    (modelRung s x 2 hole true).tally = s.tally ∧
    (modelRung s x 2 hole true).n = s.n ∧
    (modelRung s x 2 hole true).benchlen = s.benchlen := by
  simp [modelRung, invRung]

/-- The gap mul leaves `fieldMul` of the gap by `cubeTimes` on the bench, then zeros.
    A white rung stores that list. A red cube reads it. -/
theorem gap_bench_prefix
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (bM : Ecbs.Board) (ys : List Nat)
      (moves slides hole peak peakS cOps : Nat)
      (hH : 6 < bM.sudo_5Board_4home.size)
      (hD : 6 < bM.sudo_5Board_4held.size)
      (hops : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      Ecbs.mul bM ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false =
        .ok (mulNoLiveBoard bM 5 6 s.gap ys s.n s.k moves slides hole s.benchlen
          peak peakS cOps hH hD hops) ∧
      ys.take s.n = cubeTimes s.n s.k s.benchlen s.gap s.tally ∧
      (mulNoLiveBoard bM 5 6 s.gap ys s.n s.k moves slides hole s.benchlen
          peak peakS cOps hH hD hops).sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap (ys.take s.n) ++
          List.replicate (s.benchlen - s.n) 0) := by
  obtain ⟨c, bM, ys, moves, slides, hole, peak, peakS, cOps, hH, hD, hops,
      _hcopy, _hsrc, hg, hmEq, hn, hk, hbch, _hbM, hysEq, _hGap, _hX, _hFit, _hMov,
      _hSFit, _hSLe, _hOp, _hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, _hctrl0, _hhigh0,
      _hcontrol, _hlen0, _hmax0, _ht0, hmul, _hrow0, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨_, _, _⟩, ⟨_, _, _⟩, _hmulW⟩ :=
    mul_of_shape h hm hT hhome
  have hpre : ys.take c.n = cubeTimes c.n c.k c.bench c.g c.m := by
    rw [hysEq]
    exact cubeBenchIter_prefix c.n c.k c.bench c.g c.hlenx c.m
  have hList : laneFold c.n (c.n - c.k)
      (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false) =
      fieldMul c.n c.k c.bench c.g (ys.take c.n) ++ List.replicate (c.bench - c.n) 0 :=
    mul_bench_gap c.n c.k c.bench c.g ys c.hn0 c.gap_pos c.n_le
  have hBench := mul_live_bench bM 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cOps hH hD hops
  have hBench' :
      (mulNoLiveBoard bM 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cOps hH hD hops).sudo_5Board_5bench =
        embed (fieldMul c.n c.k c.bench c.g (ys.take c.n) ++
          List.replicate (c.bench - c.n) 0) := by
    dsimp only at hBench
    rw [hList] at hBench
    exact hBench
  rw [hg, hmEq, hn, hk, hbch] at hpre
  rw [hg, hn, hk, hbch] at hBench' hmul
  exact ⟨bM, ys, moves, slides, hole, peak, peakS, cOps, hH, hD, hops, hmul, hpre, hBench'⟩

theorem fieldMul_len (n k bench : Nat) (x y : List Nat) (hn : n ≤ bench) :
    (fieldMul n k bench x y).length = n := by
  have hsch : (school n x y (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using
      school_length x y (List.replicate bench 0) false n
  have hll := laneFold_length n (n - k) (school n x y (List.replicate bench 0) false)
    (by rw [hsch]; exact hn)
  rw [hsch] at hll
  unfold fieldMul
  rw [List.length_take, show reduceStrip n (n - k)
      (school n x y (List.replicate bench 0) false) =
      laneFold n (n - k) (school n x y (List.replicate bench 0) false) from rfl, hll,
    Nat.min_eq_left hn]

/-- On a final red rung the emitted mul's bench is the model gap, padded with zeros,
    and the bench is on and aimed at the gap. -/
theorem red_final_gap_bench
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bCube bRed : Ecbs.Board),
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_5bench =
        embed ((modelRung s base.x 2 0 true).gap.take s.n ++
          List.replicate (s.benchlen - s.n) 0) := by
  obtain ⟨bCube, bRed, hmul, hon, hto, hbench⟩ :=
    red_mul_emit h hm hT hhome hxLen hxT
  have hmod := (model_red_gap s base.x 0).1
  have hnle : s.n ≤ s.benchlen :=
    span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
  have hlenG : (modelRung s base.x 2 0 true).gap.length = s.n := by
    rw [hmod]
    exact fieldMul_len s.n s.k s.benchlen base.x
      (fieldCube s.n s.k s.benchlen
        (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
  have htake : (modelRung s base.x 2 0 true).gap.take s.n =
      (modelRung s base.x 2 0 true).gap := by
    rw [← hlenG]
    exact List.take_length _
  have hpad : (modelRung s base.x 2 0 true).gap.take s.n ++
      List.replicate (s.benchlen - s.n) 0 =
      fieldMul base.n s.k base.bench base.x
        (fieldCube base.n s.k base.bench
          (fieldMul base.n s.k base.bench s.gap
            (cubeTimes base.n s.k base.bench s.gap s.tally))) ++
        List.replicate (base.bench - base.n) 0 := by
    rw [htake, hmod, h.hn, h.hbench]
  have hbench' : bRed.sudo_5Board_5bench =
      embed ((modelRung s base.x 2 0 true).gap.take s.n ++
        List.replicate (s.benchlen - s.n) 0) := by
    rw [hbench, hpad]
  exact ⟨bCube, bRed, hmul, hon, hto, hbench'⟩

/-- A live cube then a live nocopy mul copies the row, the tally origin, and the
    control counter. Those fields on the red board are the cleared board's. -/
theorem cube_mul_row
    (b : Ecbs.Board) (xs ys x : List Nat)
    (n k moves slides hole bench peak peakS cOps moves2 slides2 hole2 peak2 peakS2 cOps2 : Nat)
    (hH : 5 < b.sudo_5Board_4home.size) (hD : 5 < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (h6 : 6 < (cubeLiveBoard b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4home.size)
    (hD6 : 6 < (cubeLiveBoard b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4held.size)
    (hops0 : 0 < (cubeLiveBoard b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    let bC := cubeLiveBoard b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops
    let bR := mulNoLiveBoard bC 5 6 x ys n k moves2 slides2 hole2 bench peak2 peakS2 cOps2 h6 hD6 hops0
    bR.sudo_5Board_3row = b.sudo_5Board_3row ∧
    bR.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_live_row _ 5 6 x ys n k moves2 slides2 hole2 bench peak2 peakS2 cOps2 h6 hD6 hops0).trans
      (cube_live_row b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops)
  · exact (mul_live_tally _ 5 6 x ys n k moves2 slides2 hole2 bench peak2 peakS2 cOps2 h6 hD6 hops0).trans
      (cube_live_tally b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops)
  · exact (mul_live_ctrl _ 5 6 x ys n k moves2 slides2 hole2 bench peak2 peakS2 cOps2 h6 hD6 hops0).trans
      (cube_live_ctrl b 6 5 xs n k moves slides hole bench peak peakS cOps hH hD hops)

/-- The gap-mul board's row is the tally painted red. The mul does not write the row. -/
theorem gap_mul_row
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (bM bMul : Ecbs.Board),
      Ecbs.mul bM ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      bMul.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) := by
  obtain ⟨c, bM, ys, moves, slides, hole, peak, peakS, cOps, hH, hD, hops,
      _hcopy, _hsrc, _hg, _hmEq, _hn, _hk, _hbch, _hbM, _hys, _hGap, _hX, _hFit, _hMov,
      _hSFit, _hSLe, _hOp, hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, _hctrl0, _hhigh0,
      _hcontrol, _hlen0, _hmax0, _ht0, hmul, _hrow0, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨_, _, _⟩, ⟨_, _, _⟩, _hmulW⟩ :=
    mul_of_shape h hm hT hhome
  have hkeep := (mul_live_row bM 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cOps
    hH hD hops).trans hRow
  exact ⟨bM, mulNoLiveBoard bM 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cOps
    hH hD hops, hmul, hkeep⟩

/-- The emitted copy of the idle park, then the emitted cube-peg loop, is the
    peg context `parked_peg_ctx` names. On a final red rung that loop's board
    has the model's row, counter, parked-from hole, rung index, and tally length. -/
theorem parked_final_red
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark : Ecbs.Board) (c : PegCtx),
      Ecbs.park_rung b ((2 : Nat) : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
      SudoRt.runLoopOn (Int.ofNat 0, c.b0)
          (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
          (cubePegStep c.src (Int.ofNat (c.m - 1)))
          (fun σ => .ok σ)
          (fun r => .ok ((0 : Int), r)) =
        .ok (Int.ofNat (c.m - 1), pegBoard c c.m) ∧
      let hole := climbAt base.ladder0 base.R s.ridx
      let st := modelRung s base.x 2 hole true
      (pegBoard c c.m).sudo_5Board_3row = embed st.row ∧
      (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_4ctrl = (st.ctrl : Int) ∧
      (pegBoard c c.m).sudo_5Board_11parked_from = st.fromHole ∧
      (pegBoard c c.m).sudo_5Board_8rung_idx = (st.ridx : Int) ∧
      (pegBoard c c.m).sudo_5Board_9tally_len = (st.tally : Int) := by
  obtain ⟨bPark, c, hpark, hcopy, hrow0, hctrl0, hmT, ht0, _, _, _, _, _, hfrom, hridx, hlen, _⟩ :=
    parked_peg_ctx h hF hm hT hhome
  let hole := climbAt base.ladder0 base.R s.ridx
  have hIdle : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hrow0' : c.row0 = afterPark s.row s.fromHole s.parkAt hole 2 := by
    rw [hrow0, hIdle]
  have hFive := peg_is_final_red s base.x hole hF c c.hm hrow0' hctrl0 hmT ht0 hfrom hridx hlen
  have hEq : (pegPack c c.m c.hm (Nat.le_refl _)).b = pegBoard c c.m :=
    (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  refine ⟨bPark, c, hpark, hcopy, cube_peg_loop_refines c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hEq]; exact hFive.1
  · rw [← hEq]; exact hFive.2.1
  · rw [← hEq]; exact hFive.2.2.1
  · rw [← hEq]; exact hFive.2.2.2.1
  · rw [← hEq]; exact hFive.2.2.2.2

/-- The emitted gap mul of that parked peg loop has the final red model's row,
    counter, parked-from hole, rung index, and tally length. -/
theorem parked_gap_mul_fields
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (c : PegCtx) (bMul : Ecbs.Board),
      Ecbs.mul (pegBoard c c.m) ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      let hole := climbAt base.ladder0 base.R s.ridx
      let st := modelRung s base.x 2 hole true
      bMul.sudo_5Board_3row = embed st.row ∧
      bMul.sudo_5Board_4cost.sudo_5Costs_4ctrl = (st.ctrl : Int) ∧
      bMul.sudo_5Board_11parked_from = st.fromHole ∧
      bMul.sudo_5Board_8rung_idx = (st.ridx : Int) ∧
      bMul.sudo_5Board_9tally_len = (st.tally : Int) := by
  obtain ⟨c, bMul, hmul, hrow, hctrl, hfromB, hridxB, hlenB, hrow0, hctrl0, hmT, ht0,
      hfrom, hridx, hlen, _hlive⟩ := parked_gap_mul h hF hm hT hhome
  let hole := climbAt base.ladder0 base.R s.ridx
  have hIdle : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hrow0' : c.row0 = afterPark s.row s.fromHole s.parkAt hole 2 := by
    rw [hrow0, hIdle]
  have hM := model_final_red s base.x hole hF
  refine ⟨c, bMul, hmul, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrow, hrow0', ht0, hmT, hM.2.2.2.2.2.2.1]
  · rw [hctrl, hctrl0, hmT, hM.2.2.2.2.1]
  · rw [hfromB, hfrom, hM.2.2.2.2.2.2.2.1]
  · rw [hridxB, hridx, hM.2.2.2.2.2.2.2.2.1]
  · rw [hlenB, hlen, hM.2.1]

/-- On a final red rung, clear of home 5, the cube spare→gap, and the mul by the
    input succeed on the parked gap-mul board. The result's row, counter,
    parked-from hole, rung index, and tally length are the model rung, the bench
    is on and aimed at the gap, and the bench is that model's gap padded with zeros. -/
theorem final_red_fields
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bMul bClear bCube bRed : Ecbs.Board),
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      let hole := climbAt base.ladder0 base.R s.ridx
      let st := modelRung s base.x 2 hole true
      bRed.sudo_5Board_3row = embed st.row ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_4ctrl = (st.ctrl : Int) ∧
      bRed.sudo_5Board_11parked_from = st.fromHole ∧
      bRed.sudo_5Board_8rung_idx = (st.ridx : Int) ∧
      bRed.sudo_5Board_9tally_len = (st.tally : Int) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (st.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0) := by
  obtain ⟨bMul, bClear, bCube, bRed, hclear, hcube, hmul, hrow, hctrl, hfrom, hridx,
      hlen, hon, hto, hbench⟩ :=
    final_red_emit h hF hm hT hhome hxLen hxT
  let hole := climbAt base.ladder0 base.R s.ridx
  let st := modelRung s base.x 2 hole true
  have hM := model_final_red s base.x hole hF
  have hIdle : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hnle : s.n ≤ s.benchlen :=
    span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
  have hlenG : st.gap.length = s.n := by
    rw [show st.gap = (modelRung s base.x 2 hole true).gap from rfl, hM.1]
    exact fieldMul_len s.n s.k s.benchlen base.x
      (fieldCube s.n s.k s.benchlen
        (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
  have htake : st.gap.take s.n = st.gap := by
    rw [← hlenG]
    exact List.take_length _
  refine ⟨bMul, bClear, bCube, bRed, hclear, hcube, hmul, ?_, ?_, ?_, ?_, ?_, hon, hto, ?_⟩
  · rw [hrow, hM.2.2.2.2.2.2.1, hIdle]
  · rw [hctrl, hM.2.2.2.2.1]
  · rw [hfrom, hM.2.2.2.2.2.2.2.1]
  · rw [hridx, hM.2.2.2.2.2.2.2.2.1, ofNat_eq_natCast]
  · rw [hlen, hM.2.1]
  · rw [hbench, htake, hM.1]

end EcbsLink2.Link2
