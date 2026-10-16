/-
  `invert` on a walk board. The fresh `bottomBoard` is the special case whose
  counters are the two copies and whose other homes are empty. A walk board
  enters the same climb when the control row, the ladder, and the park are
  still the ones `new_board` laid, the gap and the spare are empty, home
  `bottom` holds the input, and the counters still fit the climb budget.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CheckTail
import EcbsLink2.Link2.ClimbLadder
import EcbsLink2.Link2.SettleFrame
import EcbsLink2.Link2.SlideGap

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- What `invert` reads off a marker-off board before it copies the bottom
    into the gap. The control frame is the fresh ladder. Counters are naturals
    with room for that copy and for the tally peg. -/
structure OpenLay (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat) where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  marker : b.sudo_5Board_9marker_on = false
  bench : b.sudo_5Board_8bench_on = false
  held2 : b.sudo_5Board_4held[2]'(by rw [szD]; decide) = true
  home2 : b.sudo_5Board_4home[2]'(by rw [szH]; decide) = embed xs
  held5 : b.sudo_5Board_4held[5]'(by rw [szD]; decide) = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  /-- Homes 0, 1, and 4. The climb does not write them. -/
  side0 : List Nat
  side1 : List Nat
  side4 : List Nat
  flag0 : Bool
  flag1 : Bool
  flag4 : Bool
  home0 : b.sudo_5Board_4home[0]'(by rw [szH]; decide) = embed side0
  held0 : b.sudo_5Board_4held[0]'(by rw [szD]; decide) = flag0
  home1 : b.sudo_5Board_4home[1]'(by rw [szH]; decide) = embed side1
  held1 : b.sudo_5Board_4held[1]'(by rw [szD]; decide) = flag1
  home4 : b.sudo_5Board_4home[4]'(by rw [szH]; decide) = embed side4
  held4 : b.sudo_5Board_4held[4]'(by rw [szD]; decide) = flag4
  /-- Home 3 is the base. The climb does not write it. -/
  base3 : List Nat
  flag3 : Bool
  home3 : b.sudo_5Board_4home[3]'(by rw [szH]; decide) = embed base3
  held3 : b.sudo_5Board_4held[3]'(by rw [szD]; decide) = flag3
  /-- Script marker index and its maximum. The climb does not write them. -/
  mark : Nat
  mx : Nat
  hmark : b.sudo_5Board_6marker = Int.ofNat mark
  hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  len : xs.length = t.n
  tri : allTritList xs
  tier : b.sudo_5Board_1t = embTier t
  moves : Nat
  slides : Nat
  peak : Nat
  ctrl : Nat
  high : Nat
  cOps : Nat
  opsCap : Nat
  peakS : Nat
  hole : Nat
  hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak
  hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = Int.ofNat high
  tmax : Nat
  htally : b.sudo_5Board_9tally_len = 0
  ht0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  hrow : b.sudo_5Board_3row = embed (paintedRow t)
  htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int)
  /-- The first cell raises the high. A later cell already has the high at or
      above the origin. `1 ≤ tally_max` is not part of this branch: `open_climb`
      and `chord_add_live` do not read it. `tally_start_high` records `max` of
      the old maximum and `1` either way. -/
  hStart : (high < tallyOrigin t ∧ tmax = 0) ∨ tallyOrigin t ≤ high
  hlad : b.sudo_5Board_6ladder = embed (tierClimb t)
  hl0 : b.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2)
  hnr : b.sudo_5Board_6nrungs = Int.ofNat (tierR t)
  hpark : b.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t)
  hfrom : b.sudo_5Board_11parked_from = -1
  hridx : b.sudo_5Board_8rung_idx = 0
  hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS
  hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  ops2 : 2 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop2 : b.sudo_5Board_4cost.sudo_5Costs_3ops[2]'ops2 = Int.ofNat cOps
  fitOps : FitsLen (cOps + 1)
  fitCopy : FitsLen (moves + pegCount xs)
  fitCtrl : FitsLen (ctrl + 1)
  opsAll : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ c, b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = Int.ofNat c ∧
      (if i = 2 then c + 1 else c) ≤ opsCap

/-- The climb budget is this board's counters after the gap copy, and the
    tier's ladder. `peak0` is the peak `place` leaves when the gap becomes held. -/
structure OpenMatch {b : Ecbs.Board} {t : Spec.Tier} {xs : List Nat}
    (lay : OpenLay b t xs) (base : ClimbBudget) : Prop where
  n : base.n = t.n
  bench : base.bench = t.benchlen
  moves0 : base.moves0 = lay.moves + pegCount xs
  slides0 : base.slides0 = lay.slides
  ops0 : base.ops0 = lay.opsCap
  peak0 : base.peak0 =
    raisedPeak lay.peak
      (countHeld (b.sudo_5Board_4held.set ⟨5, by rw [lay.szD]; decide⟩ true) 7)
  tally0 : base.tally0 = 1
  R : base.R = tierR t
  mMax : base.mMax = rowRoom t
  ctrl0 : base.ctrl0 = lay.ctrl + 1
  x : base.x = xs
  xHome : base.xHome = 2
  w : base.w = t.w
  h : base.h = t.h
  r : base.r = t.r
  cg : base.cg = t.combgap
  control : base.control = t.control
  ladder0 : base.ladder0 = t.script + 2
  side0 : base.side0 = lay.side0
  side1 : base.side1 = lay.side1
  side4 : base.side4 = lay.side4
  held0 : base.held0 = lay.flag0
  held1 : base.held1 = lay.flag1
  held4 : base.held4 = lay.flag4
  tierSnap : base.tierSnap = embTier t
  markSnap : base.markSnap = Int.ofNat lay.mark
  mxSnap : base.mxSnap = Int.ofNat lay.mx
  high0 : base.high0 = lay.high
  baseRow : base.baseRow = paintedRow t
  base3 : base.base3 = lay.base3
  held3 : base.held3 = lay.flag3

/-- The model at the first tally peg. The control counter is whatever the walk
    has already charged, plus the peg `tally_start` writes. -/
def openModel (t : Spec.Tier) (xs : List Nat) (ctrl : Nat) : ClimbModel :=
  { entryModel t xs with ctrl := ctrl + 1 }

/-- The same model when the entry high may already sit at or above the origin.
    `tally_start` records `max` of that high and the origin. The high is not
    an export result. `walk_key` returns a point, and `receive_check`'s
    `Checked.control_highest` is a different, exact field. -/
def openModelAt (t : Spec.Tier) (xs : List Nat) (ctrl high : Nat) : ClimbModel :=
  { openModel t xs ctrl with high := max high (tallyOrigin t) }

/-- Bump `op_inv`, copy the bottom into the empty gap, and lay the first tally
    peg. The gap is the input. The control counter and the recorded high move
    to the tally origin. -/
theorem open_tally (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) :
    ∃ bT,
      (do
        let b ← (do
          let ix := Ecbs.op_inv
          let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
          let t2 ← SudoRt.addI t1 (1 : Int)
          let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
          pure ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } } : Ecbs.Board))
        let b ← Ecbs.copy_band b Ecbs.gap ((2 : Nat) : Int) false
        Ecbs.tally_start b) = .ok bT ∧
      bT.sudo_5Board_9marker_on = false ∧
      bT.sudo_5Board_8bench_on = false ∧
      bT.sudo_5Board_9tally_len = 1 ∧
      bT.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (lay.ctrl + 1) ∧
      bT.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((max lay.high (tallyOrigin t) : Nat) : Int) ∧
      bT.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) ∧
      bT.sudo_5Board_3row = embed (entryRow t) ∧
      bT.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) ∧
      bT.sudo_5Board_11parked_from = -1 ∧
      bT.sudo_5Board_8rung_idx = 0 ∧
      bT.sudo_5Board_6ladder = embed (tierClimb t) ∧
      bT.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) ∧
      bT.sudo_5Board_6nrungs = Int.ofNat (tierR t) ∧
      bT.sudo_5Board_1t = embTier t ∧
      bT.sudo_5Board_4home.size = 8 ∧
      bT.sudo_5Board_4held.size = 8 ∧
      (∀ h : 5 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[5] = true) ∧
      (∀ h : 5 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[5] = embed xs) ∧
      (∀ h : 6 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[6] = false) ∧
      (∀ h : 2 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[2] = true) ∧
      (∀ h : 2 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[2] = embed xs) ∧
      bT.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (lay.moves + pegCount xs) ∧
      bT.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat lay.slides ∧
      bT.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak lay.peak
          (countHeld (b.sudo_5Board_4held.set ⟨5, by rw [lay.szD]; decide⟩ true) 7)) ∧
      bT.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        ((max lay.tmax 1 : Nat) : Int) ∧
      bT.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat lay.peakS ∧
      bT.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat lay.hole ∧
      bT.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨2, lay.ops2⟩ (Int.ofNat (lay.cOps + 1)) ∧
      (∀ h : 0 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[0] = embed lay.side0) ∧
      (∀ h : 0 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[0] = lay.flag0) ∧
      (∀ h : 1 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[1] = embed lay.side1) ∧
      (∀ h : 1 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[1] = lay.flag1) ∧
      (∀ h : 4 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[4] = embed lay.side4) ∧
      (∀ h : 4 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[4] = lay.flag4) ∧
      (∀ h : 3 < bT.sudo_5Board_4home.size, bT.sudo_5Board_4home[3] = embed lay.base3) ∧
      (∀ h : 3 < bT.sudo_5Board_4held.size, bT.sudo_5Board_4held[3] = lay.flag3) ∧
      bT.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bT.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  let bB := bumpOp b 2 lay.cOps lay.ops2
  have hszHB : bB.sudo_5Board_4home.size = 8 := by
    rw [show bB.sudo_5Board_4home = b.sudo_5Board_4home from bumpOp_home b 2 lay.cOps lay.ops2,
      lay.szH]
  have hszDB : bB.sudo_5Board_4held.size = 8 := by
    rw [bumpOp_held b 2 lay.cOps lay.ops2, lay.szD]
  have h5H : 5 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h5D : 5 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h2H : 2 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h2D : 2 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h7 : 7 ≤ bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have hheldB : bB.sudo_5Board_4held = b.sudo_5Board_4held :=
    bumpOp_held b 2 lay.cOps lay.ops2
  have hhomeB : bB.sudo_5Board_4home = b.sudo_5Board_4home :=
    bumpOp_home b 2 lay.cOps lay.ops2
  have h2t : bB.sudo_5Board_4held[2]'h2D = true := cell_eq_of hheldB lay.held2
  have h2a : bB.sudo_5Board_4home[2]'h2H = embed xs := cell_eq_of hhomeB lay.home2
  have h5e : bB.sudo_5Board_4held[5]'h5D = false := cell_eq_of hheldB lay.held5
  have hnB : bB.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int) := by
    rw [show bB.sudo_5Board_1t = b.sudo_5Board_1t from rfl, lay.tier, lay.len]
    simp [embTier, ofNat_eq_natCast]
  have hmovesB : bB.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat lay.moves := by
    rw [bumpOp_moves b 2 lay.cOps lay.ops2, lay.hmoves]
  have hpeakB : bB.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat lay.peak := by
    rw [bumpOp_peak b 2 lay.cOps lay.ops2, lay.hpeak]
  have hcopy := copy_band_refines bB 5 2 xs lay.moves lay.peak h5H h5D h2H h2D h7
    h2t h2a h5e hnB (by rw [lay.len]; exact FitsLen.of_le (fits_of hOk.fits_n) (by omega))
    hmovesB hpeakB lay.fitCopy
  let bG := placeBoard bB 5 h5H h5D xs lay.moves lay.peak
  rcases place_rest bB 5 h5H h5D xs lay.moves lay.peak with
    ⟨htierG, _, _, _, _, _, _, _, hl0G, hnrG, hparkG, ht0G, hmarkIxG, hfromG, hlenG,
      hmarkG, hridxG, hladG, _, hctrlG, _, _, _, _, hstrictG, hholeG, hhighG, hmxG,
      htmaxG, _, _, hopsG⟩
  have hrowG : bG.sudo_5Board_3row = embed (paintedRow t) := by
    rw [place_row_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak,
      show bB.sudo_5Board_3row = b.sudo_5Board_3row from rfl, lay.hrow]
  have horigin : tallyOrigin t < t.control := origin_lt t sat
  have hrowSz : tallyOrigin t < bG.sudo_5Board_3row.size := by
    rw [hrowG, size_embed, painted_len]
    exact horigin
  have hfit0 : FitsLen (tallyOrigin t) :=
    FitsLen.of_le (fits_of hOk.fits_control)
      (Nat.le_trans (Nat.le_of_lt horigin) (Nat.le_succ _))
  have hctrlN : bG.sudo_5Board_1t.sudo_4Tier_7control = (t.control : Int) := by
    rw [htierG, show bB.sudo_5Board_1t = b.sudo_5Board_1t from rfl, lay.tier]
    simp [embTier, ofNat_eq_natCast]
  let bT : Ecbs.Board :=
    { bG with
      sudo_5Board_3row := bG.sudo_5Board_3row.set ⟨tallyOrigin t, hrowSz⟩ (1 : Int)
      sudo_5Board_9tally_len := 1
      sudo_5Board_4cost := { bG.sudo_5Board_4cost with
        sudo_5Costs_15control_highest := ((max lay.high (tallyOrigin t) : Nat) : Int)
        sudo_5Costs_4ctrl := Int.ofNat (lay.ctrl + 1)
        sudo_5Costs_9tally_max := ((max lay.tmax 1 : Nat) : Int) } }
  have htallyRun := tally_start_mark bG (tallyOrigin t) lay.high t.control lay.ctrl lay.tmax
    (by rw [hlenG, show bB.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len from rfl,
        lay.htally])
    (by rw [ht0G, show bB.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 from rfl, lay.ht0,
        ofNat_eq_natCast])
    hrowSz hctrlN horigin
    (by rw [hhighG, show bB.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest from rfl, lay.hhigh,
        ofNat_eq_natCast])
    hfit0
    (by rw [hctrlG, show bB.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl from rfl, lay.hctrl, ofNat_eq_natCast])
    lay.fitCtrl
    (by rw [htmaxG, show bB.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max from rfl, lay.htmax])
    lay.hStart
  have hrowSet : bG.sudo_5Board_3row.set ⟨tallyOrigin t, hrowSz⟩ (1 : Int) =
      embed (entryRow t) := by
    have hlenP : tallyOrigin t < (paintedRow t).length := by
      rw [painted_len]; exact horigin
    rw [Array.set_congr_arr hrowG hrowSz (1 : Int)]
    rw [array_set_idx (h2 := by rw [size_embed]; exact hlenP)]
    simpa [entryRow, ofNat_eq_natCast] using
      embed_set (paintedRow t) (tallyOrigin t) 1 hlenP
  have hszHG : bG.sudo_5Board_4home.size = 8 := by
    rw [place_home_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak, Array.size_set, hszHB]
  have hszDG : bG.sudo_5Board_4held.size = 8 := by
    rw [place_held_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak, Array.size_set, hszDB]
  have h5HG : 5 < bG.sudo_5Board_4home.size := by rw [hszHG]; decide
  have h5DG : 5 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have h6DG : 6 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have h2HG : 2 < bG.sudo_5Board_4home.size := by rw [hszHG]; decide
  have h2DG : 2 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have hhomeG : bG.sudo_5Board_4home = bB.sudo_5Board_4home.set ⟨5, h5H⟩ (embed xs) :=
    place_home_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak
  have hheldG : bG.sudo_5Board_4held = bB.sudo_5Board_4held.set ⟨5, h5D⟩ true :=
    place_held_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak
  have h5t : bG.sudo_5Board_4held[5]'h5DG = true := by
    have hget := Array.getElem_set_eq bB.sudo_5Board_4held ⟨5, h5D⟩ true rfl
      (by rw [Array.size_set]; exact h5D)
    exact cell_eq_of hheldG hget
  have h5a : bG.sudo_5Board_4home[5]'h5HG = embed xs := by
    have hget := Array.getElem_set_eq bB.sudo_5Board_4home ⟨5, h5H⟩ (embed xs) rfl
      (by rw [Array.size_set]; exact h5H)
    exact cell_eq_of hhomeG hget
  have h6e : bG.sudo_5Board_4held[6]'h6DG = false := by
    have hne : (5 : Nat) ≠ 6 := by decide
    have hsz : 6 < (bB.sudo_5Board_4held.set ⟨5, h5D⟩ true).size := by
      rw [Array.size_set, hszDB]; decide
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨5, h5D⟩ true hsz hne
    have h6B : bB.sudo_5Board_4held[6]'(by rw [hszDB]; decide) = false :=
      cell_eq_of hheldB lay.held6
    exact (cell_eq_of hheldG hget).trans h6B
  have h2tG : bG.sudo_5Board_4held[2]'h2DG = true := by
    have hne : (5 : Nat) ≠ 2 := by decide
    have hsz : 2 < (bB.sudo_5Board_4held.set ⟨5, h5D⟩ true).size := by
      rw [Array.size_set, hszDB]; decide
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨5, h5D⟩ true hsz hne
    exact (cell_eq_of hheldG hget).trans h2t
  have h2aG : bG.sudo_5Board_4home[2]'h2HG = embed xs := by
    have hne : (5 : Nat) ≠ 2 := by decide
    have hsz : 2 < (bB.sudo_5Board_4home.set ⟨5, h5H⟩ (embed xs)).size := by
      rw [Array.size_set, hszHB]; decide
    have hget := Array.getElem_set_ne bB.sudo_5Board_4home ⟨5, h5H⟩ (embed xs) hsz hne
    exact (cell_eq_of hhomeG hget).trans h2a
  have hcount : countHeld (bB.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 =
      countHeld (b.sudo_5Board_4held.set ⟨5, by rw [lay.szD]; decide⟩ true) 7 := by
    rw [Array.set_congr_arr hheldB h5D true]
  have hpk : bG.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak lay.peak
        (countHeld (b.sudo_5Board_4held.set ⟨5, by rw [lay.szD]; decide⟩ true) 7)) := by
    rw [place_peak_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak hpeakB, hcount]
  have hbump :
      (do
        let ix := Ecbs.op_inv
        let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
        let t2 ← SudoRt.addI t1 (1 : Int)
        let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
        pure ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } })) =
        .ok bB := by
    simpa [bB, bumpOp] using
      bump_cont b lay.cOps lay.ops2 lay.hop2 lay.fitOps pure
  have homeKeep (i : Nat) (hne : (5 : Nat) ≠ i) (hi8 : i < 8) {v : Array Int}
      (hv : b.sudo_5Board_4home[i]'(by rw [lay.szH]; exact hi8) = v)
      (hT : i < bT.sudo_5Board_4home.size) :
      bT.sudo_5Board_4home[i]'hT = v := by
    have hsz : i < (bB.sudo_5Board_4home.set ⟨5, h5H⟩ (embed xs)).size := by
      rw [Array.size_set, hszHB]; exact hi8
    have hget := Array.getElem_set_ne bB.sudo_5Board_4home ⟨5, h5H⟩ (embed xs) hsz hne
    have hB : bB.sudo_5Board_4home[i]'(by rw [hszHB]; exact hi8) = v :=
      cell_eq_of hhomeB hv
    have hset : (bB.sudo_5Board_4home.set ⟨5, h5H⟩ (embed xs))[i]'hsz = v :=
      hget.trans (idx_irrel.trans hB)
    have hG : bG.sudo_5Board_4home[i]'(by rw [hhomeG, Array.size_set, hszHB]; exact hi8) = v :=
      cell_eq_of hhomeG hset
    exact cell_eq_of (show bT.sudo_5Board_4home = bG.sudo_5Board_4home from rfl) hG
  have heldKeep (i : Nat) (hne : (5 : Nat) ≠ i) (hi8 : i < 8) {v : Bool}
      (hv : b.sudo_5Board_4held[i]'(by rw [lay.szD]; exact hi8) = v)
      (hT : i < bT.sudo_5Board_4held.size) :
      bT.sudo_5Board_4held[i]'hT = v := by
    have hsz : i < (bB.sudo_5Board_4held.set ⟨5, h5D⟩ true).size := by
      rw [Array.size_set, hszDB]; exact hi8
    have hget := Array.getElem_set_ne bB.sudo_5Board_4held ⟨5, h5D⟩ true hsz hne
    have hB : bB.sudo_5Board_4held[i]'(by rw [hszDB]; exact hi8) = v :=
      cell_eq_of hheldB hv
    have hset : (bB.sudo_5Board_4held.set ⟨5, h5D⟩ true)[i]'hsz = v :=
      hget.trans (idx_irrel.trans hB)
    have hG : bG.sudo_5Board_4held[i]'(by rw [hheldG, Array.size_set, hszDB]; exact hi8) = v :=
      cell_eq_of hheldG hset
    exact cell_eq_of (show bT.sudo_5Board_4held = bG.sudo_5Board_4held from rfl) hG
  refine ⟨bT, ?_, ?_, ?_, rfl, rfl, rfl, ?_, hrowSet, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
  · rw [hbump, ok_bind]
    rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl, hcopy, ok_bind]
    simpa [bT, ofNat_eq_natCast] using htallyRun
  · rw [show bT.sudo_5Board_9marker_on = bG.sudo_5Board_9marker_on from rfl, hmarkG,
      show bB.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on from rfl, lay.marker]
  · rw [show bT.sudo_5Board_8bench_on = bG.sudo_5Board_8bench_on from rfl,
      place_on_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak,
      show bB.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on from rfl, lay.bench]
  · rw [show bT.sudo_5Board_6tally0 = bG.sudo_5Board_6tally0 from rfl, ht0G,
      show bB.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 from rfl, lay.ht0]
  · rw [show bT.sudo_5Board_9park_hole = bG.sudo_5Board_9park_hole from rfl, hparkG,
      show bB.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole from rfl, lay.hpark]
  · rw [show bT.sudo_5Board_11parked_from = bG.sudo_5Board_11parked_from from rfl, hfromG,
      show bB.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from from rfl, lay.hfrom]
  · rw [show bT.sudo_5Board_8rung_idx = bG.sudo_5Board_8rung_idx from rfl, hridxG,
      show bB.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx from rfl, lay.hridx]
  · rw [show bT.sudo_5Board_6ladder = bG.sudo_5Board_6ladder from rfl, hladG,
      show bB.sudo_5Board_6ladder = b.sudo_5Board_6ladder from rfl, lay.hlad]
  · rw [show bT.sudo_5Board_7ladder0 = bG.sudo_5Board_7ladder0 from rfl, hl0G,
      show bB.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 from rfl, lay.hl0]
  · rw [show bT.sudo_5Board_6nrungs = bG.sudo_5Board_6nrungs from rfl, hnrG,
      show bB.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs from rfl, lay.hnr]
  · rw [show bT.sudo_5Board_1t = bG.sudo_5Board_1t from rfl, htierG,
      show bB.sudo_5Board_1t = b.sudo_5Board_1t from rfl, lay.tier]
  · rw [show bT.sudo_5Board_4home.size = bG.sudo_5Board_4home.size from rfl, hszHG]
  · rw [show bT.sudo_5Board_4held.size = bG.sudo_5Board_4held.size from rfl, hszDG]
  · intro h; exact idx_irrel.trans h5t
  · intro h; exact idx_irrel.trans h5a
  · intro h; exact idx_irrel.trans h6e
  · intro h; exact idx_irrel.trans h2tG
  · intro h; exact idx_irrel.trans h2aG
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_5moves =
        bG.sudo_5Board_4cost.sudo_5Costs_5moves from rfl,
      place_moves_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_6slides =
        bG.sudo_5Board_4cost.sudo_5Costs_6slides from rfl,
      place_slides_out bB 5 ⟨h5H, h5D⟩ xs lay.moves lay.peak,
      show bB.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides from rfl, lay.hslides]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_4peak =
        bG.sudo_5Board_4cost.sudo_5Costs_4peak from rfl, hpk]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bG.sudo_5Board_4cost.sudo_5Costs_11peak_strict from rfl, hstrictG,
      show bB.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict from rfl, lay.hstrict]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bG.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole from rfl, hholeG,
      show bB.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole from rfl, lay.hhole]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_3ops =
        bG.sudo_5Board_4cost.sudo_5Costs_3ops from rfl, hopsG, bumpOp_ops]
  · intro h; exact homeKeep 0 (by decide) (by decide) lay.home0 h
  · intro h; exact heldKeep 0 (by decide) (by decide) lay.held0 h
  · intro h; exact homeKeep 1 (by decide) (by decide) lay.home1 h
  · intro h; exact heldKeep 1 (by decide) (by decide) lay.held1 h
  · intro h; exact homeKeep 4 (by decide) (by decide) lay.home4 h
  · intro h; exact heldKeep 4 (by decide) (by decide) lay.held4 h
  · intro h; exact homeKeep 3 (by decide) (by decide) lay.home3 h
  · intro h; exact heldKeep 3 (by decide) (by decide) lay.held3 h
  · rw [show bT.sudo_5Board_6marker = bG.sudo_5Board_6marker from rfl, hmarkIxG]
    rfl
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        bG.sudo_5Board_4cost.sudo_5Costs_17script_marker_max from rfl, hmxG]
    rfl

/-- The tally board of a walk entry satisfies the climb invariant. The budget
    is the board's own counters, not the fresh two-copy budget. -/
theorem open_climb (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base) :
    ∃ bT,
      (do
        let b ← (do
          let ix := Ecbs.op_inv
          let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
          let t2 ← SudoRt.addI t1 (1 : Int)
          let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
          pure ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } } : Ecbs.Board))
        let b ← Ecbs.copy_band b Ecbs.gap ((2 : Nat) : Int) false
        Ecbs.tally_start b) = .ok bT ∧
      bT.sudo_5Board_6ladder = embed (tierClimb t) ∧
      ClimbInvK [] (tierClimb t) bT (openModelAt t xs lay.ctrl lay.high) base ∧
      2 < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  obtain ⟨bT, hdo, hmark, hbench, hlen, hctrl, hhigh, ht0, hrow, hpark, hfrom, hridx,
      hlad, hl0, hnr, htier, hszH, hszD, h5t, h5a, h6e, h2t, h2a, hmv, hsl, hpk,
      htmax, hstrict, hhole, hops, h0a, h0t, h1a, h1t, h4a, h4t, h3a, h3t,
      hmarkIx, hmxT⟩ :=
    open_tally b t xs lay hOk sat
  have hsz5 : 5 < bT.sudo_5Board_4home.size := by rw [hszH]; decide
  have hsz5D : 5 < bT.sudo_5Board_4held.size := by rw [hszD]; decide
  have hopsSlot : ∀ i (hi : i < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c, bT.sudo_5Board_4cost.sudo_5Costs_3ops[i] = Int.ofNat c ∧ c ≤ lay.opsCap := by
    intro i hi
    have hsz : bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hops, Array.size_set]
    have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hsz]; exact hi
    obtain ⟨c, hc, hle⟩ := lay.opsAll i hi0
    have hidx := idx_get hops i hi
    by_cases h2 : i = 2
    · have hget := Array.getElem_set_eq b.sudo_5Board_4cost.sudo_5Costs_3ops
          ⟨2, lay.ops2⟩ (Int.ofNat (lay.cOps + 1)) h2.symm
          (by rw [Array.size_set]; exact hi0)
      have hcEq : c = lay.cOps := by
        have hidxEq : b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi0 =
            b.sudo_5Board_4cost.sudo_5Costs_3ops[2]'lay.ops2 :=
          congrArg (fun j : Fin _ => b.sudo_5Board_4cost.sudo_5Costs_3ops.get j) (Fin.ext h2)
        exact Int.ofNat.inj (hc.symm.trans (hidxEq.trans lay.hop2))
      refine ⟨lay.cOps + 1, (hidx.trans hget), ?_⟩
      simpa [h2, hcEq] using hle
    · have hne : (2 : Nat) ≠ i := fun h => h2 h.symm
      have hget := Array.getElem_set_ne b.sudo_5Board_4cost.sudo_5Costs_3ops
          ⟨2, lay.ops2⟩ (Int.ofNat (lay.cOps + 1))
          (by rw [Array.size_set]; exact hi0) hne
      refine ⟨c, hidx.trans (hget.trans hc), ?_⟩
      simpa [h2] using hle
  have hInv : ClimbInv bT (openModelAt t xs lay.ctrl lay.high) :=
    { hG := hsz5
      hGs := hsz5D
      marker := hmark
      len := by simpa [openModelAt, openModel, entryModel, ofNat_eq_natCast] using hlen
      ctrl := by simpa [openModelAt, openModel, entryModel, ofNat_eq_natCast] using hctrl
      high := by simpa [openModelAt, openModel, entryModel, ofNat_eq_natCast] using hhigh
      t0 := by simpa [openModelAt, openModel, entryModel, ofNat_eq_natCast] using ht0
      row := by simpa [openModelAt, openModel, entryModel] using hrow
      park := by simpa [openModelAt, openModel, entryModel, ofNat_eq_natCast] using hpark
      fromP := by simpa [openModelAt, openModel, entryModel] using hfrom
      ridx := by simpa [openModelAt, openModel, entryModel] using hridx
      gapHome := by
        intro _
        refine ⟨h5t hsz5D, ?_⟩
        simpa [openModelAt, openModel, entryModel] using h5a hsz5
      gapBench := by
        intro h
        simp [openModelAt, openModel, entryModel] at h }
  have hparkR : ParkRead bT (openModelAt t xs lay.ctrl lay.high) (tierClimb t) base :=
    { ladder0B := by simp [hm.ladder0, hl0, ofNat_eq_natCast]
      nrungsB := by simp [hm.R, hnr, ofNat_eq_natCast]
      climbH := by
        simp only [hm.ladder0, hm.R]
        apply climb_holes_refines bT (t.script + 2) (tierR t)
        · simpa [ofNat_eq_natCast] using hl0
        · simpa [ofNat_eq_natCast] using hnr
        · have hsg := hsh.script_ge
          omega
        · exact FitsLen.of_le (fits_of hOk.fits_script) (by omega)
        · apply FitsLen.of_le (fits_of hOk.fits_control)
          have hL := hOk.ladder
          unfold tierR at hL ⊢
          omega
      holeLt := by
        simpa [openModelAt, openModel, entryModel, hm.ladder0, hm.R] using entry_hole_lt t hOk hR
      parkLt := by simpa [openModelAt, openModel, entryModel] using entry_park_lt t sat
      parkNe := by
        simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R, climbAt]
        omega
      parkLe := by
        have hpark : (openModelAt t xs lay.ctrl lay.high).parkAt ≤ tallyOrigin t := by
          simp [openModelAt, openModel, entryModel]
          unfold tallyOrigin
          omega
        simpa [openModelAt] using Nat.le_trans hpark (Nat.le_max_right _ _)
      parkIn := by
        simp [openModelAt, openModel, entryModel, hm.control]
        have h := origin_lt t sat
        unfold tallyOrigin at h
        omega
      parkCell := by
        intro _
        simpa [openModelAt, openModel, entryModel] using
          entry_park_cell t (entry_park_lt t sat)
      fromIdle := by
        intro _
        simp [openModelAt, openModel, entryModel]
      fromNat := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      srcOk := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      parkHeld := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      nextRung := by
        intro r rs hrest
        simpa [openModelAt, openModel, entryModel, hm.ladder0, hm.R] using
          entry_nextRung t hOk hR r rs hrest
      ladderTail := by
        intro k hk hlt
        simpa [openModelAt, openModel, entryModel, hm.ladder0, hm.R] using
          entry_ladderTail t hOk k hk
      fit2 := by
        rw [show (openModelAt t xs lay.ctrl lay.high).ctrl = lay.ctrl + 1 from rfl]
        apply FitsLen.of_le base.fitCtrl
        rw [hm.ctrl0, hm.R, hm.mMax]
        refine Nat.add_le_add_left ?_ (lay.ctrl + 1)
        have h5 : 2 ≤ 3 * rowRoom t + 5 :=
          Nat.le_trans (by decide : (2 : Nat) ≤ 5) (Nat.le_add_left 5 _)
        have hx : 3 * rowRoom t + 5 = 1 * (3 * rowRoom t + 5) := (Nat.one_mul _).symm
        have hmul : 1 * (3 * rowRoom t + 5) ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le (tierR t)))
        exact Nat.le_trans h5 (Nat.le_trans (Nat.le_of_eq hx) hmul)
      fit4 := by
        rw [show (openModelAt t xs lay.ctrl lay.high).ctrl = lay.ctrl + 1 from rfl]
        apply FitsLen.of_le base.fitCtrl
        rw [hm.ctrl0, hm.R, hm.mMax]
        have hL : (lay.ctrl + 1 + 2) + 2 = (lay.ctrl + 1) + 4 := by omega
        rw [hL]
        refine Nat.add_le_add_left ?_ (lay.ctrl + 1)
        have h5 : 4 ≤ 3 * rowRoom t + 5 :=
          Nat.le_trans (by decide : (4 : Nat) ≤ 5) (Nat.le_add_left 5 _)
        have hx : 3 * rowRoom t + 5 = 1 * (3 * rowRoom t + 5) := (Nat.one_mul _).symm
        have hmul : 1 * (3 * rowRoom t + 5) ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le (tierR t)))
        exact Nat.le_trans h5 (Nat.le_trans (Nat.le_of_eq hx) hmul)
      fitI := by
        simp only [openModelAt, openModel, entryModel]
        unfold FitsLen i64MaxNat
        decide
      l0pos := by
        rw [hm.ladder0]
        have hsg := hsh.script_ge
        omega
      fitL0 := FitsLen.of_le (fits_of hOk.fits_script) (by
        rw [hm.ladder0]
        omega)
      fitLR := by
        apply FitsLen.of_le (fits_of hOk.fits_control)
        rw [hm.ladder0, hm.R]
        have hL := hOk.ladder
        unfold tierR at hL ⊢
        omega }
  have hpeg : PegRead bT (openModelAt t xs lay.ctrl lay.high) base :=
    { opsGt := by
        have hsz : bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hops, Array.size_set]
        rw [hsz]
        exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_of_lt lay.ops2)
      cOps := by
        have hi : 1 < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          have hsz : bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hops, Array.size_set]
          rw [hsz]
          exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_of_lt lay.ops2)
        obtain ⟨c, hc, _⟩ := hopsSlot 1 hi
        exact ⟨c, by simpa [ofNat_eq_natCast] using hc⟩
      peakS := ⟨lay.peakS, by simpa [ofNat_eq_natCast] using hstrict⟩
      holeM := ⟨lay.hole, by simpa [ofNat_eq_natCast] using hhole⟩
      trits := by simpa [openModelAt, openModel, entryModel] using lay.tri
      top := by
        intro _
        have hend : (openModelAt t xs lay.ctrl lay.high).t0 +
            (openModelAt t xs lay.ctrl lay.high).tally - 1 = tallyOrigin t := by
          simp [openModelAt, openModel, entryModel]
        rw [hend]
        simpa [openModelAt] using Nat.le_max_right lay.high (tallyOrigin t)
      fitRow := by
        simp only [openModelAt, openModel, entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have h := origin_lt t sat
        omega
      fitTall := by
        simp only [openModelAt, openModel, entryModel]
        unfold FitsLen i64MaxNat
        decide
      fitCtrl := by
        rw [show (openModelAt t xs lay.ctrl lay.high).ctrl = lay.ctrl + 1 from rfl,
          show (openModelAt t xs lay.ctrl lay.high).tally = 1 from rfl]
        apply FitsLen.of_le base.fitCtrl
        rw [hm.ctrl0, hm.R, hm.mMax]
        refine Nat.add_le_add_left ?_ (lay.ctrl + 1)
        have h1 : 1 ≤ 3 * rowRoom t + 5 :=
          Nat.le_trans (by decide : (1 : Nat) ≤ 5) (Nat.le_add_left 5 _)
        have hx : 3 * rowRoom t + 5 = 1 * (3 * rowRoom t + 5) := (Nat.one_mul _).symm
        have hmul : 1 * (3 * rowRoom t + 5) ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le (tierR t)))
        exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq hx) hmul)
      n_pos := by simpa [openModelAt, openModel, entryModel] using hOk.n_pos
      span := by simpa [openModelAt, openModel, entryModel, hm.cg] using sat.cube_span
      small := by simpa [hm.w, hm.h, hm.r] using hsh.small
      n_small := by simpa [openModelAt, openModel, entryModel] using hsh.n_small
      fitN := by
        simp only [openModelAt, openModel, entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega)
      fitBn := by
        simp only [openModelAt, openModel, entryModel]
        exact FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) hsh.small.2.2.2
      fit3 := by
        simp only [openModelAt, openModel, entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega) }
  have hszOps : bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hops, Array.size_set]
  have h2Ops : 2 < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszOps]; exact lay.ops2
  refine ⟨bT, hdo, hlad, ?_, h2Ops, hszOps⟩
  exact
    { inv := hInv
      idx := by simp [openModelAt, openModel, entryModel]
      hn := by simp [openModelAt, openModel, entryModel, hm.n]
      hbench := by simp [openModelAt, openModel, entryModel, hm.bench]
      htally0 := by simp [openModelAt, openModel, entryModel, hm.tally0, climbTallyPrefix]
      kLe := by
        simp [hm.R]
        unfold tierClimb tierR
        rw [List.length_reverse]
        exact Nat.le_refl _
      shape :=
        { spareH := by rw [hszH]; decide
          spareD := by rw [hszD]; decide
          spareE := h6e (by rw [hszD]; decide)
          h7 := by rw [hszD]; decide
          gapClear := by
            intro h
            simp [openModelAt, openModel, entryModel] at h
          offWhenHome := fun _ => hbench
          xD := by rw [hm.xHome, hszD]; decide
          xH := by rw [hm.xHome, hszH]; decide
          xHeld := by simpa [hm.xHome] using h2t (by rw [hszD]; decide)
          xArr := by simpa [hm.x, hm.xHome] using h2a (by rw [hszH]; decide)
          xNe5 := by simp [hm.xHome]
          xNe6 := by simp [hm.xHome]
          gapLen := by simpa [openModelAt, openModel, entryModel, lay.len]
          seg := by simpa [openModelAt, openModel, entryModel] using entry_seg t sat hR
          tierN := by
            rw [htier]
            simp [embTier, openModelAt, openModel, entryModel, ofNat_eq_natCast]
          tierK := by
            rw [htier]
            simp [embTier, openModelAt, openModel, entryModel, ofNat_eq_natCast]
          tierB := by
            rw [htier]
            simp [embTier, openModelAt, openModel, entryModel, hm.bench, ofNat_eq_natCast]
          tierW := by rw [htier]; simp [embTier, hm.w, ofNat_eq_natCast]
          tierH := by rw [htier]; simp [embTier, hm.h, ofNat_eq_natCast]
          tierR := by rw [htier]; simp [embTier, hm.r, ofNat_eq_natCast]
          tierCg := by rw [htier]; simp [embTier, hm.cg, ofNat_eq_natCast]
          tierC := by rw [htier]; simp [embTier, hm.control, ofNat_eq_natCast]
          rowLen := by simp [openModelAt, openModel, entryModel, hm.control, entry_row_len]
          w0 := by simpa [hm.w] using hsh.w0
          h0 := by simpa [hm.h] using hsh.h0
          r0 := by simpa [hm.r] using hsh.r0
          rlt := by simpa [hm.r, hm.h] using hsh.rlt
          n_eq := by simpa [openModelAt, openModel, entryModel, hm.w, hm.h] using hsh.n_eq
          k_le := by simpa [openModelAt, openModel, entryModel] using hsh.k_le
          gap_eq := by simpa [openModelAt, openModel, entryModel, hm.w, hm.r] using hsh.gap
          side :=
            { h0H := by rw [hszH]; decide
              h0D := by rw [hszD]; decide
              h1H := by rw [hszH]; decide
              h1D := by rw [hszD]; decide
              h4H := by rw [hszH]; decide
              h4D := by rw [hszD]; decide
              home0 := by simpa [hm.side0] using h0a (by rw [hszH]; decide)
              held0 := by simpa [hm.held0] using h0t (by rw [hszD]; decide)
              home1 := by simpa [hm.side1] using h1a (by rw [hszH]; decide)
              held1 := by simpa [hm.held1] using h1t (by rw [hszD]; decide)
              home4 := by simpa [hm.side4] using h4a (by rw [hszH]; decide)
              held4 := by simpa [hm.held4] using h4t (by rw [hszD]; decide)
              h3H := by rw [hszH]; decide
              h3D := by rw [hszD]; decide
              home3 := by simpa [hm.base3] using h3a (by rw [hszH]; decide)
              held3 := by simpa [hm.held3] using h3t (by rw [hszD]; decide) }
          quiet :=
            { szH := hszH
              szD := hszD
              tier := htier.trans hm.tierSnap.symm
              marker := hmarkIx.trans (lay.hmark.trans hm.markSnap.symm)
              mx := hmxT.trans (lay.hmx.trans hm.mxSnap.symm) }
          park := hparkR
          peg := hpeg }
      moves := ⟨lay.moves + pegCount xs, by rw [hmv, ofNat_eq_natCast], by
        rw [show (openModelAt t xs lay.ctrl lay.high).onBench = false from rfl, hm.moves0]
        simp⟩
      slides := ⟨lay.slides, by rw [hsl, ofNat_eq_natCast], by
        rw [show (openModelAt t xs lay.ctrl lay.high).onBench = false from rfl, hm.slides0]
        simp⟩
      ops := by
        intro i hi
        obtain ⟨c, hc, hle⟩ := hopsSlot i hi
        refine ⟨c, hc, ?_⟩
        rw [show (openModelAt t xs lay.ctrl lay.high).onBench = false from rfl, hm.ops0]
        simpa using hle
      peak := ⟨base.peak0, by rw [hpk, ← hm.peak0, ofNat_eq_natCast],
        Nat.le_max_left _ _⟩
      highTop := by
        simp [openModelAt, openModel, entryModel, hm.high0]
      parkBelow := by
        simp [openModelAt, openModel, entryModel]
        unfold tallyOrigin
        omega
      holeBelow := by
        simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R, climbAt]
        unfold tallyOrigin
        omega
      fromBelow := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      finalLe := by
        simpa [openModelAt, openModel, entryModel, hm.tally0] using climbTally_ge 1 (tierClimb t)
      tailFit := by
        have hpre : tallyPrefixesLe 1 (rowRoom t) (tierClimb t ++ []) = true := by
          simpa using sat.prefixes
        have hct : climbTally 1 (tierClimb t) ≤ rowRoom t := by
          rw [← climbTallyPrefix_full]
          exact tallyPrefixesLe_spec 1 (rowRoom t) (tierClimb t) [] hpre
        have ht0m : (openModelAt t xs lay.ctrl lay.high).t0 = tallyOrigin t := rfl
        have hrowL : (openModelAt t xs lay.ctrl lay.high).row.length = t.control := by
          simp [openModelAt, openModel, entryModel, entry_row_len]
        rw [ht0m, hrowL, hm.tally0, List.nil_append]
        have hor := sat.origin_le
        unfold rowRoom at hct
        omega
      tailZero := by
        intro k hk1 _ hix
        have hlt : tallyOrigin t < tallyOrigin t + k := by
          simp [openModelAt, openModel, entryModel] at hk1
          omega
        simpa [openModelAt, openModel, entryModel] using entry_past t (tallyOrigin t + k) hlt hix
      openRoom := by
        intro h2
        have hroom := entry_double_room t sat h2
        simpa [openModelAt, openModel, entryModel, hm.control] using hroom
      openZero := by
        intro _ k hk hix
        have hk0 : k = 0 := by
          simp [openModelAt, openModel, entryModel] at hk
          omega
        subst hk0
        have hix' : tallyOrigin t + 1 < (entryRow t).length := by
          simpa [openModelAt, openModel, entryModel] using hix
        have hpast := entry_past t (tallyOrigin t + 1) (by omega) hix'
        simpa [openModelAt, openModel, entryModel] using hpast
      tmaxLt := ⟨max lay.tmax 1, by simpa [ofNat_eq_natCast] using htmax⟩
      ctrlLe := by
        simp [openModelAt, openModel, entryModel, hm.ctrl0]
      srcAbove := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      parkEq := by simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R]
      origin := by
        simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R]
        unfold tallyOrigin
        omega
      fromNePark := by
        intro h
        simp [openModelAt, openModel, entryModel] at h
      rowHome := by
        simpa [openModelAt, openModel, entryModel, hm.baseRow] using entry_row_home t sat
      blankTail := by
        intro j hj hix
        have hgt : tallyOrigin t < j := by
          simpa [openModelAt, openModel, entryModel] using hj
        have hpast := entry_past t j hgt
          (by simpa [openModelAt, openModel, entryModel] using hix)
        simpa [openModelAt, openModel, entryModel] using hpast }

/-- `Ecbs.invert` on an open walk board is the climb of that tally board. -/
theorem open_invert (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base) :
    ∃ bT,
      Ecbs.invert b ((2 : Nat) : Int) =
        climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) >>= finalTail ∧
      ClimbInvK [] (tierClimb t) bT (openModelAt t xs lay.ctrl lay.high) base ∧
      bT.sudo_5Board_6ladder = embed (tierClimb t) ∧
      2 < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      bT.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  obtain ⟨bT, hdo, hlad, hK, h2, hsz⟩ := open_climb b t xs lay hOk sat hR hsh base hm
  let hL : ClimbInvL (tierClimb t) 0 bT base :=
    { done := []
      rest := tierClimb t
      s := openModelAt t xs lay.ctrl lay.high
      split := by simp
      k_eq := rfl
      inv := hK
      ladder := hlad
      m_pos := by simp [openModelAt, openModel, entryModel]
      m_le := by
        rw [show (openModelAt t xs lay.ctrl lay.high).tally = 1 from rfl, hm.control]
        have hC := hOk.ladder
        unfold tierR at hC
        omega
      m_len := by simpa [ofNat_eq_natCast] using hK.inv.len }
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  have hpark : hL.s.parkAt = base.ladder0 + base.R := by
    simp [hL, openModelAt, openModel, entryModel, hm.ladder0, hm.R]
  have hcap : ∀ done rest, tierClimb t = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax := by
    intro done rest hsplit
    simpa [hm.tally0, hm.mMax] using
      tallyPrefixesLe_spec 1 (rowRoom t) done rest (by simpa [hsplit] using sat.prefixes)
  have hxLen : base.x.length = base.n := by rw [hm.x, hm.n, lay.len]
  have hxT : allTritList base.x := by simpa [hm.x] using lay.tri
  have hfitL : FitsLen (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using tierR_fit t hOk
  have hloop := invertWith_on_inv hL hpos hfitL hpark hcap hxLen hxT
  rw [hm.xHome] at hloop
  refine ⟨bT, ?_, hK, hlad, h2, hsz⟩
  rw [invert_steps b ((2 : Nat) : Int), invertWith_named_loop b ((2 : Nat) : Int)]
  suffices
      (do
        let b ← (do
          let b ← (do
            let ix := Ecbs.op_inv
            let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
            let t2 ← SudoRt.addI t1 (1 : Int)
            let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
            pure ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } } : Ecbs.Board))
          let b ← Ecbs.copy_band b Ecbs.gap ((2 : Nat) : Int) false
          Ecbs.tally_start b)
        let nr := SudoRt.listLen b.sudo_5Board_6ladder
        let toV ← SudoRt.subI nr (1 : Int)
        let fromV := (0 : Int)
        let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel
          (invertIdx ((2 : Nat) : Int) nr toV)
          (fun σ => finalTail σ.2)
          (fun r => pure r)
        pure out) =
        climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) >>= finalTail by
    simpa using this
  rw [hdo, ok_bind]
  exact hloop

/-- Home 5 after `invert` on an open walk board is `invGap` of the bottom. -/
theorem open_invGap (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base) :
    ∃ (bZ : Ecbs.Board) (h5 : 5 < bZ.sudo_5Board_4home.size),
      Ecbs.invert b ((2 : Nat) : Int) = .ok bZ ∧
      bZ.sudo_5Board_4home[5]'h5 = embed (invGap t.n t.k t.benchlen xs) := by
  obtain ⟨bT, hem, hK, _hladT, _h2T, _hszT⟩ := open_invert b t xs lay hOk sat hR hsh base hm
  have hpark : (openModelAt t xs lay.ctrl lay.high).parkAt = base.ladder0 + base.R := by
    simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R]
  have hm0 : 0 < (openModelAt t xs lay.ctrl lay.high).tally := by simp [openModelAt, openModel, entryModel]
  have hcap : ∀ done rest, tierClimb t = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax := by
    intro done rest hsplit
    simpa [hm.tally0, hm.mMax] using
      tallyPrefixesLe_spec 1 (rowRoom t) done rest (by simpa [hsplit] using sat.prefixes)
  have hxLen : base.x.length = base.n := by rw [hm.x, hm.n, lay.len]
  have hxT : allTritList base.x := by simpa [hm.x] using lay.tri
  obtain ⟨b', s', hrun, hs', hK', hgap, htmax, _hszClimb⟩ := climb_refines_emit (tierClimb t)
      bT (openModelAt t xs lay.ctrl lay.high) base hK hpark hm0 hcap hxLen hxT
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  cases hL : tierClimb t with
  | nil => simp [hL] at hpos
  | cons r rs =>
      let hole : ClimbModel → Nat → Bool → Nat := fun s _ _ =>
        climbAt base.ladder0 base.R s.ridx
      have hon : s'.onBench = true := by
        rw [hs', hL]
        exact modelClimb_onBench (openModelAt t xs lay.ctrl lay.high) base.x hole r rs
      have hge : 0 ≤ s'.fromHole := by
        rw [hs', hL]
        exact modelClimb_fromHole (openModelAt t xs lay.ctrl lay.high) base.x hole r rs
      have hmt : 0 < s'.tally := by
        rw [hs', modelClimb_tally]
        simp [openModelAt, openModel, entryModel]
        exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) (climbTally_ge 1 (tierClimb t))
      obtain ⟨bU, bC, bOut, bZ, hun, hc, hset, hz, hhome⟩ :=
        final_cube_home hK' hon hge htmax hmt
      have hrun' : climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) = .ok b' := by
        simpa [hm.xHome] using hrun
      have hok : Ecbs.invert b ((2 : Nat) : Int) = .ok bZ := by
        rw [hem, hrun', ok_bind]
        simp [finalTail, hun, hc, hset, hz, ok_bind]
      have hlay := modelClimb_params (openModelAt t xs lay.ctrl lay.high) base.x hole (tierClimb t)
      have hpair : (s'.gap, s'.tally) =
          invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) := by
        simpa [openModelAt, openModel, entryModel, hm.n, hm.bench, hm.x, lay.len] using hgap
      have hgap1 : s'.gap = (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 :=
        congrArg Prod.fst hpair
      have hn : s'.n = t.n := by
        rw [hs']
        simpa [openModelAt, openModel, entryModel] using hlay.1
      have hk : s'.k = t.k := by
        rw [hs']
        simpa [openModelAt, openModel, entryModel] using hlay.2.1
      have hb : s'.benchlen = t.benchlen := by
        rw [hs']
        simpa [openModelAt, openModel, entryModel] using hlay.2.2
      refine ⟨bZ, hhome.h5, hok, ?_⟩
      refine hhome.arr.trans (congrArg embed ?_)
      rw [hn, hk, hb, hgap1]
      exact (invGap_cube t xs).symm

/-- Counters and the quiet frame on the board the check leaves. Homes 0, 1, 2,
    4, and 5 are exported beside this. The move counter is the one
    `bench_read_and_clear` stores, already a natural in the frame above. -/
structure RiseCarry (b : Ecbs.Board) (t : Spec.Tier) (mark mx : Nat) : Prop where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  tier : b.sudo_5Board_1t = embTier t
  marker : b.sudo_5Board_6marker = Int.ofNat mark
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  benchOff : b.sudo_5Board_8bench_on = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  moves : ∃ mv : Nat, b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)
  slides : ∃ sl : Nat, b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int)
  ctrl : ∃ c : Nat, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c : Int)
  peak : ∃ pk : Nat, b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int)
  peakS : ∃ p : Nat, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  hole : ∃ h : Nat, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (h : Int)
  opsGt : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : ∃ c : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'opsGt = (c : Int)

private theorem modelClimb_t0 (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (L : List Nat) :
    (modelClimb s x hole L).t0 = s.t0 := by
  induction L generalizing s with
  | nil => rfl
  | cons _ _ ih =>
    rw [modelClimb]
    simpa [modelRung] using ih _

/-- Reading `j` through a set at `i1` and then a set at `i0`, when neither
    index is `j`. The index proof on the outer set is the one `arr_set_congr`
    builds, so the equality can be `cell_eq_of` without rewriting under `set`. -/
private theorem ops_get_set2 (a : Array Int) (j : Nat) (hj : j < a.size)
    (i1 : Nat) (hi1 : i1 < a.size) (v1 : Int)
    (i0 : Nat) (hi0 : i0 < (a.set ⟨i1, hi1⟩ v1).size) (v0 : Int)
    (hne0 : i0 ≠ j) (hne1 : i1 ≠ j) :
    ((a.set ⟨i1, hi1⟩ v1).set ⟨i0, hi0⟩ v0)[j]'(by
      rw [Array.size_set, Array.size_set]; exact hj) = a[j] := by
  rw [Array.getElem_set_ne (h := hne0), Array.getElem_set_ne (h := hne1)]

/-- Every ops slot on the checked board is a natural. Slots 2 and 3 keep a
    spare step under `cap`; every other slot is at most `cap`. -/
def CheckedOps (b : Ecbs.Board) (cap : Nat) : Prop :=
  ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ c, b.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = Int.ofNat c ∧
      (if i = 2 then c + 1 else if i = 3 then c + 1 else c) ≤ cap

/-- The check multiply on the board `open_invert` leaves. Home 5 is `invGap`,
    home 2 is still the input, and the bench prefix is their product. -/
theorem open_check_mul (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base) :
    ∃ (bZ bM bR : Ecbs.Board) (v : Array Int) (h5 : 5 < bR.sudo_5Board_4home.size),
      Ecbs.invert b ((2 : Nat) : Int) = .ok bZ ∧
      Ecbs.mul bZ Ecbs.check_target Ecbs.gap ((2 : Nat) : Int) true false false = .ok bM ∧
      Ecbs.bench_read_and_clear bM = .ok (v, bR) ∧
      v = embed (fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen xs) xs) ∧
      bR.sudo_5Board_4home[5]'h5 = embed (invGap t.n t.k t.benchlen xs) ∧
      bR.sudo_5Board_8bench_on = false ∧
      (∃ (h5D : 5 < bR.sudo_5Board_4held.size) (mv : Nat),
        bR.sudo_5Board_4held[5]'h5D = true ∧
        bR.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        FitsLen (mv + t.n) ∧
        bR.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int)) ∧
      (∀ h2 : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] = embed xs) ∧
      (∀ h2 : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] = true) ∧
      (∀ h0 : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] = embed lay.side0) ∧
      (∀ h0 : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] = lay.flag0) ∧
      (∀ h1 : 1 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[1] = embed lay.side1) ∧
      (∀ h1 : 1 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[1] = lay.flag1) ∧
      (∀ h4 : 4 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[4] = embed lay.side4) ∧
      (∀ h4 : 4 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[4] = lay.flag4) ∧
      RiseCarry bR t lay.mark lay.mx ∧
      CheckBound bR base ∧
      (∃ mv : Nat, bR.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        mv + t.n ≤ checkMoveCap base) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      (∃ high : Nat,
        bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) ∧
        tallyOrigin t ≤ high) ∧
      bR.sudo_5Board_3row = embed (paintedRow t) ∧
      bR.sudo_5Board_6ladder = embed (tierClimb t) ∧
      (∀ h3 : 3 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[3] = embed lay.base3) ∧
      (∀ h3 : 3 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[3] = lay.flag3) ∧
      bR.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) ∧
      bR.sudo_5Board_6nrungs = Int.ofNat (tierR t) ∧
      bR.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) ∧
      bR.sudo_5Board_11parked_from = -1 ∧
      bR.sudo_5Board_8rung_idx = 0 ∧
      bR.sudo_5Board_9tally_len = 0 ∧
      bR.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) ∧
      (∃ tmax : Nat, bR.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int)) ∧
      (∃ (h2 : 2 < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c2 : Nat),
        bR.sudo_5Board_4cost.sudo_5Costs_3ops[2]'h2 = (c2 : Int) ∧
        c2 + 1 ≤ checkOpsCap base + 3) ∧
      (3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size →
        ∃ (h3 : 3 < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c3 : Nat),
          bR.sudo_5Board_4cost.sudo_5Costs_3ops[3]'h3 = (c3 : Int) ∧
          c3 + 1 ≤ checkOpsCap base + 3) ∧
      CheckedOps bR (checkOpsCap base + 3) := by
  obtain ⟨bT, hem, hK, hladT, h2T, hszT⟩ := open_invert b t xs lay hOk sat hR hsh base hm
  have hpark : (openModelAt t xs lay.ctrl lay.high).parkAt = base.ladder0 + base.R := by
    simp [openModelAt, openModel, entryModel, hm.ladder0, hm.R]
  have hm0 : 0 < (openModelAt t xs lay.ctrl lay.high).tally := by simp [openModelAt, openModel, entryModel]
  have hcap : ∀ done rest, tierClimb t = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax := by
    intro done rest hsplit
    simpa [hm.tally0, hm.mMax] using
      tallyPrefixesLe_spec 1 (rowRoom t) done rest (by simpa [hsplit] using sat.prefixes)
  have hxLen : base.x.length = base.n := by rw [hm.x, hm.n, lay.len]
  have hxT : allTritList base.x := by simpa [hm.x] using lay.tri
  obtain ⟨b', s', hrun, hs', hKpost, hgap, htmax, hszClimb⟩ := climb_refines_emit (tierClimb t)
      bT (openModelAt t xs lay.ctrl lay.high) base hK hpark hm0 hcap hxLen hxT
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  cases hLc : tierClimb t with
  | nil => simp [hLc] at hpos
  | cons r rs =>
      let hole : ClimbModel → Nat → Bool → Nat := fun s _ _ =>
        climbAt base.ladder0 base.R s.ridx
      have hon : s'.onBench = true := by
        rw [hs', hLc]
        exact modelClimb_onBench (openModelAt t xs lay.ctrl lay.high) base.x hole r rs
      have hge : 0 ≤ s'.fromHole := by
        rw [hs', hLc]
        exact modelClimb_fromHole (openModelAt t xs lay.ctrl lay.high) base.x hole r rs
      have hmt : 0 < s'.tally := by
        rw [hs', modelClimb_tally]
        simp [openModelAt, openModel, entryModel]
        exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) (climbTally_ge 1 (tierClimb t))
      obtain ⟨bU, bC, bOut, bZ, hun, hc, hset, hz, hsg, hread, hsideZ, hquietZ, hbound, hhighZ,
          _hrowZ⟩ :=
        final_cube_both hKpost hon hge htmax hmt
      have hrun' : climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) =
          .ok b' := by simpa [hm.xHome] using hrun
      have hok : Ecbs.invert b ((2 : Nat) : Int) = .ok bZ := by
        rw [hem, hrun', ok_bind]
        simp [finalTail, hun, hc, hset, hz, ok_bind]
      have hlayp := modelClimb_params (openModelAt t xs lay.ctrl lay.high) base.x hole (tierClimb t)
      have hn : s'.n = t.n := by rw [hs']; simpa [openModelAt, openModel, entryModel] using hlayp.1
      have hkS : s'.k = t.k := by rw [hs']; simpa [openModelAt, openModel, entryModel] using hlayp.2.1
      have hbL : s'.benchlen = t.benchlen := by
        rw [hs']; simpa [openModelAt, openModel, entryModel] using hlayp.2.2
      have hpair : (s'.gap, s'.tally) =
          invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) := by
        simpa [openModelAt, openModel, entryModel, hm.n, hm.bench, hm.x] using hgap
      have hgap1 : s'.gap =
          (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 :=
        congrArg Prod.fst hpair
      have hcube : fieldCube s'.n s'.k s'.benchlen s'.gap =
          invGap t.n t.k t.benchlen xs := by
        rw [hn, hkS, hbL, hgap1]
        exact (invGap_cube t xs).symm
      have hArr : bZ.sudo_5Board_4home[5]'hsg.h5 = embed (invGap t.n t.k t.benchlen xs) :=
        hsg.arr.trans (congrArg embed hcube)
      let mv := hread.moves.choose
      have hmv := hread.moves.choose_spec
      let pk := hread.peak.choose
      have hpk := hread.peak.choose_spec
      let pS := hread.peakS.choose
      have hpS := hread.peakS.choose_spec
      let cOps := hread.ops0.choose
      have hcOps := hread.ops0.choose_spec
      let holeN := hread.hole.choose
      have hholeN := hread.hole.choose_spec
      let mvB := hread.fitMul.choose
      have hB1 := hread.fitMul.choose_spec
      let nB := hB1.choose
      have hB2 := hB1.choose_spec
      let benchB := hB2.choose
      have hB3 := hB2.choose_spec
      have hmvB : bZ.sudo_5Board_4cost.sudo_5Costs_5moves = (mvB : Int) := hB3.1
      have hnB : bZ.sudo_5Board_1t.sudo_4Tier_1n = (nB : Int) := hB3.2.1
      have hbB : bZ.sudo_5Board_1t.sudo_4Tier_8benchlen = (benchB : Int) := hB3.2.2.1
      have hfitB : FitsLen (mvB + nB + nB * (nB + 1) + 3 * (benchB - nB) + 2 * nB) :=
        hB3.2.2.2
      have hmvEq : mv = mvB := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        exact hmv.symm.trans hmvB
      have hnEq : nB = t.n := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        have htn : bZ.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
          rw [hread.tierEq, hKpost.shape.tierN, hn]
        exact hnB.symm.trans htn
      have hbEq : benchB = t.benchlen := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        have htb : bZ.sudo_5Board_1t.sudo_4Tier_8benchlen = (t.benchlen : Int) := by
          rw [hread.tierEq, hKpost.shape.tierB, hbL]
        exact hbB.symm.trans htb
      have hfitBig : FitsLen (mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) +
          2 * t.n) := by
        rw [← hmvEq, hnEq, hbEq] at hfitB
        exact hfitB
      have h2Z : bZ.sudo_5Board_4home[2]'hread.h2H = embed xs := by
        have hhome : b'.sudo_5Board_4home[2]'hread.h2H0 = embed xs := by
          simpa [hm.x, hm.xHome] using hKpost.shape.xArr
        exact hread.home2.trans hhome
      have h2tZ : bZ.sudo_5Board_4held[2]'hread.h2D = true := by
        have hheldZ : b'.sudo_5Board_4held[2]'hread.h2D0 = true := by
          simpa [hm.xHome] using hKpost.shape.xHeld
        exact hread.held2.trans hheldZ
      have hmul := mul_refines bZ 7 5 2 (invGap t.n t.k t.benchlen xs) xs
          t.w t.h t.r t.n t.k mv holeN t.benchlen pk pS cOps
          hread.marker hread.benchOff hread.opsGt hcOps.1 hcOps.2
          (by rw [hread.tierEq]; simpa [hbL] using hKpost.shape.tierB)
          hread.h5D hsg.h5 hread.held5 hArr
          hread.h2D hread.h2H
          (by
            have hheld : b'.sudo_5Board_4held[2]'hread.h2D0 = true := by
              simpa [hm.xHome] using hKpost.shape.xHeld
            exact hread.held2.trans hheld)
          (by
            have hhome : b'.sudo_5Board_4home[2]'hread.h2H0 = embed xs := by
              simpa [hm.x, hm.xHome] using hKpost.shape.xArr
            exact hread.home2.trans hhome)
          hread.spareD hread.spareH hread.spareE hread.h7
          (by decide) (by decide)
          (by simpa [hn] using hKpost.shape.peg.n_pos)
          (by rw [hread.tierEq]; simpa [hn] using hKpost.shape.tierN)
          (by
            rw [invGap_cube]
            exact fieldCube_length t.n t.k t.benchlen
              (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1
              (by
                have hs := sat.mul_span
                omega))
          lay.len
          (by simpa [hn] using hKpost.shape.peg.fitN)
          hmv hpk hpS
          (by
            have hpeg : pegCount xs ≤ t.n := by
              rw [← lay.len]
              exact pegCount_le xs
            apply FitsLen.of_le hfitBig
            calc
              mv + pegCount xs ≤ mv + t.n := Nat.add_le_add_left hpeg mv
              _ ≤ mv + t.n + t.n * (t.n + 1) := Nat.le_add_right _ _
              _ ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) :=
                Nat.le_add_right _ _
              _ ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n :=
                Nat.le_add_right _ _)
          sat.mul_span
          (by
            have hsp : 3 * (s'.n - 1) < s'.benchlen := by
              have hs := hKpost.shape.peg.span
              omega
            have htriG := fieldCube_trits s'.n s'.k s'.benchlen s'.gap
              hKpost.shape.peg.trits hsp hKpost.shape.k_le
            rw [hcube] at htriG
            exact htriG)
          (by
            apply FitsLen.of_le (by simpa [hn] using hKpost.shape.peg.fit3)
            have h23 : 2 * (t.n - 1) ≤ 3 * (t.n - 1) :=
              Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)
            simpa [hn] using h23)
          (by
            have hpeg : pegCount xs ≤ t.n := by
              rw [← lay.len]
              exact pegCount_le xs
            apply FitsLen.of_le hfitBig
            calc
              mv + pegCount xs + t.n * (t.n + 1)
                  ≤ mv + t.n + t.n * (t.n + 1) :=
                Nat.add_le_add_right (Nat.add_le_add_left hpeg mv) _
              _ ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) :=
                Nat.le_add_right _ _
              _ ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n :=
                Nat.le_add_right _ _)
          ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
          (by
            have h1 : bZ.sudo_5Board_1t.sudo_4Tier_1w =
                b'.sudo_5Board_1t.sudo_4Tier_1w := by rw [hread.tierEq]
            exact h1.trans (hKpost.shape.tierW.trans
              (congrArg (fun n : Nat => (n : Int)) hm.w)))
          (by
            have h1 : bZ.sudo_5Board_1t.sudo_4Tier_1h =
                b'.sudo_5Board_1t.sudo_4Tier_1h := by rw [hread.tierEq]
            exact h1.trans (hKpost.shape.tierH.trans
              (congrArg (fun n : Nat => (n : Int)) hm.h)))
          (by
            have h1 : bZ.sudo_5Board_1t.sudo_4Tier_1r =
                b'.sudo_5Board_1t.sudo_4Tier_1r := by rw [hread.tierEq]
            exact h1.trans (hKpost.shape.tierR.trans
              (congrArg (fun n : Nat => (n : Int)) hm.r)))
          (by rw [hread.tierEq]; simpa [hkS] using hKpost.shape.tierK)
          (by rw [hholeN, ofNat_eq_natCast])
          (by simpa [hbL, hm.w, hm.h, hm.r] using hKpost.shape.peg.small)
          (by simpa [hn] using hKpost.shape.peg.n_small)
          (by simpa [hbL] using hKpost.shape.peg.fitBn)
          (by
            have hpeg : pegCount xs ≤ t.n := by
              rw [← lay.len]
              exact pegCount_le xs
            apply FitsLen.of_le hfitBig
            calc
              mv + pegCount xs + t.n * (t.n + 1) + 3 * (t.benchlen - t.n)
                  ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) :=
                Nat.add_le_add_right
                  (Nat.add_le_add_right (Nat.add_le_add_left hpeg mv) _) _
              _ ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n :=
                Nat.le_add_right _ _)
      obtain ⟨bM, hmulOk, _hon, _, hbench, htake, hrest⟩ := hmul
      obtain ⟨_, hmov, hpkM, hslM, htM, hsz, hheld, h5keep, hkeep, _hmk, hopsM, hstrictM,
          hholeM, hixM, hcM, hmxM, hhighM, _hrowM, hsc⟩ :=
        hrest
      have h5M : 5 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hsg.h5
      have hhomeM : bM.sudo_5Board_4home[5]'h5M = embed (invGap t.n t.k t.benchlen xs) :=
        (h5keep hsg.h5 h5M).trans hArr
      let gapL := invGap t.n t.k t.benchlen xs
      let lane := laneFold t.n (t.n - t.k)
        (school t.n gapL xs (List.replicate t.benchlen 0) false)
      have htakeL : lane.take t.n = fieldMul t.n t.k t.benchlen gapL xs := by
        simpa [lane, gapL, invGap] using htake
      have hlenSch : (school t.n gapL xs (List.replicate t.benchlen 0) false).length =
          t.benchlen := by rw [school_length, List.length_replicate]
      have hlenL : lane.length = t.benchlen := by
        rw [laneFold_length, hlenSch]
        · rw [hlenSch]
          have hs := sat.mul_span
          omega
      have hnle : t.n ≤ lane.length := by
        rw [hlenL]
        have hs := sat.mul_span
        omega
      have hpref := prefix_refines lane t.n hnle (by simpa [hn] using hKpost.shape.peg.fitN)
      have hszV : (embed (lane.take t.n)).size = t.n := by
        rw [size_embed, List.length_take, hlenL]
        have hs := sat.mul_span
        omega
      have hnp := npeg_refines (embed (lane.take t.n)) (by
        rw [hszV]
        simpa [hn] using hKpost.shape.peg.fitN)
      let mvM := mulMoves mv gapL xs t.n t.k t.benchlen
      have hmvM : bM.sudo_5Board_4cost.sudo_5Costs_5moves = (mvM : Int) := by
        simpa [mvM, gapL, ofNat_eq_natCast] using hmov
      let nz := nnz (embed (lane.take t.n)).toList
      have hnz : nz ≤ t.n := by
        have hle := nnz_length_le (embed (lane.take t.n)).toList
        rw [toList_embed, List.length_map] at hle
        exact Nat.le_trans hle (List.length_take_le t.n lane)
      have hschool : schoolMoves gapL xs t.n t.n ≤ t.n * (t.n + 1) :=
        schoolMoves_bound gapL xs t.n
      have hfoldC : foldCharge t.n (t.n - t.k)
          (school t.n gapL xs (List.replicate t.benchlen 0) false) ≤
          3 * (t.benchlen - t.n) := by
        have hF := foldCharge_bound t.n (t.n - t.k)
          (school t.n gapL xs (List.replicate t.benchlen 0) false)
        rw [hlenSch] at hF
        exact hF
      have hmvLe : mvM + nz ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) +
          2 * t.n := by
        have hdef : mvM = mv + pegCount xs + schoolMoves gapL xs t.n t.n +
            foldCharge t.n (t.n - t.k)
              (school t.n gapL xs (List.replicate t.benchlen 0) false) := rfl
        have hpeg : pegCount xs ≤ t.n := by rw [← lay.len]; exact pegCount_le xs
        omega
      have hfitM : FitsLen (mvM + nz) := FitsLen.of_le hfitBig hmvLe
      have hnT : bM.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
        rw [htM, hread.tierEq, hKpost.shape.tierN, hn]
      let bR := { { bM with sudo_5Board_4cost :=
        { bM.sudo_5Board_4cost with sudo_5Costs_5moves := Int.ofNat (mvM + nz) } }
          with sudo_5Board_8bench_on := false }
      have hreadM : Ecbs.bench_read_and_clear bM = .ok (embed (lane.take t.n), bR) := by
        unfold Ecbs.bench_read_and_clear
        rw [hbench, hnT, ← ofNat_eq_natCast t.n]
        rw [hpref, ok_bind]
        conv => zeta
        rw [hnp, ok_bind]
        conv => zeta
        rw [hmvM, ← ofNat_eq_natCast mvM]
        rw [show nnz (embed (lane.take t.n)).toList = nz from rfl,
          addI_ofNat mvM nz hfitM, ok_bind]
        simp only [pure_eq_ok, bR, hbench]
      have h5R : 5 < bR.sudo_5Board_4home.size := by simpa [bR] using h5M
      have hhomeR : bR.sudo_5Board_4home[5]'h5R = embed gapL := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        exact cell_eq_of hEq hhomeM
      let heldInner := bZ.sudo_5Board_4held.set ⟨6, hread.spareD⟩ true
      let heldClear := heldInner.set ⟨6, by rw [Array.size_set]; exact hread.spareD⟩ false
      have hheldDef : bM.sudo_5Board_4held = heldClear := by
        simpa [heldClear, heldInner] using hheld
      have h5DM : 5 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheldDef
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hread.h5D
      have h5DR : 5 < bR.sudo_5Board_4held.size := by simpa [bR] using h5DM
      have hheldR : bR.sudo_5Board_4held[5]'h5DR = true := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        have hget : heldClear[5]'(by rw [Array.size_set, Array.size_set]; exact hread.h5D) =
            bZ.sudo_5Board_4held[5]'hread.h5D := by
          simp [heldClear, heldInner, Array.getElem_set, show (5 : Nat) ≠ 6 by decide]
        have hM : bM.sudo_5Board_4held[5]'h5DM = true :=
          (cell_eq_of hheldDef hget).trans hread.held5
        exact cell_eq_of hEq hM
      have hmvR : bR.sudo_5Board_4cost.sudo_5Costs_5moves = ((mvM + nz : Nat) : Int) := by
        simp [bR, ofNat_eq_natCast]
      have hfitR : FitsLen (mvM + nz + t.n) := by
        apply FitsLen.of_le hfitBig
        have hdef : mvM = mv + pegCount xs + schoolMoves gapL xs t.n t.n +
            foldCharge t.n (t.n - t.k)
              (school t.n gapL xs (List.replicate t.benchlen 0) false) := rfl
        have hpeg : pegCount xs ≤ t.n := by rw [← lay.len]; exact pegCount_le xs
        omega
      have hnR : bR.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by simp [bR, hnT]
      have h2M : 2 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hread.h2H
      have h2DM : 2 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hread.h2D
      have hhome2M : bM.sudo_5Board_4home[2]'h2M = embed xs :=
        (hkeep 2 hread.h2H h2M (by decide)).trans h2Z
      have hheld2M : bM.sudo_5Board_4held[2]'h2DM = true := by
        have hget : ((bZ.sudo_5Board_4held.set ⟨6, hread.spareD⟩ true).set
            ⟨6, by rw [Array.size_set]; exact hread.spareD⟩ false)[2]'(by
              rw [Array.size_set, Array.size_set]; exact hread.h2D) =
            bZ.sudo_5Board_4held[2]'hread.h2D := by
          simp [Array.getElem_set, show (6 : Nat) ≠ 2 by decide]
        exact (cell_eq_of hheld hget).trans h2tZ
      have h2R : 2 < bR.sudo_5Board_4home.size := by simpa [bR] using h2M
      have h2DR : 2 < bR.sudo_5Board_4held.size := by simpa [bR] using h2DM
      have hhome2R : bR.sudo_5Board_4home[2]'h2R = embed xs := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        exact cell_eq_of hEq hhome2M
      have hheld2R : bR.sudo_5Board_4held[2]'h2DR = true := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        exact cell_eq_of hEq hheld2M
      have h0M : 0 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hsideZ.h0H
      have h1M : 1 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hsideZ.h1H
      have h4M : 4 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hsideZ.h4H
      have h0DM : 0 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hsideZ.h0D
      have h1DM : 1 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hsideZ.h1D
      have h4DM : 4 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hsideZ.h4D
      have hhome0M : bM.sudo_5Board_4home[0]'h0M = embed base.side0 :=
        (hkeep 0 hsideZ.h0H h0M (by decide)).trans hsideZ.home0
      have hhome1M : bM.sudo_5Board_4home[1]'h1M = embed base.side1 :=
        (hkeep 1 hsideZ.h1H h1M (by decide)).trans hsideZ.home1
      have hhome4M : bM.sudo_5Board_4home[4]'h4M = embed base.side4 :=
        (hkeep 4 hsideZ.h4H h4M (by decide)).trans hsideZ.home4
      have heldSide (k : Nat) (hkZ : k < bZ.sudo_5Board_4held.size)
          (hkM : k < bM.sudo_5Board_4held.size) (hne : (6 : Nat) ≠ k)
          {v : Bool} (hv : bZ.sudo_5Board_4held[k]'hkZ = v) :
          bM.sudo_5Board_4held[k]'hkM = v := by
        have hget : ((bZ.sudo_5Board_4held.set ⟨6, hread.spareD⟩ true).set
            ⟨6, by rw [Array.size_set]; exact hread.spareD⟩ false)[k]'(by
              rw [Array.size_set, Array.size_set]; exact hkZ) =
            bZ.sudo_5Board_4held[k]'hkZ := by
          simp [Array.getElem_set, hne]
        exact (cell_eq_of hheld hget).trans hv
      have hheld0M : bM.sudo_5Board_4held[0]'h0DM = base.held0 :=
        heldSide 0 hsideZ.h0D h0DM (by decide) hsideZ.held0
      have hheld1M : bM.sudo_5Board_4held[1]'h1DM = base.held1 :=
        heldSide 1 hsideZ.h1D h1DM (by decide) hsideZ.held1
      have hheld4M : bM.sudo_5Board_4held[4]'h4DM = base.held4 :=
        heldSide 4 hsideZ.h4D h4DM (by decide) hsideZ.held4
      have hhome0R : bR.sudo_5Board_4home[0]'(by simpa [bR] using h0M) = embed lay.side0 := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        simpa [hm.side0] using cell_eq_of hEq hhome0M
      have hhome1R : bR.sudo_5Board_4home[1]'(by simpa [bR] using h1M) = embed lay.side1 := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        simpa [hm.side1] using cell_eq_of hEq hhome1M
      have hhome4R : bR.sudo_5Board_4home[4]'(by simpa [bR] using h4M) = embed lay.side4 := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        simpa [hm.side4] using cell_eq_of hEq hhome4M
      have hheld0R : bR.sudo_5Board_4held[0]'(by simpa [bR] using h0DM) = lay.flag0 := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        simpa [hm.held0] using cell_eq_of hEq hheld0M
      have hheld1R : bR.sudo_5Board_4held[1]'(by simpa [bR] using h1DM) = lay.flag1 := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        simpa [hm.held1] using cell_eq_of hEq hheld1M
      have hheld4R : bR.sudo_5Board_4held[4]'(by simpa [bR] using h4DM) = lay.flag4 := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        simpa [hm.held4] using cell_eq_of hEq hheld4M
      have h3M : 3 < bM.sudo_5Board_4home.size := by rw [hsz]; exact hsideZ.h3H
      have h3DM : 3 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hsideZ.h3D
      have hhome3M : bM.sudo_5Board_4home[3]'h3M = embed base.base3 :=
        (hkeep 3 hsideZ.h3H h3M (by decide)).trans hsideZ.home3
      have hheld3M : bM.sudo_5Board_4held[3]'h3DM = base.held3 :=
        heldSide 3 hsideZ.h3D h3DM (by decide) hsideZ.held3
      have hhome3R : bR.sudo_5Board_4home[3]'(by simpa [bR] using h3M) = embed lay.base3 := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        simpa [hm.base3] using cell_eq_of hEq hhome3M
      have hheld3R : bR.sudo_5Board_4held[3]'(by simpa [bR] using h3DM) = lay.flag3 := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        simpa [hm.held3] using cell_eq_of hEq hheld3M
      have hszHR : bR.sudo_5Board_4home.size = 8 := by
        have hM : bM.sudo_5Board_4home.size = bZ.sudo_5Board_4home.size := hsz
        have hRsz : bR.sudo_5Board_4home.size = bM.sudo_5Board_4home.size := by simp [bR]
        rw [hRsz, hM, hquietZ.szH]
      have hszDR : bR.sudo_5Board_4held.size = 8 := by
        have hs := congrArg Array.size hheld
        rw [Array.size_set, Array.size_set] at hs
        have hRsz : bR.sudo_5Board_4held.size = bM.sudo_5Board_4held.size := by simp [bR]
        rw [hRsz, hs, hquietZ.szD]
      have htierR : bR.sudo_5Board_1t = embTier t := by
        have hRt : bR.sudo_5Board_1t = bM.sudo_5Board_1t := by simp [bR]
        rw [hRt, htM, hquietZ.tier, hm.tierSnap]
      have hmarkR : bR.sudo_5Board_6marker = Int.ofNat lay.mark := by
        have hRm : bR.sudo_5Board_6marker = bM.sudo_5Board_6marker := by simp [bR]
        rw [hRm, hixM, hquietZ.marker, hm.markSnap]
      have hmxR : bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
          Int.ofNat lay.mx := by
        have hRx : bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
            bM.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by simp [bR]
        rw [hRx, hmxM, hquietZ.mx, hm.mxSnap]
      have h6eR : bR.sudo_5Board_4held[6]'(by rw [hszDR]; decide) = false := by
        have h6M : 6 < bM.sudo_5Board_4held.size := by
          have hs := congrArg Array.size hheld
          rw [Array.size_set, Array.size_set] at hs
          exact hs.symm ▸ hread.spareD
        have hget : ((bZ.sudo_5Board_4held.set ⟨6, hread.spareD⟩ true).set
            ⟨6, by rw [Array.size_set]; exact hread.spareD⟩ false)[6]'(by
              rw [Array.size_set, Array.size_set]; exact hread.spareD) = false := by
          simp [Array.getElem_set]
        have hM : bM.sudo_5Board_4held[6]'h6M = false := cell_eq_of hheld hget
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        exact cell_eq_of hEq hM
      obtain ⟨mvB, hmvB, hmvBLe⟩ := hbound.move
      obtain ⟨slB, hslB, hslBLe⟩ := hbound.slide
      obtain ⟨ctrlB, hctrlB, hctrlBLe⟩ := hbound.ctrl
      obtain ⟨_gtB, opB, hopB, hopBLe⟩ := hbound.ops
      have hwhiteTight : mvM + nz ≤ mv + (t.n * (t.n + 1)) +
          3 * (t.benchlen - t.n) + 2 * t.n := by
        have hdef : mvM = mv + pegCount xs + schoolMoves gapL xs t.n t.n +
            foldCharge t.n (t.n - t.k)
              (school t.n gapL xs (List.replicate t.benchlen 0) false) := rfl
        have hpeg : pegCount xs ≤ t.n := by rw [← lay.len]; exact pegCount_le xs
        rw [hdef]
        omega
      have hmvSame : mv = mvB := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        exact hmv.symm.trans hmvB
      have hwhiteCap : mv + (t.n * (t.n + 1)) + 3 * (t.benchlen - t.n) + 2 * t.n ≤
          checkMoveCap base := by
        have hcap := hmvBLe
        rw [← hmvSame, hm.n, hm.bench] at hcap
        omega
      have hwhiteSlack : mvM + nz + t.n ≤ checkMoveCap base := by
        have hcap := hmvBLe
        rw [← hmvSame, hm.n, hm.bench] at hcap
        omega
      have hcarryR : RiseCarry bR t lay.mark lay.mx :=
        { szH := hszHR
          szD := hszDR
          tier := htierR
          marker := hmarkR
          mx := hmxR
          benchOff := by simp [bR]
          held6 := h6eR
          moves := ⟨mvM + nz, by simpa [bR, ofNat_eq_natCast] using hmvR⟩
          slides := by
            have hslR : bR.sudo_5Board_4cost.sudo_5Costs_6slides =
                bM.sudo_5Board_4cost.sudo_5Costs_6slides := by simp [bR]
            obtain ⟨sl, hslZ⟩ := hread.slides
            refine ⟨sl, ?_⟩
            rw [hslR, hslM, hslZ]
          ctrl := by
            have hcR : bR.sudo_5Board_4cost.sudo_5Costs_4ctrl =
                bM.sudo_5Board_4cost.sudo_5Costs_4ctrl := by simp [bR]
            obtain ⟨c, hcZ⟩ := hread.ctrl
            refine ⟨c, hcR.trans (hcM.trans hcZ)⟩
          peak := by
            have hpkR : bR.sudo_5Board_4cost.sudo_5Costs_4peak =
                bM.sudo_5Board_4cost.sudo_5Costs_4peak := by simp [bR]
            exact ⟨_, by simpa [ofNat_eq_natCast] using hpkR.trans hpkM⟩
          peakS := by
            have hpR : bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
                bM.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by simp [bR]
            exact ⟨_, by simpa [ofNat_eq_natCast] using hpR.trans hstrictM⟩
          hole := by
            have hhR : bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
                bM.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by simp [bR]
            exact ⟨_, by simpa [ofNat_eq_natCast] using hhR.trans hholeM⟩
          opsGt := by
            have hEq : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
            rw [hEq, hopsM, Array.size_set]
            exact hread.opsGt
          ops0 := by
            refine ⟨cOps + 1, ?_⟩
            have hEq : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
            have hsz0 : 0 < (bZ.sudo_5Board_4cost.sudo_5Costs_3ops.set
                ⟨0, hread.opsGt⟩ (Int.ofNat (cOps + 1))).size := by
              rw [Array.size_set]; exact hread.opsGt
            have hget := Array.getElem_set_eq bZ.sudo_5Board_4cost.sudo_5Costs_3ops
              ⟨0, hread.opsGt⟩ (Int.ofNat (cOps + 1)) rfl hsz0
            have hM : bM.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
                rw [hopsM]; exact hsz0) = Int.ofNat (cOps + 1) :=
              (cell_eq_of hopsM hget)
            simpa [hEq, ofNat_eq_natCast] using hM }
      have hbnd : CheckBound bR base :=
        { move := ⟨mvM + nz, by simpa [bR, ofNat_eq_natCast] using hmvR,
            Nat.le_trans hwhiteTight hwhiteCap⟩
          slide := by
            have hslR : bR.sudo_5Board_4cost.sudo_5Costs_6slides =
                bZ.sudo_5Board_4cost.sudo_5Costs_6slides := by
              have hslM' : bM.sudo_5Board_4cost.sudo_5Costs_6slides =
                  bZ.sudo_5Board_4cost.sudo_5Costs_6slides := hslM
              exact (by simp [bR] : bR.sudo_5Board_4cost.sudo_5Costs_6slides =
                bM.sudo_5Board_4cost.sudo_5Costs_6slides).trans hslM'
            exact ⟨slB, hslR.trans hslB, hslBLe⟩
          ctrl := by
            have hcR : bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrlB : Int) := by
              exact (by simp [bR] : bR.sudo_5Board_4cost.sudo_5Costs_4ctrl =
                bM.sudo_5Board_4cost.sudo_5Costs_4ctrl).trans (hcM.trans hctrlB)
            exact ⟨ctrlB, hcR, hctrlBLe⟩
          ops := by
            refine ⟨?_, cOps + 1, ?_, ?_⟩
            · have hEq : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                  bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
              rw [hEq, hopsM, Array.size_set]
              exact hread.opsGt
            · have hEq : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                  bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
              have hsz0 : 0 < (bZ.sudo_5Board_4cost.sudo_5Costs_3ops.set
                  ⟨0, hread.opsGt⟩ (Int.ofNat (cOps + 1))).size := by
                rw [Array.size_set]; exact hread.opsGt
              have hget := Array.getElem_set_eq bZ.sudo_5Board_4cost.sudo_5Costs_3ops
                ⟨0, hread.opsGt⟩ (Int.ofNat (cOps + 1)) rfl hsz0
              have hM : bM.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
                  rw [hopsM]; exact hsz0) = Int.ofNat (cOps + 1) :=
                cell_eq_of hopsM hget
              simpa [hEq, ofNat_eq_natCast] using hM
            · have hcSame : cOps = opB := by
                apply Int.ofNat.inj
                rw [ofNat_eq_natCast, ofNat_eq_natCast]
                exact hcOps.1.symm.trans (idx_irrel.trans hopB)
              rw [hcSame]
              exact hopBLe }
      have hhighR : bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
          bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
        simp [bR, hhighM]
      have hwater : ∃ high : Nat,
          bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) ∧
          tallyOrigin t ≤ high := by
        refine ⟨s'.high, hhighZ, ?_⟩
        have hEq : s'.t0 + s'.tally - 1 ≤ s'.high := by
          rw [hKpost.highTop]
          exact Nat.le_max_right _ _
        have ht0 : s'.t0 = tallyOrigin t := by
          have hmodel : s' = modelClimb (openModelAt t xs lay.ctrl lay.high) base.x hole (tierClimb t) := hs'
          rw [hmodel, modelClimb_t0]
          simp [openModelAt, openModel, entryModel]
        omega
      have hrowR : bR.sudo_5Board_3row = embed (paintedRow t) := by
        have hBR : bR.sudo_5Board_3row = bM.sudo_5Board_3row := by simp [bR]
        simpa [hm.baseRow] using hBR.trans (_hrowM.trans _hrowZ)
      have hladClimb : b'.sudo_5Board_6ladder = embed (tierClimb t) :=
        (climbEmit_ladder ((2 : Nat) : Int) bT (tierClimb t) b' hrun').trans hladT
      obtain ⟨_bU2, _bC2, _bOut2, bZ2, hun2, hc2, hset2, hz2, hladZ, hl02, hnr2,
          hpark2, htmax2, hfrom2, hridx2, ht02, hlen2, hopsSettle⟩ :=
        settled_unpark_frame hKpost hon hge htmax hmt
      have hUeq : _bU2 = bU := by
        cases hun2.symm.trans hun
        rfl
      have hCeq : _bC2 = bC := by
        rw [hUeq] at hc2
        cases hc2.symm.trans hc
        rfl
      have hOeq : _bOut2 = bOut := by
        rw [hCeq] at hset2
        cases hset2.symm.trans hset
        rfl
      have hZeq : bZ2 = bZ := by
        rw [hOeq] at hz2
        cases hz2.symm.trans hz
        rfl
      have hladR : bR.sudo_5Board_6ladder = embed (tierClimb t) := by
        have hEq : bR.sudo_5Board_6ladder = bM.sudo_5Board_6ladder := by simp [bR]
        exact hEq.trans (hsc.ladder.trans ((hZeq ▸ hladZ).trans hladClimb))
      have hl0R : bR.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) := by
        have hBR : bR.sudo_5Board_7ladder0 = bM.sudo_5Board_7ladder0 := by simp [bR]
        have hClimb : b'.sudo_5Board_7ladder0 = (base.ladder0 : Int) :=
          hKpost.shape.park.ladder0B
        have hstep := hBR.trans (hsc.l0.trans ((hZeq ▸ hl02).trans hClimb))
        simpa [hm.ladder0, ofNat_eq_natCast] using hstep
      have hnrR : bR.sudo_5Board_6nrungs = Int.ofNat (tierR t) := by
        have hBR : bR.sudo_5Board_6nrungs = bM.sudo_5Board_6nrungs := by simp [bR]
        have hClimb : b'.sudo_5Board_6nrungs = (base.R : Int) :=
          hKpost.shape.park.nrungsB
        have hstep := hBR.trans (hsc.nr.trans ((hZeq ▸ hnr2).trans hClimb))
        simpa [hm.R, ofNat_eq_natCast] using hstep
      have hparkR : bR.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) := by
        have hBR : bR.sudo_5Board_9park_hole = bM.sudo_5Board_9park_hole := by simp [bR]
        have hClimb : b'.sudo_5Board_9park_hole = (s'.parkAt : Int) := hKpost.inv.park
        have hAt : s'.parkAt = base.ladder0 + base.R := hKpost.parkEq
        have hstep := hBR.trans (hsc.park.trans ((hZeq ▸ hpark2).trans hClimb))
        simpa [hAt, hm.ladder0, hm.R, ofNat_eq_natCast] using hstep
      have hfromR : bR.sudo_5Board_11parked_from = -1 := by
        have hBR : bR.sudo_5Board_11parked_from = bM.sudo_5Board_11parked_from := by simp [bR]
        exact hBR.trans (hsc.fromH.trans (hZeq ▸ hfrom2))
      have hridxR : bR.sudo_5Board_8rung_idx = 0 := by
        have hBR : bR.sudo_5Board_8rung_idx = bM.sudo_5Board_8rung_idx := by simp [bR]
        exact hBR.trans (hsc.ridx.trans (hZeq ▸ hridx2))
      have htlenR : bR.sudo_5Board_9tally_len = 0 := by
        have hBR : bR.sudo_5Board_9tally_len = bM.sudo_5Board_9tally_len := by simp [bR]
        exact hBR.trans (hsc.tlen.trans (hZeq ▸ hlen2))
      have ht0R : bR.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
        have hBR : bR.sudo_5Board_6tally0 = bM.sudo_5Board_6tally0 := by simp [bR]
        have ht0s : s'.t0 = tallyOrigin t := by
          have hmodel : s' =
              modelClimb (openModelAt t xs lay.ctrl lay.high) base.x hole (tierClimb t) := hs'
          rw [hmodel, modelClimb_t0]
          simp [openModelAt, openModel, entryModel]
        have hstep := hBR.trans (hsc.t0.trans (hZeq ▸ ht02))
        simpa [ht0s, ofNat_eq_natCast] using hstep
      have htmaxR : ∃ tmax : Nat,
          bR.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) := by
        obtain ⟨tmax, htmaxB⟩ := hKpost.tmaxLt
        have hBR : bR.sudo_5Board_4cost.sudo_5Costs_9tally_max =
            bM.sudo_5Board_4cost.sudo_5Costs_9tally_max := by simp [bR]
        exact ⟨tmax, hBR.trans (hsc.tmax.trans ((hZeq ▸ htmax2).trans htmaxB))⟩
      have hopSlots :
          (∃ (h2 : 2 < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c2 : Nat),
            bR.sudo_5Board_4cost.sudo_5Costs_3ops[2]'h2 = (c2 : Int) ∧
            c2 + 1 ≤ checkOpsCap base + 3) ∧
          (3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size →
            ∃ (h3 : 3 < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c3 : Nat),
              bR.sudo_5Board_4cost.sudo_5Costs_3ops[3]'h3 = (c3 : Int) ∧
              c3 + 1 ≤ checkOpsCap base + 3) := by
        obtain ⟨_c1, _hc1, hset1⟩ := hopsSettle
        have hsetZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
            b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
              (Int.ofNat (_c1 + 1)) := by simpa [hZeq] using hset1
        have hopsR : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
            bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
        have hmove := arr_set_congr hsetZ 0 hread.opsGt (Int.ofNat (cOps + 1))
        have harr : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
            (b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                (Int.ofNat (_c1 + 1))).set
              ⟨0, hsetZ ▸ hread.opsGt⟩ (Int.ofNat (cOps + 1)) :=
          hopsR.trans (hopsM.trans hmove)
        have hszR : bR.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [harr, Array.size_set, Array.size_set, hszClimb, hszT]
        have hroom (j : Nat) (hjB : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
            (hne0 : (0 : Nat) ≠ j) (hne1 : (1 : Nat) ≠ j) :
            ∃ (hj : j < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c : Nat),
              bR.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj = (c : Int) ∧
              c + 1 ≤ checkOpsCap base + 3 := by
          have hjR : j < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hszR]; exact hjB
          have hj' : j < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hszClimb, hszT]; exact hjB
          obtain ⟨c, hc, hle⟩ := hKpost.ops j hj'
          have hget : bR.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjR = (c : Int) := by
            have hvia := ops_get_set2 b'.sudo_5Board_4cost.sudo_5Costs_3ops j hj'
              1 hKpost.shape.peg.opsGt (Int.ofNat (_c1 + 1))
              0 (hsetZ ▸ hread.opsGt) (Int.ofNat (cOps + 1)) hne0 hne1
            exact cell_eq_of (ha := hjR) harr (hvia.trans hc)
          refine ⟨hjR, c, hget, ?_⟩
          have hres : c + 1 ≤ base.ops0 + (tierClimb t).length * (base.mMax + 3) := by
            simpa [hon] using hle
          have hlen : (tierClimb t).length = tierR t := by
            simp [tierClimb, tierR, List.length_reverse]
          rw [hm.ops0, hm.mMax, hlen] at hres
          unfold checkOpsCap
          rw [hm.ops0, hm.mMax, hm.R]
          exact Nat.le_trans hres (Nat.le_add_right _ 3)
        refine ⟨?_, ?_⟩
        · have h2b : 2 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := lay.ops2
          exact hroom 2 h2b (by decide) (by decide)
        · intro h3
          exact hroom 3 h3 (by decide) (by decide)
      have hopsAll : CheckedOps bR (checkOpsCap base + 3) := by
        intro j hj
        by_cases h0 : j = 0
        · subst h0
          obtain ⟨_, c0, hc0, hle0⟩ := hbnd.ops
          refine ⟨c0, idx_irrel.trans hc0, ?_⟩
          simp only [if_neg (by decide : (0 : Nat) ≠ 2), if_neg (by decide : (0 : Nat) ≠ 3)]
          exact Nat.le_trans hle0 (Nat.le_add_right _ 3)
        · by_cases h1 : j = 1
          · subst h1
            obtain ⟨c1, hc1, hset1⟩ := hopsSettle
            have hsetZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
                b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                  (Int.ofNat (c1 + 1)) := by simpa [hZeq] using hset1
            have hopsR : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
            have hmove := arr_set_congr hsetZ 0 hread.opsGt (Int.ofNat (cOps + 1))
            have harr : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                (b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                    (Int.ofNat (c1 + 1))).set
                  ⟨0, hsetZ ▸ hread.opsGt⟩ (Int.ofNat (cOps + 1)) :=
              hopsR.trans (hopsM.trans hmove)
            obtain ⟨cPre, hcPre, hlePre⟩ := hKpost.ops 1 hKpost.shape.peg.opsGt
            have hc1eq : c1 = cPre := by
              apply Int.ofNat.inj
              rw [ofNat_eq_natCast, ofNat_eq_natCast]
              exact hc1.symm.trans hcPre
            refine ⟨c1 + 1, ?_, ?_⟩
            · have hsz1 : 1 <
                  (b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                    (Int.ofNat (c1 + 1))).size := by
                rw [Array.size_set]; exact hKpost.shape.peg.opsGt
              have hne : (0 : Nat) ≠ 1 := by decide
              have hget0 := Array.getElem_set_ne
                (b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                  (Int.ofNat (c1 + 1)))
                ⟨0, hsetZ ▸ hread.opsGt⟩ (Int.ofNat (cOps + 1))
                (by rw [Array.size_set]; exact hsz1) hne
              have hget1 := Array.getElem_set_eq b'.sudo_5Board_4cost.sudo_5Costs_3ops
                ⟨1, hKpost.shape.peg.opsGt⟩ (Int.ofNat (c1 + 1)) rfl hsz1
              exact cell_eq_of harr (hget0.trans hget1)
            · simp only [if_neg (by decide : (1 : Nat) ≠ 2), if_neg (by decide : (1 : Nat) ≠ 3)]
              have hres : cPre + 1 ≤ base.ops0 + (tierClimb t).length * (base.mMax + 3) := by
                simpa [hon] using hlePre
              have hlen : (tierClimb t).length = tierR t := by
                simp [tierClimb, tierR, List.length_reverse]
              rw [hc1eq]
              rw [hm.ops0, hm.mMax, hlen] at hres
              unfold checkOpsCap
              rw [hm.ops0, hm.mMax, hm.R]
              exact Nat.le_trans hres (Nat.le_add_right _ 3)
          · obtain ⟨_c1, _hc1, hset1⟩ := hopsSettle
            have hsetZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
                b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                  (Int.ofNat (_c1 + 1)) := by simpa [hZeq] using hset1
            have hopsR : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bR]
            have hmove := arr_set_congr hsetZ 0 hread.opsGt (Int.ofNat (cOps + 1))
            have harr : bR.sudo_5Board_4cost.sudo_5Costs_3ops =
                (b'.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hKpost.shape.peg.opsGt⟩
                    (Int.ofNat (_c1 + 1))).set
                  ⟨0, hsetZ ▸ hread.opsGt⟩ (Int.ofNat (cOps + 1)) :=
              hopsR.trans (hopsM.trans hmove)
            have hszR : bR.sudo_5Board_4cost.sudo_5Costs_3ops.size =
                b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
              rw [harr, Array.size_set, Array.size_set, hszClimb, hszT]
            have hjB : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
              rw [← hszR]; exact hj
            have hne0 : (0 : Nat) ≠ j := fun h => h0 h.symm
            have hne1 : (1 : Nat) ≠ j := fun h => h1 h.symm
            have hj' : j < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
              rw [hszClimb, hszT]; exact hjB
            obtain ⟨c, hc, hle⟩ := hKpost.ops j hj'
            have hjR : j < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := hj
            have hget : bR.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjR = (c : Int) := by
              have hvia := ops_get_set2 b'.sudo_5Board_4cost.sudo_5Costs_3ops j hj'
                1 hKpost.shape.peg.opsGt (Int.ofNat (_c1 + 1))
                0 (hsetZ ▸ hread.opsGt) (Int.ofNat (cOps + 1)) hne0 hne1
              exact cell_eq_of (ha := hjR) harr (hvia.trans hc)
            refine ⟨c, hget, ?_⟩
            have hres : c + 1 ≤ base.ops0 + (tierClimb t).length * (base.mMax + 3) := by
              simpa [hon] using hle
            have hlen : (tierClimb t).length = tierR t := by
              simp [tierClimb, tierR, List.length_reverse]
            have hcap : c + 1 ≤ checkOpsCap base + 3 := by
              rw [hm.ops0, hm.mMax, hlen] at hres
              unfold checkOpsCap
              rw [hm.ops0, hm.mMax, hm.R]
              exact Nat.le_trans hres (Nat.le_add_right _ 3)
            by_cases h2 : j = 2
            · simp only [h2]
              exact hcap
            · by_cases h3 : j = 3
              · simp only [h2, h3]
                exact hcap
              · simp only [h2, h3]
                exact Nat.le_trans (Nat.le_succ c) hcap
      refine ⟨bZ, bM, bR, embed (lane.take t.n), h5R, hok, ?_, hreadM, ?_, hhomeR, rfl,
        ⟨h5DR, mvM + nz, hheldR, hmvR, hfitR, hnR⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hcarryR, hbnd, ⟨mvM + nz, by simpa [bR, ofNat_eq_natCast] using hmvR, hwhiteSlack⟩,
        hhighR, hwater, hrowR, hLc ▸ hladR, ?_, ?_, hl0R, hnrR, hparkR, hfromR, hridxR,
        htlenR, ht0R, htmaxR, hopSlots.1, hopSlots.2, hopsAll⟩
      · simpa [Ecbs.check_target, Ecbs.gap] using hmulOk
      · exact congrArg embed htakeL
      · intro _
        exact idx_irrel.trans hhome2R
      · intro _
        exact idx_irrel.trans hheld2R
      · intro _; exact idx_irrel.trans hhome0R
      · intro _; exact idx_irrel.trans hheld0R
      · intro _; exact idx_irrel.trans hhome1R
      · intro _; exact idx_irrel.trans hheld1R
      · intro _; exact idx_irrel.trans hhome4R
      · intro _; exact idx_irrel.trans hheld4R
      · intro _; exact idx_irrel.trans hhome3R
      · intro _; exact idx_irrel.trans hheld3R

private theorem getD_eq_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.getD j 0 = xs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem head_of_peg (P : List Nat) (n c : Nat) (hP : 0 < P.length)
    (hv : P = c :: List.replicate (n - 1) 0) : P[0] = c := by
  subst hv
  simp

private theorem mirror_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    home < (mirrorHome b home hH arr mv).sudo_5Board_4home.size := by
  simp [mirrorHome, withMoves, Array.size_set]
  exact hH

/-- Accepted check on an open walk board. Home 5 is the list `fieldInv` returns. -/
theorem open_checked (b : Ecbs.Board) (t : Spec.Tier) (xs ans : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base)
    (hacc : fieldInv t.n t.k t.benchlen xs = some ans) :
    ∃ (b' : Ecbs.Board) (h5 : 5 < b'.sudo_5Board_4home.size)
      (h5D : 5 < b'.sudo_5Board_4held.size),
      Ecbs.invert_checked b ((2 : Nat) : Int) = .ok b' ∧
      b'.sudo_5Board_4home[5]'h5 = embed ans ∧
      b'.sudo_5Board_4held[5]'h5D = true ∧
      b'.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) ∧
      ans.length = t.n ∧
      (∀ h2 : 2 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[2] = embed xs) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2] = true) ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed lay.side0) ∧
      (∀ h0 : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = lay.flag0) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed lay.side1) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1] = lay.flag1) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4] = embed lay.side4) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4] = lay.flag4) ∧
      RiseCarry b' t lay.mark lay.mx ∧
      CheckBound b' base ∧
      (∃ high : Nat,
        b'.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) ∧
        tallyOrigin t ≤ high) ∧
      b'.sudo_5Board_3row = embed (paintedRow t) ∧
      b'.sudo_5Board_6ladder = embed (tierClimb t) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3] = embed lay.base3) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3] = lay.flag3) ∧
      b'.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) ∧
      b'.sudo_5Board_6nrungs = Int.ofNat (tierR t) ∧
      b'.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) ∧
      b'.sudo_5Board_11parked_from = -1 ∧
      b'.sudo_5Board_8rung_idx = 0 ∧
      b'.sudo_5Board_9tally_len = 0 ∧
      b'.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) ∧
      (∃ tmax : Nat, b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int)) ∧
      (∃ (h2 : 2 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c2 : Nat),
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[2]'h2 = (c2 : Int) ∧
        c2 + 1 ≤ checkOpsCap base + 3) ∧
      (3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size →
        ∃ (h3 : 3 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size) (c3 : Nat),
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[3]'h3 = (c3 : Int) ∧
          c3 + 1 ≤ checkOpsCap base + 3) ∧
      CheckedOps b' (checkOpsCap base + 3) := by
  have hpos : 0 < t.n := hOk.n_pos
  have hnbench := mul_span_n t.n t.benchlen hpos sat.mul_span
  have hspan3 := cube_span_le t.n t.benchlen t.combgap sat.cube_span
  let g := invGap t.n t.k t.benchlen xs
  let P := fieldMul t.n t.k t.benchlen g xs
  have hlenP : P.length = t.n := fieldMul_length _ _ _ _ _ hnbench
  have hP0 : 0 < P.length := by rw [hlenP]; exact hpos
  have hshape := fieldInv_some_shape t.n t.k t.benchlen xs ans hacc
  have hpeg : P = 1 :: List.replicate (t.n - 1) 0 ∨
      P = 2 :: List.replicate (t.n - 1) 0 := by
    rcases hshape with ⟨hvP, _⟩ | ⟨hvP, _⟩
    · exact Or.inl (by simpa [P, g] using hvP)
    · exact Or.inr (by simpa [P, g] using hvP)
  have htriG : allTritList g := invGap_trits t xs sat hsh hpos lay.len lay.tri
  have hlenG : g.length = t.n := invGap_length t xs sat hpos
  obtain ⟨_bZ, _bM, bR, _v, h5, hinv, hmul, hread, hv, hhome5, _hbench, hframe, hhome2, hheld2,
      h0a, h0t, h1a, h1t, h4a, h4t, hcarry, hbnd, hslack, hhighR, hwater, hrowR, hladR,
      h3a, h3t, hl0R, hnrR, hparkF, hfromR, hridxR, htlenR, ht0R, htmaxR, hop2R, hop3R,
      hopsAll⟩ :=
    open_check_mul b t xs lay hOk sat hR hsh base hm
  obtain ⟨h5D, mv, hheld, hmv, hfit, hnT⟩ := hframe
  have hfitn : FitsLen t.n := FitsLen.of_le hfit (Nat.le_add_left t.n mv)
  unfold Ecbs.invert_checked
  rw [hinv, ok_bind]
  conv => zeta
  rw [hmul, ok_bind]
  conv => zeta
  rw [hread, ok_bind]
  dsimp
  rw [hv, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed P 0 hP0, ok_bind,
    sEq_ofNat (P[0]'(hP0)) 0]
  have hhead : (P[0]'(hP0)) ≠ 0 := by
    rcases hpeg with hvP | hvP
    · rw [head_of_peg P t.n 1 hP0 hvP]; decide
    · rw [head_of_peg P t.n 2 hP0 hvP]; decide
  rw [decide_eq_false hhead, Bool.not_false, sudoAssert_true, ok_bind]
  rw [listLen_embed, hlenP, subI_ofNat_one t.n hpos hfitn, ok_bind]
  conv => zeta
  rw [show (1 : Int) = Int.ofNat 1 from rfl, fuelRange_eq, except_bind_pure]
  rw [zeroScan_ok_of P t.n 1 hlenP ?hstep hP0 (Nat.le_refl _)
      (by rw [hlenP]; exact Nat.succ_le_of_lt hpos) (by rwa [hlenP]) ?htail]
  · have heq : fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen xs) xs = P := by
      simp [P, g]
    rcases hpeg with hvP | hvP
    · have hc : (P[0]'(hP0)) = 1 := head_of_peg P t.n 1 hP0 hvP
      simp only [heq, sEq_int, hc, pure_eq_ok,
        show decide ((1 : Int) = (2 : Int)) = false by decide,
        Bool.false_eq_true, if_false]
      rcases hshape with ⟨_, hans⟩ | ⟨hv2, _⟩
      · refine ⟨bR, h5, h5D, rfl, ?_, hheld, hnT, ?_, hhome2, hheld2,
            h0a, h0t, h1a, h1t, h4a, h4t, hcarry, hbnd, ?_, hrowR, hladR, h3a, h3t,
            hl0R, hnrR, hparkF, hfromR, hridxR, htlenR, ht0R, htmaxR, hop2R, hop3R,
            hopsAll⟩
        · rw [hans]
          simpa [g] using hhome5
        · rw [hans]
          exact hlenG
        · rcases hwater with ⟨high, hZ, hgeW⟩
          exact ⟨high, hhighR.trans hZ, hgeW⟩
      · have hv2' : P = 2 :: List.replicate (t.n - 1) 0 := by simpa [P, g] using hv2
        have h2 : (P[0]'(hP0)) = 2 := head_of_peg P t.n 2 hP0 hv2'
        rw [hc] at h2
        cases h2
    · have hc : (P[0]'(hP0)) = 2 := head_of_peg P t.n 2 hP0 hvP
      simp only [heq, sEq_int, hc, ok_bind,
        show decide (Int.ofNat 2 = 2) = true from rfl, if_true]
      have harr : bR.sudo_5Board_4home[5]'h5 = embed g := by simpa [g] using hhome5
      rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl]
      rw [mirror_refines bR 5 g t.n mv h5 h5D hheld harr hnT hlenG hpos htriG hmv hfit,
        ok_bind, pure_eq_ok]
      rcases hshape with ⟨hv1, _⟩ | ⟨_, hans⟩
      · have hv1' : P = 1 :: List.replicate (t.n - 1) 0 := by simpa [P, g] using hv1
        have h1 : (P[0]'(hP0)) = 1 := head_of_peg P t.n 1 hP0 hv1'
        rw [hc] at h1
        cases h1
      · let bM := mirrorHome bR 5 h5 (embed (mirrorTrits g)) (mv + pegCount g)
        have h5' : 5 < bM.sudo_5Board_4home.size := mirror_size _ _ _ _ _
        have h5D' : 5 < bM.sudo_5Board_4held.size := by
          rw [show bM.sudo_5Board_4held = bR.sudo_5Board_4held from
            mirrorHome_held bR 5 h5 _ _]
          exact h5D
        refine ⟨bM, h5', h5D', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hans]
          exact mirrorHome_at bR 5 h5 (embed (mirrorTrits g)) (mv + pegCount g) h5'
        · exact hheld
        · rw [show bM.sudo_5Board_1t = bR.sudo_5Board_1t from
            mirrorHome_tier bR 5 h5 _ _]
          exact hnT
        · rw [hans, mirrorTrits_flip, List.length_map]
          exact hlenG
        · intro h2
          have h2R : 2 < bR.sudo_5Board_4home.size := by
            rw [show bM.sudo_5Board_4home.size = bR.sudo_5Board_4home.size from ?_] at h2
            · exact h2
            · simp [bM, mirrorHome, withMoves, Array.size_set]
          exact (mirrorHome_other bR 5 2 h5 (embed (mirrorTrits g)) (mv + pegCount g)
            (by decide) h2R h2).trans (hhome2 h2R)
        · intro h2
          have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
            mirrorHome_held bR 5 h5 _ _
          exact cell_eq_of hEq (hheld2 (by
            have hs := congrArg Array.size hEq
            exact hs ▸ h2))
        · intro h0
          have h0R : 0 < bR.sudo_5Board_4home.size := by
            have hs : bM.sudo_5Board_4home.size = bR.sudo_5Board_4home.size := by
              simp [bM, mirrorHome, withMoves, Array.size_set]
            exact hs ▸ h0
          exact (mirrorHome_other bR 5 0 h5 (embed (mirrorTrits g)) (mv + pegCount g)
            (by decide) h0R h0).trans (h0a h0R)
        · intro h0
          have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
            mirrorHome_held bR 5 h5 _ _
          exact cell_eq_of hEq (h0t (by
            have hs := congrArg Array.size hEq
            exact hs ▸ h0))
        · intro h1
          have h1R : 1 < bR.sudo_5Board_4home.size := by
            have hs : bM.sudo_5Board_4home.size = bR.sudo_5Board_4home.size := by
              simp [bM, mirrorHome, withMoves, Array.size_set]
            exact hs ▸ h1
          exact (mirrorHome_other bR 5 1 h5 (embed (mirrorTrits g)) (mv + pegCount g)
            (by decide) h1R h1).trans (h1a h1R)
        · intro h1
          have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
            mirrorHome_held bR 5 h5 _ _
          exact cell_eq_of hEq (h1t (by
            have hs := congrArg Array.size hEq
            exact hs ▸ h1))
        · intro h4
          have h4R : 4 < bR.sudo_5Board_4home.size := by
            have hs : bM.sudo_5Board_4home.size = bR.sudo_5Board_4home.size := by
              simp [bM, mirrorHome, withMoves, Array.size_set]
            exact hs ▸ h4
          exact (mirrorHome_other bR 5 4 h5 (embed (mirrorTrits g)) (mv + pegCount g)
            (by decide) h4R h4).trans (h4a h4R)
        · intro h4
          have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
            mirrorHome_held bR 5 h5 _ _
          exact cell_eq_of hEq (h4t (by
            have hs := congrArg Array.size hEq
            exact hs ▸ h4))
        · refine
            { szH := by simp [bM, mirrorHome, withMoves, Array.size_set, hcarry.szH]
              szD := by
                rw [show bM.sudo_5Board_4held = bR.sudo_5Board_4held from
                  mirrorHome_held bR 5 h5 _ _]
                exact hcarry.szD
              tier := by
                rw [show bM.sudo_5Board_1t = bR.sudo_5Board_1t from
                  mirrorHome_tier bR 5 h5 _ _]
                exact hcarry.tier
              marker := by
                simp [bM, mirrorHome, withMoves]
                exact hcarry.marker
              mx := by
                simp [bM, mirrorHome, withMoves]
                exact hcarry.mx
              benchOff := by
                simp [bM, mirrorHome, withMoves]
                exact hcarry.benchOff
              held6 := by
                have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
                  mirrorHome_held bR 5 h5 _ _
                exact cell_eq_of hEq hcarry.held6
              moves := ⟨mv + pegCount g, by
                simp [bM, mirrorHome, withMoves, ofNat_eq_natCast]⟩
              slides := by
                obtain ⟨sl, hsl⟩ := hcarry.slides
                refine ⟨sl, ?_⟩
                simp [bM, mirrorHome, withMoves, hsl]
              ctrl := by
                obtain ⟨c, hc⟩ := hcarry.ctrl
                refine ⟨c, ?_⟩
                simp [bM, mirrorHome, withMoves, hc]
              peak := by
                obtain ⟨pk, hpk⟩ := hcarry.peak
                refine ⟨pk, ?_⟩
                simp [bM, mirrorHome, withMoves, hpk]
              peakS := by
                obtain ⟨p, hp⟩ := hcarry.peakS
                refine ⟨p, ?_⟩
                simp [bM, mirrorHome, withMoves, hp]
              hole := by
                obtain ⟨holeN, hh⟩ := hcarry.hole
                refine ⟨holeN, ?_⟩
                simp [bM, mirrorHome, withMoves, hh]
              opsGt := by
                simp [bM, mirrorHome, withMoves]
                exact hcarry.opsGt
              ops0 := by
                obtain ⟨c, hc⟩ := hcarry.ops0
                refine ⟨c, ?_⟩
                simp [bM, mirrorHome, withMoves]
                exact hc }
        · obtain ⟨mvW, hmvW, hroom⟩ := hslack
          obtain ⟨slW, hslW, hslLe⟩ := hbnd.slide
          obtain ⟨cW, hcW, hcLe⟩ := hbnd.ctrl
          obtain ⟨gtW, opW, hopW, hopLe⟩ := hbnd.ops
          have hmvW' : mv = mvW := by
            apply Int.ofNat.inj
            rw [ofNat_eq_natCast, ofNat_eq_natCast]
            exact hmv.symm.trans hmvW
          have hpegG : pegCount g ≤ t.n := by
            rw [← hlenG]
            exact pegCount_le g
          refine
            { move := ⟨mv + pegCount g, by
                simp [bM, mirrorHome, withMoves, ofNat_eq_natCast], ?_⟩
              slide := ⟨slW, by simp [bM, mirrorHome, withMoves, hslW], hslLe⟩
              ctrl := ⟨cW, by simp [bM, mirrorHome, withMoves, hcW], hcLe⟩
              ops := ⟨by simp [bM, mirrorHome, withMoves]; exact gtW, opW,
                by simp [bM, mirrorHome, withMoves]; exact hopW, hopLe⟩ }
          rw [hmvW']
          omega
        · rcases hwater with ⟨high, hZ, hgeW⟩
          have hhiM : bM.sudo_5Board_4cost.sudo_5Costs_15control_highest =
              bR.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
            simp [bM, mirrorHome, withMoves]
          exact ⟨high, hhiM.trans (hhighR.trans hZ), hgeW⟩
        · simpa [bM, mirrorHome_row] using hrowR
        · exact (mirrorHome_ladder bR 5 h5 (embed (mirrorTrits g)) (mv + pegCount g)).trans hladR
        · intro h3
          have h3R : 3 < bR.sudo_5Board_4home.size := by
            have hs : bM.sudo_5Board_4home.size = bR.sudo_5Board_4home.size := by
              simp [bM, mirrorHome, withMoves, Array.size_set]
            exact hs ▸ h3
          exact (mirrorHome_other bR 5 3 h5 (embed (mirrorTrits g)) (mv + pegCount g)
            (by decide) h3R h3).trans (h3a h3R)
        · intro h3
          have hEq : bM.sudo_5Board_4held = bR.sudo_5Board_4held :=
            mirrorHome_held bR 5 h5 _ _
          exact cell_eq_of hEq (h3t (by
            have hs := congrArg Array.size hEq
            exact hs ▸ h3))
        · simpa [bM, mirrorHome, withMoves] using hl0R
        · simpa [bM, mirrorHome, withMoves] using hnrR
        · simpa [bM, mirrorHome, withMoves] using hparkF
        · simpa [bM, mirrorHome, withMoves] using hfromR
        · simpa [bM, mirrorHome, withMoves] using hridxR
        · simpa [bM, mirrorHome, withMoves] using htlenR
        · simpa [bM, mirrorHome, withMoves] using ht0R
        · obtain ⟨tmax, ht⟩ := htmaxR
          exact ⟨tmax, by simpa [bM, mirrorHome, withMoves] using ht⟩
        · obtain ⟨h2, c2, hc2, hle2⟩ := hop2R
          have hsz : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            simp [bM, mirrorHome, withMoves]
          refine ⟨hsz ▸ h2, c2, ?_, hle2⟩
          simpa [bM, mirrorHome, withMoves] using hc2
        · intro h3
          obtain ⟨h3R, c3, hc3, hle3⟩ := hop3R h3
          have hsz : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            simp [bM, mirrorHome, withMoves]
          refine ⟨hsz ▸ h3R, c3, ?_, hle3⟩
          simpa [bM, mirrorHome, withMoves] using hc3
        · intro j hj
          have hsz : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            simp [bM, mirrorHome, withMoves]
          obtain ⟨c, hc, hle⟩ := hopsAll j (hsz ▸ hj)
          refine ⟨c, ?_, hle⟩
          simpa [bM, mirrorHome, withMoves] using hc
  · intro k
    rfl
  · intro j hj1 hj
    rw [← getD_eq_get P j hj]
    rcases hpeg with hvP | hvP
    · rw [hvP, show j = j - 1 + 1 from (Nat.sub_add_cancel hj1).symm, List.getD_cons_succ,
        List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos (by omega : j - 1 < t.n - 1), Option.getD_some]
    · rw [hvP, show j = j - 1 + 1 from (Nat.sub_add_cancel hj1).symm, List.getD_cons_succ,
        List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos (by omega : j - 1 < t.n - 1), Option.getD_some]

end EcbsLink2.Link2
