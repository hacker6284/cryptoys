/-
  `invert` on a walk board. The fresh `bottomBoard` is the special case whose
  counters are the two copies and whose other homes are empty. A walk board
  enters the same climb when the control row, the ladder, and the park are
  still the ones `new_board` laid, the gap and the spare are empty, home
  `bottom` holds the input, and the counters still fit the climb budget.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CheckTail
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
  highLt : high < tallyOrigin t
  htally : b.sudo_5Board_9tally_len = 0
  ht0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  hrow : b.sudo_5Board_3row = embed (paintedRow t)
  htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0
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

/-- The model at the first tally peg. The control counter is whatever the walk
    has already charged, plus the peg `tally_start` writes. -/
def openModel (t : Spec.Tier) (xs : List Nat) (ctrl : Nat) : ClimbModel :=
  { entryModel t xs with ctrl := ctrl + 1 }

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
        ((tallyOrigin t : Nat) : Int) ∧
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
      bT.sudo_5Board_4cost.sudo_5Costs_9tally_max = 1 ∧
      bT.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat lay.peakS ∧
      bT.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat lay.hole ∧
      bT.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨2, lay.ops2⟩ (Int.ofNat (lay.cOps + 1)) := by
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
    ⟨htierG, _, _, _, _, _, _, _, hl0G, hnrG, hparkG, ht0G, _, hfromG, hlenG,
      hmarkG, hridxG, hladG, _, hctrlG, _, _, _, _, hstrictG, hholeG, hhighG, _,
      htmaxG, _, _, hopsG⟩
  have hrowG : bG.sudo_5Board_3row = embed (paintedRow t) := by
    rw [place_row_out bB 5 h5H h5D xs lay.moves lay.peak,
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
        sudo_5Costs_15control_highest := ((tallyOrigin t : Nat) : Int)
        sudo_5Costs_4ctrl := Int.ofNat (lay.ctrl + 1)
        sudo_5Costs_9tally_max := 1 } }
  have htallyRun := tally_start_raise bG (tallyOrigin t) lay.high t.control lay.ctrl 0
    (by rw [hlenG, show bB.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len from rfl,
        lay.htally])
    (by rw [ht0G, show bB.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 from rfl, lay.ht0,
        ofNat_eq_natCast])
    hrowSz hctrlN horigin
    (by rw [hhighG, show bB.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest from rfl, lay.hhigh,
        ofNat_eq_natCast])
    lay.highLt hfit0
    (by rw [hctrlG, show bB.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl from rfl, lay.hctrl, ofNat_eq_natCast])
    lay.fitCtrl
    (by
      rw [htmaxG, show bB.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max from rfl, lay.htmax]
      rfl)
    (by decide)
  have hrowSet : bG.sudo_5Board_3row.set ⟨tallyOrigin t, hrowSz⟩ (1 : Int) =
      embed (entryRow t) := by
    have hlenP : tallyOrigin t < (paintedRow t).length := by
      rw [painted_len]; exact horigin
    rw [Array.set_congr_arr hrowG hrowSz (1 : Int)]
    rw [array_set_idx (h2 := by rw [size_embed]; exact hlenP)]
    simpa [entryRow, ofNat_eq_natCast] using
      embed_set (paintedRow t) (tallyOrigin t) 1 hlenP
  have hszHG : bG.sudo_5Board_4home.size = 8 := by
    rw [place_home_out bB 5 h5H h5D xs lay.moves lay.peak, Array.size_set, hszHB]
  have hszDG : bG.sudo_5Board_4held.size = 8 := by
    rw [place_held_out bB 5 h5H h5D xs lay.moves lay.peak, Array.size_set, hszDB]
  have h5HG : 5 < bG.sudo_5Board_4home.size := by rw [hszHG]; decide
  have h5DG : 5 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have h6DG : 6 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have h2HG : 2 < bG.sudo_5Board_4home.size := by rw [hszHG]; decide
  have h2DG : 2 < bG.sudo_5Board_4held.size := by rw [hszDG]; decide
  have hhomeG : bG.sudo_5Board_4home = bB.sudo_5Board_4home.set ⟨5, h5H⟩ (embed xs) :=
    place_home_out bB 5 h5H h5D xs lay.moves lay.peak
  have hheldG : bG.sudo_5Board_4held = bB.sudo_5Board_4held.set ⟨5, h5D⟩ true :=
    place_held_out bB 5 h5H h5D xs lay.moves lay.peak
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
    rw [place_peak_out bB 5 h5H h5D xs lay.moves lay.peak hpeakB, hcount]
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
  refine ⟨bT, ?_, ?_, ?_, rfl, rfl, rfl, ?_, hrowSet, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hbump, ok_bind]
    rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl, hcopy, ok_bind]
    simpa [bT, ofNat_eq_natCast] using htallyRun
  · rw [show bT.sudo_5Board_9marker_on = bG.sudo_5Board_9marker_on from rfl, hmarkG,
      show bB.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on from rfl, lay.marker]
  · rw [show bT.sudo_5Board_8bench_on = bG.sudo_5Board_8bench_on from rfl,
      place_on_out bB 5 h5H h5D xs lay.moves lay.peak,
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
      place_moves_out bB 5 h5H h5D xs lay.moves lay.peak]
  · rw [show bT.sudo_5Board_4cost.sudo_5Costs_6slides =
        bG.sudo_5Board_4cost.sudo_5Costs_6slides from rfl,
      place_slides_out bB 5 h5H h5D xs lay.moves lay.peak,
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
      ClimbInvK [] (tierClimb t) bT (openModel t xs lay.ctrl) base := by
  obtain ⟨bT, hdo, hmark, hbench, hlen, hctrl, hhigh, ht0, hrow, hpark, hfrom, hridx,
      hlad, hl0, hnr, htier, hszH, hszD, h5t, h5a, h6e, h2t, h2a, hmv, hsl, hpk,
      htmax, hstrict, hhole, hops⟩ :=
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
  have hInv : ClimbInv bT (openModel t xs lay.ctrl) :=
    { hG := hsz5
      hGs := hsz5D
      marker := hmark
      len := by simpa [openModel, entryModel, ofNat_eq_natCast] using hlen
      ctrl := by simpa [openModel, entryModel, ofNat_eq_natCast] using hctrl
      high := by simpa [openModel, entryModel, ofNat_eq_natCast] using hhigh
      t0 := by simpa [openModel, entryModel, ofNat_eq_natCast] using ht0
      row := by simpa [openModel, entryModel] using hrow
      park := by simpa [openModel, entryModel, ofNat_eq_natCast] using hpark
      fromP := by simpa [openModel, entryModel] using hfrom
      ridx := by simpa [openModel, entryModel] using hridx
      gapHome := by
        intro _
        refine ⟨h5t hsz5D, ?_⟩
        simpa [openModel, entryModel] using h5a hsz5
      gapBench := by
        intro h
        simp [openModel, entryModel] at h }
  have hparkR : ParkRead bT (openModel t xs lay.ctrl) (tierClimb t) base :=
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
        simpa [openModel, entryModel, hm.ladder0, hm.R] using entry_hole_lt t hOk hR
      parkLt := by simpa [openModel, entryModel] using entry_park_lt t sat
      parkNe := by
        simp [openModel, entryModel, hm.ladder0, hm.R, climbAt]
        omega
      parkLe := by
        simp [openModel, entryModel]
        unfold tallyOrigin
        omega
      parkIn := by
        simp [openModel, entryModel, hm.control]
        have h := origin_lt t sat
        unfold tallyOrigin at h
        omega
      parkCell := by
        intro _
        simpa [openModel, entryModel] using
          entry_park_cell t (entry_park_lt t sat)
      fromIdle := by
        intro _
        simp [openModel, entryModel]
      fromNat := by
        intro h
        simp [openModel, entryModel] at h
      srcOk := by
        intro h
        simp [openModel, entryModel] at h
      parkHeld := by
        intro h
        simp [openModel, entryModel] at h
      nextRung := by
        intro r rs hrest
        simpa [openModel, entryModel, hm.ladder0, hm.R] using
          entry_nextRung t hOk hR r rs hrest
      ladderTail := by
        intro k hk hlt
        simpa [openModel, entryModel, hm.ladder0, hm.R] using
          entry_ladderTail t hOk k hk
      fit2 := by
        rw [show (openModel t xs lay.ctrl).ctrl = lay.ctrl + 1 from rfl]
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
        rw [show (openModel t xs lay.ctrl).ctrl = lay.ctrl + 1 from rfl]
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
        simp only [openModel, entryModel]
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
  have hpeg : PegRead bT (openModel t xs lay.ctrl) base :=
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
      trits := by simpa [openModel, entryModel] using lay.tri
      top := by
        intro _
        simp [openModel, entryModel]
      fitRow := by
        simp only [openModel, entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have h := origin_lt t sat
        omega
      fitTall := by
        simp only [openModel, entryModel]
        unfold FitsLen i64MaxNat
        decide
      fitCtrl := by
        rw [show (openModel t xs lay.ctrl).ctrl = lay.ctrl + 1 from rfl,
          show (openModel t xs lay.ctrl).tally = 1 from rfl]
        apply FitsLen.of_le base.fitCtrl
        rw [hm.ctrl0, hm.R, hm.mMax]
        refine Nat.add_le_add_left ?_ (lay.ctrl + 1)
        have h1 : 1 ≤ 3 * rowRoom t + 5 :=
          Nat.le_trans (by decide : (1 : Nat) ≤ 5) (Nat.le_add_left 5 _)
        have hx : 3 * rowRoom t + 5 = 1 * (3 * rowRoom t + 5) := (Nat.one_mul _).symm
        have hmul : 1 * (3 * rowRoom t + 5) ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le (tierR t)))
        exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq hx) hmul)
      n_pos := by simpa [openModel, entryModel] using hOk.n_pos
      span := by simpa [openModel, entryModel, hm.cg] using sat.cube_span
      small := by simpa [hm.w, hm.h, hm.r] using hsh.small
      n_small := by simpa [openModel, entryModel] using hsh.n_small
      fitN := by
        simp only [openModel, entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega)
      fitBn := by
        simp only [openModel, entryModel]
        exact FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) hsh.small.2.2.2
      fit3 := by
        simp only [openModel, entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega) }
  refine ⟨bT, hdo, hlad, ?_⟩
  exact
    { inv := hInv
      idx := by simp [openModel, entryModel]
      hn := by simp [openModel, entryModel, hm.n]
      hbench := by simp [openModel, entryModel, hm.bench]
      htally0 := by simp [openModel, entryModel, hm.tally0, climbTallyPrefix]
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
            simp [openModel, entryModel] at h
          offWhenHome := fun _ => hbench
          xD := by rw [hm.xHome, hszD]; decide
          xH := by rw [hm.xHome, hszH]; decide
          xHeld := by simpa [hm.xHome] using h2t (by rw [hszD]; decide)
          xArr := by simpa [hm.x, hm.xHome] using h2a (by rw [hszH]; decide)
          xNe5 := by simp [hm.xHome]
          xNe6 := by simp [hm.xHome]
          gapLen := by simpa [openModel, entryModel, lay.len]
          seg := by simpa [openModel, entryModel] using entry_seg t sat hR
          tierN := by
            rw [htier]
            simp [embTier, openModel, entryModel, ofNat_eq_natCast]
          tierK := by
            rw [htier]
            simp [embTier, openModel, entryModel, ofNat_eq_natCast]
          tierB := by
            rw [htier]
            simp [embTier, openModel, entryModel, hm.bench, ofNat_eq_natCast]
          tierW := by rw [htier]; simp [embTier, hm.w, ofNat_eq_natCast]
          tierH := by rw [htier]; simp [embTier, hm.h, ofNat_eq_natCast]
          tierR := by rw [htier]; simp [embTier, hm.r, ofNat_eq_natCast]
          tierCg := by rw [htier]; simp [embTier, hm.cg, ofNat_eq_natCast]
          tierC := by rw [htier]; simp [embTier, hm.control, ofNat_eq_natCast]
          rowLen := by simp [openModel, entryModel, hm.control, entry_row_len]
          w0 := by simpa [hm.w] using hsh.w0
          h0 := by simpa [hm.h] using hsh.h0
          r0 := by simpa [hm.r] using hsh.r0
          rlt := by simpa [hm.r, hm.h] using hsh.rlt
          n_eq := by simpa [openModel, entryModel, hm.w, hm.h] using hsh.n_eq
          k_le := by simpa [openModel, entryModel] using hsh.k_le
          gap_eq := by simpa [openModel, entryModel, hm.w, hm.r] using hsh.gap
          park := hparkR
          peg := hpeg }
      moves := ⟨lay.moves + pegCount xs, by rw [hmv, ofNat_eq_natCast], by
        rw [show (openModel t xs lay.ctrl).onBench = false from rfl, hm.moves0]
        simp⟩
      slides := ⟨lay.slides, by rw [hsl, ofNat_eq_natCast], by
        rw [show (openModel t xs lay.ctrl).onBench = false from rfl, hm.slides0]
        simp⟩
      ops := by
        intro i hi
        obtain ⟨c, hc, hle⟩ := hopsSlot i hi
        refine ⟨c, hc, ?_⟩
        rw [show (openModel t xs lay.ctrl).onBench = false from rfl, hm.ops0]
        simpa using hle
      peak := ⟨base.peak0, by rw [hpk, ← hm.peak0, ofNat_eq_natCast],
        Nat.le_max_left _ _⟩
      highTop := by
        intro _
        simp [openModel, entryModel]
      parkBelow := by
        simp [openModel, entryModel]
        unfold tallyOrigin
        omega
      holeBelow := by
        simp [openModel, entryModel, hm.ladder0, hm.R, climbAt]
        unfold tallyOrigin
        omega
      fromBelow := by
        intro h
        simp [openModel, entryModel] at h
      finalLe := by
        simpa [openModel, entryModel, hm.tally0] using climbTally_ge 1 (tierClimb t)
      tailFit := by
        have hpre : tallyPrefixesLe 1 (rowRoom t) (tierClimb t ++ []) = true := by
          simpa using sat.prefixes
        have hct : climbTally 1 (tierClimb t) ≤ rowRoom t := by
          rw [← climbTallyPrefix_full]
          exact tallyPrefixesLe_spec 1 (rowRoom t) (tierClimb t) [] hpre
        have ht0m : (openModel t xs lay.ctrl).t0 = tallyOrigin t := rfl
        have hrowL : (openModel t xs lay.ctrl).row.length = t.control := by
          simp [openModel, entryModel, entry_row_len]
        rw [ht0m, hrowL, hm.tally0, List.nil_append]
        have hor := sat.origin_le
        unfold rowRoom at hct
        omega
      tailZero := by
        intro k hk1 _ hix
        have hlt : tallyOrigin t < tallyOrigin t + k := by
          simp [openModel, entryModel] at hk1
          omega
        simpa [openModel, entryModel] using entry_past t (tallyOrigin t + k) hlt hix
      openRoom := by
        intro h2
        have hroom := entry_double_room t sat h2
        simpa [openModel, entryModel, hm.control] using hroom
      openZero := by
        intro _ k hk hix
        have hk0 : k = 0 := by
          simp [openModel, entryModel] at hk
          omega
        subst hk0
        have hix' : tallyOrigin t + 1 < (entryRow t).length := by
          simpa [openModel, entryModel] using hix
        have hpast := entry_past t (tallyOrigin t + 1) (by omega) hix'
        simpa [openModel, entryModel] using hpast
      tmaxLt := ⟨1, by simpa [ofNat_eq_natCast] using htmax, by
        intro _
        simp [openModel, entryModel]⟩
      ctrlLe := by
        simp [openModel, entryModel, hm.ctrl0]
      srcAbove := by
        intro h
        simp [openModel, entryModel] at h }

/-- `Ecbs.invert` on an open walk board is the climb of that tally board. -/
theorem open_invert (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base) :
    ∃ bT,
      Ecbs.invert b ((2 : Nat) : Int) =
        climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) >>= finalTail ∧
      ClimbInvK [] (tierClimb t) bT (openModel t xs lay.ctrl) base := by
  obtain ⟨bT, hdo, hlad, hK⟩ := open_climb b t xs lay hOk sat hR hsh base hm
  let hL : ClimbInvL (tierClimb t) 0 bT base :=
    { done := []
      rest := tierClimb t
      s := openModel t xs lay.ctrl
      split := by simp
      k_eq := rfl
      inv := hK
      ladder := hlad
      m_pos := by simp [openModel, entryModel]
      m_le := by
        rw [show (openModel t xs lay.ctrl).tally = 1 from rfl, hm.control]
        have hC := hOk.ladder
        unfold tierR at hC
        omega
      m_len := by simpa [ofNat_eq_natCast] using hK.inv.len }
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  have hpark : hL.s.parkAt = base.ladder0 + base.R := by
    simp [hL, openModel, entryModel, hm.ladder0, hm.R]
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
  refine ⟨bT, ?_, hK⟩
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
  obtain ⟨bT, hem, hK⟩ := open_invert b t xs lay hOk sat hR hsh base hm
  have hpark : (openModel t xs lay.ctrl).parkAt = base.ladder0 + base.R := by
    simp [openModel, entryModel, hm.ladder0, hm.R]
  have hm0 : 0 < (openModel t xs lay.ctrl).tally := by simp [openModel, entryModel]
  have hcap : ∀ done rest, tierClimb t = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax := by
    intro done rest hsplit
    simpa [hm.tally0, hm.mMax] using
      tallyPrefixesLe_spec 1 (rowRoom t) done rest (by simpa [hsplit] using sat.prefixes)
  have hxLen : base.x.length = base.n := by rw [hm.x, hm.n, lay.len]
  have hxT : allTritList base.x := by simpa [hm.x] using lay.tri
  obtain ⟨b', s', hrun, hs', hK', hgap, htmax⟩ := climb_refines_emit (tierClimb t)
      bT (openModel t xs lay.ctrl) base hK hpark hm0 hcap hxLen hxT
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  cases hL : tierClimb t with
  | nil => simp [hL] at hpos
  | cons r rs =>
      let hole : ClimbModel → Nat → Bool → Nat := fun s _ _ =>
        climbAt base.ladder0 base.R s.ridx
      have hon : s'.onBench = true := by
        rw [hs', hL]
        exact modelClimb_onBench (openModel t xs lay.ctrl) base.x hole r rs
      have hge : 0 ≤ s'.fromHole := by
        rw [hs', hL]
        exact modelClimb_fromHole (openModel t xs lay.ctrl) base.x hole r rs
      have hmt : 0 < s'.tally := by
        rw [hs', modelClimb_tally]
        simp [openModel, entryModel]
        exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) (climbTally_ge 1 (tierClimb t))
      obtain ⟨bU, bC, bOut, bZ, hun, hc, hset, hz, hhome⟩ :=
        final_cube_home hK' hon hge htmax hmt
      have hrun' : climbEmit (climbStepBoard ((2 : Nat) : Int)) bT (tierClimb t) = .ok b' := by
        simpa [hm.xHome] using hrun
      have hok : Ecbs.invert b ((2 : Nat) : Int) = .ok bZ := by
        rw [hem, hrun', ok_bind]
        simp [finalTail, hun, hc, hset, hz, ok_bind]
      have hlay := modelClimb_params (openModel t xs lay.ctrl) base.x hole (tierClimb t)
      have hpair : (s'.gap, s'.tally) =
          invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) := by
        simpa [openModel, entryModel, hm.n, hm.bench, hm.x, lay.len] using hgap
      have hgap1 : s'.gap = (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 :=
        congrArg Prod.fst hpair
      have hn : s'.n = t.n := by
        rw [hs']
        simpa [openModel, entryModel] using hlay.1
      have hk : s'.k = t.k := by
        rw [hs']
        simpa [openModel, entryModel] using hlay.2.1
      have hb : s'.benchlen = t.benchlen := by
        rw [hs']
        simpa [openModel, entryModel] using hlay.2.2
      refine ⟨bZ, hhome.h5, hok, ?_⟩
      refine hhome.arr.trans (congrArg embed ?_)
      rw [hn, hk, hb, hgap1]
      exact (invGap_cube t xs).symm

end EcbsLink2.Link2
