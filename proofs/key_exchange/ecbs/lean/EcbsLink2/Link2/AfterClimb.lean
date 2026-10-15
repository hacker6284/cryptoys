/-
  After the ladder. The climb invariant reserves `2 · n` on the move and slide
  counters while the gap sits on the bench. That reservation is the settle
  inside the final `cube` of the gap. Unpark does not touch those counters.
-/
import EcbsLink2.Link2.ClimbStep
import EcbsLink2.Link2.SetCongr

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- At the end of a bench-on climb, `mv + 2 · n` is inside `moves0 + R · rungCharge`,
    so `mv + 2 · pegs` fits whenever `pegs ≤ n`. -/
theorem pending_move_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (mv : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      FitsLen (mv + 2 * pegs) := by
  obtain ⟨mv, heq, hle⟩ := h.moves
  have hres : mv + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon] using hle
  have hfitN : FitsLen (mv + 2 * base.n) := by
    apply FitsLen.of_le base.fitM
    exact Nat.le_trans hres
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  refine ⟨mv, heq, ?_⟩
  apply FitsLen.of_le hfitN
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpegs) mv

/-- The same reservation on the slide counter. -/
theorem pending_slide_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (sl : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      FitsLen (sl + 2 * pegs) := by
  obtain ⟨sl, heq, hle⟩ := h.slides
  have hres : sl + 2 * base.n ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    simpa [hon] using hle
  have hfitN : FitsLen (sl + 2 * base.n) := by
    apply FitsLen.of_le base.fitS
    exact Nat.le_trans hres
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  refine ⟨sl, heq, ?_⟩
  apply FitsLen.of_le hfitN
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpegs) sl

/-- Unpark leaves the move counter alone, so the reserved settle still fits
    on the board the final cube reads. -/
theorem pending_move_fit_unpark
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (hk : done.length ≤ base.R)
    (pegs : Nat) (hpegs : pegs ≤ base.n) :
    ∃ (bU : Ecbs.Board) (mv : Nat),
      Ecbs.unpark_rung b = .ok bU ∧
      bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bU.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bU.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bU.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      FitsLen (mv + 2 * pegs) := by
  obtain ⟨bU, hun, _, _, _, _, hbon, _, hbench, hmvU, hslU, _, _, _, _, _, _, _, _, _, _⟩ :=
    unpark_after_climb h hge
  obtain ⟨mv, hmv, hfit⟩ := pending_move_fit h hon hk pegs hpegs
  refine ⟨bU, mv, hun, hmvU.trans hmv, hslU, hbon, hbench, hfit⟩

/-- Case 1. A home rung's cube writes ops slot 1 even when the following settle
    is a no-op, and that write is at most the tally. With the tally at most
    `mMax`, every slot grows by at most `mMax + 2`, one under the charge, so a
    bench-on board still has room for one op inside `fitO`. -/
theorem pending_ops_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R)
    (i : Nat) (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ∃ (c : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      FitsLen (c + 1) := by
  obtain ⟨c, hc, hle⟩ := h.ops i hi
  have hres : c + 1 ≤ base.ops0 + done.length * (base.mMax + 3) := by
    simpa [hon] using hle
  refine ⟨c, hc, ?_⟩
  apply FitsLen.of_le base.fitO
  exact Nat.le_trans hres (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)

/-- Comb, fold, and the outer settle, past the settle reserved while on the bench. -/
theorem tail_move_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R) :
    ∃ (mv : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      FitsLen (mv + 2 * base.n + pegCharge base.n base.bench) := by
  obtain ⟨mv, heq, hle⟩ := h.moves
  have hres : mv + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon] using hle
  have hcap : mv + 2 * base.n + pegCharge base.n base.bench ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax +
        pegCharge base.n base.bench := by
    have hmul : done.length * rungCharge base.n base.bench base.mMax ≤
        base.R * rungCharge base.n base.bench base.mMax :=
      Nat.mul_le_mul_right _ hk
    omega
  exact ⟨mv, heq, FitsLen.of_le base.fitTailM hcap⟩

/-- The outer settle's slides, past the settle reserved while on the bench. -/
theorem tail_slide_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hk : done.length ≤ base.R) :
    ∃ (sl : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      FitsLen (sl + 2 * base.n + 2 * base.n) := by
  obtain ⟨sl, heq, hle⟩ := h.slides
  have hres : sl + 2 * base.n ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    simpa [hon] using hle
  have hcap : sl + 2 * base.n + 2 * base.n ≤
      base.slides0 + base.R * rungSlideCharge base.n base.mMax + 2 * base.n := by
    have hmul : done.length * rungSlideCharge base.n base.mMax ≤
        base.R * rungSlideCharge base.n base.mMax :=
      Nat.mul_le_mul_right _ hk
    omega
  exact ⟨sl, heq, FitsLen.of_le base.fitTailS hcap⟩

/-- Unpark adds two and `tally_clear` adds one per tally hole. Both fit in the
    extra control step the climb budget already carries. -/
theorem tail_ctrl_fit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hk : done.length ≤ base.R)
    (ht : s.tally ≤ base.mMax) :
    FitsLen (s.ctrl + 2 + s.tally) := by
  apply FitsLen.of_le base.fitCtrl
  have hmul : done.length * (3 * base.mMax + 5) ≤
      base.R * (3 * base.mMax + 5) :=
    Nat.mul_le_mul_right _ hk
  have hextra : 2 + s.tally ≤ 3 * base.mMax + 5 := by omega
  have hsplit : base.R * (3 * base.mMax + 5) + (3 * base.mMax + 5) =
      (base.R + 1) * (3 * base.mMax + 5) := by
    rw [← Nat.succ_mul]
  have hctrl := h.ctrlLe
  omega

/-- Moves, slides, ops, the control counter, and peak, for the whole tail
    unpark → final cube → outer settle → `tally_clear`. Unpark copies the
    counters. The reserved settle covers the cube's internal slide. `pegCharge`
    covers the comb, the fold, and the outer settle. `2 · n` covers that
    settle's slides. One op covers the cube's slot-1 bump. -/
theorem tail_counters
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax)
    (i : Nat) (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ∃ (bU : Ecbs.Board) (mv sl c pk : Nat),
      Ecbs.unpark_rung b = .ok bU ∧
      bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bU.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      bU.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
      pk ≤ max base.peak0 7 ∧
      bU.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bU.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      FitsLen (mv + 2 * base.n + pegCharge base.n base.bench) ∧
      FitsLen (sl + 2 * base.n + 2 * base.n) ∧
      FitsLen (c + 1) ∧
      FitsLen (s.ctrl + 2 + s.tally) := by
  have hk : done.length ≤ base.R := by simpa using h.kLe
  obtain ⟨bU, hun, _, _, _, _, hbon, _, hbench, hmvU, hslU, hpkU, _, _, _, _, hopsU,
      _, _, _, _⟩ :=
    unpark_after_climb h hge
  obtain ⟨mv, hmv, hfitM⟩ := tail_move_fit h hon hk
  obtain ⟨sl, hsl, hfitS⟩ := tail_slide_fit h hon hk
  obtain ⟨c, hc, hfitO⟩ := pending_ops_fit h hon hk i hi
  obtain ⟨pk, hpk, hpkLe⟩ := h.peak
  exact ⟨bU, mv, sl, c, pk, hun, hmvU.trans hmv, hslU.trans hsl, hopsU, hc, hpk,
    hpkLe, hbon, hbench, hfitM, hfitS, hfitO, tail_ctrl_fit h hk ht⟩

/-- The settled counter plus the comb, the fold, and one more settle of `2 · n`
    is the reserved settle plus `pegCharge`. -/
theorem move_tail_bound (mv pegs n bench : Nat) (hpeg : 2 * pegs ≤ 2 * n) :
    mv + 2 * pegs + 2 * n + 3 * (bench - n) ≤
      mv + 2 * n + (4 * n + 3 * (bench - n)) := by
  omega

theorem move_tail_bound_outer (mv pegs n bench : Nat) (hpeg : 2 * pegs ≤ 2 * n) :
    mv + 2 * pegs + 2 * n + 3 * (bench - n) + 2 * n ≤
      mv + 2 * n + (4 * n + 3 * (bench - n)) := by
  omega


/-- `settle` writes a home and the move, slide, and peak counters. The row,
    the tally bookkeeping, the control counter, and the tier stay. -/
theorem settleBoard_plain (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_3row =
      b.sudo_5Board_3row ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · rw [settle_peak b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [settle_keep b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unpark writes the parked colour back and clears the park hole. Both holes
    sit on the embedded control row, so the row stays an embedding. -/
theorem unpark_row_embed
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base) (hge : 0 ≤ s.fromHole) :
    ∃ (bU : Ecbs.Board) (row : List Nat),
      Ecbs.unpark_rung b = .ok bU ∧
      bU.sudo_5Board_3row = embed row ∧
      row.length = s.row.length := by
  obtain ⟨colour, hcell⟩ := h.shape.park.parkHeld hge
  have hsrc := h.shape.park.srcOk hge
  let src := s.fromHole.toNat
  have hRowS : src < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact hsrc.1
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hColour : b.sudo_5Board_3row[s.parkAt] = (colour : Int) := by
    have hget := embed_nat s.row s.parkAt h.shape.park.parkLt
    simp [h.inv.row, hget, hcell]
  have hFrom : b.sudo_5Board_11parked_from = (src : Int) := by
    rw [h.inv.fromP]
    exact h.shape.park.fromNat hge
  have hback := unpark_rung_back b src s.parkAt colour s.high base.control s.ctrl
    hFrom h.inv.park hRowS hRowP hColour h.shape.tierC hsrc.2.1 h.inv.high
    hsrc.2.2.1 h.inv.ctrl h.shape.park.fit2
  let row1 := s.row.set src colour
  let row := row1.set s.parkAt 0
  have hcast : (colour : Int) = Int.ofNat colour := (ofNat_eq_natCast colour).symm
  have h1 := Array.set_congr_arr h.inv.row hRowS (Int.ofNat colour)
  have h1e : (embed s.row).set ⟨src, h.inv.row ▸ hRowS⟩ (Int.ofNat colour) =
      embed row1 := by
    have hset := embed_set s.row src colour hsrc.1
    have hfin : (⟨src, h.inv.row ▸ hRowS⟩ : Fin (embed s.row).size) =
        ⟨src, by rw [size_embed]; exact hsrc.1⟩ := Fin.ext rfl
    rw [hfin]
    exact hset
  have hmid : b.sudo_5Board_3row.set ⟨src, hRowS⟩ (colour : Int) = embed row1 := by
    rw [hcast]
    exact h1.trans h1e
  have hi2 : s.parkAt < (b.sudo_5Board_3row.set ⟨src, hRowS⟩ (colour : Int)).size := by
    rw [Array.size_set]; exact hRowP
  have h2 := Array.set_congr_arr hmid hi2 (Int.ofNat 0)
  have hparkLen : s.parkAt < row1.length := by
    simp [row1, List.length_set]
    exact h.shape.park.parkLt
  have h2e : (embed row1).set ⟨s.parkAt, hmid ▸ hi2⟩ (Int.ofNat 0) = embed row := by
    have hset := embed_set row1 s.parkAt 0 hparkLen
    have hfin : (⟨s.parkAt, hmid ▸ hi2⟩ : Fin (embed row1).size) =
        ⟨s.parkAt, by rw [size_embed]; exact hparkLen⟩ := Fin.ext rfl
    rw [hfin]
    exact hset
  refine ⟨_, row, hback, ?_, ?_⟩
  · exact h2.trans h2e
  · simp [row, row1, List.length_set]

/-- Home 5 holds `xs` after the final settle and the tally clear. The index
    proof stays inside the structure so a later `obtain` does not case on it. -/
structure SettledHome (b : Ecbs.Board) (xs : List Nat) : Prop where
  h5 : 5 < b.sudo_5Board_4home.size
  arr : b.sudo_5Board_4home[5]'h5 = embed xs

/-- What the check multiply reads, carried from the climb board through the
    tail. Home 2 is not written: unpark keeps the homes, and the cube and both
    settles write home 5 only. The i64 fact on ops slot 0 stays inside `ops0`. -/
structure CheckRead (b0 b : Ecbs.Board) : Prop where
  h2H0 : 2 < b0.sudo_5Board_4home.size
  h2D0 : 2 < b0.sudo_5Board_4held.size
  h2H : 2 < b.sudo_5Board_4home.size
  h2D : 2 < b.sudo_5Board_4held.size
  home2 : b.sudo_5Board_4home[2]'h2H = b0.sudo_5Board_4home[2]'h2H0
  held2 : b.sudo_5Board_4held[2]'h2D = b0.sudo_5Board_4held[2]'h2D0
  marker : b.sudo_5Board_9marker_on = false
  benchOff : b.sudo_5Board_8bench_on = false
  spareD : 6 < b.sudo_5Board_4held.size
  spareH : 6 < b.sudo_5Board_4home.size
  spareE : b.sudo_5Board_4held[6]'spareD = false
  h7 : 7 ≤ b.sudo_5Board_4held.size
  opsGt : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : ∃ c : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'opsGt = (c : Int) ∧
    FitsLen (c + 1)
  moves : ∃ mv : Nat, b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)
  peak : ∃ pk : Nat, b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int)
  peakS : ∃ p : Nat, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  hole : ∃ hole : Nat, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hole : Int)
  h5D : 5 < b.sudo_5Board_4held.size
  held5 : b.sudo_5Board_4held[5]'h5D = true
  tierEq : b.sudo_5Board_1t = b0.sudo_5Board_1t
  /-- The check multiply's copy, schoolbook, and fold still fit an i64.
      `n` is the tier length and `bench` its bench, read off `b`. The copy is
      bounded by `n`, which is at least `pegCount` of a length-`n` home. -/
  fitMul : ∃ (mv n bench : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
    b.sudo_5Board_1t.sudo_4Tier_8benchlen = (bench : Int) ∧
    FitsLen (mv + n + n * (n + 1) + 3 * (bench - n) + 2 * n)

/-- Unpark, the final cube of the gap onto the gap, and the outer settle.
    The cube's internal settle spends the reserved `2 · n`. The comb, the fold,
    and the outer settle spend `pegCharge`. The outer settle's slides spend
    another `2 · n`. The cube's ops bump spends the reserved op. -/
theorem final_cube_settle
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax)
    (hm : 0 < s.tally) :
    ∃ (bU bC bOut bZ : Ecbs.Board) (mv sl : Nat) (row : List Nat),
      Ecbs.unpark_rung b = .ok bU ∧
      Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC ∧
      Ecbs.settle bC = .ok bOut ∧
      Ecbs.tally_clear bOut = .ok bZ ∧
      bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bU.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      bOut.sudo_5Board_8bench_on = false ∧
      bOut.sudo_5Board_3row = embed row ∧
      bZ.sudo_5Board_9tally_len = 0 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves =
        bOut.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides =
        bOut.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
        bOut.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      SettledHome bZ (fieldCube s.n s.k s.benchlen s.gap) ∧
      CheckRead b bZ ∧
      FitsLen (mv + 2 * base.n + pegCharge base.n base.bench) ∧
      FitsLen (sl + 2 * base.n + 2 * base.n) ∧
      FitsLen (s.ctrl + 2 + s.tally) := by
  have hk : done.length ≤ base.R := by simpa using h.kLe
  obtain ⟨bU, hun, _, _, hhomeU, hheldU, hbonU, htoU, hbenchU, hmvU, hslU, hpkU,
      hctrlU, ht0U, htierU, hmkU, hopsU, hstrictU, hholeU, hlenU, hhighU⟩ :=
    unpark_after_climb h hge
  obtain ⟨mv, hmv, htailM⟩ := tail_move_fit h hon hk
  obtain ⟨sl, hsl, htailS⟩ := tail_slide_fit h hon hk
  have hmvB : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := hmvU.trans hmv
  have hslB : bU.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := hslU.trans hsl
  obtain ⟨pk, hpk, _⟩ := h.peak
  have hpkB : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
    rw [hpkU, hpk, ofNat_eq_natCast]
  have hgapB := h.inv.gapBench hon
  have hbon : bU.sudo_5Board_8bench_on = true := hbonU.trans hgapB.1
  have hto : bU.sudo_5Board_8bench_to = (5 : Int) := htoU.trans hgapB.2.1
  let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
  have hbench : bU.sudo_5Board_5bench = embed xs := by
    simpa [xs] using hbenchU.trans hgapB.2.2.1
  have h5H : 5 < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact h.inv.hG
  have h5D : 5 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact h.inv.hGs
  have h7 : 7 ≤ bU.sudo_5Board_4held.size := by rw [hheldU]; exact h.shape.h7
  have hempty : bU.sudo_5Board_4held[5] = false :=
    cell_eq_of hheldU (h.shape.gapClear hon)
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [htierU]; exact h.shape.tierN
  have hnle : s.n ≤ s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hlenX : xs.length = s.benchlen :=
    bench_pad_len s.gap s.n s.benchlen h.shape.gapLen hnle
  have hposX : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnle
  have hzero := bench_pad_zero s.gap s.n s.benchlen h.shape.gapLen hnle
  have htake : xs.take s.n = s.gap := by
    have hge : s.n ≤ s.gap.length := Nat.le_of_eq h.shape.gapLen.symm
    have hpre : s.gap.take s.n = s.gap :=
      List.take_of_length_le (Nat.le_of_eq h.shape.gapLen)
    rw [show xs = s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0 from rfl, hpre,
      List.take_append_of_le_length hge]
    exact hpre
  have hpegs : pegCount (xs.take s.n) ≤ s.n := by
    rw [htake, ← h.shape.gapLen]
    exact pegCount_le s.gap
  have hfitMove := pending_move_fit h hon hk (pegCount (xs.take s.n))
    (Nat.le_trans hpegs (Nat.le_of_eq h.hn))
  obtain ⟨mv0, hmv0, hfitM⟩ := hfitMove
  have hmvSame : mv = mv0 := ofNat_inj_nat (hmv.symm.trans hmv0)
  have hfitSl := pending_slide_fit h hon hk (pegCount (xs.take s.n))
    (Nat.le_trans hpegs (Nat.le_of_eq h.hn))
  obtain ⟨sl0, hsl0, hfitS0⟩ := hfitSl
  have hslSame : sl = sl0 := ofNat_inj_nat (hsl.symm.trans hsl0)
  have hpeg2 : FitsLen (2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le (by rw [hmvSame]; exact hfitM) (Nat.le_add_left _ mv)
  have hmk : bU.sudo_5Board_9marker_on = false := hmkU.trans h.inv.marker
  have hops1 : 1 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact h.shape.peg.opsGt
  obtain ⟨cOps, hcOps, hfops⟩ := pending_ops_fit h hon hk 1 h.shape.peg.opsGt
  have hop1 : bU.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOps : Int) := by
    have hget := arr_get hopsU 1 hops1
    exact hget.trans ((array_get_irrel (h1 := hopsU ▸ hops1)
      (h2 := h.shape.peg.opsGt)).trans hcOps)
  have hfitBn : FitsLen s.benchlen := h.shape.peg.fitBn
  have hslideEq := cube_settle_other bU 5 5 5 xs s.n mv sl pk cOps
    hmk hbon hto h5H h5D h7 hempty hbench hnU hposX (by rw [hlenX]; exact hnle) hzero
    h.shape.peg.fitN (by rw [hlenX]; exact hfitBn)
    (by rw [hmvB, ofNat_eq_natCast]) (by rw [hslB, ofNat_eq_natCast]) hpkB
    hpeg2 (by rw [hmvSame]; exact hfitM) (by rw [hslSame]; exact hfitS0)
    hops1 hop1 hfops
  let bS := settleBoard bU 5 h5H h5D xs s.n mv sl pk
  have hcubeEq : Ecbs.cube bU Ecbs.gap Ecbs.gap = Ecbs.cube bS (5 : Int) (5 : Int) := by
    simpa [bS, Ecbs.gap] using hslideEq
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hF : 5 < bS.sudo_5Board_4held.size :=
    settle_held_lt bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hHome : 5 < bS.sudo_5Board_4home.size :=
    settle_home_lt bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hHF : bS.sudo_5Board_4held[5] = true := by
    have heq := settle_held_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hget := arr_get heq 5 hF
    exact hget.trans (Array.getElem_set_eq _ ⟨5, h5D⟩ true rfl
      (by rw [Array.size_set]; exact h5D))
  have hArr : bS.sudo_5Board_4home[5] = embed s.gap := by
    have heq := settle_home_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hget := arr_get heq 5 hHome
    have hset := Array.getElem_set_eq _ ⟨5, h5H⟩ (embed (xs.take s.n)) rfl
      (by rw [Array.size_set]; exact h5H)
    exact (hget.trans hset).trans (congrArg embed htake)
  let pegs := pegCount (xs.take s.n)
  let mvS : Nat := mv + 2 * pegs
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [settle_moves_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, ofNat_eq_natCast]
  let slS : Nat := sl + 2 * pegs
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = (slS : Int) := by
    rw [settle_slides_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, ofNat_eq_natCast]
  let pkS : Nat :=
    if pk < countHeld (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 then
      countHeld (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 else pk
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    rw [settle_peak_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk hpkB, ofNat_eq_natCast]
  have htierS : bS.sudo_5Board_1t = b.sudo_5Board_1t :=
    (settle_tier_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk).trans htierU
  have hmkS : bS.sudo_5Board_9marker_on = false :=
    (settle_marker_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk).trans hmk
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk]; exact hops1
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOps : Int) := by
    have hget := arr_get (settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk) 1 hopsS
    exact hget.trans hop1
  obtain ⟨peakS, hpeakS0⟩ := h.shape.peg.peakS
  have hpeakS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, hstrictU]
    exact hpeakS0
  obtain ⟨holeN, hhole0⟩ := h.shape.peg.holeM
  have hhole : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    rw [settle_hole_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, hholeU]
    exact hhole0
  have hbody : mvS + 2 * s.n + 3 * (s.benchlen - s.n) ≤
      mv + 2 * base.n + pegCharge base.n base.bench := by
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have hraw := move_tail_bound mv pegs base.n base.bench h2
    rw [show mvS = mv + 2 * pegs from rfl, h.hn, h.hbench, pegCharge]
    exact hraw
  have htop : mvS + 2 * s.n + 3 * (s.benchlen - s.n) + 2 * s.n ≤
      mv + 2 * base.n + pegCharge base.n base.bench := by
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have hraw := move_tail_bound_outer mv pegs base.n base.bench h2
    rw [show mvS = mv + 2 * pegs from rfl, h.hn, h.hbench, pegCharge]
    exact hraw
  have hfold : FitsLen (mvS + 2 * s.n + 3 * (s.benchlen - s.n)) :=
    FitsLen.of_le htailM hbody
  have hfm : FitsLen (mvS + 2 * s.n) :=
    FitsLen.of_le hfold (Nat.le_add_right _ _)
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk, Array.size_set]
    exact h7
  have hcube := cube_refines bS 5 5 s.gap base.w base.h base.r s.n s.k mvS holeN s.benchlen pkS peakS cOps base.cg hmkS hoffS hopsS hopS hfops (by rw [htierS, h.shape.tierB, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierCg, ofNat_eq_natCast]) h.shape.peg.span hF hHome hHF hArr h7S h.shape.peg.n_pos (by rw [htierS]; exact h.shape.tierN) h.shape.gapLen h.shape.peg.fitN hmvS hpkS hpeakS h.shape.peg.trits h.shape.peg.fit3 hfm ⟨h.shape.w0, h.shape.h0, h.shape.rlt, h.shape.r0, h.shape.n_eq, h.shape.k_le, h.shape.gap_eq⟩ (by rw [htierS, h.shape.tierW, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierH, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierR, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierK, ofNat_eq_natCast]) (by rw [hhole, ofNat_eq_natCast]) h.shape.peg.small h.shape.peg.n_small h.shape.peg.fitBn hfold
  obtain ⟨bC, hrunC, honC, htoC, hbenchC, htakeC, hzeroC, hmvC, _hpkC, hslC,
      _htierC, _hszH, _hhomeC, _hheldC, _hmkC, _hrowC, _hopsC, _ht0C, _hhighC, _hctrlC⟩ :=
    hcube
  have hprog : Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC := hcubeEq.trans hrunC
  let fold := laneFold s.n (s.n - s.k) (combStrip s.n s.benchlen s.gap)
  have hlenF : fold.length = s.benchlen := by
    rw [laneFold_length _ _ _ (by rw [combStrip_length]; exact hnle), combStrip_length]
  have hzeroF : ∀ i, s.n ≤ i → ∀ hi : i < fold.length, fold[i] = 0 := by
    intro i hi hix
    have hc := hzeroC i hi (by rw [hlenF] at hix; exact hix)
    rw [← coeff_eq_get fold i hix]
    exact hc
  have hmvN : cubeMoves mvS s.gap s.n s.k s.benchlen ≤
      mvS + 2 * s.n + 3 * (s.benchlen - s.n) :=
    cubeMoves_le mvS s.gap s.n s.k s.benchlen
  have hpegF : pegCount (fold.take s.n) ≤ s.n := pegCount_take_le fold s.n
  have hfitOut : FitsLen (cubeMoves mvS s.gap s.n s.k s.benchlen +
      2 * pegCount (fold.take s.n)) := by
    apply FitsLen.of_le htailM
    have hsum := Nat.add_le_add hmvN (Nat.mul_le_mul_left 2 hpegF)
    exact Nat.le_trans hsum htop
  have hfitOutS : FitsLen (slS + 2 * pegCount (fold.take s.n)) := by
    apply FitsLen.of_le htailS
    have h2 : 2 * pegs ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegs
    have h3 : 2 * pegCount (fold.take s.n) ≤ 2 * base.n := by
      rw [← h.hn]
      exact Nat.mul_le_mul_left 2 hpegF
    rw [show slS = sl + 2 * pegs from rfl]
    exact Nat.add_le_add (Nat.add_le_add_left h2 sl) h3
  have hfitPeg : FitsLen (2 * pegCount (fold.take s.n)) :=
    FitsLen.of_le hfitOut (Nat.le_add_left _ _)
  have h5HC : 5 < bC.sudo_5Board_4home.size := by
    rw [_hszH]; exact hHome
  have h5DC : 5 < bC.sudo_5Board_4held.size := by
    rw [_hheldC, Array.size_set]; exact hF
  have hemptyC : bC.sudo_5Board_4held[5] = false := by
    have hget := arr_get _hheldC 5 h5DC
    exact hget.trans (Array.getElem_set_eq _ ⟨5, hF⟩ false rfl
      (by rw [Array.size_set]; exact hF))
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    rw [_hheldC, Array.size_set]; exact h7S
  have hpkCnat : bC.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7)) :=
    _hpkC
  have hsettle := settle_refines bC 5 fold s.n
      (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
      (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
    h5HC h5DC h7C honC htoC hemptyC
    (by simpa [fold] using hbenchC)
    (by rw [_htierC, htierS]; exact h.shape.tierN)
    (by
      rw [hlenF]
      exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnle)
    (by rw [hlenF]; exact hnle)
    hzeroF h.shape.peg.fitN (by rw [hlenF]; exact h.shape.peg.fitBn)
    (by rw [hmvC, ofNat_eq_natCast])
    (by rw [hslC, hslS, ofNat_eq_natCast])
    (by rw [hpkCnat, ofNat_eq_natCast])
    hfitPeg hfitOut hfitOutS
  let bOut := settleBoard bC 5 h5HC h5DC fold s.n
      (cubeMoves mvS s.gap s.n s.k s.benchlen) slS
      (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have hplainS := settleBoard_plain bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hOff := cube_off_eq bS 5 5 s.gap base.w base.h base.r s.n s.k mvS holeN s.benchlen pkS peakS cOps base.cg hmkS hoffS hopsS hopS hfops (by rw [htierS, h.shape.tierB, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierCg, ofNat_eq_natCast]) h.shape.peg.span hF hHome hHF hArr h7S h.shape.peg.n_pos (by rw [htierS]; exact h.shape.tierN) h.shape.gapLen h.shape.peg.fitN hmvS hpkS hpeakS h.shape.peg.trits h.shape.peg.fit3 hfm ⟨h.shape.w0, h.shape.h0, h.shape.rlt, h.shape.r0, h.shape.n_eq, h.shape.k_le, h.shape.gap_eq⟩ (by rw [htierS, h.shape.tierW, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierH, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierR, ofNat_eq_natCast]) (by rw [htierS, h.shape.tierK, ofNat_eq_natCast]) (by rw [hhole, ofNat_eq_natCast]) h.shape.peg.small h.shape.peg.n_small h.shape.peg.fitBn hfold
  have hbC : bC = cubeOffBoard bS 5 5 s.gap s.n s.k mvS holeN s.benchlen pkS peakS cOps
      hopsS hF hHome :=
    Except.ok.inj (hrunC.symm.trans hOff)
  have hplainO := settleBoard_plain bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  obtain ⟨bRow, row, hunR, hrowE, hlenR⟩ := unpark_row_embed h hge
  have hbU : bU = bRow := Except.ok.inj (hun.symm.trans hunR)
  have hrowOut : bOut.sudo_5Board_3row = embed row := by
    have hU : bU.sudo_5Board_3row = embed row := by rw [hbU]; exact hrowE
    have hSrow : bS.sudo_5Board_3row = bU.sudo_5Board_3row := hplainS.1
    have hCrow : bC.sudo_5Board_3row = bS.sudo_5Board_3row := by rw [hbC]; simp [cubeOffBoard]
    have hOrow : bOut.sudo_5Board_3row = bC.sudo_5Board_3row := by
      simpa [bOut] using hplainO.1
    exact hOrow.trans (hCrow.trans (hSrow.trans hU))
  have hlenOut : bOut.sudo_5Board_9tally_len = (s.tally : Int) := by
    have hU : bU.sudo_5Board_9tally_len = (s.tally : Int) := hlenU.trans h.inv.len
    have hSlen : bS.sudo_5Board_9tally_len = bU.sudo_5Board_9tally_len := hplainS.2.1
    have hClen : bC.sudo_5Board_9tally_len = bS.sudo_5Board_9tally_len := by rw [hbC]; simp [cubeOffBoard]
    have hOlen : bOut.sudo_5Board_9tally_len = bC.sudo_5Board_9tally_len := by
      simpa [bOut] using hplainO.2.1
    exact hOlen.trans (hClen.trans (hSlen.trans hU))
  have ht0Out : bOut.sudo_5Board_6tally0 = (s.t0 : Int) := by
    have hU : bU.sudo_5Board_6tally0 = (s.t0 : Int) := ht0U.trans h.inv.t0
    have hSt : bS.sudo_5Board_6tally0 = bU.sudo_5Board_6tally0 := hplainS.2.2.1
    have hCt : bC.sudo_5Board_6tally0 = bS.sudo_5Board_6tally0 := by rw [hbC]; simp [cubeOffBoard]
    have hOt : bOut.sudo_5Board_6tally0 = bC.sudo_5Board_6tally0 := by
      simpa [bOut] using hplainO.2.2.1
    exact hOt.trans (hCt.trans (hSt.trans hU))
  have hctrlOut : bOut.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 : Nat) : Int) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 : Nat) : Int) := by
      rw [hctrlU, ofNat_eq_natCast]
    have hSc : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        bU.sudo_5Board_4cost.sudo_5Costs_4ctrl := hplainS.2.2.2.1
    have hCc : bC.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl := by rw [hbC]; simp [cubeOffBoard]
    have hOc : bOut.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        bC.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
      simpa [bOut] using hplainO.2.2.2.1
    exact hOc.trans (hCc.trans (hSc.trans hU))
  have hhighOut : bOut.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
      hhighU.trans h.inv.high
    have hSh : bS.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bU.sudo_5Board_4cost.sudo_5Costs_15control_highest := hplainS.2.2.2.2.1
    have hCh : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bS.sudo_5Board_4cost.sudo_5Costs_15control_highest := by rw [hbC]; simp [cubeOffBoard]
    have hOh : bOut.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bC.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
      simpa [bOut] using hplainO.2.2.2.2.1
    exact hOh.trans (hCh.trans (hSh.trans hU))
  have htierOut : bOut.sudo_5Board_1t = b.sudo_5Board_1t := by
    have hSt : bS.sudo_5Board_1t = bU.sudo_5Board_1t := hplainS.2.2.2.2.2
    have hCt : bC.sudo_5Board_1t = bS.sudo_5Board_1t := by rw [hbC]; simp [cubeOffBoard]
    have hOt : bOut.sudo_5Board_1t = bC.sudo_5Board_1t := by
      simpa [bOut] using hplainO.2.2.2.2.2
    exact hOt.trans (hCt.trans (hSt.trans htierU))
  have hroom : s.t0 + s.tally ≤ row.length := by
    rw [hlenR]
    exact h.shape.seg.room
  have hIn : s.t0 + s.tally ≤ base.control := by
    have hlenRow : row.length = base.control := hlenR.trans h.shape.rowLen
    rw [hlenRow] at hroom
    exact hroom
  have hTop : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop hm]
    exact Nat.le_refl _
  have hclear := tally_clear_refines bOut row s.t0 s.tally (s.ctrl + 2) s.high base.control
    hm hlenOut ht0Out hrowOut hroom
    (by rw [htierOut]; exact h.shape.tierC)
    hhighOut hTop hctrlOut hIn
    h.shape.peg.fitRow (tail_ctrl_fit h hk ht) h.shape.peg.fitTall
  let bZ := { touchRow bOut (embed (paintZero row s.t0 s.tally))
      (Int.ofNat (s.ctrl + 2 + s.tally)) with sudo_5Board_9tally_len := 0 }
  have hclearZ : Ecbs.tally_clear bOut = .ok bZ := by
    simpa [bZ] using hclear
  have hhomeOut := settle_home_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have htake : fold.take s.n = fieldCube s.n s.k s.benchlen s.gap := htakeC
  have h5Z : 5 < bZ.sudo_5Board_4home.size := by
    have h5O : 5 < bOut.sudo_5Board_4home.size := by
      rw [hhomeOut, Array.size_set]
      exact h5HC
    simpa [bZ, touchRow] using h5O
  have hgetZ : bZ.sudo_5Board_4home[5]'h5Z =
      embed (fieldCube s.n s.k s.benchlen s.gap) := by
    have hZh : bZ.sudo_5Board_4home = bOut.sudo_5Board_4home := by
      simp [bZ, touchRow]
    have hsz : 5 < (bC.sudo_5Board_4home.set ⟨5, h5HC⟩ (embed (fold.take s.n))).size := by
      rw [Array.size_set]
      exact h5HC
    have hget := Array.getElem_set_eq bC.sudo_5Board_4home ⟨5, h5HC⟩
        (embed (fold.take s.n)) rfl hsz
    have hcell : bOut.sudo_5Board_4home[5]'(by rw [hhomeOut]; exact hsz) =
        embed (fieldCube s.n s.k s.benchlen s.gap) :=
      (cell_eq_of hhomeOut hget).trans (congrArg embed htake)
    exact cell_eq_of hZh hcell
  have hne52 : (5 : Nat) ≠ 2 := by decide
  have hne56 : (5 : Nat) ≠ 6 := by decide
  have h2H0 : 2 < b.sudo_5Board_4home.size :=
    Nat.lt_trans (by decide : (2 : Nat) < 5) h.inv.hG
  have h2D0 : 2 < b.sudo_5Board_4held.size :=
    Nat.lt_trans (by decide : (2 : Nat) < 5) h.inv.hGs
  have h2HU : 2 < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact h2H0
  have h2DU : 2 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact h2D0
  have hhome2U : bU.sudo_5Board_4home[2]'h2HU = b.sudo_5Board_4home[2]'h2H0 :=
    cell_eq_of hhomeU (Eq.refl (b.sudo_5Board_4home[2]'h2H0))
  have hheld2U : bU.sudo_5Board_4held[2]'h2DU = b.sudo_5Board_4held[2]'h2D0 :=
    cell_eq_of hheldU (Eq.refl (b.sudo_5Board_4held[2]'h2D0))
  have hhomeS := settle_home_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have hheldS := settle_held_eq bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
  have h2HS : 2 < bS.sudo_5Board_4home.size := by
    rw [hhomeS, Array.size_set]; exact h2HU
  have h2DS : 2 < bS.sudo_5Board_4held.size := by
    rw [hheldS, Array.size_set]; exact h2DU
  have hhome2S : bS.sudo_5Board_4home[2]'h2HS = bU.sudo_5Board_4home[2]'h2HU := by
    have hsz : 2 < (bU.sudo_5Board_4home.set ⟨5, h5H⟩ (embed (xs.take s.n))).size := by
      rw [Array.size_set]; exact h2HU
    exact cell_eq_of hhomeS
      (Array.getElem_set_ne bU.sudo_5Board_4home ⟨5, h5H⟩ (embed (xs.take s.n)) hsz hne52)
  have hheld2S : bS.sudo_5Board_4held[2]'h2DS = bU.sudo_5Board_4held[2]'h2DU := by
    have hsz : 2 < (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true).size := by
      rw [Array.size_set]; exact h2DU
    exact cell_eq_of hheldS
      (Array.getElem_set_ne bU.sudo_5Board_4held ⟨5, h5D⟩ true hsz hne52)
  have h2HC : 2 < bC.sudo_5Board_4home.size := by
    rw [_hhomeC, Array.size_set]; exact h2HS
  have h2DC : 2 < bC.sudo_5Board_4held.size := by
    rw [_hheldC, Array.size_set]; exact h2DS
  have hhome2C : bC.sudo_5Board_4home[2]'h2HC = bS.sudo_5Board_4home[2]'h2HS := by
    have hsz : 2 < (bS.sudo_5Board_4home.set ⟨5, hHome⟩ (#[] : Array Int)).size := by
      rw [Array.size_set]; exact h2HS
    exact cell_eq_of _hhomeC
      (Array.getElem_set_ne bS.sudo_5Board_4home ⟨5, hHome⟩ (#[] : Array Int) hsz hne52)
  have hheld2C : bC.sudo_5Board_4held[2]'h2DC = bS.sudo_5Board_4held[2]'h2DS := by
    have hsz : 2 < (bS.sudo_5Board_4held.set ⟨5, hF⟩ false).size := by
      rw [Array.size_set]; exact h2DS
    exact cell_eq_of _hheldC
      (Array.getElem_set_ne bS.sudo_5Board_4held ⟨5, hF⟩ false hsz hne52)
  have hheldOut := settle_held_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have h2HO : 2 < bOut.sudo_5Board_4home.size := by
    rw [hhomeOut, Array.size_set]; exact h2HC
  have h2DO : 2 < bOut.sudo_5Board_4held.size := by
    rw [hheldOut, Array.size_set]; exact h2DC
  have hhome2O : bOut.sudo_5Board_4home[2]'h2HO = bC.sudo_5Board_4home[2]'h2HC := by
    have hsz : 2 < (bC.sudo_5Board_4home.set ⟨5, h5HC⟩ (embed (fold.take s.n))).size := by
      rw [Array.size_set]; exact h2HC
    exact cell_eq_of hhomeOut
      (Array.getElem_set_ne bC.sudo_5Board_4home ⟨5, h5HC⟩ (embed (fold.take s.n)) hsz hne52)
  have hheld2O : bOut.sudo_5Board_4held[2]'h2DO = bC.sudo_5Board_4held[2]'h2DC := by
    have hsz : 2 < (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true).size := by
      rw [Array.size_set]; exact h2DC
    exact cell_eq_of hheldOut
      (Array.getElem_set_ne bC.sudo_5Board_4held ⟨5, h5DC⟩ true hsz hne52)
  have h2HZ : 2 < bZ.sudo_5Board_4home.size := by
    simp [bZ, touchRow]; exact h2HO
  have h2DZ : 2 < bZ.sudo_5Board_4held.size := by
    simp [bZ, touchRow]; exact h2DO
  have hhome2Z : bZ.sudo_5Board_4home[2]'h2HZ = b.sudo_5Board_4home[2]'h2H0 := by
    have hZh2 : bZ.sudo_5Board_4home = bOut.sudo_5Board_4home := by simp [bZ, touchRow]
    exact (cell_eq_of hZh2 hhome2O).trans
      (hhome2C.trans (hhome2S.trans hhome2U))
  have hheld2Z : bZ.sudo_5Board_4held[2]'h2DZ = b.sudo_5Board_4held[2]'h2D0 := by
    have hZh2 : bZ.sudo_5Board_4held = bOut.sudo_5Board_4held := by simp [bZ, touchRow]
    exact (cell_eq_of hZh2 hheld2O).trans
      (hheld2C.trans (hheld2S.trans hheld2U))
  have h6D0 := h.shape.spareD
  have h6H0 := h.shape.spareH
  have h6DZ : 6 < bZ.sudo_5Board_4held.size := by
    have h6DU : 6 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact h6D0
    have h6DS : 6 < bS.sudo_5Board_4held.size := by rw [hheldS, Array.size_set]; exact h6DU
    have h6DC : 6 < bC.sudo_5Board_4held.size := by rw [_hheldC, Array.size_set]; exact h6DS
    have h6DO : 6 < bOut.sudo_5Board_4held.size := by rw [hheldOut, Array.size_set]; exact h6DC
    simp [bZ, touchRow]; exact h6DO
  have h6HZ : 6 < bZ.sudo_5Board_4home.size := by
    have h6HU : 6 < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact h6H0
    have h6HS : 6 < bS.sudo_5Board_4home.size := by rw [hhomeS, Array.size_set]; exact h6HU
    have h6HC : 6 < bC.sudo_5Board_4home.size := by rw [_hhomeC, Array.size_set]; exact h6HS
    have h6HO : 6 < bOut.sudo_5Board_4home.size := by rw [hhomeOut, Array.size_set]; exact h6HC
    simp [bZ, touchRow]; exact h6HO
  have hspareZ : bZ.sudo_5Board_4held[6]'h6DZ = false := by
    have hspU : bU.sudo_5Board_4held[6]'(by rw [hheldU]; exact h6D0) = false :=
      cell_eq_of hheldU h.shape.spareE
    have hszS : 6 < (bU.sudo_5Board_4held.set ⟨5, h5D⟩ true).size := by
      rw [Array.size_set]; rw [hheldU]; exact h6D0
    have hspS : bS.sudo_5Board_4held[6]'(by rw [hheldS]; exact hszS) = false :=
      (cell_eq_of hheldS (Array.getElem_set_ne bU.sudo_5Board_4held ⟨5, h5D⟩ true hszS hne56)).trans
        hspU
    have hszC : 6 < (bS.sudo_5Board_4held.set ⟨5, hF⟩ false).size := by
      rw [Array.size_set]; rw [hheldS, Array.size_set]; rw [hheldU]; exact h6D0
    have hspC : bC.sudo_5Board_4held[6]'(by rw [_hheldC]; exact hszC) = false :=
      (cell_eq_of _hheldC (Array.getElem_set_ne bS.sudo_5Board_4held ⟨5, hF⟩ false hszC hne56)).trans
        hspS
    have hszO : 6 < (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true).size := by
      rw [Array.size_set]; rw [_hheldC, Array.size_set, hheldS, Array.size_set, hheldU]; exact h6D0
    have hspO : bOut.sudo_5Board_4held[6]'(by rw [hheldOut]; exact hszO) = false :=
      (cell_eq_of hheldOut (Array.getElem_set_ne bC.sudo_5Board_4held ⟨5, h5DC⟩ true hszO hne56)).trans
        hspC
    have hZh6 : bZ.sudo_5Board_4held = bOut.sudo_5Board_4held := by simp [bZ, touchRow]
    exact cell_eq_of hZh6 hspO
  have h7Z : 7 ≤ bZ.sudo_5Board_4held.size := by
    have h7U' : 7 ≤ bU.sudo_5Board_4held.size := by rw [hheldU]; exact h.shape.h7
    have h7S' : 7 ≤ bS.sudo_5Board_4held.size := by rw [hheldS, Array.size_set]; exact h7U'
    have h7C' : 7 ≤ bC.sudo_5Board_4held.size := by rw [_hheldC, Array.size_set]; exact h7S'
    have h7O' : 7 ≤ bOut.sudo_5Board_4held.size := by rw [hheldOut, Array.size_set]; exact h7C'
    simp [bZ, touchRow]; exact h7O'
  have hmkZ : bZ.sudo_5Board_9marker_on = false := by
    have hmkC : bC.sudo_5Board_9marker_on = false := by
      rw [hbC]; simp [cubeOffBoard]
    have hmkO := (settle_marker_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))).trans hmkC
    simpa [bZ, touchRow] using hmkO
  have hbonZ : bZ.sudo_5Board_8bench_on = false := by
    simpa [bZ, touchRow] using
      (settle_bench_off bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7)))
  have hops0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
  obtain ⟨c0, hc0, hle0⟩ := h.ops 0 hops0
  have hfit0 : FitsLen (c0 + 1) := by
    have hstep : c0 + 1 ≤ base.ops0 + done.length * (base.mMax + 3) := by
      simpa [hon] using hle0
    have hcap : c0 + 1 ≤ base.ops0 + base.R * (base.mMax + 3) :=
      Nat.le_trans hstep (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
    exact FitsLen.of_le base.fitO hcap
  have hopsZ : 0 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hopsUeq := hopsU
    have hSops := settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hCops : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, by
          rw [hSops, hopsU]; exact h.shape.peg.opsGt⟩ (Int.ofNat (cOps + 1)) := by
      rw [hbC]; simp [cubeOffBoard]
    have hOops := settle_ops bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
    have hZops : bZ.sudo_5Board_4cost.sudo_5Costs_3ops =
        bOut.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bZ, touchRow]
    rw [hZops, hOops, hCops, Array.size_set, hSops, hopsUeq]
    exact hops0
  have hopZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsZ = (c0 : Int) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by rw [hopsU]; exact hops0) = (c0 : Int) :=
      cell_eq_of hopsU hc0
    have hSops := settle_ops bU 5 ⟨h5H, h5D⟩ xs s.n mv sl pk
    have hS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by rw [hSops, hopsU]; exact hops0) =
        (c0 : Int) := (cell_eq_of hSops hU)
    have hCset : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, by
          rw [hSops, hopsU]; exact h.shape.peg.opsGt⟩ (Int.ofNat (cOps + 1)) := by
      rw [hbC]; simp [cubeOffBoard]
    have hsz : 0 < (bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, by
        rw [hSops, hopsU]; exact h.shape.peg.opsGt⟩ (Int.ofNat (cOps + 1))).size := by
      rw [Array.size_set, hSops, hopsU]; exact hops0
    have hne10 : (1 : Nat) ≠ 0 := by decide
    have hC : bC.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by rw [hCset]; exact hsz) = (c0 : Int) :=
      (cell_eq_of hCset (Array.getElem_set_ne _ ⟨1, by rw [hSops, hopsU]; exact h.shape.peg.opsGt⟩
        (Int.ofNat (cOps + 1)) hsz hne10)).trans hS
    have hOops := settle_ops bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
    have hO : bOut.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by rw [hOops, hCset]; exact hsz) =
        (c0 : Int) := (cell_eq_of hOops hC)
    have hZops : bZ.sudo_5Board_4cost.sudo_5Costs_3ops = bOut.sudo_5Board_4cost.sudo_5Costs_3ops := by
      simp [bZ, touchRow]
    exact cell_eq_of hZops hO
  have hmvOut := settle_moves_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))
  have hmvNat : bZ.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((cubeMoves mvS s.gap s.n s.k s.benchlen + 2 * pegCount (fold.take s.n) : Nat) : Int) := by
    have hEq : bZ.sudo_5Board_4cost.sudo_5Costs_5moves = bOut.sudo_5Board_4cost.sudo_5Costs_5moves := by
      simp [bZ, touchRow]
    rw [hEq, hmvOut, ofNat_eq_natCast]
  let pkC : Nat := raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7)
  have hpkOut := settle_peak_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS pkC hpkCnat
  have hpkNat : bZ.sudo_5Board_4cost.sudo_5Costs_4peak =
      ((if pkC < countHeld (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true) 7
        then countHeld (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true) 7 else pkC : Nat) : Int) := by
    have hEq : bZ.sudo_5Board_4cost.sudo_5Costs_4peak = bOut.sudo_5Board_4cost.sudo_5Costs_4peak := by
      simp [bZ, touchRow]
    rw [hEq, hpkOut, ofNat_eq_natCast]
  have hpsC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      ((raisedPeak peakS (countHeld bS.sudo_5Board_4held 7) : Nat) : Int) := by
    rw [hbC, cube_off_strict, ofNat_eq_natCast]
  have hpsO := (settle_strict_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS pkC).trans hpsC
  have hpsZ : bZ.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      ((raisedPeak peakS (countHeld bS.sudo_5Board_4held 7) : Nat) : Int) := by
    simpa [bZ, touchRow] using hpsO
  have hholeC : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      ((raisedHole holeN (topIdx (combStrip s.n s.benchlen s.gap)) : Nat) : Int) := by
    rw [hbC, cube_off_hole, ofNat_eq_natCast]
  have hholeO := (settle_hole_eq bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS pkC).trans hholeC
  have hholeZ : bZ.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      ((raisedHole holeN (topIdx (combStrip s.n s.benchlen s.gap)) : Nat) : Int) := by
    simpa [bZ, touchRow] using hholeO
  have h5DZ : 5 < bZ.sudo_5Board_4held.size := by
    have h5DO : 5 < bOut.sudo_5Board_4held.size := by
      rw [hheldOut, Array.size_set]
      exact h5DC
    have hEq : bZ.sudo_5Board_4held = bOut.sudo_5Board_4held := by simp [bZ, touchRow]
    rw [hEq]
    exact h5DO
  let mvZ : Nat :=
    cubeMoves mvS s.gap s.n s.k s.benchlen + 2 * pegCount (fold.take s.n)
  have hleZ : mvZ ≤ mv + 2 * base.n + pegCharge base.n base.bench := by
    have hsum : mvZ ≤ mvS + 2 * s.n + 3 * (s.benchlen - s.n) + 2 * s.n := by
      have h2 : 2 * pegCount (fold.take s.n) ≤ 2 * s.n :=
        Nat.mul_le_mul_left 2 hpegF
      omega
    exact Nat.le_trans hsum htop
  obtain ⟨mvC, hmvCeq, hleC⟩ := h.moves
  have hmvSame : mvC = mv := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact hmvCeq.symm.trans (hmvU.symm.trans hmvB)
  have hclimb : mv + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon, hmvSame] using hleC
  have hdone : done.length * rungCharge base.n base.bench base.mMax ≤
      base.R * rungCharge base.n base.bench base.mMax :=
    Nat.mul_le_mul_right _ hk
  have hcapZ : mvZ + base.n + base.n * (base.n + 1) + 3 * (base.bench - base.n) +
      2 * base.n ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax +
        pegCharge base.n base.bench + base.n + base.n * (base.n + 1) +
        3 * (base.bench - base.n) + 2 * base.n := by
    have h2 : mv + 2 * base.n ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax :=
      Nat.le_trans hclimb (Nat.add_le_add_left hdone _)
    omega
  have hfitZ : FitsLen (mvZ + base.n + base.n * (base.n + 1) +
      3 * (base.bench - base.n) + 2 * base.n) :=
    FitsLen.of_le base.fitCheckM hcapZ
  have htierZ : bZ.sudo_5Board_1t = b.sudo_5Board_1t := by
    simpa [bZ, touchRow] using htierOut
  have hmvZ : bZ.sudo_5Board_4cost.sudo_5Costs_5moves = (mvZ : Int) := by
    simpa [mvZ] using hmvNat
  have hnZ : bZ.sudo_5Board_1t.sudo_4Tier_1n = (base.n : Int) := by
    rw [htierZ, h.shape.tierN, h.hn]
  have hbZlen : bZ.sudo_5Board_1t.sudo_4Tier_8benchlen = (base.bench : Int) := by
    rw [htierZ, h.shape.tierB, h.hbench]
  have hheld5Z : bZ.sudo_5Board_4held[5]'h5DZ = true := by
    have hEq : bZ.sudo_5Board_4held = bOut.sudo_5Board_4held := by simp [bZ, touchRow]
    have h5DO : 5 < bOut.sudo_5Board_4held.size := by
      rw [hheldOut, Array.size_set]
      exact h5DC
    have h5set : 5 < (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true).size := by
      rw [Array.size_set]
      exact h5DC
    have hget : (bC.sudo_5Board_4held.set ⟨5, h5DC⟩ true)[5]'h5set = true := by
      rw [Array.getElem_set, if_pos rfl]
    exact cell_eq_of (ha := h5DZ) (hb := h5DO) hEq
      (cell_eq_of (ha := h5DO) (hb := h5set) hheldOut hget)
  refine ⟨bU, bC, bOut, bZ, mv, sl, row, hun, hprog, by simpa [bOut] using hsettle,
    hclearZ, hmvB, hslB, by simpa [bOut] using
      (settle_bench_off bC 5 ⟨h5HC, h5DC⟩ fold s.n (cubeMoves mvS s.gap s.n s.k s.benchlen) slS (raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨5, hF⟩ false) 7))),
    hrowOut, rfl, rfl, rfl, rfl, ⟨h5Z, hgetZ⟩,
    ⟨h2H0, h2D0, h2HZ, h2DZ, hhome2Z, hheld2Z, hmkZ, hbonZ, h6DZ, h6HZ, hspareZ, h7Z,
      hopsZ, ⟨c0, hopZ, hfit0⟩,
      ⟨_, hmvNat⟩, ⟨_, hpkNat⟩, ⟨_, hpsZ⟩, ⟨_, hholeZ⟩, h5DZ, hheld5Z,
      (by simpa [bZ, touchRow] using htierOut),
      ⟨mvZ, base.n, base.bench, hmvZ, hnZ, hbZlen, hfitZ⟩⟩,
    htailM, htailS, tail_ctrl_fit h hk ht⟩

/-- The final tail's boards and the settled gap. The i64 bounds stay inside
    `final_cube_settle` and are not opened here. -/
theorem final_cube_home
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true)
    (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax)
    (hm : 0 < s.tally) :
    ∃ (bU bC bOut bZ : Ecbs.Board),
      Ecbs.unpark_rung b = .ok bU ∧
      Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC ∧
      Ecbs.settle bC = .ok bOut ∧
      Ecbs.tally_clear bOut = .ok bZ ∧
      SettledHome bZ (fieldCube s.n s.k s.benchlen s.gap) :=
  Exists.elim (final_cube_settle h hon hge ht hm) fun bU pack1 =>
  Exists.elim pack1 fun bC pack2 =>
  Exists.elim pack2 fun bOut pack3 =>
  Exists.elim pack3 fun bZ pack4 =>
  Exists.elim pack4 fun _mv pack5 =>
  Exists.elim pack5 fun _sl pack6 =>
  Exists.elim pack6 fun _row hpack =>
    ⟨bU, bC, bOut, bZ, hpack.1, hpack.2.1, hpack.2.2.1, hpack.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end EcbsLink2.Link2
