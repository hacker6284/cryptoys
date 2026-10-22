/-
  The home rung's peg loop spends one settle less than `pegCharge`. The first
  cube is bench-off, so its settle is a no-op. That `2 · n` is the slack a
  bench-start rung spends when it slides the gap home. One lemma for the loop;
  the white clear and the red extras are Nat compositions of it.
-/
import EcbsLink2.Link2.SlideGap
import EcbsLink2.Link2.InvertDelta

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The bench-off peg loop, shared by all eight home successors. Copy adds at
    most `n`. The `m` pegs add one `pegCharge` each in the loose bound, but the
    first cube does not pay its settle, so the loop is `2 · n` under
    `moves0 + m · pegCharge`. Same for slides. -/
theorem peg_loop_delta_tight
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (mv sl loop sloop : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      loop + 2 * base.n ≤
        mv + pegCount s.gap + s.tally * pegCharge base.n base.bench ∧
      pegCount s.gap ≤ base.n ∧
      sloop + 2 * base.n ≤ sl + s.tally * (2 * base.n) := by
  obtain ⟨mv, sl, pk, c, hmv, hsl, _hpk, hmv0, hsl0, hmEq, hn, _hk, hbch, _hsrc, _hg,
      _hOps0, _hb0, _hpkLe, _hmoves, _hmovN, _hslides, _hsldN, _hpeakN, _hpeak, _hOps⟩ :=
    peg_entry_pack h hm hT hhome
  have hslack := pegPack_move_slack c c.m c.hm (Nat.le_refl _)
  have hslide := pegPack_slide_slack c c.m c.hm (Nat.le_refl _)
  have hnB : s.n = base.n := h.hn
  have hbB : s.benchlen = base.bench := h.hbench
  have hpegs : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, hnB] at h1
    exact h1
  refine ⟨mv, sl, (pegPack c c.m c.hm (Nat.le_refl _)).moves,
      (pegPack c c.m c.hm (Nat.le_refl _)).slides, hmv, hsl, ?_, hpegs, ?_⟩
  · have hmov : (pegPack c c.m c.hm (Nat.le_refl _)).moves + 2 * c.n ≤
        c.moves0 + c.m * pegCharge c.n c.bench := hslack
    simp only [hmv0, hn, hnB, hmEq, hbch, hbB] at hmov
    exact hmov
  · have hsld : (pegPack c c.m c.hm (Nat.le_refl _)).slides + 2 * c.n ≤
        c.slides0 + c.m * (2 * c.n) := hslide
    simp only [hsl0, hn, hnB, hmEq] at hsld
    exact hsld

/-- A clear that adds at most one mul charge and `n` on top of a short loop
    stays `2 · n` under one `rungCharge`. -/
theorem white_clear_of_loop (mv loop mvC pegs m n bench : Nat)
    (hpegs : pegs ≤ n)
    (hloop : loop + 2 * n ≤ mv + pegs + m * pegCharge n bench)
    (hrest : mvC ≤ loop + mulCharge n bench + n) :
    mvC + 2 * n ≤ mv + rungCharge n bench m := by
  have hwhite := charge_white_settle n bench m
  have h1 : mvC + 2 * n ≤
      mv + pegs + m * pegCharge n bench + mulCharge n bench + n := by
    omega
  have h2 : pegs + m * pegCharge n bench + mulCharge n bench + n ≤
      n + m * pegCharge n bench + mulCharge n bench + n := by
    omega
  omega

/-- The red cube and the red mul add one peg charge and one mul charge. On a
    clear that is already `2 · n` short, the sum is still `2 · n` short of
    `rungCharge`. -/
theorem red_of_short_clear (mv mvC mvRed m n bench : Nat)
    (hC : mvC + 2 * n ≤
      mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hRed : mvRed ≤ mvC + pegCharge n bench + mulCharge n bench) :
    mvRed + 2 * n ≤ mv + rungCharge n bench m := by
  have hred := charge_final_red n bench m
  omega

/-- Gap-mul slides are at most `2 · n`. A short loop plus that stays `2 · n`
    under the slide charge, which budgets three extra settles. -/
theorem white_slides_of_loop (sl sloop slC m n : Nat)
    (hloop : sloop + 2 * n ≤ sl + m * (2 * n))
    (hrest : slC ≤ sloop + 2 * n) :
    slC + 2 * n ≤ sl + rungSlideCharge n m := by
  have h1 : slC + 2 * n ≤ sl + m * (2 * n) + 2 * n := by
    omega
  unfold rungSlideCharge
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by
    rw [Nat.add_mul]
  have h3 : 2 * n ≤ 3 * (2 * n) := by
    omega
  rw [hsplit]
  omega

/-- The red cube and the red mul add at most `2 · n` slides each. -/
theorem red_slides_of_short (sl slC slR m n : Nat)
    (hW : slC + 2 * n ≤ sl + m * (2 * n) + 2 * n)
    (hR : slR ≤ slC + 2 * n + 2 * n) :
    slR + 2 * n ≤ sl + rungSlideCharge n m := by
  have h1 : slR + 2 * n ≤ sl + m * (2 * n) + 2 * n + 2 * n + 2 * n := by
    omega
  unfold rungSlideCharge
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by
    rw [Nat.add_mul]
  have h3 : 2 * n + 2 * n + 2 * n = 3 * (2 * n) := by
    omega
  rw [hsplit, ← h3]
  omega

/-- Bench-start delta: the slide (`≤ 2 · n`) plus a home delta that is
    `2 · n` under the charge. -/
theorem bench_delta_add (dSet dHome charge n : Nat)
    (hS : dSet ≤ 2 * n) (hH : dHome + 2 * n ≤ charge) :
    dSet + dHome ≤ charge := by
  omega

/-- The settle raises peak against at most seven homes, and a home rung does
    the same, so the bench-start peak stays `max(prev, 7)`. -/
theorem bench_peak (pk pkS pk' : Nat)
    (hS : pkS ≤ max pk 7) (hH : pk' ≤ max pkS 7) :
    pk' ≤ max pk 7 :=
  peak_carry pk pkS pk' hS hH

/-- The number the white clear's move counter is at most: the short loop, one
    mul charge, and `n` for the clear. That is already `2 · n` under
    `rungCharge`. The eight home successors build their clear from this loop. -/
theorem home_clear_delta_tight
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :
    ∃ (mv loop mvC : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      loop + 2 * base.n ≤
        mv + pegCount s.gap + s.tally * pegCharge base.n base.bench ∧
      mvC ≤ loop + mulCharge base.n base.bench + base.n ∧
      mvC + 2 * base.n ≤ mv + rungCharge base.n base.bench s.tally := by
  obtain ⟨mv, _sl, _pk, c, hmv, _hsl, _hpk, hmv0, _hsl0, hmEq, hn, _hk, hbch,
      _hsrc, _hg, _hOps0, _hb0, _hpkLe, _hmoves, _hmovN, _hslides, _hsldN, _hpeakN,
      _hpeak, _hOps⟩ :=
    peg_entry_pack h hm hT hhome
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hslack := pegPack_move_slack c c.m c.hm (Nat.le_refl _)
  have hnB : s.n = base.n := h.hn
  have hbB : s.benchlen = base.bench := h.hbench
  have hpegs : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, hnB] at h1
    exact h1
  have hloop : d.moves + 2 * base.n ≤
      mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
    have hraw := hslack
    simp only [hmv0, hn, hnB, hmEq, hbch, hbB] at hraw
    exact hraw
  let mvC := d.moves + mulCharge base.n base.bench + base.n
  have htight := white_clear_of_loop mv d.moves mvC (pegCount s.gap) s.tally
    base.n base.bench hpegs hloop (Nat.le_refl _)
  refine ⟨mv, d.moves, mvC, hmv, hloop, Nat.le_refl _, htight⟩

/-- A home rung's tight delta, read on the board `settle` just wrote, is one
    loose `RungDelta` on the board from before that slide. The settle spends
    `2 · pegs ≤ 2 · n`, which is the slack the tight conjuncts left. Ops are
    copied. The peak is `max` of the settle's raise and the home rung's raise. -/
theorem rungDelta_of_slide
    {b bS b' : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDeltaTight bS b' base m)
    (mv sl pk mvS slS pkS pegs : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int))
    (hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int))
    (hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = (slS : Int))
    (hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int))
    (hmvAdd : mvS = mv + 2 * pegs)
    (hslAdd : slS = sl + 2 * pegs)
    (hpegs : pegs ≤ base.n)
    (hpkLe : pkS ≤ max pk 7)
    (hops : bS.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict)
    (hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) :
    RungDelta b b' base m := by
  have hpeg2 : 2 * pegs ≤ 2 * base.n := Nat.mul_le_mul_left 2 hpegs
  refine
    { moves := ?_
      slides := ?_
      opsSize := ?_
      ops := ?_
      peak := ?_
      strict := ?_
      hole := ?_ }
  · obtain ⟨mv0, mv', hb, hb', hle⟩ := hδ.moveTight
    have h0 : mv0 = mvS := ofNat_inj_nat (hb.symm.trans hmvS)
    refine ⟨mv, mv', hmv, hb', ?_⟩
    have hle' : mv' + 2 * base.n ≤ mv + 2 * pegs + rungCharge base.n base.bench m := by
      simpa [h0, hmvAdd] using hle
    omega
  · obtain ⟨sl0, sl', hb, hb', hle⟩ := hδ.slideTight
    have h0 : sl0 = slS := ofNat_inj_nat (hb.symm.trans hslS)
    refine ⟨sl, sl', hsl, hb', ?_⟩
    have hle' : sl' + 2 * base.n ≤ sl + 2 * pegs + rungSlideCharge base.n m := by
      simpa [h0, hslAdd] using hle
    omega
  · exact hδ.delta.opsSize.trans (congrArg Array.size hops)
  · intro i hi
    have hiS : i < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hops]; exact hi
    obtain ⟨c, c', hc, hc', hle⟩ := hδ.delta.ops i hiS
    have hcB : b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) :=
      (idx_get hops.symm i hi).trans hc
    have hix :
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'
          ((hδ.delta.opsSize.trans (congrArg Array.size hops)) ▸ hi) =
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδ.delta.opsSize ▸ hiS) :=
      get_proof_irrel _ i _ _
    exact ⟨c, c', hcB, hix.symm.trans hc', hle⟩
  · obtain ⟨pk0, pk', hb, hb', hle⟩ := hδ.delta.peak
    have h0 : pk0 = pkS := ofNat_inj_nat (hb.symm.trans hpkS)
    refine ⟨pk, pk', hpk, hb', bench_peak pk pkS pk' hpkLe (by simpa [h0] using hle)⟩
  · obtain ⟨ps0, ps', hb, hb', hle⟩ := hδ.delta.strict
    refine ⟨ps0, ps', hstrictS.symm.trans hb, hb', hle⟩
  · obtain ⟨ho, ho', hb, hb', hle⟩ := hδ.delta.hole
    refine ⟨ho, ho', hholeS.symm.trans hb, hb', hle⟩

end EcbsLink2.Link2
