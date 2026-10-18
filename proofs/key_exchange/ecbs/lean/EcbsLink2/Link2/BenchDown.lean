/-
  A cube whose script marker is lifted (`marker < 0`) and whose bench is on.
  `marker_step` seats the marker, `settle` slides the bench, then the comb is
  `cube_tail_flag`. This is the across cube of `frobenius_point` when `ProjOn`
  is `yBench` or `zBench`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerBench

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem array_at_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- Marker lifted, bench on and aimed at `home`, which is not the cube's
    source. `Ecbs.cube` seats the marker, slides that bench, then runs the
    marker-off comb of `xs` with the flag put back. -/
theorem cube_bench_down (b : Ecbs.Board) (dst src home : Nat) (xs ys : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfit : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hne : src ≠ home)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (hDh : home < b.sudo_5Board_4held.size)
    (hHh : home < b.sudo_5Board_4home.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hposY : 0 < ys.length) (hnle : n ≤ ys.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen ys.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeg : FitsLen (2 * pegCount (ys.take n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      (do
        let r ← Ecbs.cube (markerDownFeed b ctrl mx) ((dst : Nat) : Int) ((src : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  let feed := markerDownFeed b ctrl mx
  have hopsF : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerDownFeed] using hops
  have hop1F : feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsF) = (cOps : Int) := by
    simpa [feed, markerDownFeed] using hop1
  rw [cube_open b ((dst : Nat) : Int) ((src : Nat) : Int) cOps hops hop1 hfops]
  rw [cube_open feed ((dst : Nat) : Int) ((src : Nat) : Int) cOps hopsF hop1F hfops]
  have hmkB : (bumpOp b 1 cOps hops).sudo_5Board_9marker_on = true := by simp [bumpOp, hmk]
  rw [log_op_on _ hmkB]
  have hmB : (bumpOp b 1 cOps hops).sudo_5Board_6marker < 0 := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 1 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hs
  rw [marker_step_down (bumpOp b 1 cOps hops) ctrl mx script hmB hcB hxB hsB hpos hfit]
  rw [← down_bump b ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let bF := bumpOp feed 1 cOps hopsF
  have hsame : bumpOp feed 1 cOps (by simpa [markerDownFeed] using hops) = bF :=
    bumpOp_irrel feed 1 cOps (by simpa [markerDownFeed] using hops) hopsF
  rw [hsame]
  have hfeedB : bF.sudo_5Board_9marker_on = false := by simp [bF, bumpOp, feed, markerDownFeed]
  rw [log_op_off _ hfeedB]
  simp only [ok_bind]
  have honF : bF.sudo_5Board_8bench_on = true := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hon
  have htoF : bF.sudo_5Board_8bench_to = (home : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hto
  have hemptyF : bF.sudo_5Board_4held[home] = false := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hempty
  have hbenchF : bF.sudo_5Board_5bench = embed ys := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hbench
  have hnF : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hn
  have hmovesF : bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hmoves
  have hslidesF : bF.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hslides
  have hpeakF : bF.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hpeak
  have h7F : 7 ≤ bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerDownFeed] using h7
  have hDhF : home < bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hDh
  have hHhF : home < bF.sudo_5Board_4home.size := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hHh
  rw [settle_flag bF home ys n moves slides peak hfeedB hHhF hDhF h7F honF htoF hemptyF hbenchF
      hnF hposY hnle hzero hf hfitL hmovesF hslidesF hpeakF hpeg hfitMv hfitSl]
  rw [settle_refines bF home ys n moves slides peak hHhF hDhF h7F honF htoF hemptyF hbenchF
      hnF hposY hnle hzero hf hfitL hmovesF hslidesF hpeakF hpeg hfitMv hfitSl]
  simp only [ok_bind, pure_eq_ok]
  let movesT := moves + 2 * pegCount (ys.take n)
  let bS := settleBoard bF home hHhF hDhF ys n moves slides peak
  change cubeTail { bS with sudo_5Board_9marker_on := true } ((dst : Nat) : Int) ((src : Nat) : Int) =
    (do
      let r ← cubeTail bS ((dst : Nat) : Int) ((src : Nat) : Int)
      pure { r with sudo_5Board_9marker_on := true })
  let peakT :=
    if peak < countHeld (bF.sudo_5Board_4held.set ⟨home, hDhF⟩ true) 7
    then countHeld (bF.sudo_5Board_4held.set ⟨home, hDhF⟩ true) 7
    else peak
  have hflagS : bS.sudo_5Board_9marker_on = false := by
    rw [settle_marker_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    exact hfeedB
  have hFs : src < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak, Array.size_set]
    simpa [bF, bumpOp, feed, markerDownFeed] using hF
  have hHomes : src < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak, Array.size_set]
    simpa [bF, bumpOp, feed, markerDownFeed] using hHome
  have hHFs : bS.sudo_5Board_4held[src] = true := by
    have hget := array_at_eq
      (settle_held_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak) src hFs
    have hneH : home ≠ src := hne.symm
    simp only [Array.getElem_set, hneH] at hget
    exact hget.trans (by simpa [bF, bumpOp, feed, markerDownFeed] using hHF)
  have hArrs : bS.sudo_5Board_4home[src] = embed xs := by
    have hget := array_at_eq
      (settle_home_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak) src hHomes
    have hneH : home ≠ src := hne.symm
    simp only [Array.getElem_set, hneH] at hget
    exact hget.trans (by simpa [bF, bumpOp, feed, markerDownFeed] using hArr)
  have h7s : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak, Array.size_set]
    exact h7F
  have hpS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hp
  have hpeakS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peakT : Int) := by
    rw [settle_peak_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak hpeakF, ofNat_eq_natCast]
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    exact hnF
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (movesT : Int) := by
    rw [settle_moves_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak, ofNat_eq_natCast]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hbl
  have hcgS : bS.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hcg
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hhole
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hw
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hh
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hr
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [settle_tier_eq bF home ⟨hHhF, hDhF⟩ ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerDownFeed] using hk
  exact cube_tail_flag bS dst src xs w h r n k movesT hole bench peakT peakS cg
    hflagS hFs hHomes hHFs hArrs h7s hpS hpeakS hn0 hnS hlenx hf hmovS hblS hcgS hspan h3 hfm
    hholeS hxsT hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS hsm hnsm hfitB hfold

/-- `markerDownFeed` writes the marker and the control counter. `settleBoard`
    writes the home, the bench, and the move counters. Either order is the
    same board. -/
theorem feed_settle_comm
    (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak ctrl mx : Nat) :
    settleBoard (markerDownFeed b ctrl mx) home hH hD xs n moves slides peak =
      markerDownFeed (settleBoard b home hH hD xs n moves slides peak) ctrl mx := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkF :
        peak < countHeld
          ((markerDownFeed b ctrl mx).sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
      simpa [markerDownFeed] using hpk
    rw [settle_peak (markerDownFeed b ctrl mx) home ⟨hH, hD⟩ xs n moves slides peak hpkF]
    rw [settle_peak b home ⟨hH, hD⟩ xs n moves slides peak hpk]
    unfold markerDownFeed
    rfl
  · have hnkF :
        ¬ peak < countHeld
          ((markerDownFeed b ctrl mx).sudo_5Board_4held.set ⟨home, hD⟩ true) 7 := by
      simpa [markerDownFeed] using hpk
    rw [settle_keep (markerDownFeed b ctrl mx) home ⟨hH, hD⟩ xs n moves slides peak hnkF]
    rw [settle_keep b home ⟨hH, hD⟩ xs n moves slides peak hpk]
    unfold markerDownFeed
    rfl

/-- Marker already off, bench still on. Settling before the cube is the cube. -/
theorem cube_feed_settled
    (b : Ecbs.Board) (dst src home : Nat) (ys : List Nat)
    (n moves slides peak cOps ctrl mx : Nat)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < ys.length) (hnle : n ≤ ys.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen ys.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (ys.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (ys.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (ys.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.cube (markerDownFeed b ctrl mx) (dst : Int) (src : Int) =
      Ecbs.cube
        (markerDownFeed (settleBoard b home hH hD ys n moves slides peak) ctrl mx)
        (dst : Int) (src : Int) := by
  let feed := markerDownFeed b ctrl mx
  have hopsF : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerDownFeed] using hops
  have hop1F : feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsF = (cOps : Int) := by
    simpa [feed, markerDownFeed] using hop1
  have hcube := cube_settle_other feed dst src home ys n moves slides peak cOps
    (by simp [feed, markerDownFeed]) hon hto hH hD h7 hempty hbench hn
    hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS hopsF hop1F hfops
  rw [hcube, feed_settle_comm b home hH hD ys n moves slides peak ctrl mx]

/-- Marker lifted, bench on and aimed at `home`, which is not the cube source.
    `Ecbs.cube` seats the marker and slides that bench, so it is the cube of the
    board `settle` would have left, still with the marker lifted. -/
theorem cube_lifted_bench
    (b : Ecbs.Board) (dst src home : Nat) (xs ys : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfit : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hne : src ≠ home)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (hDh : home < b.sudo_5Board_4held.size)
    (hHh : home < b.sudo_5Board_4home.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hposY : 0 < ys.length) (hnle : n ≤ ys.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen ys.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeg : FitsLen (2 * pegCount (ys.take n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      Ecbs.cube (settleBoard b home hHh hDh ys n moves slides peak)
        ((dst : Nat) : Int) ((src : Nat) : Int) := by
  let bS := settleBoard b home hHh hDh ys n moves slides peak
  let movesS := moves + 2 * pegCount (ys.take n)
  let peakT :=
    if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hDh⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨home, hDh⟩ true) 7
    else peak
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    rw [settle_marker_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hmk
  have hmS : bS.sudo_5Board_6marker < 0 := by
    rw [settle_ix_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hm
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    rw [settle_ctrl_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hc
  have hxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [settle_mx_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hx
  have hsS : bS.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hs
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b home ⟨hHh, hDh⟩ ys n moves slides peak
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 home hops ⟨hHh, hDh⟩ ys n moves slides peak
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    have h? : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps : Int) := by
      rw [settle_ops b home ⟨hHh, hDh⟩ ys n moves slides peak]
      rw [Array.getElem?_eq_getElem hops]
      exact congrArg some hop1
    rw [Array.getElem?_eq_getElem hopsS] at h?
    exact Option.some.inj h?
  have hFS : src < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b home ⟨hHh, hDh⟩ ys n moves slides peak, Array.size_set]
    exact hF
  have hHomeS : src < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b home ⟨hHh, hDh⟩ ys n moves slides peak, Array.size_set]
    exact hHome
  have hHFS : bS.sudo_5Board_4held[src] = true := by
    have hget := array_at_eq (settle_held_eq b home ⟨hHh, hDh⟩ ys n moves slides peak) src hFS
    simp only [Array.getElem_set, hne.symm] at hget
    exact hget.trans hHF
  have hArrS : bS.sudo_5Board_4home[src] = embed xs := by
    have hget := array_at_eq (settle_home_eq b home ⟨hHh, hDh⟩ ys n moves slides peak) src hHomeS
    simp only [Array.getElem_set, hne.symm] at hget
    exact hget.trans hArr
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b home ⟨hHh, hDh⟩ ys n moves slides peak, Array.size_set]
    exact h7
  have hpS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]
    exact hp.trans (ofNat_eq_natCast peakS)
  have hpeakS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peakT : Int) :=
    (settle_peak_eq b home ⟨hHh, hDh⟩ ys n moves slides peak hpeak).trans (ofNat_eq_natCast _)
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hn
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (movesS : Int) :=
    (settle_moves_eq b home ⟨hHh, hDh⟩ ys n moves slides peak).trans (ofNat_eq_natCast _)
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hbl
  have hcgS : bS.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hcg
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hhole
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hw
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hh
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hr
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [settle_tier_eq b home ⟨hHh, hDh⟩ ys n moves slides peak]; exact hk
  rw [cube_bench_down b dst src home xs ys w h r n k moves slides hole bench peak peakS cOps cg
      ctrl mx script hmk hon hm hc hx hs hpos hfit hops hop1 hfops hne hF hHome hHF hArr hDh hHh
      h7 hto hempty hbench hp hpeak hn0 hn hlenx hposY hnle hzero hf hfitL hmoves hslides hpeg
      hfitMv hfitSl hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm
      hnsm hfitB hfold]
  rw [cube_feed_settled b dst src home ys n moves slides peak cOps ctrl mx hon hto hHh hDh h7
      hempty hbench hn hposY hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitMv hfitSl hops hop1
      hfops]
  have hoffF : (markerDownFeed bS ctrl mx).sudo_5Board_8bench_on = false := by
    simpa [markerDownFeed] using hoffS
  have hoffEq := cube_off_eq (markerDownFeed bS ctrl mx) dst src xs w h r n k movesS hole bench
      peakT peakS cOps cg
      (by simp [markerDownFeed]) hoffF
      (by simpa [markerDownFeed] using hopsS)
      (by simpa [markerDownFeed] using hopS)
      hfops hblS hcgS hspan hFS hHomeS
      (by simpa [markerDownFeed] using hHFS)
      (by simpa [markerDownFeed] using hArrS)
      h7S hn0 hnS hlenx hf
      (by simpa [markerDownFeed] using hmovS)
      (by simpa [markerDownFeed] using hpeakS)
      (by simpa [markerDownFeed] using hpS)
      hxsT h3 hfm
      ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩
      hwS hhS hrS hkS hholeS hsm hnsm hfitB hfold
  rw [hoffEq, ok_bind, pure_eq_ok]
  exact (cube_down_eq bS dst src xs w h r n k movesS hole bench peakT peakS cOps cg ctrl mx script
      hmkS hoffS hmS hcS hxS hsS hpos hfit hopsS hopS hfops hFS hHomeS hHFS hArrS h7S hpS hpeakS
      hn0 hnS hlenx hf hmovS hblS hcgS hspan h3 hfm hholeS hxsT hw0 hh0 hrR hrP hnE hkLe hgap
      hwS hhS hrS hkS hsm hnsm hfitB hfold).symm

end EcbsLink2.Link2
