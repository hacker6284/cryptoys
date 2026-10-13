/-
  A cube whose script marker is on and whose bench is already on.
  `settle` slides that bench, then the comb is `cube_tail_flag`.
  The second cube of `frobenius_affine` has this shape: the first cube
  leaves the bench on. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem array_at_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- `settle` does not read the marker flag. The flag on the result is the flag
    it was given. -/
theorem settleBoard_flag (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard { b with sudo_5Board_9marker_on := true } home hH hD xs n moves slides peak =
      { settleBoard b home hH hD xs n moves slides peak with
          sudo_5Board_9marker_on := true } := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hpkOn :
        peak < countHeld
          (({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4held.set ⟨home, hD⟩ true) 7 :=
      hpk
    rw [settle_peak ({ b with sudo_5Board_9marker_on := true }) home hH hD xs n moves slides peak
        hpkOn]
    rw [settle_peak b home hH hD xs n moves slides peak hpk]
  · have hnkOn :
        ¬ peak < countHeld
          (({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4held.set ⟨home, hD⟩ true) 7 :=
      hpk
    rw [settle_keep ({ b with sudo_5Board_9marker_on := true }) home hH hD xs n moves slides peak
        hnkOn]
    rw [settle_keep b home hH hD xs n moves slides peak hpk]

theorem settle_flag (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (n moves slides peak : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n))) :
    Ecbs.settle { b with sudo_5Board_9marker_on := true } =
      (do
        let r ← Ecbs.settle b
        pure { r with sudo_5Board_9marker_on := true }) := by
  let bOn := { b with sudo_5Board_9marker_on := true }
  rw [settle_refines bOn home xs n moves slides peak hH hD h7 hon hto hempty hbench hn hpos hnle
      hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
  rw [settle_refines b home xs n moves slides peak hH hD h7 hon hto hempty hbench hn hpos hnle
      hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
  rw [settleBoard_flag b home hH hD xs n moves slides peak]
  simp only [ok_bind, pure_eq_ok]

/-- Marker seated at `m`, bench on and aimed at `home`, which is not the cube's
    source. `Ecbs.cube` steps the marker, slides that bench, then runs the
    marker-off comb of `xs` with the flag put back. -/
theorem cube_bench_up (b : Ecbs.Board) (dst src home : Nat) (xs ys : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
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
        let r ← Ecbs.cube (markerUpFeed b m ctrl mx) ((dst : Nat) : Int) ((src : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  let feed := markerUpFeed b m ctrl mx
  have hopsF : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  have hop1F : feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsF) = (cOps : Int) := by
    simpa [feed, markerUpFeed] using hop1
  rw [cube_open b ((dst : Nat) : Int) ((src : Nat) : Int) cOps hops hop1 hfops]
  rw [cube_open feed ((dst : Nat) : Int) ((src : Nat) : Int) cOps hopsF hop1F hfops]
  have hmkB : (bumpOp b 1 cOps hops).sudo_5Board_9marker_on = true := by simp [bumpOp, hmk]
  rw [log_op_on _ hmkB]
  have hmB : (bumpOp b 1 cOps hops).sudo_5Board_6marker = Int.ofNat m := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 1 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hs
  rw [marker_step_up (bumpOp b 1 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitM hfitC hfit2]
  rw [← up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let bF := bumpOp feed 1 cOps hopsF
  have hsame : bumpOp feed 1 cOps (by simpa [markerUpFeed] using hops) = bF := by
    simpa [bF] using (bumpOp_irrel feed 1 cOps (by simpa [markerUpFeed] using hops) hopsF)
  rw [hsame]
  have hfeedB : bF.sudo_5Board_9marker_on = false := by simp [bF, bumpOp, feed, markerUpFeed]
  rw [log_op_off _ hfeedB]
  simp only [ok_bind]
  have honF : bF.sudo_5Board_8bench_on = true := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hon
  have htoF : bF.sudo_5Board_8bench_to = (home : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hto
  have hemptyF : bF.sudo_5Board_4held[home] = false := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hempty
  have hbenchF : bF.sudo_5Board_5bench = embed ys := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hbench
  have hnF : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hn
  have hmovesF : bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hmoves
  have hslidesF : bF.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hslides
  have hpeakF : bF.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hpeak
  have h7F : 7 ≤ bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerUpFeed] using h7
  have hDhF : home < bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hDh
  have hHhF : home < bF.sudo_5Board_4home.size := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hHh
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
    rw [settle_marker_eq bF home hHhF hDhF ys n moves slides peak]
    exact hfeedB
  have hFs : src < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bF home hHhF hDhF ys n moves slides peak, Array.size_set]
    simpa [bF, bumpOp, feed, markerUpFeed] using hF
  have hHomes : src < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq bF home hHhF hDhF ys n moves slides peak, Array.size_set]
    simpa [bF, bumpOp, feed, markerUpFeed] using hHome
  have hHFs : bS.sudo_5Board_4held[src] = true := by
    have hget := array_at_eq
      (settle_held_eq bF home hHhF hDhF ys n moves slides peak) src hFs
    have hneH : home ≠ src := hne.symm
    simp only [Array.getElem_set, hneH] at hget
    exact hget.trans (by simpa [bF, bumpOp, feed, markerUpFeed] using hHF)
  have hArrs : bS.sudo_5Board_4home[src] = embed xs := by
    have hget := array_at_eq
      (settle_home_eq bF home hHhF hDhF ys n moves slides peak) src hHomes
    have hneH : home ≠ src := hne.symm
    simp only [Array.getElem_set, hneH] at hget
    exact hget.trans (by simpa [bF, bumpOp, feed, markerUpFeed] using hArr)
  have h7s : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq bF home hHhF hDhF ys n moves slides peak, Array.size_set]
    exact h7F
  have hpS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hp
  have hpeakS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peakT : Int) := by
    rw [settle_peak_eq bF home hHhF hDhF ys n moves slides peak hpeakF, ofNat_eq_natCast]
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    exact hnF
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (movesT : Int) := by
    rw [settle_moves_eq bF home hHhF hDhF ys n moves slides peak, ofNat_eq_natCast]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hbl
  have hcgS : bS.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hcg
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hhole
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hw
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hh
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hr
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [settle_tier_eq bF home hHhF hDhF ys n moves slides peak]
    simpa [bF, bumpOp, feed, markerUpFeed] using hk
  exact cube_tail_flag bS dst src xs w h r n k movesT hole bench peakT peakS cg
    hflagS hFs hHomes hHFs hArrs h7s hpS hpeakS hn0 hnS hlenx hf hmovS hblS hcgS hspan h3 hfm
    hholeS hxsT hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS hsm hnsm hfitB hfold

end EcbsLink2.Link2
