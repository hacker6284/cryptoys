/-
  `finish` after `invert_checked`. Across and up are multiplied by the gap,
  the up bench is settled, and the gap and the bottom are cleared. Homes 0
  and 1 are the affine coordinates. Home reads go through `getElem?`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FinishRun
import EcbsLink2.Link2.FinishBranch

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem cell_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (hi : i < a.size) (h : a[i]'hi = v) : a[i]? = some v := by
  rw [Array.getElem?_eq_getElem hi]
  exact congrArg some h

/-- `finish` on the board `invert_checked` returns. -/
theorem finish_affine (b0 b : Board) (px py xP yP g z : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps : Nat)
    (hinv : invert_checked b0 bottom = .ok b)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h5D : 5 < b.sudo_5Board_4held.size) (h5H : 5 < b.sudo_5Board_4home.size)
    (h5t : b.sudo_5Board_4held[5] = true) (h5a : b.sudo_5Board_4home[5] = embed g)
    (h0D : 0 < b.sudo_5Board_4held.size) (h0H : 0 < b.sudo_5Board_4home.size)
    (h0t : b.sudo_5Board_4held[0] = true) (h0a : b.sudo_5Board_4home[0] = embed xP)
    (h1D : 1 < b.sudo_5Board_4held.size) (h1H : 1 < b.sudo_5Board_4home.size)
    (h1t : b.sudo_5Board_4held[1] = true) (h1a : b.sudo_5Board_4home[1] = embed yP)
    (h2D : 2 < b.sudo_5Board_4held.size) (h2H : 2 < b.sudo_5Board_4home.size)
    (h2t : b.sudo_5Board_4held[2] = true) (h2a : b.sudo_5Board_4home[2] = embed z)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n) (hgap0 : 0 < n - k)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hgL : g.length = n) (hxL : xP.length = n) (hyL : yP.length = n) (hzL : z.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench) (hgT : allTritList g)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hb : n ≤ bench)
    (hclear : fieldMul n k bench g xP = px)
    (hclearY : fieldMul n k bench g yP = py)
    (hpeg : FitsLen (2 * pegCount px))
    (hfitM : FitsLen (mulMovesNo moves g xP n k bench + 2 * pegCount px))
    (hfitS : FitsLen (slides + 2 * pegCount px))
    (hfm2 : FitsLen (mulMovesNo moves g xP n k bench + 2 * pegCount px + n * (n + 1)))
    (hfold2 : FitsLen (mulMovesNo moves g xP n k bench + 2 * pegCount px +
      n * (n + 1) + 3 * (bench - n)))
    (hpegY : FitsLen (2 * pegCount py))
    (hfitMY : FitsLen (mulMovesNo (mulMovesNo moves g xP n k bench + 2 * pegCount px)
      g yP n k bench + 2 * pegCount py))
    (hfitSY : FitsLen (slides + 2 * pegCount px + 2 * pegCount py))
    (hfitG : FitsLen (mulMovesNo (mulMovesNo moves g xP n k bench + 2 * pegCount px)
      g yP n k bench + 2 * pegCount py + pegCount g))
    (hfitZ : FitsLen (mulMovesNo (mulMovesNo moves g xP n k bench + 2 * pegCount px)
      g yP n k bench + 2 * pegCount py + pegCount g + pegCount z)) :
    ∃ b',
      finish b0 = .ok b' ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  let mv1 := mulMovesNo moves g xP n k bench
  let pk1 := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ false) 7)
  let hole1 := raisedHole hole (topIdx (school n g xP (List.replicate bench 0) false))
  let ps1 := raisedPeak peakS (countHeld b.sudo_5Board_4held 7)
  let c1 := cOps + 1
  rw [finish_steps, hinv, ok_bind]
  conv => zeta
  obtain ⟨b1, hmul1, hon1, hto1, hbench1, htake, hlen1, hzero1, hmk1, hb1⟩ :=
    across_by_gap b px xP g w h r n k moves hole bench peak peakS cOps
      hmk hoff hops hop0 hfops hbl h5D h5H h5t h5a h0D h0H h0t h0a h7 hn0 hgap0 hn
      hgL hxL hf hmoves hpeak hpeakS hspan hgT hfi hfm shape hwF hhF hrF hkF hHole
      hsm hnsm hfitB hfold hb hclear
  rw [hmul1, ok_bind]
  conv => zeta
  have hhome1 : b1.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨0, h0H⟩ #[] := by
    rw [hb1]; exact mul_no_home b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  have hheld1 : b1.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨0, h0D⟩ false := by
    rw [hb1]; exact mul_no_held b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  have ht1 : b1.sudo_5Board_1t = b.sudo_5Board_1t := by rw [hb1]; rfl
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv1 := by
    rw [hb1]; exact mul_no_moves b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  have hsl1 : b1.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [hb1, mul_no_slides b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H]
    exact hslides
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk1 := by
    rw [hb1]; exact mul_no_peak b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  have hhole1 : b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1 := by
    rw [hb1]; rfl
  have hps1 : b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps1 := by
    rw [hb1]; rfl
  have hopsA : b1.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat c1) := by
    rw [hb1]; exact mul_no_ops b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  have hops1 : 0 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsA, Array.size_set]; exact hops
  have hop? : b1.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c1) := by
    rw [hopsA, Array.getElem?_set_eq]
  have hop01 : b1.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hops1 = Int.ofNat c1 :=
    some_get _ 0 _ hop? hops1
  have hszH1 : b1.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    rw [hhome1, Array.size_set]
  have hszD1 : b1.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
    rw [hheld1, Array.size_set]
  have h0H1 : 0 < b1.sudo_5Board_4home.size := by rw [hszH1]; exact h0H
  have h0D1 : 0 < b1.sudo_5Board_4held.size := by rw [hszD1]; exact h0D
  have h0? : b1.sudo_5Board_4held[0]? = some false := by
    rw [hheld1, Array.getElem?_set_eq]
  have h0e : b1.sudo_5Board_4held[0]'h0D1 = false := some_get _ 0 _ h0? h0D1
  have h5H1 : 5 < b1.sudo_5Board_4home.size := by rw [hszH1]; exact h5H
  have h5D1 : 5 < b1.sudo_5Board_4held.size := by rw [hszD1]; exact h5D
  have h5a? : b1.sudo_5Board_4home[5]? = some (embed g) := by
    rw [hhome1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 5)]
    exact cell_some _ 5 _ h5H h5a
  have h5t? : b1.sudo_5Board_4held[5]? = some true := by
    rw [hheld1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 5)]
    exact cell_some _ 5 _ h5D h5t
  have h5a1 := some_get _ 5 _ h5a? h5H1
  have h5t1 := some_get _ 5 _ h5t? h5D1
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; exact h1H
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; exact h1D
  have h1a? : b1.sudo_5Board_4home[1]? = some (embed yP) := by
    rw [hhome1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact cell_some _ 1 _ h1H h1a
  have h1t? : b1.sudo_5Board_4held[1]? = some true := by
    rw [hheld1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact cell_some _ 1 _ h1D h1t
  have h1a1 := some_get _ 1 _ h1a? h1H1
  have h1t1 := some_get _ 1 _ h1t? h1D1
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by rw [hszH1]; exact h2H
  have h2D1 : 2 < b1.sudo_5Board_4held.size := by rw [hszD1]; exact h2D
  have h2a? : b1.sudo_5Board_4home[2]? = some (embed z) := by
    rw [hhome1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 2)]
    exact cell_some _ 2 _ h2H h2a
  have h2t? : b1.sudo_5Board_4held[2]? = some true := by
    rw [hheld1, Array.getElem?_set_ne _ _ _ (by decide : (0 : Nat) ≠ 2)]
    exact cell_some _ 2 _ h2D h2t
  have h7₁ : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; exact h7
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [ht1]; exact hn
  have hbl1 : b1.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [ht1]; exact hbl
  have hw1 : b1.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [ht1]; exact hwF
  have hh1 : b1.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [ht1]; exact hhF
  have hr1 : b1.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [ht1]; exact hrF
  have hk1 : b1.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [ht1]; exact hkF
  let lane := laneFold n (n - k) (school n g xP (List.replicate bench 0) false)
  have hpos1 : 0 < lane.length := by rw [hlen1]; exact Nat.lt_of_lt_of_le hn0 hb
  have hfitL : FitsLen lane.length := by rw [hlen1]; exact hfitB
  have hpeg1 : FitsLen (2 * pegCount (lane.take n)) := by rw [htake]; exact hpeg
  have hfitM1 : FitsLen (mv1 + 2 * pegCount (lane.take n)) := by rw [htake]; exact hfitM
  have hfitS1 : FitsLen (slides + 2 * pegCount (lane.take n)) := by rw [htake]; exact hfitS
  have hfm1 : FitsLen (mv1 + 2 * pegCount (lane.take n) + n * (n + 1)) := by
    rw [htake]; exact hfm2
  have hfold1 : FitsLen (mv1 + 2 * pegCount (lane.take n) + n * (n + 1) + 3 * (bench - n)) := by
    rw [htake]; exact hfold2
  obtain ⟨b2, hmul2, hb2, htake2, hlen2, hzero2⟩ :=
    up_by_gap b1 py g yP lane w h r n k mv1 slides hole1 bench pk1 ps1 c1
      hmk1 hon1 hto1 h0H1 h0D1 h7₁ h0e hbench1 hn1 hn0 hgap0 hpos1
      (by rw [hlen1]; exact hb) hzero1 hf hfitL hmv1 hsl1 hpk1 hpeg1 hfitM1 hfitS1
      hops1 hop01 hfops2 hbl1 h5D1 h5H1 h5t1 h5a1 h1D1 h1H1 h1t1 h1a1
      hgL hyL hspan hgT hfi hfm1 shape hw1 hh1 hr1 hk1 hhole1 hps1
      hsm hnsm hfitB hfold1 hb hclearY
  have hmul2' : mul b1 up gap up false false false = .ok b2 := by
    rw [hmul2, hb2]
  rw [hmul2', ok_bind]
  conv => zeta
  have h0? : b2.sudo_5Board_4home[0]? = some (embed (lane.take n)) := by
    rw [hb2]; exact aim_across? b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hszH2 : b2.sudo_5Board_4home.size = b1.sudo_5Board_4home.size := by
    rw [hb2]
    exact aim_home_size b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hszD2 : b2.sudo_5Board_4held.size = b1.sudo_5Board_4held.size := by
    rw [hb2]
    exact aim_held_size b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have h0H2 : 0 < b2.sudo_5Board_4home.size := by rw [hszH2]; exact h0H1
  have h0a2 : b2.sudo_5Board_4home[0]'h0H2 = embed px :=
    (some_get _ 0 _ h0? h0H2).trans (congrArg embed htake)
  have h1off? : b2.sudo_5Board_4held[1]? = some false := by
    rw [hb2]; exact aim_up_off? b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have h1D2 : 1 < b2.sudo_5Board_4held.size := by rw [hszD2]; exact h1D1
  have h1H2 : 1 < b2.sudo_5Board_4home.size := by rw [hszH2]; exact h1H1
  have h1e2 := some_get _ 1 _ h1off? h1D2
  have hon2 : b2.sudo_5Board_8bench_on = true := by
    rw [hb2]; exact aim_on b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hto2 : b2.sudo_5Board_8bench_to = up := by
    rw [hb2]
    simpa [up] using aim_to b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  let lane2 := laneFold n (n - k) (school n g yP (List.replicate bench 0) false)
  have hbench2 : b2.sudo_5Board_5bench = embed lane2 := by
    rw [hb2]; exact aim_bench b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hn2 : b2.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [hb2]; exact aim_n b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1 hn1
  have h7₂ : 7 ≤ b2.sudo_5Board_4held.size := by rw [hszD2]; exact h7₁
  let mv2 := mulMovesNo (mv1 + 2 * pegCount (lane.take n)) g yP n k bench
  let sl2 := slides + 2 * pegCount (lane.take n)
  let pk2 := raisedPeak
    (raisedPeak pk1 (countHeld (b1.sudo_5Board_4held.set ⟨0, h0D1⟩ true) 7))
    (countHeld ((settleBoard b1 0 h0H1 h0D1 lane n mv1 slides pk1).sudo_5Board_4held.set
      ⟨1, settle_other_held b1 0 1 ⟨h0H1, h0D1⟩ lane n mv1 slides pk1 h1D1⟩ false) 7)
  have hmv2 : b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 := by
    rw [hb2]; exact aim_moves b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hsl2 : b2.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl2 := by
    rw [hb2]; exact aim_slides b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hpk2 : b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 := by
    rw [hb2]; exact aim_peak b1 g yP lane n k mv1 slides hole1 bench pk1 ps1 c1
      hops1 h0H1 h0D1 h1D1 h1H1
  have hpos2 : 0 < lane2.length := by rw [hlen2]; exact Nat.lt_of_lt_of_le hn0 hb
  have hfitL2 : FitsLen lane2.length := by rw [hlen2]; exact hfitB
  have hpeg2 : FitsLen (2 * pegCount (lane2.take n)) := by rw [htake2]; exact hpegY
  have hfitM2 : FitsLen (mv2 + 2 * pegCount (lane2.take n)) := by
    rw [htake2]; simpa [mv2, mv1, htake] using hfitMY
  have hfitS2 : FitsLen (sl2 + 2 * pegCount (lane2.take n)) := by
    rw [htake2]; simpa [sl2, htake] using hfitSY
  obtain ⟨b3, hset, hb3, h0px, h1py⟩ :=
    settle_up b2 px py lane2 n mv2 sl2 pk2 h1H2 h1D2 h0H2 h7₂ hon2 hto2 h1e2
      hbench2 hn2 hpos2 (by rw [hlen2]; exact hb) hzero2 hf hfitL2 hmv2 hsl2 hpk2
      hpeg2 hfitM2 hfitS2 htake2 h0a2
  rw [hset, ok_bind]
  conv => zeta
  have h5b2? : b2.sudo_5Board_4home[5]? = some (embed g) := by
    rw [hb2]
    exact aim_keep_home? b1 g yP lane (embed g) n k mv1 slides hole1 bench pk1 ps1 c1 5
      hops1 h0H1 h0D1 h1D1 h1H1 (by decide) (by decide) h5a?
  have h5t2? : b2.sudo_5Board_4held[5]? = some true := by
    rw [hb2]
    exact aim_keep_held? b1 g yP lane true n k mv1 slides hole1 bench pk1 ps1 c1 5
      hops1 h0H1 h0D1 h1D1 h1H1 (by decide) (by decide) h5t?
  have h2b2? : b2.sudo_5Board_4home[2]? = some (embed z) := by
    rw [hb2]
    exact aim_keep_home? b1 g yP lane (embed z) n k mv1 slides hole1 bench pk1 ps1 c1 2
      hops1 h0H1 h0D1 h1D1 h1H1 (by decide) (by decide) h2a?
  have h2t2? : b2.sudo_5Board_4held[2]? = some true := by
    rw [hb2]
    exact aim_keep_held? b1 g yP lane true n k mv1 slides hole1 bench pk1 ps1 c1 2
      hops1 h0H1 h0D1 h1D1 h1H1 (by decide) (by decide) h2t?
  have hSe : b3.sudo_5Board_4home =
      b2.sudo_5Board_4home.set ⟨1, h1H2⟩ (embed (lane2.take n)) := by
    rw [hb3]; exact settle_home_eq b2 1 ⟨h1H2, h1D2⟩ lane2 n mv2 sl2 pk2
  have hSd : b3.sudo_5Board_4held = b2.sudo_5Board_4held.set ⟨1, h1D2⟩ true := by
    rw [hb3]; exact settle_held_eq b2 1 ⟨h1H2, h1D2⟩ lane2 n mv2 sl2 pk2
  have h5H3 : 5 < b3.sudo_5Board_4home.size := by
    rw [hSe, Array.size_set, hszH2]; exact h5H1
  have h5D3 : 5 < b3.sudo_5Board_4held.size := by
    rw [hSd, Array.size_set, hszD2]; exact h5D1
  have h5a3? : b3.sudo_5Board_4home[5]? = some (embed g) := by
    rw [hSe, Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 5)]
    exact h5b2?
  have h5t3? : b3.sudo_5Board_4held[5]? = some true := by
    rw [hSd, Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 5)]
    exact h5t2?
  have h5a3 := some_get _ 5 _ h5a3? h5H3
  have h5t3 := some_get _ 5 _ h5t3? h5D3
  have h2H3 : 2 < b3.sudo_5Board_4home.size := by
    rw [hSe, Array.size_set, hszH2]; exact h2H1
  have h2D3 : 2 < b3.sudo_5Board_4held.size := by
    rw [hSd, Array.size_set, hszD2]; exact h2D1
  have h2a3? : b3.sudo_5Board_4home[2]? = some (embed z) := by
    rw [hSe, Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
    exact h2b2?
  have h2t3? : b3.sudo_5Board_4held[2]? = some true := by
    rw [hSd, Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
    exact h2t2?
  have h2a3 := some_get _ 2 _ h2a3? h2H3
  have h2t3 := some_get _ 2 _ h2t3? h2D3
  have h0H3 : 0 < b3.sudo_5Board_4home.size := by
    rw [hSe, Array.size_set]; exact h0H2
  have h1H3 : 1 < b3.sudo_5Board_4home.size := by
    rw [hSe, Array.size_set]; exact h1H2
  have h0k := h0px h0H3
  have h1k := h1py h1H3
  have hmv3 : b3.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv2 + 2 * pegCount (lane2.take n)) := by
    rw [hb3]; exact settle_moves_eq b2 1 ⟨h1H2, h1D2⟩ lane2 n mv2 sl2 pk2
  have hmv3' : b3.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv2 + 2 * pegCount py) := by rw [hmv3, htake2]
  have hfitG' : FitsLen (mv2 + 2 * pegCount py + pegCount g) := by
    simpa [mv2, mv1, htake] using hfitG
  obtain ⟨b4, hclG, hb4, h0g⟩ :=
    clear_kept b3 5 0 g px (mv2 + 2 * pegCount py) h5H3 h5D3 h0H3 h5t3 h5a3 hmv3'
      (by rw [hgL]; exact hf) hfitG' (by decide) h0k
  have hclG' : clear b3 gap = .ok b4 := by simpa [gap] using hclG
  rw [hclG', ok_bind]
  conv => zeta
  have hhome4 : b4.sudo_5Board_4home = b3.sudo_5Board_4home.set ⟨5, h5H3⟩ #[] := by
    rw [hb4]
  have hheld4 : b4.sudo_5Board_4held = b3.sudo_5Board_4held.set ⟨5, h5D3⟩ false := by
    rw [hb4]
  have h1H4 : 1 < b4.sudo_5Board_4home.size := by rw [hhome4, Array.size_set]; exact h1H3
  have h1g? : b4.sudo_5Board_4home[1]? = some (embed py) := by
    rw [hhome4, Array.getElem?_set_ne _ _ _ (by decide : (5 : Nat) ≠ 1)]
    exact cell_some _ 1 _ h1H3 h1k
  have h1g := some_get _ 1 _ h1g? h1H4
  have h2H4 : 2 < b4.sudo_5Board_4home.size := by rw [hhome4, Array.size_set]; exact h2H3
  have h2D4 : 2 < b4.sudo_5Board_4held.size := by rw [hheld4, Array.size_set]; exact h2D3
  have h2a4? : b4.sudo_5Board_4home[2]? = some (embed z) := by
    rw [hhome4, Array.getElem?_set_ne _ _ _ (by decide : (5 : Nat) ≠ 2)]
    exact cell_some _ 2 _ h2H3 h2a3
  have h2t4? : b4.sudo_5Board_4held[2]? = some true := by
    rw [hheld4, Array.getElem?_set_ne _ _ _ (by decide : (5 : Nat) ≠ 2)]
    exact cell_some _ 2 _ h2D3 h2t3
  have h2a4 := some_get _ 2 _ h2a4? h2H4
  have h2t4 := some_get _ 2 _ h2t4? h2D4
  have h0H4 : 0 < b4.sudo_5Board_4home.size := by rw [hhome4, Array.size_set]; exact h0H3
  have hmv4 : b4.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv2 + 2 * pegCount py + pegCount g) := by rw [hb4]
  have hfitZ' : FitsLen (mv2 + 2 * pegCount py + pegCount g + pegCount z) := by
    simpa [mv2, mv1, htake] using hfitZ
  obtain ⟨b5, hclZ, _, h0z⟩ :=
    clear_kept b4 2 0 z px (mv2 + 2 * pegCount py + pegCount g) h2H4 h2D4 h0H4
      h2t4 h2a4 hmv4 (by rw [hzL]; exact hf) hfitZ' (by decide) (h0g h0H4)
  obtain ⟨b5', hcl1, _, h1z⟩ :=
    clear_kept b4 2 1 z py (mv2 + 2 * pegCount py + pegCount g) h2H4 h2D4 h1H4
      h2t4 h2a4 hmv4 (by rw [hzL]; exact hf) hfitZ' (by decide) h1g
  have hb5 : b5 = b5' := Except.ok.inj (hclZ.symm.trans hcl1)
  have hclZ' : clear b4 bottom = .ok b5 := by simpa [bottom] using hclZ
  rw [hclZ', ok_bind, pure_eq_ok]
  refine ⟨b5, rfl, h0z, ?_⟩
  intro h1
  exact hb5 ▸ h1z (by rw [← hb5]; exact h1)

end EcbsLink2.Link2
