/-
  The two aimed multiplies in `finish`. The gap holds `Z`'s inverse. The
  first multiply writes `g · X` onto a bench aimed at across. The second
  settles that bench, then writes `g · Y` onto a bench aimed at up.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FinishAffine
import EcbsLink2.Link2.FinishMul

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem coeff_at (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    coeff xs i = xs[i] := by
  unfold coeff
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem fold_len (n k bench : Nat) (xs ys : List Nat) (hb : n ≤ bench) :
    (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)).length = bench := by
  have hsch : (school n xs ys (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hb), hsch]

private theorem high_tail (n k bench : Nat) (xs ys : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hb : n ≤ bench) :
    let lane := laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)
    ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
  intro lane i hi hlt
  have hlen : lane.length = bench := fold_len n k bench xs ys hb
  have hco := mul_no_high xs ys n k bench hn0 hgap0 i hi (by rw [← hlen]; exact hlt)
  rw [← coeff_at lane i hlt]
  exact hco

/-- Gap times across, aimed at across. The bench prefix is the affine coordinate. -/
theorem across_by_gap (b : Board) (px xP g : List Nat)
    (w h r n k moves hole bench peak peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h5D : 5 < b.sudo_5Board_4held.size) (h5H : 5 < b.sudo_5Board_4home.size)
    (h5t : b.sudo_5Board_4held[5] = true)
    (h5a : b.sudo_5Board_4home[5] = embed g)
    (h0D : 0 < b.sudo_5Board_4held.size) (h0H : 0 < b.sudo_5Board_4home.size)
    (h0t : b.sudo_5Board_4held[0] = true)
    (h0a : b.sudo_5Board_4home[0] = embed xP)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n) (hgap0 : 0 < n - k)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hgL : g.length = n) (hxL : xP.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hgT : allTritList g)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hb : n ≤ bench)
    (hclear : fieldMul n k bench g xP = px) :
    let lane := laneFold n (n - k) (school n g xP (List.replicate bench 0) false)
    ∃ b1,
      mul b across gap across false false false = .ok b1 ∧
      b1.sudo_5Board_8bench_on = true ∧
      b1.sudo_5Board_8bench_to = across ∧
      b1.sudo_5Board_5bench = embed lane ∧
      lane.take n = px ∧
      lane.length = bench ∧
      (∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
      b1.sudo_5Board_9marker_on = false ∧
      b1 = mulNoOffBoard b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H := by
  have hne : (5 : Nat) ≠ 0 := by decide
  have hmul := mul_no_eq b 0 5 0 g xP w h r n k moves hole bench peak peakS cOps
    hmk hoff hops hop0 hfops hbl h5D h5H h5t h5a h0D h0H h0t h0a h7 hne hn0 hn
    hgL hxL hf hmoves hpeak hpeakS hspan hgT hfi hfm shape hwF hhF hrF hkF hHole
    hsm hnsm hfitB hfold
  have hpre := mul_no_prefix n k bench g xP
  have hlen := fold_len n k bench g xP hb
  have htail := high_tail n k bench g xP hn0 hgap0 hb
  let lane := laneFold n (n - k) (school n g xP (List.replicate bench 0) false)
  have hpx : lane.take n = px := hpre.trans hclear
  let b1 := mulNoOffBoard b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H
  refine ⟨b1, ?_, mul_no_on b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H,
    ?_, mul_no_bench b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H,
    hpx, hlen, htail, rfl, rfl⟩
  · simpa [across, gap] using hmul
  · simpa [across] using
      mul_no_to b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H

/-- Gap times up, after the across bench has been settled. The new bench is
    aimed at up and its prefix is the other affine coordinate. -/
theorem up_by_gap (b : Board) (py g yP lane : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = across)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[0] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hn0 : 0 < n) (hgap0 : 0 < n - k)
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h5D : 5 < b.sudo_5Board_4held.size) (h5H : 5 < b.sudo_5Board_4home.size)
    (h5t : b.sudo_5Board_4held[5] = true)
    (h5a : b.sudo_5Board_4home[5] = embed g)
    (h1D : 1 < b.sudo_5Board_4held.size) (h1H : 1 < b.sudo_5Board_4home.size)
    (h1t : b.sudo_5Board_4held[1] = true)
    (h1a : b.sudo_5Board_4home[1] = embed yP)
    (hgL : g.length = n) (hyL : yP.length = n)
    (hspan : 2 * (n - 1) < bench)
    (hgT : allTritList g)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1) +
      3 * (bench - n)))
    (hb : n ≤ bench)
    (hclear : fieldMul n k bench g yP = py) :
    let lane2 := laneFold n (n - k) (school n g yP (List.replicate bench 0) false)
    ∃ b2,
      mul b up gap up false false false =
        .ok (mulAimBoard b 1 1 0 g yP lane n k moves slides hole bench peak peakS cOps
          hops ⟨h0H, h0D⟩ h1D h1H) ∧
      b2 = mulAimBoard b 1 1 0 g yP lane n k moves slides hole bench peak peakS cOps
        hops ⟨h0H, h0D⟩ h1D h1H ∧
      lane2.take n = py ∧
      lane2.length = bench ∧
      (∀ i, n ≤ i → ∀ hi : i < lane2.length, lane2[i] = 0) := by
  have hne : (5 : Nat) ≠ 1 := by decide
  have hneF : (0 : Nat) ≠ 5 := by decide
  have hneS : (0 : Nat) ≠ 1 := by decide
  have hto0 : b.sudo_5Board_8bench_to = ((0 : Nat) : Int) := by simpa [across] using hto
  have hmul := mul_aim_eq b 1 5 1 0 g yP lane w h r n k moves slides hole bench peak peakS cOps
    hmk hon hto0 h0H h0D h7 hempty hbench hn hn0 hpos hnle hzero hf hfitL hmoves hslides hpeak
    hpeg hfitM hfitS hops hop0 hfops hbl h5D h5H h5t h5a h1D h1H h1t h1a hne hneF hneS
    hgL hyL hspan hgT hfi hfm shape hwF hhF hrF hkF hHole hpeakS hsm hnsm hfitB hfold
  let lane2 := laneFold n (n - k) (school n g yP (List.replicate bench 0) false)
  have hpre : lane2.take n = py := (mul_no_prefix n k bench g yP).trans hclear
  have hlen := fold_len n k bench g yP hb
  have htail := high_tail n k bench g yP hn0 hgap0 hb
  refine ⟨mulAimBoard b 1 1 0 g yP lane n k moves slides hole bench peak peakS cOps
      hops ⟨h0H, h0D⟩ h1D h1H, ?_, rfl, hpre, hlen, htail⟩
  simpa [up, gap] using hmul

private theorem get_congr {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem kept_set {α : Type} (a : Array α) (i j : Nat) (hi : i < a.size) (v x : α)
    (hj : j < a.size) (hne : i ≠ j) (h : a[j]'hj = x)
    (hk : j < (a.set ⟨i, hi⟩ v).size) : (a.set ⟨i, hi⟩ v)[j]'hk = x := by
  rw [Array.getElem_set_ne]
  · exact h
  · exact hne

/-- Settle the bench aimed at up. Home 1 becomes the prefix. Home 0 stays. -/
theorem settle_up (b : Board) (px py lane : List Nat) (n moves slides peak : Nat)
    (h1H : 1 < b.sudo_5Board_4home.size) (h1D : 1 < b.sudo_5Board_4held.size)
    (h0H : 0 < b.sudo_5Board_4home.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = up)
    (hempty : b.sudo_5Board_4held[1] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hpre : lane.take n = py)
    (h0a : b.sudo_5Board_4home[0] = embed px) :
    ∃ b',
      settle b = .ok b' ∧
      b' = settleBoard b 1 h1H h1D lane n moves slides peak ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  have hto1 : b.sudo_5Board_8bench_to = ((1 : Nat) : Int) := by simpa [up] using hto
  have hset := settle_refines b 1 lane n moves slides peak h1H h1D h7 hon hto1 hempty
    hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let bS := settleBoard b 1 h1H h1D lane n moves slides peak
  have hhome := settle_home_eq b 1 ⟨h1H, h1D⟩ lane n moves slides peak
  refine ⟨bS, by simpa [up] using hset, rfl, ?_, ?_⟩
  · intro h0
    have hget := get_congr hhome 0 h0
    have hset0 : (b.sudo_5Board_4home.set ⟨1, h1H⟩ (embed (lane.take n)))[0]'(hhome ▸ h0) =
        embed px := by
      exact kept_set _ 1 0 h1H _ _ h0H (by decide) h0a (hhome ▸ h0)
    exact hget.trans hset0
  · intro h1
    have hget := get_congr hhome 1 h1
    refine hget.trans ?_
    rw [Array.getElem_set]
    simp [hpre]

/-- `clear` of one held home leaves every other home. -/
theorem clear_kept (b : Board) (home j : Nat) (xs px : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (hj : j < b.sudo_5Board_4home.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hf : FitsLen xs.length) (hfit : FitsLen (moves + pegCount xs))
    (hne : home ≠ j)
    (hkeep : b.sudo_5Board_4home[j] = embed px) :
    ∃ b',
      clear b (home : Int) = .ok b' ∧
      b' = { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } } ∧
      (∀ h : j < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[j] = embed px) := by
  have hcl := clear_held_refines b home xs moves hH hD hheld harr hmoves hf hfit
  let b' := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }
  refine ⟨b', hcl, rfl, ?_⟩
  intro hk
  have harrEq : b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hH⟩ #[] := rfl
  have hget := get_congr harrEq j hk
  exact hget.trans (kept_set _ home j hH _ _ hj hne hkeep _)

end EcbsLink2.Link2
