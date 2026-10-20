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
      b1.sudo_5Board_9marker_on = false := by
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
    hpx, hlen, htail, rfl⟩
  · simpa [across, gap] using hmul
  · simpa [across] using
      mul_no_to b 0 0 g xP n k moves hole bench peak peakS cOps hops h0D h0H

end EcbsLink2.Link2
