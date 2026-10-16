/-
  After `chord_gap_mul`, clear the gap. The home was still held, so this is the
  held-home branch of `clear`: the bench, which holds the product and is aimed
  at the gap, stays. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordGap
import EcbsLink2.Link2.Place

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The gap multiply's board, marker flag put back. -/
def gapMulBoard (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) : Ecbs.Board :=
  { mulNoOffBoard (markerUpFeed b m ctrl mx) 5 6 inv rise n k moves hole bench
      peak peakS cOps hops hS hHomeS with
    sudo_5Board_9marker_on := true }

theorem gapMul_home (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[] := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_held (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨6, hS⟩ false := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_row (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_3row =
      b.sudo_5Board_3row := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_high (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_moves (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mulMovesNo moves inv rise n k bench) := by
  unfold gapMulBoard mulNoOffBoard
  rfl

theorem gapMul_bench (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_5bench =
      embed (laneFold n (n - k) (school n inv rise (List.replicate bench 0) false)) ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_8bench_on = true ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_8bench_to =
      (5 : Int) ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_9marker_on =
      true := by
  unfold gapMulBoard mulNoOffBoard
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Clear the gap after the product is on the bench. The bench stays aimed at
    the gap, and the gap home is empty. -/
theorem chord_gap_clear (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : 5 < b.sudo_5Board_4held.size) (hHome : 5 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[5] = true)
    (hArr : b.sudo_5Board_4home[5] = embed inv)
    (hS : 6 < b.sudo_5Board_4held.size) (hHomeS : 6 < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[6] = true)
    (hYs : b.sudo_5Board_4home[6] = embed rise)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : inv.length = n) (hleny : rise.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList inv)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hfitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv)) :
    let bM := gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
    let mv := mulMovesNo moves inv rise n k bench
    ∃ (bC : Ecbs.Board) (h5 : 5 < bM.sudo_5Board_4home.size)
      (h5D : 5 < bM.sudo_5Board_4held.size),
      (do
        let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
        Ecbs.clear b Ecbs.gap) = .ok bC ∧
      bC.sudo_5Board_4home = bM.sudo_5Board_4home.set ⟨5, h5⟩ #[] ∧
      bC.sudo_5Board_4held = bM.sudo_5Board_4held.set ⟨5, h5D⟩ false ∧
      bC.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n inv rise (List.replicate bench 0) false)) ∧
      bC.sudo_5Board_8bench_on = true ∧
      bC.sudo_5Board_8bench_to = (5 : Int) ∧
      bC.sudo_5Board_9marker_on = true ∧
      bC.sudo_5Board_4cost.sudo_5Costs_5moves = ((mv + pegCount inv : Nat) : Int) := by
  intro bM mv
  have hmul := chord_gap_mul b inv rise w h r n k moves hole bench peak peakS cOps m ctrl mx
    script hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hops hop0 hfops hbl hF hHome hHF
    hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm
    hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  have h5 : 5 < bM.sudo_5Board_4home.size := by
    rw [gapMul_home, Array.size_set]
    exact hHome
  have h5D : 5 < bM.sudo_5Board_4held.size := by
    rw [gapMul_held, Array.size_set]
    exact hF
  have harr5 : bM.sudo_5Board_4home[5] = embed inv := by
    have hEq := gapMul_home (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[]).size := by
      rw [Array.size_set]; exact hHome
    have htrans : bM.sudo_5Board_4home[5] =
        (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[])[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hArr]
  have hheld5 : bM.sudo_5Board_4held[5] = true := by
    have hEq := gapMul_held (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4held.set ⟨6, hS⟩ false).size := by
      rw [Array.size_set]; exact hF
    have htrans : bM.sudo_5Board_4held[5] =
        (b.sudo_5Board_4held.set ⟨6, hS⟩ false)[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hHF]
  have hmv : bM.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [gapMul_moves, ofNat_eq_natCast]
  have hfI : FitsLen inv.length := by rw [hlenx]; exact hf
  have hclear := clear_held_refines bM 5 inv mv h5 h5D hheld5 harr5 hmv hfI hfitClear
  let bC := { bM with
    sudo_5Board_4home := bM.sudo_5Board_4home.set ⟨5, h5⟩ #[]
    sudo_5Board_4held := bM.sudo_5Board_4held.set ⟨5, h5D⟩ false
    sudo_5Board_4cost := { bM.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (mv + pegCount inv) } }
  have hbench := gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
  refine ⟨bC, h5, h5D, ?_, rfl, rfl, ?_, hbench.2.1, hbench.2.2.1, hbench.2.2.2, ?_⟩
  · have hmulEq : Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false = .ok bM := by
      simpa [bM, gapMulBoard] using hmul.1
    rw [hmulEq, ok_bind]
    simpa [bC, show Ecbs.gap = ((5 : Nat) : Int) from rfl, ofNat_eq_natCast] using hclear
  · simpa [bC] using hbench.1
  · simp [bC, ofNat_eq_natCast]
