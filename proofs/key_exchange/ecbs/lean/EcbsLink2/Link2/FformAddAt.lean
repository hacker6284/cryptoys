/-
  `AddAt` from the comb. `sum_at_of_room` is the onto sum. `add_on_sum`
  aims that sum at the empty gap, and the bench prefix is `fformF`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformSumAt
import EcbsLink2.Link2.FformAddApply

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The board `add_on_sum` returns. The bench prefix is `fformF`. -/
theorem add_at_of_room (b : Ecbs.Board)
    (x x2 y y2 z lane : List Nat) (red : Bool)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (h1H : 1 < b.sudo_5Board_4home.size) (h1D : 1 < b.sudo_5Board_4held.size)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h3H : 3 < b.sudo_5Board_4home.size) (h3D : 3 < b.sudo_5Board_4held.size)
    (h4H : 4 < b.sudo_5Board_4home.size) (h4D : 4 < b.sudo_5Board_4held.size)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hheld0 : b.sudo_5Board_4held[0] = true)
    (hhome0 : b.sudo_5Board_4home[0] = embed x)
    (hheld1 : b.sudo_5Board_4held[1] = true)
    (hhome1 : b.sudo_5Board_4home[1] = embed y)
    (hheld2 : b.sudo_5Board_4held[2] = false)
    (hheld3 : b.sudo_5Board_4held[3] = true)
    (hhome3 : b.sudo_5Board_4home[3] = embed x2)
    (hheld4 : b.sudo_5Board_4held[4] = true)
    (hhome4 : b.sudo_5Board_4home[4] = embed y2)
    (hheld5 : b.sudo_5Board_4held[5] = false)
    (hheld6 : b.sudo_5Board_4held[6] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : x.length = n) (hpos : 0 < n) (htri : allTritList x)
    (hleny : y.length = n) (hty : allTritList y)
    (hleny2 : y2.length = n) (hty2 : allTritList y2)
    (hlen2 : x2.length = n) (hx2 : allTritList x2) (hz : allTritList z)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (htake : lane.take n = z)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hnb : n ≤ bench)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hfi : FitsLen (2 * (n - 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (h24 : FitsLen (moves + 24 * stepBudget n bench))
    (h28 : FitsLen (slides + 28 * n))
    (h40 : FitsLen (ctrl + 40))
    (hOps : FitsLen (cOps + 8))
    (hMark : FitsLen (m + 8))
    (hScr : m + 8 < script) :
    ∃ (bMir bRun bUp bRise bU b3 bV bZ bS bA : Ecbs.Board) (laneA : List Nat)
      (mA ctrlA mxA cA movesA slidesA holeA peakOut strictOut : Nat),
      Ecbs.mirror b Ecbs.across = .ok bMir ∧
      Ecbs.mul bMir Ecbs.across Ecbs.base_across Ecbs.bottom true true false = .ok bRun ∧
      Ecbs.is_zero bRun Ecbs.across =
        .ok (decide (fformRun n k bench x2 z x = List.replicate n 0)) ∧
      Ecbs.mirror bRun Ecbs.up = .ok bUp ∧
      Ecbs.mul bUp Ecbs.up Ecbs.base_up Ecbs.bottom true true red = .ok bRise ∧
      Ecbs.mul bRise Ecbs.gap Ecbs.up Ecbs.up true false false = .ok bU ∧
      Ecbs.mul bU Ecbs.gap Ecbs.bottom Ecbs.gap false false false = .ok b3 ∧
      Ecbs.mul b3 Ecbs.spare Ecbs.across Ecbs.across true false false = .ok bV ∧
      Ecbs.mul bV Ecbs.bottom Ecbs.spare Ecbs.bottom false false false = .ok bZ ∧
      Ecbs.mul bZ Ecbs.gap Ecbs.across Ecbs.spare false true false = .ok bS ∧
      Ecbs.add bS Ecbs.gap Ecbs.bottom false = .ok bA ∧
      AddAt bA laneA n k bench
        (fformRise n k bench (if red then mirrorTrits y2 else y2) z y)
        (fformRun n k bench x2 z x) z x2 y2 script w h r
        mA ctrlA mxA cA movesA slidesA holeA peakOut strictOut := by
  obtain ⟨bMir, bRun, bUp, bRise, bU, b3, bV, bZ, bS, laneS, mS, ctrlS, mxS, cOpsS,
      movesS, slidesS, holeS, peakOut, strictOut, hmir, hmulR, hzero, hmirU, hmulU, hU, hUZ, hV, hVZ, hSumM,
      hSum⟩ :=
    sum_at_of_room b x x2 y y2 z lane red
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h0H h0D h1H h1D h2H h2D h3H h3D h4H h4D h5H h5D h6H h6D
      hheld0 hhome0 hheld1 hhome1 hheld2 hheld3 hhome3 hheld4 hhome4 hheld5 hheld6
      hn hlen hpos htri hleny hty hleny2 hty2 hlen2 hx2 hz
      hmv hmk hon hto hm hc hmx hscript hops hop0 h7
      hbench hposL hnle hzero htake hf hfitL hslides hpeak hbl hnb
      hpeakS hspan hfi hhole hw0 hh0 hrR hrP hnE hkLe hgapN
      hw hh hr hk hsm hnsm hfitB h24 h28 h40 hOps hMark hScr
  let u := fformRise n k bench (if red then mirrorTrits y2 else y2) z y
  let v := fformRun n k bench x2 z x
  obtain ⟨bA, laneA, movesA, hok, _hmv, hA⟩ :=
    add_on_sum bS laneS n k bench u v z x2 y2 script w h r
      mS ctrlS mxS cOpsS movesS slidesS holeS peakOut strictOut hSum
  exact ⟨bMir, bRun, bUp, bRise, bU, b3, bV, bZ, bS, bA, laneA,
    mS, ctrlS, mxS, cOpsS, movesA, slidesS, holeS, peakOut, strictOut,
    hmir, hmulR, hzero, hmirU, hmulU, hU, hUZ, hV, hVZ, hSumM,
    by simpa [Ecbs.gap, Ecbs.bottom] using hok, by simpa [u, v] using hA⟩

end EcbsLink2.Link2
