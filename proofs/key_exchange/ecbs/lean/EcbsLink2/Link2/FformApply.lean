/-
  The nonzero cell after `u²Z`. `gap_v2_on_u2z` squares the run on the
  board `comb_u2z` leaves. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCell
import EcbsLink2.Link2.FformV2
import EcbsLink2.Link2.FformV2z
import EcbsLink2.Link2.FformGapSum

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem fold_room (moves3 cap n bench peg pv : Nat)
    (hm : moves3 ≤ cap) (hp : peg ≤ n) (hv : pv ≤ n) :
    (moves3 + 2 * peg) + pv + n * (n + 1) + 3 * (bench - n) ≤
      cap + 16 * stepBudget n bench := by
  have h1 : (moves3 + 2 * peg) + pv + n * (n + 1) + 3 * (bench - n) ≤
      cap + 2 * n + n + n * (n + 1) + 3 * (bench - n) := by omega
  have h2 : cap + 2 * n + n + n * (n + 1) + 3 * (bench - n) ≤
      cap + 16 * stepBudget n bench := by
    simp only [stepBudget]
    omega
  exact Nat.le_trans h1 h2

private theorem under_fold (a p q r s : Nat) : a ≤ ((a + p) + q) + r + s := by
  omega

private theorem under_sum (a p q r : Nat) : a ≤ ((a + p) + q) + r := by
  omega

private theorem under_two (a p q : Nat) : a ≤ (a + p) + q := by
  omega

private theorem under_one (a p : Nat) : a ≤ a + p := Nat.le_add_right a p

private theorem peg_under (a peg q r s : Nat) :
    2 * peg ≤ ((a + 2 * peg) + q) + r + s := by
  omega

/-- The board the onto sum leaves. The bench prefix is `u²Z + v³`, aimed at
    the empty gap. The bottom holds `v²Z`. Homes 0, 1, 3, and 4 stay held. -/
structure SumAt (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat) : Prop where
  on : b.sudo_5Board_8bench_on = true
  to5 : b.sudo_5Board_8bench_to = (5 : Int)
  markOn : b.sudo_5Board_9marker_on = true
  marker : b.sudo_5Board_6marker = Int.ofNat m
  ctrlEq : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  mxEq : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  movesEq : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  slidesEq : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  peakEq : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak
  strictEq : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  holeEq : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  opsSz : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'opsSz = Int.ofNat cOps
  nEq : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  kEq : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k
  benchEq : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench
  scriptEq : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script
  wEq : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hEq : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  rEq : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  home7 : 7 ≤ b.sudo_5Board_4home.size
  home0 : b.sudo_5Board_4home[0]? = some (embed v)
  held0 : b.sudo_5Board_4held[0]? = some true
  home1 : b.sudo_5Board_4home[1]? = some (embed u)
  held1 : b.sudo_5Board_4held[1]? = some true
  home2 : b.sudo_5Board_4home[2]? =
    some (embed (fieldMul n k bench (fieldMul n k bench v v) z))
  held2 : b.sudo_5Board_4held[2]? = some true
  home3 : b.sudo_5Board_4home[3]? = some (embed x2)
  held3 : b.sudo_5Board_4held[3]? = some true
  home4 : b.sudo_5Board_4home[4]? = some (embed y2)
  held4 : b.sudo_5Board_4held[4]? = some true
  held5 : b.sudo_5Board_4held[5]? = some false
  held6 : b.sudo_5Board_4held[6]? = some false
  benchArr : b.sudo_5Board_5bench = embed lane
  posL : 0 < lane.length
  nle : n ≤ lane.length
  fitL : FitsLen lane.length
  zero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i]'hi = 0
  take : lane.take n =
    fieldAdd n (fieldMul n k bench z (fieldMul n k bench u u))
      (fieldMul n k bench v (fieldMul n k bench v v))
  fitN : FitsLen (moves + n)
  lenU : u.length = n
  lenV : v.length = n
  lenZ : z.length = n
  lenX : x2.length = n
  lenY : y2.length = n
  triU : allTritList u
  triV : allTritList v
  triZ : allTritList z
  triX : allTritList x2
  triY : allTritList y2
  span : 2 * (n - 1) < bench
  npos : 0 < n
  nbench : n ≤ bench
  peak7 : 7 ≤ peak
  peakS7 : 7 ≤ peakS
  fi : FitsLen (2 * (n - 1))

private theorem sum_room (movesZ cap peg pu sch fold n bench : Nat)
    (hm : movesZ ≤ cap + 2 * stepBudget n bench + n)
    (hp : peg ≤ n) (hu : pu ≤ n) (hs : sch ≤ n * (n + 1))
    (hf : fold ≤ 3 * (bench - n)) :
    (((movesZ + 2 * peg) + 2 * pu) + sch + fold) + n ≤
      cap + 16 * stepBudget n bench := by
  simp only [stepBudget] at *
  omega

private theorem slide_room (slides3 cap n peg : Nat)
    (hs : slides3 ≤ cap) (hp : peg ≤ n) :
    slides3 + 2 * peg ≤ cap + 16 * n := by
  omega

private theorem moves_after (moves3 cap n bench peg pv sch fold : Nat)
    (hm : moves3 ≤ cap) (hp : peg ≤ n) (hv : pv ≤ n)
    (hs : sch ≤ n * (n + 1)) (hf : fold ≤ 3 * (bench - n)) :
    (moves3 + 2 * peg) + pv + sch + fold ≤ cap + stepBudget n bench + n := by
  simp only [stepBudget]
  omega

private theorem after_room (movesV cap n bench peg : Nat)
    (hm : movesV ≤ cap + stepBudget n bench + n) (hp : peg ≤ n) :
    (movesV + 2 * peg) + n * (n + 1) + 3 * (bench - n) ≤
      cap + 16 * stepBudget n bench := by
  simp only [stepBudget] at *
  omega

private theorem peg2_under (a peg r s : Nat) :
    2 * peg ≤ ((a + 2 * peg) + r) + s := by
  omega

private theorem tail2 (a p q : Nat) : a ≤ (a + p) + q := by
  omega

private theorem peg_sum (a peg n q r : Nat) :
    2 * peg ≤ (((a + 2 * peg) + 2 * n) + q) + r := by
  omega

private theorem settle_sum (a n q r : Nat) : a ≤ ((a + 2 * n) + q) + r := by
  omega

private theorem z_moves (movesV cap n bench peg sch fold : Nat)
    (hm : movesV ≤ cap + stepBudget n bench + n) (hp : peg ≤ n)
    (hs : sch ≤ n * (n + 1)) (hf : fold ≤ 3 * (bench - n)) :
    (movesV + 2 * peg) + sch + fold ≤ cap + 2 * stepBudget n bench + n := by
  simp only [stepBudget] at *
  omega

private theorem sum_fold_le (movesZ cap n bench peg : Nat)
    (hm : movesZ ≤ cap + 2 * stepBudget n bench + n) (hp : peg ≤ n) :
    (movesZ + 2 * peg) + 2 * n + n * (n + 1) + 3 * (bench - n) ≤
      cap + 16 * stepBudget n bench := by
  simp only [stepBudget] at *
  omega

private theorem ctrl_at_sum (ctrl : Nat) :
    (((ctrl + 8) + 2) + 2) + 2 ≤ ctrl + 40 := by omega

private theorem sum_mark (m script : Nat) (h : m + 8 < script) :
    (((m + 4) + 1) + 1) + 1 < script := by omega

private theorem slide_settle (s cap n p q t : Nat)
    (hs : s ≤ cap) (hp : p ≤ n) (hq : q ≤ n) (ht : t ≤ n) :
    ((s + 2 * p) + 2 * q) + 2 * t ≤ cap + 16 * n := by
  omega

private theorem slide_sum (s cap n p q t : Nat)
    (hs : s ≤ cap) (hp : p ≤ n) (hq : q ≤ n) (ht : t ≤ n) :
    ((s + 2 * p) + 2 * q) + 2 * t + 2 * n ≤ cap + 16 * n := by
  omega

private theorem slide_after (slides3 cap n peg peg2 : Nat)
    (hs : slides3 ≤ cap) (hp : peg ≤ n) (hp2 : peg2 ≤ n) :
    (slides3 + 2 * peg) + 2 * peg2 ≤ cap + 16 * n := by
  omega

/-- Square the run on the board `comb_u2z` leaves. The spare receives `v²`.
    The gap stays held and contains `u²Z`. -/
theorem v2_on_comb (b : Ecbs.Board)
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
    (hpeak7 : 7 ≤ peak)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hnb : n ≤ bench)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeakS7 : 7 ≤ peakS)
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
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hCtrl : FitsLen (ctrl + 12))
    (hOps : FitsLen (cOps + 8))
    (hMark : FitsLen (m + 8))
    (hScr : m + 8 < script)
    (hfitR : FitsLen (fformRunMoves moves n k bench x x2 z lane + n))
    (hpegRR : FitsLen (2 * pegCount ((fformRunLane n k bench x x2 z).take n)))
    (hfitMsR : FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n)))
    (hfitSsR : FitsLen (fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n)))
    (hfitMR : FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n))
    (hfitSR : FitsLen (fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 2 * n))
    (hfmR : FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1)))
    (hfoldR : FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) +
      3 * (bench - n)))
    (hSquare : FitsLen (riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n)))
    (hRiseSlide : FitsLen (riseSlideCount y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 2 * n))
    (hNext : FitsLen ((riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n)) +
        2 * n + n * (n + 1) + 3 * (bench - n)))
    (hSlideZ : FitsLen (riseSlideCount y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 2 * n + 2 * n))
    (hVRoom : FitsLen (u2zMoveCap y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) + 16 * stepBudget n bench))
    (hSRoom : FitsLen (u2zSlideCap y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 16 * n))
    (hCtrlRoom : FitsLen (ctrl + 40)) :
    ∃ (bS : Ecbs.Board) (laneS : List Nat)
      (mS ctrlS mxS cOpsS movesS slidesS holeS : Nat),
      SumAt bS laneS n k bench
        (fformRise n k bench (if red then mirrorTrits y2 else y2) z y)
        (fformRun n k bench x2 z x) z x2 y2 script w h r
        mS ctrlS mxS cOpsS movesS slidesS holeS peak peakS := by
  let u := fformRise n k bench (if red then mirrorTrits y2 else y2) z y
  let v := fformRun n k bench x2 z x
  let cap := u2zMoveCap y y2 z (fformRunLane n k bench x x2 z) red n k bench
    (fformRunMoves moves n k bench x x2 z lane)
  let scap := u2zSlideCap y (fformRunLane n k bench x x2 z) n
    (fformRunSlides slides n x lane)
  let mx3 := max (max (max mx (m + 2)) ((m + 1) + 3)) (((m + 1) + 2) + 2)
  obtain ⟨_bRun, _bMid, b3, lane3, hole3, moves3, slides3,
      _hokR, _hmul, htake3, hhome0, hheld0, hhome2, hheld2,
      hbench3, hon3, hto3, hmk3, hix3, hctrl3, hmv3, hsl3, hmx3,
      hszD3, hszH3, hgapF, htier3, carry3,
      hhome1, hheld1, hhome3, hheld3, hhome4, hheld4, hmvLe, hslLe⟩ :=
    comb_u2z b x x2 y y2 z lane red
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h0H h0D h1H h1D h2H h2D h3H h3D h4H h4D h5H h5D h6H h6D
      hheld0 hhome0 hheld1 hhome1 hheld2 hheld3 hhome3 hheld4 hhome4 hheld5 hheld6
      hn hlen hpos htri hleny hty hleny2 hty2 hlen2 hx2 hz
      hmv hmk hon hto hm hc hmx hscript hops hop0 h7
      hbench hposL hnle hzero htake hf hfitL hslides hpeak hpeak7 hbl hnb
      hpeakS hpeakS7 hspan hfi hhole hw0 hh0 hrR hrP hnE hkLe hgapN
      hw hh hr hk hsm hnsm hfitB hBig hSlide hCtrl hOps hMark hScr
      hfitR hpegRR hfitMsR hfitSsR hfitMR hfitSR hfmR hfoldR
      hSquare hRiseSlide hNext hSlideZ
  have hvlen : v.length = n := by
    simp [v, fformRun, fieldAdd, List.length_map, List.length_range]
  have hvT : allTritList v := by
    simpa [v, fformRun] using
      fieldAdd_trits n (mirrorTrits x) (fieldMul n k bench x2 z)
  have htakeLen : (lane3.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left carry3.nle]
  have hpeg3 : pegCount (lane3.take n) ≤ n := by
    simpa [htakeLen] using pegCount_le (lane3.take n)
  have hpv : pegCount v ≤ n := by
    simpa [hvlen] using pegCount_le v
  have hfoldLe := fold_room moves3 cap n bench (pegCount (lane3.take n)) (pegCount v)
    (by simpa [cap] using hmvLe) hpeg3 hpv
  have hfold : FitsLen ((moves3 + 2 * pegCount (lane3.take n)) + pegCount v +
      n * (n + 1) + 3 * (bench - n)) :=
    fits_le hVRoom (by simpa [cap] using hfoldLe)
  have hslideLe := slide_room slides3 scap n (pegCount (lane3.take n))
    (by simpa [scap] using hslLe) hpeg3
  have hfitS : FitsLen (slides3 + 2 * pegCount (lane3.take n)) :=
    fits_le hSRoom (by simpa [scap] using hslideLe)
  have h5H3 : 5 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h5H
  have h5D3 : 5 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h5D
  have h0H3 : 0 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h0H
  have h0D3 : 0 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h0D
  have h6H3 : 6 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h6H
  have hto5 : b3.sudo_5Board_8bench_to = (5 : Int) := by
    simpa [Ecbs.gap] using hto3
  have hpk : b3.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [ofNat_eq_natCast] using carry3.peakEq
  obtain ⟨bV, laneV, holeV, hok, htV, _hpref, carryV, honV, htoV, hmkV, hixV, hctrlV,
      hhomeG, hheldG, hbV, htierV, hmxV, hmvV, hslV, hszDV, hszHV, hkeepH, hkeepD⟩ :=
    gap_v2_on_u2z b3 6 5 0 v lane3 u z
      (m + 4) (ctrl + 8) mx3 script (cOps + 4) (cOps + 1) n k w h r moves3 slides3
      hole3 peak peakS bench
      (by omega) h5H3 h5D3 h0H3 h0D3 (hheld0 h0D3) (by simpa [v] using hhome0 h0H3)
      hmk3 hon3 hto5 hix3 hctrl3 (by simpa [mx3] using hmx3)
      (by rw [htier3]; exact hscript)
      (by omega) (fits_le hMark (by omega)) (fits_le hCtrl (by omega))
      (fits_le hMark (by omega))
      (by rw [htier3]; exact hn)
      carry3.opsSz carry3.ops0 (fits_le hOps (by omega))
      (by rw [hszD3]; exact h7) (hgapF h5D3) hbench3
      carry3.posL carry3.nle carry3.zero (by simpa [u] using htake3)
      hf carry3.fitL hmv3 hsl3 hpk
      (fits_le hfold (peg_under moves3 (pegCount (lane3.take n))
        (pegCount v) (n * (n + 1)) (3 * (bench - n))))
      (fits_le hfold (under_sum (moves3 + 2 * pegCount (lane3.take n)) (pegCount v)
        (n * (n + 1)) (3 * (bench - n))))
      hfitS
      (by rw [htier3]; exact hbl)
      carry3.spareSz h6H3 carry3.spare
      (by decide) (by decide) (by decide)
      hpos hnb hvlen carry3.peak7 carry3.strictEq hpeakS7
      (fits_le hfold (under_two ((moves3 + 2 * pegCount (lane3.take n)) + pegCount v)
        (n * (n + 1)) (3 * (bench - n))))
      hspan hvT hfi
      (fits_le hfold (under_one
        ((moves3 + 2 * pegCount (lane3.take n)) + pegCount v + n * (n + 1))
        (3 * (bench - n))))
      carry3.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htier3]; exact hw) (by rw [htier3]; exact hh)
      (by rw [htier3]; exact hr) (by rw [htier3]; exact hk)
      hsm hnsm hfitB hfold
  let v2 := fieldMul n k bench v v
  let gHome := fieldMul n k bench z (fieldMul n k bench u u)
  let movesV := (moves3 + 2 * pegCount (lane3.take n)) + pegCount v +
    schoolMoves v v n n +
    foldCharge n (n - k) (school n v v (List.replicate bench 0) false)
  let slidesV := slides3 + 2 * pegCount (lane3.take n)
  have hlenZ : z.length = n := by
    have htake0 : (lane.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left hnle]
    rw [← htake, htake0]
  have hlenv2 : v2.length = n := fieldMul_len n k bench v v hnb
  have hv2T : allTritList v2 := prod_trits n k bench v v hspan hnb
  have htakeV : laneV.take n = v2 := by simpa [v2] using htV
  have hpegV : pegCount (laneV.take n) ≤ n := by
    have hl : (laneV.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left carryV.nle]
    simpa [hl] using pegCount_le (laneV.take n)
  have hschLen : (school n v v (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfcV : foldCharge n (n - k) (school n v v (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
    simpa [hschLen] using
      foldCharge_bound n (n - k) (school n v v (List.replicate bench 0) false)
  have hsmV : schoolMoves v v n n ≤ n * (n + 1) := schoolMoves_bound v v n
  have hmvBound : movesV ≤ cap + stepBudget n bench + n := by
    simpa [movesV] using
      moves_after moves3 cap n bench (pegCount (lane3.take n)) (pegCount v)
        (schoolMoves v v n n)
        (foldCharge n (n - k) (school n v v (List.replicate bench 0) false))
        (by simpa [cap] using hmvLe) hpeg3 hpv hsmV hfcV
  have hfoldZ : FitsLen ((movesV + 2 * pegCount (laneV.take n)) + n * (n + 1) +
      3 * (bench - n)) :=
    fits_le hVRoom (after_room movesV cap n bench (pegCount (laneV.take n)) hmvBound hpegV)
  have hslideZ : FitsLen (slidesV + 2 * pegCount (laneV.take n)) :=
    fits_le hSRoom (by
      simpa [slidesV, scap] using
        slide_after slides3 scap n (pegCount (lane3.take n)) (pegCount (laneV.take n))
          hslLe hpeg3 hpegV)
  have h2H3 : 2 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h2H
  have h2D3 : 2 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h2D
  have h2HV : 2 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h2H3
  have h2DV : 2 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h2D3
  have h6HV : 6 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h6H3
  have h6DV : 6 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact carry3.spareSz
  have h5HV : 5 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h5H3
  have h5DV : 5 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h5D3
  have hmvCast : bV.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesV := by
    simpa [movesV] using hmvV
  have hslCast : bV.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesV := by
    simpa [slidesV] using hslV
  have hpkV : bV.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [ofNat_eq_natCast] using carryV.peakEq
  obtain ⟨bZ, laneZ, _hokZ, htZ, hopsZ, honZ, htoZ, hixZ, hhomeGZ, hheldGZ,
      hhomeSZ, hheldSZ, hemptyZ, hbZ, hmkZ, htierZ, hctrlZ, hmxZ, hmvZ, hslZ,
      hszDZ, hszHZ, hkeepHZ, hkeepDZ, hpkZ, hstZ, hholeZ,
      hposZ, hnleZ, hfitLZ, hzeroZ, hopsSzZ⟩ :=
    gap_v2z_on_v2 bV 6 2 5 v v2 z laneV gHome u
      ((m + 4) + 1) ((ctrl + 8) + 2) (max mx3 ((m + 4) + 2)) script
      ((cOps + 1) + 4) (cOps + 1) n k w h r movesV slidesV holeV peak peakS bench
      rfl h6HV h6DV h2HV h2DV
      ((hkeepD 2 (by decide) (by decide) h2D3 h2DV).trans (hheld2 h2D3))
      ((hkeepH 2 (by decide) (by decide) h2H3 h2HV).trans (hhome2 h2H3))
      h5HV h5DV (hheldG h5DV) (by simpa [gHome] using hhomeG h5HV)
      (by decide) (by decide) rfl
      hmkV honV htoV hixV hctrlV (by simpa using hmxV)
      (by rw [htierV, htier3]; exact hscript)
      (by omega) (fits_le hMark (by omega)) (fits_le hCtrl (by omega))
      (fits_le hMark (by omega))
      (by rw [htierV, htier3]; exact hn)
      carryV.opsSz carryV.ops0 (fits_le hOps (by omega))
      (by rw [hszDV, hszD3]; exact h7) carryV.spare hbV
      carryV.posL carryV.nle carryV.zero hf carryV.fitL
      hmvCast hslCast hpkV
      (fits_le hfoldZ (peg2_under movesV (pegCount (laneV.take n))
        (n * (n + 1)) (3 * (bench - n))))
      (fits_le hfoldZ (tail2 (movesV + 2 * pegCount (laneV.take n))
        (n * (n + 1)) (3 * (bench - n))))
      (fits_le hSRoom (by
        simpa [slidesV, scap] using
          slide_after slides3 scap n (pegCount (lane3.take n)) (pegCount (laneV.take n))
            hslLe hpeg3 hpegV))
      (by rw [htierV, htier3]; exact hbl)
      (by decide) hpos hnb htakeV hlenv2 hlenZ (by simpa [v2] using htV)
      carryV.peak7 carryV.strictEq hpeakS7 hspan hv2T hfi
      (fits_le hfoldZ (under_one
        ((movesV + 2 * pegCount (laneV.take n)) + n * (n + 1))
        (3 * (bench - n))))
      carryV.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htierV, htier3]; exact hw) (by rw [htierV, htier3]; exact hh)
      (by rw [htierV, htier3]; exact hr) (by rw [htierV, htier3]; exact hk)
      hsm hnsm hfitB hfoldZ
  let movesZ := (movesV + 2 * pegCount (laneV.take n)) + schoolMoves v2 z n n +
    foldCharge n (n - k) (school n v2 z (List.replicate bench 0) false)
  let slidesZ := slidesV + 2 * pegCount (laneV.take n)
  let holeZ := if holeV < topIdx (school n v2 z (List.replicate bench 0) false) then
    topIdx (school n v2 z (List.replicate bench 0) false) else holeV
  have hschVZ : (school n v2 z (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfcVZ : foldCharge n (n - k) (school n v2 z (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
    simpa [hschVZ] using
      foldCharge_bound n (n - k) (school n v2 z (List.replicate bench 0) false)
  have hsmVZ : schoolMoves v2 z n n ≤ n * (n + 1) := schoolMoves_bound v2 z n
  have hmvZle : movesZ ≤ cap + 2 * stepBudget n bench + n := by
    simpa [movesZ] using
      z_moves movesV cap n bench (pegCount (laneV.take n)) (schoolMoves v2 z n n)
        (foldCharge n (n - k) (school n v2 z (List.replicate bench 0) false))
        hmvBound hpegV hsmVZ hfcVZ
  have hpegZ : pegCount (laneZ.take n) ≤ n := by
    have hl : (laneZ.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left hnleZ]
    simpa [hl] using pegCount_le (laneZ.take n)
  have hfoldS : FitsLen ((movesZ + 2 * pegCount (laneZ.take n)) + 2 * n +
      n * (n + 1) + 3 * (bench - n)) :=
    fits_le hVRoom (sum_fold_le movesZ cap n bench (pegCount (laneZ.take n)) hmvZle hpegZ)
  have h0H3 : 0 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h0H
  have h0D3 : 0 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h0D
  have h0HV : 0 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h0H3
  have h0DV : 0 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h0D3
  have h0HZ : 0 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h0HV
  have h0DZ : 0 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h0DV
  have hhome0Z : bZ.sudo_5Board_4home[0]'h0HZ = embed v :=
    ((hkeepHZ 0 (by decide) (by decide) h0HV h0HZ).trans
      ((hkeepH 0 (by decide) (by decide) h0H3 h0HV).trans (hhome0 h0H3)))
  have hheld0Z : bZ.sudo_5Board_4held[0]'h0DZ = true :=
    ((hkeepDZ 0 (by decide) (by decide) h0DV h0DZ).trans
      ((hkeepD 0 (by decide) (by decide) h0D3 h0DV).trans (hheld0 h0D3)))
  have hu2zT : allTritList gHome := prod_trits n k bench z (fieldMul n k bench u u) hspan hnb
  have hlenG : gHome.length = n := fieldMul_len n k bench z (fieldMul n k bench u u) hnb
  have hmvZS : bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesZ := by
    simpa [movesZ] using hmvZ
  have hslZS : bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesZ := by
    simpa [slidesZ] using hslZ
  have hpkZS : bZ.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [ofNat_eq_natCast] using hpkZ
  have htakeZS : laneZ.take n = fieldMul n k bench v2 z := by
    simpa [v2] using htZ
  have h5HZ : 5 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h5HV
  have h5DZ : 5 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h5DV
  have h6HZ : 6 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h6HV
  have h6DZ : 6 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h6DV
  have h2HZ : 2 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h2HV
  have h2DZ : 2 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h2DV
  obtain ⟨bS, laneS, _hokS, hbS, htS, hopsS, honS, htoS, hmkS, hixS, hbotS, hheldBS,
      hgapES, hspES, hctrlS, hmxS, htierS, hmvS, hslS, hszDS, hszHS, hkeepS, hkeepDS,
      hposS, hnleS, hfitLS, hzeroS, hpkS, hstS, hopsSzS, ⟨holeS, hholeOutS⟩⟩ :=
    gap_sum_on_v2z bZ 5 0 6 2 u v v2 gHome z laneZ
      (((m + 4) + 1) + 1) (((ctrl + 8) + 2) + 2)
      (max (max mx3 ((m + 4) + 2)) (((m + 4) + 1) + 2))
      script ((cOps + 1) + 5) (cOps + 1) n k w h r movesZ slidesZ holeZ peak peakS bench
      rfl h5HZ h5DZ (hheldGZ h5DZ) (by simpa [gHome] using hhomeGZ h5HZ)
      h0HZ h0DZ hheld0Z hhome0Z
      h6HZ h6DZ (hheldSZ h6DZ) (by simpa [v2] using hhomeSZ h6HZ)
      h2HZ h2DZ (hemptyZ h2DZ)
      hmkZ honZ htoZ hixZ hctrlZ hmxZ
      (by rw [htierZ, htierV, htier3]; exact hscript)
      (sum_mark m script hScr) (fits_le hMark (by omega))
      (fits_le hCtrlRoom (ctrl_at_sum ctrl))
      (fits_le hMark (by omega))
      (by rw [htierZ, htierV, htier3]; exact hn)
      hopsSzZ (by simpa [ofNat_eq_natCast] using hopsZ hopsSzZ)
      (fits_le hOps (by omega))
      (by rw [hszDZ, hszDV, hszD3]; exact h7)
      hbZ hposZ hnleZ hzeroZ htakeZS
      hf hfitLZ hmvZS hslZS hpkZS
      (fits_le hfoldS (peg_sum movesZ (pegCount (laneZ.take n)) n
        (n * (n + 1)) (3 * (bench - n))))
      (fits_le hfoldS (settle_sum (movesZ + 2 * pegCount (laneZ.take n)) n
        (n * (n + 1)) (3 * (bench - n))))
      (fits_le hSRoom (by
        simpa [slidesZ, slidesV, scap] using
          slide_settle slides3 scap n (pegCount (lane3.take n))
            (pegCount (laneV.take n)) (pegCount (laneZ.take n))
            hslLe hpeg3 hpegV hpegZ))
      (by rw [htierZ, htierV, htier3]; exact hbl)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hpos hnb hlenG hvlen hlenv2 rfl rfl
      carryV.peak7 hstZ hpeakS7 hspan hu2zT hvT hfi
      (fits_le hfoldS (under_two ((movesZ + 2 * pegCount (laneZ.take n)) + 2 * n)
        (n * (n + 1)) (3 * (bench - n))))
      (fits_le hSRoom (by
        simpa [slidesZ, scap] using
          slide_sum slides3 scap n (pegCount (lane3.take n))
            (pegCount (laneV.take n)) (pegCount (laneZ.take n))
            (by simpa [scap] using hslLe) hpeg3 hpegV hpegZ))
      (fits_le hfoldS (under_one
        (((movesZ + 2 * pegCount (laneZ.take n)) + 2 * n) + n * (n + 1))
        (3 * (bench - n))))
      (by simpa [holeZ] using hholeZ)
      hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htierZ, htierV, htier3]; exact hw)
      (by rw [htierZ, htierV, htier3]; exact hh)
      (by rw [htierZ, htierV, htier3]; exact hr)
      (by rw [htierZ, htierV, htier3]; exact hk)
      hsm hnsm hfitB hfoldS
  have h1H3 : 1 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h1H
  have h1D3 : 1 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h1D
  have h3H3 : 3 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h3H
  have h3D3 : 3 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h3D
  have h4H3 : 4 < b3.sudo_5Board_4home.size := by rw [hszH3]; exact h4H
  have h4D3 : 4 < b3.sudo_5Board_4held.size := by rw [hszD3]; exact h4D
  have h1HV : 1 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h1H3
  have h1DV : 1 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h1D3
  have h3HV : 3 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h3H3
  have h3DV : 3 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h3D3
  have h4HV : 4 < bV.sudo_5Board_4home.size := by rw [hszHV]; exact h4H3
  have h4DV : 4 < bV.sudo_5Board_4held.size := by rw [hszDV]; exact h4D3
  have h1HZ : 1 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h1HV
  have h1DZ : 1 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h1DV
  have h3HZ : 3 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h3HV
  have h3DZ : 3 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h3DV
  have h4HZ : 4 < bZ.sudo_5Board_4home.size := by rw [hszHZ]; exact h4HV
  have h4DZ : 4 < bZ.sudo_5Board_4held.size := by rw [hszDZ]; exact h4DV
  have h1HS : 1 < bS.sudo_5Board_4home.size := by rw [hszHS]; exact h1HZ
  have h1DS : 1 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h1DZ
  have h3HS : 3 < bS.sudo_5Board_4home.size := by rw [hszHS]; exact h3HZ
  have h3DS : 3 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h3DZ
  have h4HS : 4 < bS.sudo_5Board_4home.size := by rw [hszHS]; exact h4HZ
  have h4DS : 4 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h4DZ
  have h0HS : 0 < bS.sudo_5Board_4home.size := by rw [hszHS]; exact h0HZ
  have h0DS : 0 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h0DZ
  have h2HS : 2 < bS.sudo_5Board_4home.size := by rw [hszHS]; exact h2HZ
  have h2DS : 2 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h2DZ
  have h5HS : 5 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h5DZ
  have h6HS : 6 < bS.sudo_5Board_4held.size := by rw [hszDS]; exact h6DZ
  have hhome1S : bS.sudo_5Board_4home[1]'h1HS = embed u :=
    (hkeepS 1 (by decide) (by decide) (by decide) h1HZ h1HS).trans
      ((hkeepHZ 1 (by decide) (by decide) h1HV h1HZ).trans
        ((hkeepH 1 (by decide) (by decide) h1H3 h1HV).trans (by simpa [u] using hhome1 h1H3)))
  have hheld1S : bS.sudo_5Board_4held[1]'h1DS = true :=
    (hkeepDS 1 (by decide) (by decide) (by decide) h1DZ h1DS).trans
      ((hkeepDZ 1 (by decide) (by decide) h1DV h1DZ).trans
        ((hkeepD 1 (by decide) (by decide) h1D3 h1DV).trans (hheld1 h1D3)))
  have hhome3S : bS.sudo_5Board_4home[3]'h3HS = embed x2 :=
    (hkeepS 3 (by decide) (by decide) (by decide) h3HZ h3HS).trans
      ((hkeepHZ 3 (by decide) (by decide) h3HV h3HZ).trans
        ((hkeepH 3 (by decide) (by decide) h3H3 h3HV).trans (hhome3 h3H3)))
  have hheld3S : bS.sudo_5Board_4held[3]'h3DS = true :=
    (hkeepDS 3 (by decide) (by decide) (by decide) h3DZ h3DS).trans
      ((hkeepDZ 3 (by decide) (by decide) h3DV h3DZ).trans
        ((hkeepD 3 (by decide) (by decide) h3D3 h3DV).trans (hheld3 h3D3)))
  have hhome4S : bS.sudo_5Board_4home[4]'h4HS = embed y2 :=
    (hkeepS 4 (by decide) (by decide) (by decide) h4HZ h4HS).trans
      ((hkeepHZ 4 (by decide) (by decide) h4HV h4HZ).trans
        ((hkeepH 4 (by decide) (by decide) h4H3 h4HV).trans (hhome4 h4H3)))
  have hheld4S : bS.sudo_5Board_4held[4]'h4DS = true :=
    (hkeepDS 4 (by decide) (by decide) (by decide) h4DZ h4DS).trans
      ((hkeepDZ 4 (by decide) (by decide) h4DV h4DZ).trans
        ((hkeepD 4 (by decide) (by decide) h4D3 h4DV).trans (hheld4 h4D3)))
  have hhome0S : bS.sudo_5Board_4home[0]'h0HS = embed v :=
    (hkeepS 0 (by decide) (by decide) (by decide) h0HZ h0HS).trans hhome0Z
  have hheld0S : bS.sudo_5Board_4held[0]'h0DS = true :=
    (hkeepDS 0 (by decide) (by decide) (by decide) h0DZ h0DS).trans
      ((hkeepDZ 0 (by decide) (by decide) h0DV h0DZ).trans
        ((hkeepD 0 (by decide) (by decide) h0D3 h0DV).trans (hheld0 h0D3)))
  have huT : allTritList u := by
    simpa [u, fformRise] using
      fieldAdd_trits n (mirrorTrits y)
        (fieldMul n k bench (if red then mirrorTrits y2 else y2) z)
  have huLen : u.length = n := by
    simp [u, fformRise, fieldAdd, List.length_map, List.length_range]
  let mS := (((m + 4) + 1) + 1) + 1
  let cS := (((ctrl + 8) + 2) + 2) + 2
  let cOpsS := ((cOps + 1) + 5) + 1
  let mxS := max (max (max mx3 ((m + 4) + 2)) (((m + 4) + 1) + 2))
    ((((m + 4) + 1) + 1) + 2)
  let movesS := ((movesZ + 2 * pegCount (laneZ.take n)) + 2 * pegCount gHome) +
    schoolMoves v v2 n n +
    foldCharge n (n - k) (school n v v2 (pref gHome bench n) false)
  let slidesS := (slidesZ + 2 * pegCount (laneZ.take n)) + 2 * pegCount gHome
  exact ⟨bS, laneS, mS, cS, mxS, cOpsS, movesS, slidesS, holeS, {
    on := honS
    to5 := by simpa using htoS
    markOn := hmkS
    marker := by simpa [mS] using hixS
    ctrlEq := by simpa [cS] using hctrlS
    mxEq := by simpa using hmxS
    movesEq := by simpa [movesS, gHome] using hmvS
    slidesEq := by simpa [slidesS, gHome] using hslS
    peakEq := by simpa [ofNat_eq_natCast] using hpkS
    strictEq := hstS
    holeEq := hholeOutS
    opsSz := hopsSzS
    ops0 := by simpa [cOpsS, ofNat_eq_natCast] using hopsS hopsSzS
    nEq := by rw [htierS, htierZ, htierV, htier3]; exact hn
    kEq := by rw [htierS, htierZ, htierV, htier3]; exact hk
    benchEq := by rw [htierS, htierZ, htierV, htier3]; exact hbl
    scriptEq := by rw [htierS, htierZ, htierV, htier3]; exact hscript
    wEq := by rw [htierS, htierZ, htierV, htier3]; exact hw
    hEq := by rw [htierS, htierZ, htierV, htier3]; exact hh
    rEq := by rw [htierS, htierZ, htierV, htier3]; exact hr
    home7 := by rw [hszHS, hszHZ, hszHV, hszH3]; exact Nat.succ_le_of_lt h6H
    home0 := (Array.getElem?_eq_getElem h0HS).trans (congrArg some hhome0S)
    held0 := (Array.getElem?_eq_getElem h0DS).trans (congrArg some hheld0S)
    home1 := (Array.getElem?_eq_getElem h1HS).trans (congrArg some hhome1S)
    held1 := (Array.getElem?_eq_getElem h1DS).trans (congrArg some hheld1S)
    home2 := (Array.getElem?_eq_getElem h2HS).trans (congrArg some (hbotS h2HS))
    held2 := (Array.getElem?_eq_getElem h2DS).trans (congrArg some (hheldBS h2DS))
    home3 := (Array.getElem?_eq_getElem h3HS).trans (congrArg some hhome3S)
    held3 := (Array.getElem?_eq_getElem h3DS).trans (congrArg some hheld3S)
    home4 := (Array.getElem?_eq_getElem h4HS).trans (congrArg some hhome4S)
    held4 := (Array.getElem?_eq_getElem h4DS).trans (congrArg some hheld4S)
    held5 := (Array.getElem?_eq_getElem h5HS).trans (congrArg some (hgapES h5HS))
    held6 := (Array.getElem?_eq_getElem h6HS).trans (congrArg some (hspES h6HS))
    benchArr := hbS
    posL := hposS
    nle := hnleS
    fitL := hfitLS
    zero := hzeroS
    take := by simpa [v2] using htS
    fitN := fits_le hVRoom (by
      have hpu : pegCount gHome ≤ n := by simpa [hlenG] using pegCount_le gHome
      have hsch : schoolMoves v v2 n n ≤ n * (n + 1) := schoolMoves_bound v v2 n
      have hlenSch : (school n v v2 (pref gHome bench n) false).length = bench := by
        rw [school_length, pref_length hnb (by rw [hlenG]; exact Nat.le_refl n)]
      have hfc : foldCharge n (n - k) (school n v v2 (pref gHome bench n) false) ≤
          3 * (bench - n) := by
        simpa [hlenSch] using
          foldCharge_bound n (n - k) (school n v v2 (pref gHome bench n) false)
      simpa [movesS] using
        sum_room movesZ cap (pegCount (laneZ.take n)) (pegCount gHome)
          (schoolMoves v v2 n n)
          (foldCharge n (n - k) (school n v v2 (pref gHome bench n) false))
          n bench hmvZle hpegZ hpu hsch hfc)
    lenU := huLen
    lenV := hvlen
    lenZ := hlenZ
    lenX := hlen2
    lenY := hleny2
    triU := huT
    triV := hvT
    triZ := hz
    triX := hx2
    triY := hty2
    span := hspan
    npos := hpos
    nbench := hnb
    peak7 := carryV.peak7
    peakS7 := hpeakS7
    fi := hfi
  }⟩

end EcbsLink2.Link2
