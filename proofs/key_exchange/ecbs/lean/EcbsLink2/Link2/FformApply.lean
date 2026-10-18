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
    ∃ _bZ : Ecbs.Board, True := by
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
  obtain ⟨bS, _laneS, _⟩ :=
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
      carryV.peak7 hstZ hspan hu2zT hvT hfi
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
  exact ⟨bS, trivial⟩

end EcbsLink2.Link2
