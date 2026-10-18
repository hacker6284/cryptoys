/-
  The nonzero cell, from the comb the Frobenius leaves.
  The run reads ops slot 0. The rise reads that slot plus 1.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformRun
import EcbsLink2.Link2.FformPointDo

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def fformRunLane (n k bench : Nat) (x x2 z : List Nat) : List Nat :=
  laneFold n (n - k) (school n x2 z (pref (mirrorTrits x) bench n) false)

def fformRunMoves (moves n k bench : Nat) (x x2 z lane : List Nat) : Nat :=
  (moves + pegCount x + 2 * pegCount (lane.take n)) +
    2 * pegCount (mirrorTrits x) + pegCount z + schoolMoves x2 z n n +
    foldCharge n (n - k) (school n x2 z (pref (mirrorTrits x) bench n) false)

def fformRunSlides (slides n : Nat) (x lane : List Nat) : Nat :=
  slides + 2 * pegCount (lane.take n) + 2 * pegCount (mirrorTrits x)

private theorem budget_ge_n (n bench : Nat) : n ≤ stepBudget n bench := by
  simp only [stepBudget]
  omega

private theorem moves_add_n (moves n bench : Nat) :
    moves + n ≤ moves + 8 * stepBudget n bench :=
  Nat.add_le_add_left
    (Nat.le_trans (budget_ge_n n bench)
      (by simpa using Nat.mul_le_mul_right (stepBudget n bench) (by decide : (1 : Nat) ≤ 8)))
    moves

private theorem twice_le (moves n bench p : Nat) (hp : p ≤ n) :
    2 * p ≤ moves + 8 * stepBudget n bench := by
  have h2 : 2 * p ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have h2b : 2 * n ≤ 2 * stepBudget n bench := Nat.mul_le_mul_left 2 (budget_ge_n n bench)
  have h8 : 2 * stepBudget n bench ≤ 8 * stepBudget n bench :=
    Nat.mul_le_mul_right (stepBudget n bench) (by decide : (2 : Nat) ≤ 8)
  exact Nat.le_trans (Nat.le_trans h2 (Nat.le_trans h2b h8)) (Nat.le_add_left _ moves)

private theorem sum_ms (moves n bench a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (moves + a) + 2 * b ≤ moves + 8 * stepBudget n bench := by
  rw [Nat.add_assoc]
  have hab : a + 2 * b ≤ 3 * n := by omega
  have h3 : 3 * n ≤ 3 * stepBudget n bench := Nat.mul_le_mul_left 3 (budget_ge_n n bench)
  have h8 : 3 * stepBudget n bench ≤ 8 * stepBudget n bench :=
    Nat.mul_le_mul_right (stepBudget n bench) (by decide : (3 : Nat) ≤ 8)
  exact Nat.add_le_add_left (Nat.le_trans (Nat.le_trans hab h3) h8) moves

private theorem sum_m (moves n bench a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (moves + a) + 2 * b + 3 * n ≤ moves + 8 * stepBudget n bench := by
  have h6 : a + 2 * b + 3 * n ≤ 6 * n := by omega
  have h6b : 6 * n ≤ 3 * stepBudget n bench := by
    rw [show 6 * n = 3 * (2 * n) by omega]
    exact Nat.mul_le_mul_left 3 (by
      have := budget_ge_n n bench
      -- 2 * n ≤ stepBudget because stepBudget = 2 * n + …
      simp only [stepBudget] at this ⊢
      omega)
  have h8 : 3 * stepBudget n bench ≤ 8 * stepBudget n bench :=
    Nat.mul_le_mul_right (stepBudget n bench) (by decide : (3 : Nat) ≤ 8)
  have ht : a + 2 * b + 3 * n ≤ 8 * stepBudget n bench :=
    Nat.le_trans (Nat.le_trans h6 h6b) h8
  have hassoc : (moves + a) + 2 * b + 3 * n = moves + (a + 2 * b + 3 * n) := by
    simp [Nat.add_assoc]
  exact Nat.le_trans (Nat.le_of_eq hassoc) (Nat.add_le_add_left ht moves)

private theorem sum_q (moves n bench a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (moves + a) + 2 * b + 3 * n + n * (n + 1) ≤ moves + 8 * stepBudget n bench := by
  have hab : a + 2 * b + 3 * n + n * (n + 1) ≤ 6 * n + n * (n + 1) := by omega
  have hsum : 6 * n + n * (n + 1) ≤ stepBudget n bench + 4 * n := by
    simp only [stepBudget]
    omega
  have h4 : 4 * n ≤ 2 * stepBudget n bench := by
    rw [show 4 * n = 2 * (2 * n) by omega]
    have h2 : 2 * n ≤ stepBudget n bench := by simp only [stepBudget]; omega
    exact Nat.mul_le_mul_left 2 h2
  have h3 : stepBudget n bench + 4 * n ≤ 3 * stepBudget n bench := by
    have : stepBudget n bench + 2 * stepBudget n bench = 3 * stepBudget n bench := by omega
    exact Nat.le_trans (Nat.add_le_add_left h4 _) (Nat.le_of_eq this)
  have h8 : 3 * stepBudget n bench ≤ 8 * stepBudget n bench :=
    Nat.mul_le_mul_right (stepBudget n bench) (by decide : (3 : Nat) ≤ 8)
  have ht : a + 2 * b + 3 * n + n * (n + 1) ≤ 8 * stepBudget n bench :=
    Nat.le_trans hab (Nat.le_trans hsum (Nat.le_trans h3 h8))
  have hassoc : (moves + a) + 2 * b + 3 * n + n * (n + 1) =
      moves + (a + 2 * b + 3 * n + n * (n + 1)) := by simp [Nat.add_assoc]
  exact Nat.le_trans (Nat.le_of_eq hassoc) (Nat.add_le_add_left ht moves)

private theorem sum_fold (moves n bench a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (moves + a) + 2 * b + 3 * n + n * (n + 1) + 3 * (bench - n) ≤
      moves + 8 * stepBudget n bench := by
  have hab : a + 2 * b + 3 * n + n * (n + 1) + 3 * (bench - n) ≤
      6 * n + n * (n + 1) + 3 * (bench - n) := by omega
  have hsum : 6 * n + n * (n + 1) + 3 * (bench - n) = stepBudget n bench + 4 * n := by
    simp only [stepBudget]
    omega
  have h4 : 4 * n ≤ 2 * stepBudget n bench := by
    rw [show 4 * n = 2 * (2 * n) by omega]
    have h2 : 2 * n ≤ stepBudget n bench := by simp only [stepBudget]; omega
    exact Nat.mul_le_mul_left 2 h2
  have h3 : stepBudget n bench + 4 * n ≤ 3 * stepBudget n bench := by
    have : stepBudget n bench + 2 * stepBudget n bench = 3 * stepBudget n bench := by omega
    exact Nat.le_trans (Nat.add_le_add_left h4 _) (Nat.le_of_eq this)
  have h8 : 3 * stepBudget n bench ≤ 8 * stepBudget n bench :=
    Nat.mul_le_mul_right (stepBudget n bench) (by decide : (3 : Nat) ≤ 8)
  have ht : a + 2 * b + 3 * n + n * (n + 1) + 3 * (bench - n) ≤ 8 * stepBudget n bench :=
    Nat.le_trans hab (Nat.le_trans (Nat.le_of_eq hsum) (Nat.le_trans h3 h8))
  have hassoc : (moves + a) + 2 * b + 3 * n + n * (n + 1) + 3 * (bench - n) =
      moves + (a + 2 * b + 3 * n + n * (n + 1) + 3 * (bench - n)) := by
    simp [Nat.add_assoc]
  exact Nat.le_trans (Nat.le_of_eq hassoc) (Nat.add_le_add_left ht moves)

private theorem slide_one (slides n p : Nat) (hp : p ≤ n) :
    slides + 2 * p ≤ slides + 8 * n := by omega

private theorem slide_two (slides n p : Nat) (hp : p ≤ n) :
    slides + 2 * p + 2 * n ≤ slides + 8 * n := by omega

/-- Mirror the across and lay the run, then mirror the up and lay the rise.
    `cOps` is ops slot 0 on the comb. The run reads it. The rise reads `cOps + 1`
    and leaves `cOps + 2`. The across home becomes `fformRun`, because the rise
    settles the bench the run left. SPEC.md §3 R7 lines 149–150. -/
theorem rise_on_run (b : Ecbs.Board)
    (x x2 y y2 z lane : List Nat) (red : Bool)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (h1H : 1 < b.sudo_5Board_4home.size) (h1D : 1 < b.sudo_5Board_4held.size)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h3H : 3 < b.sudo_5Board_4home.size) (h3D : 3 < b.sudo_5Board_4held.size)
    (h4H : 4 < b.sudo_5Board_4home.size) (h4D : 4 < b.sudo_5Board_4held.size)
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
    (hScr : m + 6 < script)
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
      3 * (bench - n))) :
    ∃ bRun bRise,
      (Ecbs.mirror b Ecbs.across >>= fun b1 =>
          Ecbs.mul b1 Ecbs.across Ecbs.base_across Ecbs.bottom true true false) = .ok bRun ∧
      (Ecbs.mirror bRun Ecbs.up >>= fun b1 =>
          Ecbs.mul b1 Ecbs.up Ecbs.base_up Ecbs.bottom true true red) = .ok bRise ∧
      (fformRunLane n k bench x x2 z).take n = fformRun n k bench x2 z x ∧
      (∀ h0 : 0 < bRise.sudo_5Board_4home.size,
        bRise.sudo_5Board_4home[0]'h0 = embed (fformRun n k bench x2 z x)) ∧
      (∀ h0 : 0 < bRise.sudo_5Board_4held.size,
        bRise.sudo_5Board_4held[0]'h0 = true) ∧
      (∀ h2 : 2 < bRise.sudo_5Board_4home.size,
        bRise.sudo_5Board_4home[2]'h2 = embed z) ∧
      (∀ h2 : 2 < bRise.sudo_5Board_4held.size,
        bRise.sudo_5Board_4held[2]'h2 = true) ∧
      bRise.sudo_5Board_8bench_on = true ∧
      bRise.sudo_5Board_8bench_to = Ecbs.up ∧
      bRise.sudo_5Board_9marker_on = true ∧
      bRise.sudo_5Board_6marker = Int.ofNat (m + 2) ∧
      bRise.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) ∧
      ∃ laneU holeU,
        bRise.sudo_5Board_5bench = embed laneU ∧
        laneU.take n =
          fformRise n k bench (if red then mirrorTrits y2 else y2) z y ∧
        BenchCarry bRise laneU n (cOps + 2) peak holeU peakS := by
  let laneR := fformRunLane n k bench x x2 z
  let movesR := fformRunMoves moves n k bench x x2 z lane
  let slidesR := fformRunSlides slides n x lane
  have hlenT : (lane.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hnle]
  have hlenZ : z.length = n := by rw [← htake, hlenT]
  have hpegX : pegCount x ≤ n := by simpa [hlen] using pegCount_le x
  have hpegL : pegCount (lane.take n) ≤ n := by simpa [hlenT] using pegCount_le (lane.take n)
  have hfit : FitsLen (moves + n) := fits_le hBig (moves_add_n moves n bench)
  have hfitMk : FitsLen (m + 1) := fits_le hMark (by omega)
  have hfitC : FitsLen (ctrl + 2) := fits_le hCtrl (by omega)
  have hfit2 : FitsLen (m + 2) := fits_le hMark (by omega)
  have hfops : FitsLen (cOps + 1) := fits_le hOps (by omega)
  have hpeg : FitsLen (2 * pegCount (lane.take n)) :=
    fits_le hBig (twice_le moves n bench _ hpegL)
  have hfitMs : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n)) :=
    fits_le hBig (sum_ms moves n bench _ _ hpegX hpegL)
  have hfitSs : FitsLen (slides + 2 * pegCount (lane.take n)) :=
    fits_le hSlide (slide_one slides n _ hpegL)
  have hfitM : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n) :=
    fits_le hBig (sum_m moves n bench _ _ hpegX hpegL)
  have hfitS : FitsLen (slides + 2 * pegCount (lane.take n) + 2 * n) :=
    fits_le hSlide (slide_two slides n _ hpegL)
  have hfm : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n + n * (n + 1)) :=
    fits_le hBig (sum_q moves n bench _ _ hpegX hpegL)
  have hfold : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n +
      n * (n + 1) + 3 * (bench - n)) :=
    fits_le hBig (sum_fold moves n bench _ _ hpegX hpegL)
  obtain ⟨bRun, hokR, hbenchR, htakeR, honR, htoR, hmkR, htierR, hemptyR, _hzero,
      hixR, hctrlR, hmxR, hmvR, hslR, hszDR, hszHR, hhomeR, hheldR, hbotA, hbotH, holeR, carryR⟩ :=
    run_on_bench b 0 3 2 2 x x2 z lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h0H h0D hheld0 hhome0 hn hlen hpos htri hmv hfit hmk hon hto (by decide) rfl
      hm hc hmx hscript (by omega) hfitMk hfitC hfit2 hops hop0 hfops
      h2H h2D h7 hheld2 hbench hposL hnle hzero htake hf hfitL hslides hpeak hpeak7 hpeg
      hfitMs hfitSs hbl h3D h3H hheld3 hhome3 h2D h2H h6D h6H hheld6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnb
      hlen2 hpeakS hpeakS7 hspan hx2 hfi hfitM hfitS hfm hhole hw0 hh0 hrR hrP hnE hkLe hgapN
      hw hh hr hk hsm hnsm hfitB hfold
  have hmvCast : bRun.sudo_5Board_4cost.sudo_5Costs_5moves = (movesR : Int) := by
    simpa [movesR, fformRunMoves, ofNat_eq_natCast] using hmvR
  have hslCast : bRun.sudo_5Board_4cost.sudo_5Costs_6slides = (slidesR : Int) := by
    simpa [slidesR, fformRunSlides, ofNat_eq_natCast] using hslR
  have h1HR : 1 < bRun.sudo_5Board_4home.size := by rw [hszHR]; exact h1H
  have h1DR : 1 < bRun.sudo_5Board_4held.size := by rw [hszDR]; exact h1D
  have h4HR : 4 < bRun.sudo_5Board_4home.size := by rw [hszHR]; exact h4H
  have h4DR : 4 < bRun.sudo_5Board_4held.size := by rw [hszDR]; exact h4D
  have h2HR : 2 < bRun.sudo_5Board_4home.size := by rw [hszHR]; exact h2H
  have h2DR : 2 < bRun.sudo_5Board_4held.size := by rw [hszDR]; exact h2D
  have h0HR : 0 < bRun.sudo_5Board_4home.size := by rw [hszHR]; exact h0H
  have h0DR : 0 < bRun.sudo_5Board_4held.size := by rw [hszDR]; exact h0D
  have h6HR : 6 < bRun.sudo_5Board_4home.size := by rw [hszHR]; exact h6H
  have h6DR : 6 < bRun.sudo_5Board_4held.size := by rw [hszDR]; exact h6D
  have hhome1 : bRun.sudo_5Board_4home[1]'h1HR = embed y :=
    (hhomeR 1 (by decide) (by decide) (by decide) h1H h1HR).trans hhome1
  have hheld1R : bRun.sudo_5Board_4held[1]'h1DR = true :=
    (hheldR 1 (by decide) (by decide) (by decide) h1D h1DR).trans hheld1
  have hhome4 : bRun.sudo_5Board_4home[4]'h4HR = embed y2 :=
    (hhomeR 4 (by decide) (by decide) (by decide) h4H h4HR).trans hhome4
  have hheld4R : bRun.sudo_5Board_4held[4]'h4DR = true :=
    (hheldR 4 (by decide) (by decide) (by decide) h4D h4DR).trans hheld4
  have hUpH : 1 < bRun.sudo_5Board_4home.size := h1HR
  obtain ⟨bRise, hokU, _hbenchU, htakeU, honU, htoU, hmkU, _htierU, _hemptyU, hixU, hctrlU,
      _hmxU, _hmvU, _hslU, _hszDU, _hszHU, _hhomeU, _hheldU, hseatA, hseatH, _holeU, carryU⟩ :=
    rise_on_board bRun 1 4 2 0 y y2 z laneR red
      (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1) n k w h r movesR slidesR
      holeR peak peakS bench
      hUpH h1DR hheld1R hhome1 (by rw [htierR]; exact hn) hleny hpos hty hmvCast hfitR
      hmkR honR htoR (by decide) hixR hctrlR hmxR
      (by rw [htierR]; exact hscript)
      (by omega) (fits_le hMark (by omega)) (fits_le hCtrl (by omega)) (fits_le hMark (by omega))
      carryR.opsSz (by simpa [ofNat_eq_natCast] using carryR.ops0) (fits_le hOps (by omega))
      h0HR h0DR (by rw [hszDR]; exact h7) (hemptyR h0DR) hbenchR carryR.posL carryR.nle
      carryR.zero hf carryR.fitL hslCast (by simpa [ofNat_eq_natCast] using carryR.peakEq)
      carryR.peak7 hpegRR hfitMsR hfitSsR
      (by rw [htierR]; exact hbl)
      h4DR h4HR hheld4R hhome4 h2DR h2HR (hbotH h2DR) (hbotA h2HR)
      carryR.spareSz h6HR carryR.spare
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hnb
      hleny2 hlenZ carryR.strictEq hpeakS7 hspan hty2 hz hfi hfitMR hfitSR hfmR
      carryR.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htierR]; exact hw) (by rw [htierR]; exact hh)
      (by rw [htierR]; exact hr) (by rw [htierR]; exact hk)
      hsm hnsm hfitB hfoldR
  have htakeRun : laneR.take n = fformRun n k bench x2 z x := by
    simpa [laneR, fformRunLane] using htakeR
  let laneU := laneFold n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) red)
  refine ⟨bRun, bRise, ?_, ?_, htakeRun, ?_, ?_, ?_, ?_, honU, ?_, hmkU, ?_, ?_, ?_⟩
  · simpa [Ecbs.across, Ecbs.base_across, Ecbs.bottom] using hokR
  · simpa [Ecbs.up, Ecbs.base_up, Ecbs.bottom] using hokU
  · intro h0
    rw [hseatA h0, htakeRun]
  · intro h0
    exact hseatH h0
  · intro h2
    have h2S : 2 < bRun.sudo_5Board_4home.size := h2HR
    have hkeep := _hhomeU 2 (by decide) (by decide) (by decide) h2S h2
    exact hkeep.trans (hbotA h2S)
  · intro h2
    have h2S : 2 < bRun.sudo_5Board_4held.size := h2DR
    have hkeep := _hheldU 2 (by decide) (by decide) (by decide) h2S h2
    exact hkeep.trans (hbotH h2S)
  · simpa [Ecbs.up] using htoU
  · have hm2 : (m + 1) + 1 = m + 2 := by omega
    simpa [hm2] using hixU
  · have hc4 : (ctrl + 2) + 2 = ctrl + 4 := by omega
    simpa [hc4] using hctrlU
  · refine ⟨laneU, _holeU, ?_, ?_, ?_⟩
    · simpa [laneU] using _hbenchU
    · simpa [laneU] using htakeU
    · have hc2 : (cOps + 1) + 1 = cOps + 2 := by omega
      simpa [laneU, hc2] using carryU
