/-
  The rise, then the square of that rise. `gap_u2` reads the `BenchCarry`
  the rise left and leaves the next one. The bench prefix is `u²`.
  SPEC.md §3 R7 lines 150–151. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformRise
import EcbsLink2.Link2.FformGapLay
import EcbsLink2.Link2.FformPointLay
import EcbsLink2.Link2.FieldNeg

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def riseMoveCount (y y2 z lane : List Nat) (mirror : Bool)
    (n k bench moves : Nat) : Nat :=
  (moves + pegCount y + 2 * pegCount (lane.take n)) +
    2 * pegCount (mirrorTrits y) + pegCount z + schoolMoves y2 z n n +
    foldCharge n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) mirror)

def riseSlideCount (y lane : List Nat) (n slides : Nat) : Nat :=
  slides + 2 * pegCount (lane.take n) + 2 * pegCount (mirrorTrits y)

/-- Moves on the board `u²Z` leaves, counted from the moves the rise read. -/
def u2zMoveCap (y y2 z lane : List Nat) (mirror : Bool)
    (n k bench moves : Nat) : Nat :=
  (riseMoveCount y y2 z lane mirror n k bench moves + 2 * n + n + n * (n + 1) +
      3 * (bench - n)) + 2 * n + n * (n + 1) + 3 * (bench - n)

/-- Slides on that same board. -/
def u2zSlideCap (y lane : List Nat) (n slides : Nat) : Nat :=
  riseSlideCount y lane n slides + 2 * n + 2 * n

private theorem fits_le {a b : Nat} (h : FitsLen b) (hle : a ≤ b) : FitsLen a :=
  FitsLen.of_le h hle

/-- Square the rise the board just wrote. `cOps` is the ops cell on the board
    the rise reads. The rise leaves `cOps + 1`. This square reads that cell and
    leaves `cOps + 2`. The bench prefix is `u²`. -/
theorem rise_gap_u2 (b : Ecbs.Board) (dst first second seat gap : Nat)
    (y y2 z lane : List Nat) (mirror : Bool)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hH : dst < b.sudo_5Board_4home.size)
    (hD : dst < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[dst] = true)
    (harr : b.sudo_5Board_4home[dst] = embed y)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : y.length = n) (hpos : 0 < n) (htri : allTritList y)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hHseat : seat < b.sudo_5Board_4home.size)
    (hDseat : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMs : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n)))
    (hfitSs : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size)
    (hHomeF : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed y2)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed z)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second)
    (hneSeatF : seat ≠ first) (hneSeatS : seat ≠ second) (hneSeat6 : seat ≠ 6)
    (hne6D : dst ≠ 6) (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hnb : n ≤ bench)
    (hlen2 : y2.length = n) (hlenz : z.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hy2 : allTritList y2) (hz : allTritList z)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n) + 2 * n))
    (hfm : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n + n * (n + 1)))
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
    (hfold : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n +
        n * (n + 1) + 3 * (bench - n)))
    (hGapD : gap < b.sudo_5Board_4held.size)
    (hGapE : b.sudo_5Board_4held[gap] = false)
    (hneG : gap ≠ dst) (hneGS : gap ≠ seat) (hneG6 : gap ≠ 6)
    (hbound2 : m + 2 < script) (hfitM2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hfops2 : FitsLen (cOps + 2))
    (hSquare : FitsLen (riseMoveCount y y2 z lane mirror n k bench moves +
        2 * n + n + n * (n + 1) + 3 * (bench - n)))
    (hSlide : FitsLen (riseSlideCount y lane n slides + 2 * n)) :
    let u := fformRise n k bench (if mirror then mirrorTrits y2 else y2) z y
    ∃ b1 bR b2 lane2 hole2 peak2 strict2,
      Ecbs.mirror b ((dst : Nat) : Int) = .ok b1 ∧
      Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror = .ok bR ∧
      Ecbs.mul bR ((gap : Nat) : Int) ((dst : Nat) : Int) ((dst : Nat) : Int)
          true false false = .ok b2 ∧
      lane2.take n = fieldMul n k bench u u ∧
      BenchCarry b2 lane2 n (cOps + 2) peak2 hole2 strict2 ∧
      b2.sudo_5Board_8bench_on = true ∧
      b2.sudo_5Board_8bench_to = ((gap : Nat) : Int) ∧
      b2.sudo_5Board_9marker_on = true ∧
      b2.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b2.sudo_5Board_6marker = Int.ofNat (m + 2) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 3)) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat ((riseMoveCount y y2 z lane mirror n k bench moves +
            2 * pegCount ((laneFold n (n - k)
              (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n)) +
          pegCount u + schoolMoves u u n n +
          foldCharge n (n - k) (school n u u (List.replicate bench 0) false)) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (riseSlideCount y lane n slides +
          2 * pegCount ((laneFold n (n - k)
            (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n)) ∧
      b2.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b2.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      (∀ h2 : second < b2.sudo_5Board_4home.size,
        b2.sudo_5Board_4home[second]'h2 = embed z) ∧
      (∀ h2 : second < b2.sudo_5Board_4held.size,
        b2.sudo_5Board_4held[second]'h2 = true) ∧
      (∀ hg : gap < b2.sudo_5Board_4held.size,
        b2.sudo_5Board_4held[gap]'hg = false) ∧
      (∀ hs : seat < b2.sudo_5Board_4home.size,
        b2.sudo_5Board_4home[seat]'hs = embed (lane.take n)) ∧
      (∀ hs : seat < b2.sudo_5Board_4held.size,
        b2.sudo_5Board_4held[seat]'hs = true) ∧
      b2.sudo_5Board_5bench = embed lane2 ∧
      (∀ h : dst < b2.sudo_5Board_4home.size,
        b2.sudo_5Board_4home[dst]'h = embed u) ∧
      (∀ h : dst < b2.sudo_5Board_4held.size,
        b2.sudo_5Board_4held[dst]'h = true) ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4home.size,
        ∀ hj' : j < b2.sudo_5Board_4home.size,
          b2.sudo_5Board_4home[j]'hj' = b.sudo_5Board_4home[j]'hj) ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4held.size,
        ∀ hj' : j < b2.sudo_5Board_4held.size,
          b2.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj) := by
  intro u
  obtain ⟨b1, bR, hmir, hmulR, hbenchR, htakeR, honR, htoR, hmkR, htierR, hemptyR, hixR, hctrlR, hmxR,
      hmvR, hslR, hszH, hszHome, hhomeR, hheldR, hseatA, hseatH, holeR, peakR, strictR, carry⟩ :=
    rise_on_board b dst first second seat y y2 z lane mirror
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      hH hD hheld harr hn hlen hpos htri hmv hfit hmk hon hto hseat hm hc hx hscript
      hbound hfitMk hfitC hfit2 hops hop0 hfops hHseat hDseat h7 hempty hbench hposL hnle
      hzero hf hfitL hslides hpeak hpeg hfitMs hfitSs hbl hF hHomeF hHF hArr
      hS hHomeS hHS hYs hSpH hSpHome hSpE hneD1 hneD2 hneSeatF hneSeatS hneSeat6
      hne6D hne6F hne6S hnb hlen2 hlenz hpeakS hspan hy2 hz hfi hfitM hfitS hfm
      hhole hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB hfold
  let laneR := laneFold n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) mirror)
  let movesR := riseMoveCount y y2 z lane mirror n k bench moves
  let slidesR := riseSlideCount y lane n slides
  have hUpH : dst < bR.sudo_5Board_4home.size := by
    rw [hszHome]; exact hH
  have hUpD : dst < bR.sudo_5Board_4held.size := by
    rw [hszH]; exact hD
  have hGD : gap < bR.sudo_5Board_4held.size := by
    rw [hszH]; exact hGapD
  have h6H : 6 < bR.sudo_5Board_4home.size := by
    rw [hszHome]; exact hSpHome
  have hGE : bR.sudo_5Board_4held[gap]'hGD = false :=
    (hheldR gap hneG hneGS hneG6 hGapD hGD).trans hGapE
  have hlenU : u.length = n := by
    simp [u, fformRise, fieldAdd, List.length_map, List.length_range]
  have hu : allTritList u := by
    simpa [u, fformRise] using
      fieldAdd_trits n (mirrorTrits y)
        (fieldMul n k bench (if mirror then mirrorTrits y2 else y2) z)
  have htakeLen : (laneR.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left carry.nle]
  have hpegR : FitsLen (2 * pegCount (laneR.take n)) :=
    fits_le hSquare (by
      have hp := pegCount_le (laneR.take n)
      rw [htakeLen] at hp
      omega)
  have hpu : pegCount u ≤ n := by
    have hp := pegCount_le u
    rwa [hlenU] at hp
  have hpt : pegCount (laneR.take n) ≤ n := by
    have hp := pegCount_le (laneR.take n)
    rwa [htakeLen] at hp
  have hfitMsR : FitsLen (movesR + 2 * pegCount (laneR.take n)) :=
    fits_le hSquare (by omega)
  have hfitPR : FitsLen (movesR + 2 * pegCount (laneR.take n) + pegCount u) :=
    fits_le hSquare (by omega)
  have hfmR : FitsLen (movesR + 2 * pegCount (laneR.take n) + pegCount u + n * (n + 1)) :=
    fits_le hSquare (by omega)
  have hfoldR : FitsLen (movesR + 2 * pegCount (laneR.take n) + pegCount u +
      n * (n + 1) + 3 * (bench - n)) :=
    fits_le hSquare (by omega)
  have hfitSsR : FitsLen (slidesR + 2 * pegCount (laneR.take n)) :=
    fits_le hSlide (by omega)
  have hmvCast : bR.sudo_5Board_4cost.sudo_5Costs_5moves = (movesR : Int) := by
    simpa [movesR, riseMoveCount, ofNat_eq_natCast] using hmvR
  have hslCast : bR.sudo_5Board_4cost.sudo_5Costs_6slides = (slidesR : Int) := by
    simpa [slidesR, riseSlideCount, ofNat_eq_natCast] using hslR
  have hpkCast : bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakR := by
    simpa [ofNat_eq_natCast] using carry.peakEq
  have hopCast : bR.sudo_5Board_4cost.sudo_5Costs_3ops[0]'carry.opsSz = ((cOps + 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using carry.ops0
  obtain ⟨b2, lane2, hole2, peak2, strict2, hok2, hb2, ht2, carry2, hon2, hto2, hmk2, htier2,
      hix2, hctrl2, hmx2, hmv2, hsl2, hszH2, hszHome2, hhome2, hheld2, hupA, hupH⟩ :=
    gap_u2 bR gap dst u laneR (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1)
      n k w h r movesR slidesR holeR peakR strictR bench
      hUpH hUpD hmkR honR htoR hixR hctrlR hmxR
      (by rw [htierR]; exact hscript)
      hbound2 hfitM2 hfitC4 hfit3
      (by rw [htierR]; exact hn)
      carry.opsSz hopCast hfops2
      (by have := carry.spareSz; omega)
      (hemptyR hUpD) hbenchR carry.posL carry.nle carry.zero hf carry.fitL
      hmvCast hslCast hpkCast hpegR hfitMsR hfitSsR
      (by rw [htierR]; exact hbl)
      carry.spareSz h6H carry.spare hne6D hpos hnb
      (by simpa [u, laneR] using htakeR) hlenU carry.strictEq
      hfitPR hspan hu hfi hfmR carry.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htierR]; exact hw) (by rw [htierR]; exact hh)
      (by rw [htierR]; exact hr) (by rw [htierR]; exact hk)
      hsm hnsm hfitB hfoldR
  have hszHeld2 : b2.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
    rw [hszH2, hszH]
  have hszHome2b : b2.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    rw [hszHome2, hszHome]
  have hBotR : second < bR.sudo_5Board_4home.size := by
    rw [hszHome]; exact hHomeS
  have hBotD : second < bR.sudo_5Board_4held.size := by
    rw [hszH]; exact hS
  have hmark : (m + 1) + 1 = m + 2 := by omega
  have hctrl4 : (ctrl + 2) + 2 = ctrl + 4 := by omega
  have hmx3 : max (max mx (m + 2)) ((m + 1) + 2) = max mx (m + 3) := by omega
  refine ⟨b1, bR, b2, lane2, hole2, peak2, strict2, hmir, hmulR, hok2, ht2, ?_, hon2, hto2, hmk2,
      htier2.trans htierR, ?_, ?_, ?_, ?_, ?_, hszHeld2, hszHome2b, ?_, ?_, ?_, ?_, ?_, hb2,
      ?_, ?_, ?_, ?_⟩
  · have hc : (cOps + 1) + 1 = cOps + 2 := by omega
    simpa [hc] using carry2
  · simpa [hmark] using hix2
  · simpa [hctrl4] using hctrl2
  · simpa [hmx3] using hmx2
  · simpa [movesR, laneR, riseMoveCount] using hmv2
  · simpa [slidesR, laneR, riseSlideCount] using hsl2
  · intro h2
    have hR : bR.sudo_5Board_4home[second]'hBotR = embed z :=
      (hhomeR second (Ne.symm hneD2) (Ne.symm hneSeatS) hne6S hHomeS hBotR).trans hYs
    exact ((hhome2 second (Ne.symm hneD2) hne6S hBotR h2).trans hR)
  · intro h2
    have hR : bR.sudo_5Board_4held[second]'hBotD = true :=
      (hheldR second (Ne.symm hneD2) (Ne.symm hneSeatS) hne6S hS hBotD).trans hHS
    exact ((hheld2 second (Ne.symm hneD2) hne6S hBotD h2).trans hR)
  · intro hg
    exact ((hheld2 gap hneG hneG6 hGD hg).trans hGE)
  · intro hs
    have hsR : seat < bR.sudo_5Board_4home.size := by
      rw [hszHome2] at hs
      exact hs
    exact (hhome2 seat hseat hneSeat6 hsR hs).trans (hseatA hsR)
  · intro hs
    have hsR : seat < bR.sudo_5Board_4held.size := by
      rw [hszH2] at hs
      exact hs
    exact (hheld2 seat hseat hneSeat6 hsR hs).trans (hseatH hsR)
  · intro h
    exact hupA h
  · intro h
    exact hupH h
  · intro j hneD hneSeat hne6 hj hj'
    have hjR : j < bR.sudo_5Board_4home.size := by
      rw [hszHome2] at hj'
      exact hj'
    exact (hhome2 j hneD hne6 hjR hj').trans (hhomeR j hneD hneSeat hne6 hj hjR)
  · intro j hneD hneSeat hne6 hj hj'
    have hjR : j < bR.sudo_5Board_4held.size := by
      rw [hszH2] at hj'
      exact hj'
    exact (hheld2 j hneD hne6 hjR hj').trans (hheldR j hneD hneSeat hne6 hj hjR)

/-- The bottom times the squared rise. `cOps` is the ops cell the rise reads.
    The square reads `cOps + 1` and leaves `cOps + 2`. This multiply reads
    `cOps + 2` and leaves `cOps + 3`. The bench prefix is `Z` times `u²`. -/
theorem rise_gap_u2z (b : Ecbs.Board) (dst first second seat gap : Nat)
    (y y2 z lane : List Nat) (mirror : Bool)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hH : dst < b.sudo_5Board_4home.size)
    (hD : dst < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[dst] = true)
    (harr : b.sudo_5Board_4home[dst] = embed y)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : y.length = n) (hpos : 0 < n) (htri : allTritList y)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hHseat : seat < b.sudo_5Board_4home.size)
    (hDseat : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMs : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n)))
    (hfitSs : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size)
    (hHomeF : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed y2)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed z)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second)
    (hneSeatF : seat ≠ first) (hneSeatS : seat ≠ second) (hneSeat6 : seat ≠ 6)
    (hne6D : dst ≠ 6) (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hnb : n ≤ bench)
    (hlen2 : y2.length = n) (hlenz : z.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hy2 : allTritList y2) (hz : allTritList z)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n) + 2 * n))
    (hfm : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n + n * (n + 1)))
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
    (hfold : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n +
        n * (n + 1) + 3 * (bench - n)))
    (hGapD : gap < b.sudo_5Board_4held.size)
    (hGapH : gap < b.sudo_5Board_4home.size)
    (hGapE : b.sudo_5Board_4held[gap] = false)
    (hneG : gap ≠ dst) (hneGS : gap ≠ seat) (hneG6 : gap ≠ 6)
    (hneBot : second ≠ gap)
    (hbound2 : m + 2 < script) (hfitM2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hfops2 : FitsLen (cOps + 2))
    (hSquare : FitsLen (riseMoveCount y y2 z lane mirror n k bench moves +
        2 * n + n + n * (n + 1) + 3 * (bench - n)))
    (hSlide : FitsLen (riseSlideCount y lane n slides + 2 * n))
    (hbound3 : m + 3 < script) (hfitM3 : FitsLen (m + 3))
    (hfitC6 : FitsLen (ctrl + 6)) (hfit4 : FitsLen (m + 4))
    (hfops3 : FitsLen (cOps + 3))
    (hNext : FitsLen ((riseMoveCount y y2 z lane mirror n k bench moves + 2 * n + n +
        n * (n + 1) + 3 * (bench - n)) + 2 * n + n * (n + 1) + 3 * (bench - n)))
    (hSlideZ : FitsLen (riseSlideCount y lane n slides + 2 * n + 2 * n)) :
    let u := fformRise n k bench (if mirror then mirrorTrits y2 else y2) z y
    ∃ b1 bR b2 b3 lane3 hole3 peak3 strict3 moves3 slides3,
      Ecbs.mirror b ((dst : Nat) : Int) = .ok b1 ∧
      Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror = .ok bR ∧
      Ecbs.mul bR ((gap : Nat) : Int) ((dst : Nat) : Int) ((dst : Nat) : Int)
          true false false = .ok b2 ∧
      Ecbs.mul b2 ((gap : Nat) : Int) ((second : Nat) : Int) ((gap : Nat) : Int)
          false false false = .ok b3 ∧
      lane3.take n = fieldMul n k bench z (fieldMul n k bench u u) ∧
      BenchCarry b3 lane3 n (cOps + 3) peak3 hole3 strict3 ∧
      (∀ hs : seat < b3.sudo_5Board_4home.size,
        b3.sudo_5Board_4home[seat]'hs = embed (lane.take n)) ∧
      (∀ hs : seat < b3.sudo_5Board_4held.size,
        b3.sudo_5Board_4held[seat]'hs = true) ∧
      b3.sudo_5Board_5bench = embed lane3 ∧
      b3.sudo_5Board_8bench_on = true ∧
      b3.sudo_5Board_8bench_to = ((gap : Nat) : Int) ∧
      b3.sudo_5Board_9marker_on = true ∧
      b3.sudo_5Board_6marker = Int.ofNat ((m + 2) + 1) ∧
      b3.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ((ctrl + 4) + 2) ∧
      b3.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max mx (m + 3)) ((m + 2) + 2)) ∧
      b3.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves3 ∧
      b3.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides3 ∧
      (∀ hg : gap < b3.sudo_5Board_4held.size, b3.sudo_5Board_4held[gap]'hg = false) ∧
      b3.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b3.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b3.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      (∀ h2 : second < b3.sudo_5Board_4home.size,
        b3.sudo_5Board_4home[second]'h2 = embed z) ∧
      (∀ h2 : second < b3.sudo_5Board_4held.size,
        b3.sudo_5Board_4held[second]'h2 = true) ∧
      (∀ h : dst < b3.sudo_5Board_4home.size,
        b3.sudo_5Board_4home[dst]'h = embed u) ∧
      (∀ h : dst < b3.sudo_5Board_4held.size,
        b3.sudo_5Board_4held[dst]'h = true) ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ gap → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4home.size,
        ∀ hj' : j < b3.sudo_5Board_4home.size,
          b3.sudo_5Board_4home[j]'hj' = b.sudo_5Board_4home[j]'hj) ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ gap → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4held.size,
        ∀ hj' : j < b3.sudo_5Board_4held.size,
          b3.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj) ∧
      moves3 ≤ u2zMoveCap y y2 z lane mirror n k bench moves ∧
      slides3 ≤ u2zSlideCap y lane n slides := by
  intro u
  obtain ⟨b1, bR, b2, lane2, hole2, peak2, strict2, hmir, hmulR, hok2, ht2, carry2, hon2, hto2, hmk2, htier2,
      hix2, hctrl2, hmx2, hmv2, hsl2, hszH2, hszHome2, hbotA, hbotH, hgapE,
      _hseatA, _hseatH, hb2, hupA, hupH, hkeepH, hkeepD⟩ :=
    rise_gap_u2 b dst first second seat gap y y2 z lane mirror
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      hH hD hheld harr hn hlen hpos htri hmv hfit hmk hon hto hseat hm hc hx hscript
      hbound hfitMk hfitC hfit2 hops hop0 hfops hHseat hDseat h7 hempty hbench hposL hnle
      hzero hf hfitL hslides hpeak hpeg hfitMs hfitSs hbl hF hHomeF hHF hArr
      hS hHomeS hHS hYs hSpH hSpHome hSpE hneD1 hneD2 hneSeatF hneSeatS hneSeat6
      hne6D hne6F hne6S hnb hlen2 hlenz hpeakS hspan hy2 hz hfi hfitM hfitS hfm
      hhole hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB hfold
      hGapD hGapE hneG hneGS hneG6 hbound2 hfitM2 hfitC4 hfit3 hfops2 hSquare hSlide
  let u2 := fieldMul n k bench u u
  let moves2 := (riseMoveCount y y2 z lane mirror n k bench moves +
      2 * pegCount ((laneFold n (n - k)
        (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n)) +
    pegCount u + schoolMoves u u n n +
    foldCharge n (n - k) (school n u u (List.replicate bench 0) false)
  let slides2 := riseSlideCount y lane n slides +
    2 * pegCount ((laneFold n (n - k)
      (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n)
  have hGH : gap < b2.sudo_5Board_4home.size := by
    rw [hszHome2]; exact hGapH
  have hGD : gap < b2.sudo_5Board_4held.size := by
    rw [hszH2]; exact hGapD
  have hBH : second < b2.sudo_5Board_4home.size := by
    rw [hszHome2]; exact hHomeS
  have hBD : second < b2.sudo_5Board_4held.size := by
    rw [hszH2]; exact hS
  have hu2 : allTritList u2 := prod_trits n k bench u u hspan hnb
  have hlen2u : u2.length = n := fieldMul_len n k bench u u hnb
  have hpu : pegCount u ≤ n := by
    have hp := pegCount_le u
    have hlenU : u.length = n := by
      simp [u, fformRise, fieldAdd, List.length_map, List.length_range]
    rwa [hlenU] at hp
  have hrisePeg : pegCount ((laneFold n (n - k)
      (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n) ≤ n := by
    have hmir : (mirrorTrits y).length = n := by
      simp [mirrorTrits, List.length_map, hlen]
    have hsch : (school n y2 z (pref (mirrorTrits y) bench n) mirror).length = bench := by
      rw [school_length, pref_length hnb (by rw [hmir]; exact Nat.le_refl n)]
    have hlenL : (laneFold n (n - k)
        (school n y2 z (pref (mirrorTrits y) bench n) mirror)).length = bench := by
      rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hnb), hsch]
    have htake : ((laneFold n (n - k)
        (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n).length = n := by
      rw [List.length_take, hlenL, Nat.min_eq_left hnb]
    have hp := pegCount_le ((laneFold n (n - k)
      (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n)
    rwa [htake] at hp
  have hschU : (school n u u (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfc : foldCharge n (n - k) (school n u u (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
    simpa [hschU] using
      foldCharge_bound n (n - k) (school n u u (List.replicate bench 0) false)
  have hschMv : schoolMoves u u n n ≤ n * (n + 1) := schoolMoves_bound u u n
  have hmovesLe : moves2 ≤ riseMoveCount y y2 z lane mirror n k bench moves +
      2 * n + n + n * (n + 1) + 3 * (bench - n) := by
    simp only [moves2]
    omega
  have htakeLen : (lane2.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left carry2.nle]
  have hpt : pegCount (lane2.take n) ≤ n := by
    have hp := pegCount_le (lane2.take n)
    rwa [htakeLen] at hp
  have hslideLe : slides2 ≤ riseSlideCount y lane n slides + 2 * n := by
    simp only [slides2]
    omega
  have hpeg2 : FitsLen (2 * pegCount (lane2.take n)) :=
    fits_le hNext (by omega)
  have hfitM2z : FitsLen (moves2 + 2 * pegCount (lane2.take n)) :=
    fits_le hNext (by omega)
  have hfm2 : FitsLen (moves2 + 2 * pegCount (lane2.take n) + n * (n + 1)) :=
    fits_le hNext (by omega)
  have hfold2 : FitsLen (moves2 + 2 * pegCount (lane2.take n) + n * (n + 1) +
      3 * (bench - n)) :=
    fits_le hNext (by
      have hpt' := hpt
      omega)
  have hfitS2 : FitsLen (slides2 + 2 * pegCount (lane2.take n)) :=
    fits_le hSlideZ (by omega)
  have hmvCast : b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves2 := by
    simpa [moves2] using hmv2
  have hslCast : b2.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides2 := by
    simpa [slides2] using hsl2
  have hpkCast : b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak2 := by
    simpa [ofNat_eq_natCast] using carry2.peakEq
  have hopCast : b2.sudo_5Board_4cost.sudo_5Costs_3ops[0]'carry2.opsSz =
      ((cOps + 2 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using carry2.ops0
  obtain ⟨b3, lane3, hole3, peak3, strict3, hok3, _hb3, ht3, carry3, _hon3, _hto3, _hmk3, _htier3,
      _hix3, _hctrl3, _hmx3, _hsec3, _hmv3, _hsl3, _hszD3, hszH3, hhomeJ, hheldJ⟩ :=
    gap_u2z b2 gap second u2 z lane2 (m + 2) (ctrl + 4) (max mx (m + 3)) script (cOps + 2)
      n k w h r moves2 slides2 hole2 peak2 strict2 bench
      hGH hGD hBH hBD (hbotH hBD) (hbotA hBH)
      hmk2 hon2 hto2 hix2 hctrl2 hmx2
      (by rw [htier2]; exact hscript)
      hbound3 hfitM3 hfitC6 hfit4
      (by rw [htier2]; exact hn)
      carry2.opsSz hopCast hfops3
      (by have := carry2.spareSz; omega)
      (hgapE hGD) hb2 carry2.posL carry2.nle carry2.zero hf carry2.fitL
      hmvCast hslCast hpkCast hpeg2 hfitM2z hfitS2
      (by rw [htier2]; exact hbl)
      hneBot hpos hnb
      (by simpa [u2] using ht2) hlen2u hlenz
      carry2.strictEq hspan hz hfi hfm2 carry2.holeEq
      hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htier2]; exact hw) (by rw [htier2]; exact hh)
      (by rw [htier2]; exact hr) (by rw [htier2]; exact hk)
      hsm hnsm hfitB hfold2 carry2.spareSz carry2.spare hneG6
  let moves3 := (moves2 + 2 * pegCount (lane2.take n)) + schoolMoves z u2 n n +
    foldCharge n (n - k) (school n z u2 (List.replicate bench 0) false)
  let slides3 := slides2 + 2 * pegCount (lane2.take n)
  have hschZ : (school n z u2 (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfc3 : foldCharge n (n - k) (school n z u2 (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
    simpa [hschZ] using
      foldCharge_bound n (n - k) (school n z u2 (List.replicate bench 0) false)
  have hsm3 : schoolMoves z u2 n n ≤ n * (n + 1) := schoolMoves_bound z u2 n
  have hmoves3Le : moves3 ≤ moves2 + 2 * n + n * (n + 1) + 3 * (bench - n) := by
    simp only [moves3]
    omega
  have hmovesCap : moves3 ≤ u2zMoveCap y y2 z lane mirror n k bench moves := by
    simp only [u2zMoveCap]
    have h2 := hmovesLe
    have h3 := hmoves3Le
    have h4 := hfc3
    have h5 := hsm3
    omega
  have hslidesCap : slides3 ≤ u2zSlideCap y lane n slides := by
    simp only [slides3, u2zSlideCap]
    have h2 := hslideLe
    omega
  refine ⟨b1, bR, b2, b3, lane3, hole3, peak3, strict3, moves3, slides3, hmir, hmulR, hok2, hok3, ht3, ?_, ?_, ?_,
      _hb3, _hon3, _hto3, _hmk3, _hix3, _hctrl3, _hmx3, ?_, ?_, _hsec3,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmovesCap, hslidesCap⟩
  · have hc : (cOps + 2) + 1 = cOps + 3 := by omega
    simpa [hc] using carry3
  · intro hs
    have hs2 : seat < b2.sudo_5Board_4home.size := by
      rw [hszH3] at hs
      exact hs
    exact (hhomeJ seat (Ne.symm hneGS) hs2 hs).trans (_hseatA hs2)
  · intro hs
    have hs2 : seat < b2.sudo_5Board_4held.size := by
      have hszD : b3.sudo_5Board_4held.size = b2.sudo_5Board_4held.size := by
        rw [_hszD3]
      rw [hszD] at hs
      exact hs
    exact (hheldJ seat (Ne.symm hneGS) hs2 hs).trans (_hseatH hs2)
  · simpa [moves3] using _hmv3
  · simpa [slides3] using _hsl3
  · exact _htier3.trans htier2
  · rw [_hszD3, hszH2]
  · rw [hszH3, hszHome2]
  · intro h2
    have h2b : second < b2.sudo_5Board_4home.size := by
      rw [hszH3] at h2
      exact h2
    exact (hhomeJ second hneBot h2b h2).trans (hbotA h2b)
  · intro h2
    have h2b : second < b2.sudo_5Board_4held.size := by
      have hszD : b3.sudo_5Board_4held.size = b2.sudo_5Board_4held.size := by
        rw [_hszD3]
      rw [hszD] at h2
      exact h2
    exact (hheldJ second hneBot h2b h2).trans (hbotH h2b)
  · intro h
    have hb : dst < b2.sudo_5Board_4home.size := by
      rw [hszH3] at h
      exact h
    exact (hhomeJ dst (Ne.symm hneG) hb h).trans (hupA hb)
  · intro h
    have hb : dst < b2.sudo_5Board_4held.size := by
      have hszD : b3.sudo_5Board_4held.size = b2.sudo_5Board_4held.size := by
        rw [_hszD3]
      rw [hszD] at h
      exact h
    exact (hheldJ dst (Ne.symm hneG) hb h).trans (hupH hb)
  · intro j hneD hneSeat hneGap hne6 hj hj'
    have hj2 : j < b2.sudo_5Board_4home.size := by
      rw [hszH3] at hj'
      exact hj'
    exact (hhomeJ j hneGap hj2 hj').trans (hkeepH j hneD hneSeat hne6 hj hj2)
  · intro j hneD hneSeat hneGap hne6 hj hj'
    have hj2 : j < b2.sudo_5Board_4held.size := by
      have hszD : b3.sudo_5Board_4held.size = b2.sudo_5Board_4held.size := by
        rw [_hszD3]
      rw [hszD] at hj'
      exact hj'
    exact (hheldJ j hneGap hj2 hj').trans (hkeepD j hneD hneSeat hne6 hj hj2)

end EcbsLink2.Link2
