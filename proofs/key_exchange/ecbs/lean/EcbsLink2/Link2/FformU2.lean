/-
  The rise, then the square of that rise. `gap_u2` reads the `BenchCarry`
  the rise left and leaves the next one. The bench prefix is `u²`.
  SPEC.md §3 R7 lines 150–151. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformRise
import EcbsLink2.Link2.FformGapLay
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

private theorem fits_le {a b : Nat} (h : FitsLen b) (hle : a ≤ b) : FitsLen a :=
  FitsLen.of_le h hle

/-- Square the rise the board just wrote. The new bench prefix is `u²`, and
    the carry the next gap line reads is on that lane. -/
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
    (hpeak7 : 7 ≤ peak)
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
    (hpeakS7 : 7 ≤ peakS)
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
    ∃ bR b2 lane2 hole2,
      (Ecbs.mirror b ((dst : Nat) : Int) >>= fun b1 =>
          Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
            true true mirror) = .ok bR ∧
      Ecbs.mul bR ((gap : Nat) : Int) ((dst : Nat) : Int) ((dst : Nat) : Int)
          true false false = .ok b2 ∧
      lane2.take n = fieldMul n k bench u u ∧
      BenchCarry b2 lane2 n (cOps + 2) peak hole2 peakS := by
  intro u
  obtain ⟨bR, hokR, hbenchR, htakeR, honR, htoR, hmkR, htierR, hemptyR, hixR, hctrlR, hmxR,
      hmvR, hslR, hszH, hszHome, _hhome, hheldK, holeR, carry⟩ :=
    rise_on_board b dst first second seat y y2 z lane mirror
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      hH hD hheld harr hn hlen hpos htri hmv hfit hmk hon hto hseat hm hc hx hscript
      hbound hfitMk hfitC hfit2 hops hop0 hfops hHseat hDseat h7 hempty hbench hposL hnle
      hzero hf hfitL hslides hpeak hpeak7 hpeg hfitMs hfitSs hbl hF hHomeF hHF hArr
      hS hHomeS hHS hYs hSpH hSpHome hSpE hneD1 hneD2 hneSeatF hneSeatS hneSeat6
      hne6D hne6F hne6S hnb hlen2 hlenz hpeakS hpeakS7 hspan hy2 hz hfi hfitM hfitS hfm
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
    (hheldK gap hneG hneGS hneG6 hGapD hGD).trans hGapE
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
  have hpkCast : bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [ofNat_eq_natCast] using carry.peakEq
  have hopCast : bR.sudo_5Board_4cost.sudo_5Costs_3ops[0]'carry.opsSz = ((cOps + 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using carry.ops0
  obtain ⟨b2, lane2, hole2, hok2, _hb, ht2, carry2, _⟩ :=
    gap_u2 bR gap dst u laneR (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1)
      n k w h r movesR slidesR holeR peak peakS bench
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
      (by simpa [u, laneR] using htakeR) hlenU carry.peak7 carry.strictEq hpeakS7
      hfitPR hspan hu hfi hfmR carry.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [htierR]; exact hw) (by rw [htierR]; exact hh)
      (by rw [htierR]; exact hr) (by rw [htierR]; exact hk)
      hsm hnsm hfitB hfoldR
  refine ⟨bR, b2, lane2, hole2, hokR, hok2, ht2, ?_⟩
  · have hc : (cOps + 1) + 1 = cOps + 2 := by omega
    simpa [hc] using carry2

end EcbsLink2.Link2
