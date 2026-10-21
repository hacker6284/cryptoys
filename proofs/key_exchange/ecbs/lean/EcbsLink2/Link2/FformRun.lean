/-
  The run of `fform_add` from the board `frobenius_point` leaves.
  The bench holds `Z` and is aimed at the bottom, and that home is empty.
  Mirror the across, settle `Z` into the bottom, and lay base across times
  that bottom onto the mirrored across. The bench prefix is SPEC.md §3 R7
  line 149, `v = x₂Z − X`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformRise

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem mirror_trits_local (y : List Nat) : allTritList (mirrorTrits y) := by
  intro a ha
  simp only [mirrorTrits, List.mem_map] at ha
  rcases ha with ⟨c, _, rfl⟩
  by_cases hc0 : c = 0
  · simp [hc0]
  · by_cases hc1 : c = 1
    · simp [hc1]
    · by_cases hc2 : c = 2
      · simp [hc2]
      · have hge : 3 ≤ c := by omega
        simp [hc0]
        omega

private theorem mirror_len (y : List Nat) (n : Nat) (hlen : y.length = n) :
    (mirrorTrits y).length = n := by
  simp [mirrorTrits, List.length_map, hlen]

private theorem idx_eq_local {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- Mirror the across, then the onto multiply. The bench is aimed at the
    bottom, and that home is empty, so the settle writes the bench prefix
    there before the product. The new bench prefix is `fformRun`.
    SPEC.md §3 R7 line 149. -/
theorem run_on_bench (b : Ecbs.Board) (dst first second seat : Nat)
    (x x2 z lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hH : dst < b.sudo_5Board_4home.size)
    (hD : dst < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[dst] = true)
    (harr : b.sudo_5Board_4home[dst] = embed x)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : x.length = n) (hpos : 0 < n) (htri : allTritList x)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hseatEq : seat = second)
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
    (htake : lane.take n = z)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMs : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n)))
    (hfitSs : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size)
    (hHomeF : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed x2)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second)
    (hneSeatF : seat ≠ first) (hneSeat6 : seat ≠ 6)
    (hne6D : dst ≠ 6) (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hnb : n ≤ bench)
    (hlen2 : x2.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hx2 : allTritList x2)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n) + 2 * n))
    (hfm : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n + n * (n + 1)))
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
    (hfold : FitsLen ((moves + pegCount x) + 2 * pegCount (lane.take n) + 3 * n +
        n * (n + 1) + 3 * (bench - n))) :
    ∃ b1 b',
      Ecbs.mirror b ((dst : Nat) : Int) = .ok b1 ∧
      Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true false = .ok b' ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k)
          (school n x2 z (pref (mirrorTrits x) bench n) false)) ∧
      (laneFold n (n - k)
          (school n x2 z (pref (mirrorTrits x) bench n) false)).take n =
        fformRun n k bench x2 z x ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = ((dst : Nat) : Int) ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      (∀ hD' : dst < b'.sudo_5Board_4held.size,
        b'.sudo_5Board_4held[dst]'hD' = false) ∧
      Ecbs.is_zero b' ((dst : Nat) : Int) =
        .ok (decide (fformRun n k bench x2 z x = List.replicate n 0)) ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat ((moves + pegCount x + 2 * pegCount (lane.take n)) +
          2 * pegCount (mirrorTrits x) + pegCount z + schoolMoves x2 z n n +
          foldCharge n (n - k)
            (school n x2 z (pref (mirrorTrits x) bench n) false)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n) + 2 * pegCount (mirrorTrits x)) ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4home.size,
        ∀ hj' : j < b'.sudo_5Board_4home.size,
          b'.sudo_5Board_4home[j]'hj' = b.sudo_5Board_4home[j]'hj) ∧
      (∀ j, j ≠ dst → j ≠ seat → j ≠ 6 →
        ∀ hj : j < b.sudo_5Board_4held.size,
        ∀ hj' : j < b'.sudo_5Board_4held.size,
          b'.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj) ∧
      (∀ h2 : second < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[second]'h2 = embed z) ∧
      (∀ h2 : second < b'.sudo_5Board_4held.size,
        b'.sudo_5Board_4held[second]'h2 = true) ∧
      (∃ (hole' peak' strict' : Nat),
        BenchCarry b'
          (laneFold n (n - k) (school n x2 z (pref (mirrorTrits x) bench n) false))
          n (cOps + 1) peak' hole' strict') ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      ∀ j, j ≠ 0 →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[j]? =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[j]? := by
  let bM := mirrorHome b dst hH (embed (mirrorTrits x)) (moves + pegCount x)
  let feed := markerUpFeed bM m ctrl mx
  let hopsM : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [bM, mirrorHome, withMoves] using hops
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hopsM
  let bU := bumpOp feed 0 cOps hopsF
  let mvM := moves + pegCount x
  let pegL := pegCount (lane.take n)
  let mvS := mvM + 2 * pegL
  let slS := slides + 2 * pegL
  have hrise := rise_marker b dst dst first second seat x m ctrl mx script cOps n moves false
    hH hD hheld harr hn hlen hpos htri hmv hfit hmk hon hto hseat hm hc hx hscript
    hbound hfitMk hfitC hfit2 hops hop0 hfops
  have hmkU : bU.sudo_5Board_9marker_on = false := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have honU : bU.sudo_5Board_8bench_on = true := by
    simp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves, hon]
  have htoU : bU.sudo_5Board_8bench_to = (seat : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves, hto]
  have hHU : seat < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp_home, feed, markerUpFeed, bM, mirrorHome, withMoves] using hHseat
  have hDU : seat < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp_held, feed, markerUpFeed, bM, mirrorHome, withMoves] using hDseat
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp_held, feed, markerUpFeed, bM, mirrorHome, withMoves] using h7
  have hemptyU : bU.sudo_5Board_4held[seat]'(hDU) = false := by
    have hemptyM : bM.sudo_5Board_4held[seat]'(by
        simpa [bM, mirrorHome, withMoves] using hDseat) = false := by
      simpa [bM, mirrorHome_held] using hempty
    simpa [bU, bumpOp_held, feed, markerUpFeed] using hemptyM
  have hbenchU : bU.sudo_5Board_5bench = embed lane := by
    simp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome_bench, hbench]
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome_tier, hn]
  have hmovesU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvM := by
    simp [bU, bumpOp_moves, feed, markerUpFeed, bM, mirrorHome, withMoves, mvM]
  have hslidesU : bU.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves, hslides]
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [bU, bumpOp_peak, feed, markerUpFeed, bM, mirrorHome, withMoves, hpeak]
  have hflag := run_else_flag bU dst first second seat lane n mvM slides peak false
    hmkU honU htoU hHU hDU h7U hemptyU hbenchU hnU hposL hnle hzero hf hfitL
    hmovesU hslidesU hpeakU hpeg hfitMs hfitSs
  let bS := markerOn (settleBoard bU seat hHU hDU lane n mvM slides peak)
  have hinS : HomeIn bU seat := ⟨hHU, hDU⟩
  let peakIn := raisedPeak peak (countHeld (bU.sudo_5Board_4held.set ⟨seat, hDU⟩ true) 7)
  have hcostS0 : bS.sudo_5Board_4cost =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakSboard : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peakIn : Int) := by
    rw [hcostS0, settle_peak_eq bU seat hinS lane n mvM slides peak hpeakU]
    simp [peakIn, raisedPeak, ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS0, settle_moves_eq bU seat hinS lane n mvM slides peak]
    dsimp [mvS, pegL]
  have hslidesS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = (slS : Int) := by
    rw [hcostS0, settle_slides_eq bU seat hinS lane n mvM slides peak]
    dsimp [slS, pegL]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU seat ⟨hHU, hDU⟩ lane n mvM slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves]
  have hhomeU : bU.sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨dst, hH⟩ (embed (mirrorTrits x)) := by
    dsimp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hbl]
  have hHD : dst < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hH
  have hDD : dst < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hD
  have hHeldD : bS.sudo_5Board_4held[dst]'(hDD) = true := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hheldS0.trans hset) dst hDD
    rw [Array.getElem_set_ne (h := hseat)] at hget
    have hszU : dst < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hD
    exact (hget.trans (idx_eq_local hheldU dst hszU)).trans hheld
  have hHomeD : bS.sudo_5Board_4home[dst]'(hHD) = embed (mirrorTrits x) := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hhomeS.trans hset) dst hHD
    rw [Array.getElem_set_ne (h := hseat)] at hget
    have hszU : dst < bU.sudo_5Board_4home.size := by rw [hhomeU, Array.size_set]; exact hH
    rw [hget, idx_eq_local hhomeU dst hszU]
    simp [Array.getElem_set]
  have hF' : first < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hF
  have hHomeF' : first < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hHomeF
  have hHF' : bS.sudo_5Board_4held[first]'(hF') = true := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hheldS0.trans hset) first hF'
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hszU : first < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hF
    exact (hget.trans (idx_eq_local hheldU first hszU)).trans hHF
  have hArr' : bS.sudo_5Board_4home[first]'(hHomeF') = embed x2 := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hhomeS.trans hset) first hHomeF'
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hszU : first < bU.sudo_5Board_4home.size := by
      rw [hhomeU, Array.size_set]; exact hHomeF
    rw [hget, idx_eq_local hhomeU first hszU, Array.getElem_set_ne (h := hneD1)]
    exact hArr
  have hS' : second < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hS
  have hHomeS' : second < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hHomeS
  have hlenz : z.length = n := by
    rw [← htake, List.length_take, Nat.min_eq_left hnle]
  have hHS' : bS.sudo_5Board_4held[second]'(hS') = true := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hheldS0.trans hset) second hS'
    simp only [Array.getElem_set, hseatEq, if_true] at hget
    exact hget
  have hYs' : bS.sudo_5Board_4home[second]'(hHomeS') = embed z := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hhomeS.trans hset) second hHomeS'
    simp only [Array.getElem_set, hseatEq, if_true] at hget
    rw [htake] at hget
    exact hget
  have hSpH' : 6 < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hSpH
  have hSpHome' : 6 < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hSpHome
  have hSpE' : bS.sudo_5Board_4held[6]'(hSpH') = false := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hheldS0.trans hset) 6 hSpH'
    rw [Array.getElem_set_ne (h := hneSeat6)] at hget
    have hszU : 6 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSpH
    exact (hget.trans (idx_eq_local hheldU 6 hszU)).trans hSpE
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost :=
    hcostS0
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves]
    exact hpeakS
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed, bM, mirrorHome, withMoves]
    exact hhole
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU seat hinS lane n mvM slides peak, hstrictU]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU seat hinS lane n mvM slides peak, hholeU]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hr]
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hn]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU, hk]
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact h7
  have hmU : bU.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hcU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hxU : bU.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hmS : bS.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    rw [show bS.sudo_5Board_6marker =
        (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_6marker from by
          dsimp [bS, markerOn],
      settle_ix_eq bU seat hinS lane n mvM slides peak, hmU]
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    rw [hcostS, settle_ctrl_eq bU seat hinS lane n mvM slides peak, hcU]
  have hxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    rw [hcostS, settle_mx_eq bU seat hinS lane n mvM slides peak, hxU]
  obtain ⟨b', hok, hbench', htakeF, hon', hto', hmk', htier', hsz', hempty',
      hszH, hhome, hheldK, hix, hctrl, hmx, hopsEq, hmv, hsl, hpk, hst, hho, hsp6⟩ :=
    run_else_field bS dst first second
      (mirrorTrits x) x2 z w h r n k mvS slS hole peakIn peakS bench
      hoffS hblS hDD hHD hHeldD hHomeD hF' hHomeF' hHF' hArr' hS' hHomeS' hHS' hYs'
      hSpH' hSpHome' hSpE' h7S hneD1 hneD2 hne6D hne6F hne6S hpos hnb hnS
      (mirror_len x n hlen) hlen2 hlenz hf hmovesS hslidesS hpeakSboard hstrictS
      hspan (mirror_trits_local x) hx2 hfi hfitM hfitS hfm hholeS hw0 hh0 hrR hrP hnE hkLe hgap
      hwS hhS hrS hkS hsm hnsm hfitB hfold
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    simp [bS, markerOn]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [htier', htierS, settle_tier_eq bU seat hinS lane n mvM slides peak, htierU]
  have hDD' : dst < b'.sudo_5Board_4held.size := by
    rw [hsz', hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set,
      hheldU]
    exact hD
  let laneR := laneFold n (n - k) (school n x2 z (pref (mirrorTrits x) bench n) false)
  have hschLen : (school n x2 z (pref (mirrorTrits x) bench n) false).length = bench := by
    have hnleM : n ≤ (mirrorTrits x).length := by
      rw [mirror_len x n hlen]
      exact Nat.le_refl n
    rw [school_length, pref_length hnb hnleM]
  have hlenR : laneR.length = bench := by
    rw [laneFold_length n (n - k) _ (by rw [hschLen]; exact hnb), hschLen]
  have htakeLen : (laneR.take n).length = n := by
    rw [List.length_take, hlenR, Nat.min_eq_left hnb]
  have hn' : b'.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierB, hn]
  have hzero := bench_is_zero b' dst laneR n hDD' (hempty' hDD') hon' hto' hbench' hn'
    (by rw [hlenR]; exact hnb) hf htakeLen
  have hzeroR : Ecbs.is_zero b' ((dst : Nat) : Int) =
      .ok (decide (fformRun n k bench x2 z x = List.replicate n 0)) := by
    rw [hzero, htakeF]
    unfold fformRun
    rfl
  have hszHeld : b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
    rw [hsz', hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
  have hszHomeB : b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    rw [hszH, hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set,
      hhomeU, Array.size_set]
  have h2Home : second < b'.sudo_5Board_4home.size := by
    rw [hszH]; exact hHomeS'
  have h2Held : second < b'.sudo_5Board_4held.size := by
    rw [hsz']; exact hS'
  have hbind :
      (Ecbs.mirror b ((dst : Nat) : Int) >>= fun b1 =>
          Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
            true true false) = .ok b' := by
    rw [hrise, hflag]
    exact hok
  obtain ⟨b1, hmir, hmul⟩ := bind_ok_split hbind
  refine ⟨b1, b', hmir, hmul, hbench', ?_, hon', hto', ?_, htierB, hempty', hzeroR,
      hix.trans hmS, hctrl.trans hcS, hmx.trans hxS, ?_, ?_, hszHeld, hszHomeB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htakeF]
    unfold fformRun
    rfl
  · rw [hmk', hmkS]
  · simpa [mvS, pegL] using hmv
  · simpa [slS, pegL] using hsl
  · intro j hneD hneSeat hne6 hj hj'
    have hjS : j < bS.sudo_5Board_4home.size := by
      rw [hszH] at hj'
      exact hj'
    have hEqS := hhome j hneD hne6 hjS hj'
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hhomeS.trans hset) j hjS
    rw [Array.getElem_set_ne (h := Ne.symm hneSeat)] at hget
    have hjU : j < bU.sudo_5Board_4home.size := by
      rw [hhomeU, Array.size_set]
      exact hj
    have hraw := idx_eq_local hhomeU j hjU
    have hBU : bU.sudo_5Board_4home[j]'hjU = b.sudo_5Board_4home[j]'hj := by
      rw [Array.getElem_set_ne (h := Ne.symm hneD)] at hraw
      exact hraw
    exact hEqS.trans (hget.trans hBU)
  · intro j hneD hneSeat hne6 hj hj'
    have hjS : j < bS.sudo_5Board_4held.size := by
      rw [hsz'] at hj'
      exact hj'
    have hEqS := hheldK j hneD hne6 hjS hj'
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq_local (hheldS0.trans hset) j hjS
    rw [Array.getElem_set_ne (h := Ne.symm hneSeat)] at hget
    have hjU : j < bU.sudo_5Board_4held.size := by
      rw [hheldU]
      exact hj
    exact hEqS.trans (hget.trans (idx_eq_local hheldU j hjU))
  · intro h2
    exact (hhome second (Ne.symm hneD2) hne6S hHomeS' h2).trans hYs'
  · intro h2
    exact (hheldK second (Ne.symm hneD2) hne6S hS' h2).trans hHS'
  · let schR := school n x2 z (pref (mirrorTrits x) bench n) false
    let hole' := if hole < topIdx schR then topIdx schR else hole
    have hgapPos : 0 < n - k := by
      have hwr : 0 < w * r := Nat.mul_pos hw0 hrP
      omega
    have hholeN : (if decide (Int.ofNat (topIdx schR) > Int.ofNat hole) then
          Int.ofNat (topIdx schR) else Int.ofNat hole) = Int.ofNat hole' := by
      by_cases hlt : hole < topIdx schR
      · have hgt : Int.ofNat (topIdx schR) > Int.ofNat hole := by
          rw [gt_iff_lt, ofNat_lt_iff]
          exact hlt
        simp [hole', hlt, hgt]
      · have hng : ¬ Int.ofNat (topIdx schR) > Int.ofNat hole := by
          rw [gt_iff_lt, ofNat_lt_iff]
          exact hlt
        simp [hole', hlt, hng]
    have hhole' : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole' := by
      rw [hho, hholeN]
    have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops = bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops =
          (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost.sudo_5Costs_3ops
          from by dsimp [bS, markerOn]]
      exact settle_ops bU seat hinS lane n mvM slides peak
    have hopSet := bumpOp_ops feed 0 cOps hopsF
    have hszU : 0 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopSet, Array.size_set]
      exact hopsF
    have hopU : bU.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hszU = Int.ofNat (cOps + 1) :=
      cell_eq_of hopSet
        (Array.getElem_set_eq feed.sudo_5Board_4cost.sudo_5Costs_3ops ⟨0, hopsF⟩
          (Int.ofNat (cOps + 1)) rfl (by rw [Array.size_set]; exact hopsF))
    have hszOp : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsEq, hopsS]
      exact hszU
    have hop' : b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hszOp = Int.ofNat (cOps + 1) :=
      cell_eq_of (hopsEq.trans hopsS) hopU
    have h6 : 6 < b'.sudo_5Board_4held.size := by
      rw [hsz', hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
      exact hSpH
    refine ⟨hole',
        sparePeak (bS.sudo_5Board_4held.set ⟨dst, hDD⟩ false)
          (by rw [Array.size_set]; exact hSpH') peakIn,
        spareStrict (bS.sudo_5Board_4held.set ⟨dst, hDD⟩ false)
          (by rw [Array.size_set]; exact hSpH') peakS,
        hszOp, hop', h6, hsp6 h6, hpk, hst, hhole', ?_, ?_, ?_, ?_⟩
    · rw [hlenR]
      exact Nat.lt_of_lt_of_le hpos hnb
    · rw [hlenR]
      exact hnb
    · rw [hlenR]
      exact hfitB
    · intro i hi hii
      have hiiS : i < schR.length := by
        rwa [hlenR, ← hschLen] at hii
      rw [← coeff_eq_get laneR i hii]
      exact laneFold_high n (n - k) schR i hpos hgapPos
        (by rw [hschLen]; exact hnb) hi hiiS
  · have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops =
          (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost.sudo_5Costs_3ops
          from by dsimp [bS, markerOn]]
      exact settle_ops bU seat hinS lane n mvM slides peak
    have hopSet := bumpOp_ops feed 0 cOps hopsF
    have hfeed : feed.sudo_5Board_4cost.sudo_5Costs_3ops =
        bM.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
    have hmirO : bM.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
    rw [hopsEq, hopsS, hopSet, Array.size_set, hfeed, hmirO]
  · intro j hne
    have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops =
          (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost.sudo_5Costs_3ops
          from by dsimp [bS, markerOn]]
      exact settle_ops bU seat hinS lane n mvM slides peak
    have hopSet := bumpOp_ops feed 0 cOps hopsF
    have hfeed : feed.sudo_5Board_4cost.sudo_5Costs_3ops =
        bM.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
    have hmirO : bM.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
    rw [hopsEq, hopsS, hopSet, Array.getElem?_set_ne _ _ _ hne.symm, hfeed, hmirO]

end EcbsLink2.Link2
