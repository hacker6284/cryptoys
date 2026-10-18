/-
  The rise of `fform_add`: mirror the up, then lay base up times the bottom
  onto it. White keeps the mirror flag off. Red turns it on, which negates
  the base up. The bench prefix is SPEC.md §3 R7 line 150. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.FformFold
import EcbsLink2.Link2.BenchCarry

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem mirror_trits (y : List Nat) : allTritList (mirrorTrits y) := by
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

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- The lane fold of the rise schoolbook is `fformRise`. White uses `y₂`.
    Red uses `−y₂`, which is the mirrored schoolbook. -/
theorem rise_lane_spec (mirror : Bool) (n k bench : Nat) (y2 z y : List Nat)
    (hy2 : allTritList y2) (hz : allTritList z) (hlen : y.length = n)
    (hspan : 2 * (n - 1) < bench) (hnb : n ≤ bench) :
    (laneFold n (n - k)
        (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n =
      fformRise n k bench (if mirror then mirrorTrits y2 else y2) z y := by
  have hmir := mirror_trits y
  have hlenM := mirror_len y n hlen
  cases mirror with
  | false =>
    rw [onto_add n k bench y2 z (mirrorTrits y) hmir hlenM (Or.inl hspan) hnb]
    unfold fformRise
    rfl
  | true =>
    rw [onto_add_mirror n k bench y2 z (mirrorTrits y) hmir hy2 hz hlenM hspan hnb]
    rw [← fieldMul_mirror_left n k bench y2 z hy2 hz]
    unfold fformRise
    rfl

/-- Mirror the up, then the onto multiply. The bench that was aimed at `seat`
    settles first. The new bench prefix is SPEC.md §3 R7 line 150. -/
theorem rise_on_board (b : Ecbs.Board) (dst first second seat : Nat)
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
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + pegCount y) + 2 * pegCount (lane.take n) + 3 * n +
        n * (n + 1) + 3 * (bench - n))) :
    ∃ b',
      (Ecbs.mirror b ((dst : Nat) : Int) >>= fun b1 =>
          Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
            true true mirror) = .ok b' ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k)
          (school n y2 z (pref (mirrorTrits y) bench n) mirror)) ∧
      (laneFold n (n - k)
          (school n y2 z (pref (mirrorTrits y) bench n) mirror)).take n =
        fformRise n k bench (if mirror then mirrorTrits y2 else y2) z y ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = ((dst : Nat) : Int) ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      (∀ hD' : dst < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[dst]'hD' = false) ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat ((moves + pegCount y + 2 * pegCount (lane.take n)) +
          2 * pegCount (mirrorTrits y) + pegCount z + schoolMoves y2 z n n +
          foldCharge n (n - k)
            (school n y2 z (pref (mirrorTrits y) bench n) mirror)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n) + 2 * pegCount (mirrorTrits y)) ∧
      ∃ hole',
        BenchCarry b'
          (laneFold n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) mirror))
          n (cOps + 1) peak hole' peakS := by
  let bM := mirrorHome b dst hH (embed (mirrorTrits y)) (moves + pegCount y)
  let feed := markerUpFeed bM m ctrl mx
  let hopsM : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [bM, mirrorHome, withMoves] using hops
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hopsM
  let bU := bumpOp feed 0 cOps hopsF
  let mvM := moves + pegCount y
  let pegL := pegCount (lane.take n)
  let mvS := mvM + 2 * pegL
  let slS := slides + 2 * pegL
  have hrise := rise_marker b dst dst first second seat y m ctrl mx script cOps n moves mirror
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
  have hflag := run_else_flag bU dst first second seat lane n mvM slides peak mirror
    hmkU honU htoU hHU hDU h7U hemptyU hbenchU hnU hposL hnle hzero hf hfitL
    hmovesU hslidesU hpeakU hpeg hfitMs hfitSs
  let bS := markerOn (settleBoard bU seat hHU hDU lane n mvM slides peak)
  have hinS : HomeIn bU seat := ⟨hHU, hDU⟩
  have hcount : countHeld (bU.sudo_5Board_4held.set ⟨seat, hDU⟩ true) 7 ≤ 7 :=
    countHeld_seven _
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨seat, hDU⟩ true) 7 := by
    omega
  have hcostS0 : bS.sudo_5Board_4cost =
      (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakSboard : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [hcostS0, settle_peak_eq bU seat hinS lane n mvM slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
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
      b.sudo_5Board_4home.set ⟨dst, hH⟩ (embed (mirrorTrits y)) := by
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
    have hget := idx_eq (hheldS0.trans hset) dst hDD
    rw [Array.getElem_set_ne (h := hseat)] at hget
    have hszU : dst < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hD
    exact (hget.trans (idx_eq hheldU dst hszU)).trans hheld
  have hHomeD : bS.sudo_5Board_4home[dst]'(hHD) = embed (mirrorTrits y) := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq (hhomeS.trans hset) dst hHD
    rw [Array.getElem_set_ne (h := hseat)] at hget
    have hszU : dst < bU.sudo_5Board_4home.size := by rw [hhomeU, Array.size_set]; exact hH
    rw [hget, idx_eq hhomeU dst hszU]
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
    have hget := idx_eq (hheldS0.trans hset) first hF'
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hszU : first < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hF
    exact (hget.trans (idx_eq hheldU first hszU)).trans hHF
  have hArr' : bS.sudo_5Board_4home[first]'(hHomeF') = embed y2 := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq (hhomeS.trans hset) first hHomeF'
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hszU : first < bU.sudo_5Board_4home.size := by
      rw [hhomeU, Array.size_set]; exact hHomeF
    rw [hget, idx_eq hhomeU first hszU, Array.getElem_set_ne (h := hneD1)]
    exact hArr
  have hS' : second < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hS
  have hHomeS' : second < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hHomeS
  have hHS' : bS.sudo_5Board_4held[second]'(hS') = true := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq (hheldS0.trans hset) second hS'
    rw [Array.getElem_set_ne (h := hneSeatS)] at hget
    have hszU : second < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hS
    exact (hget.trans (idx_eq hheldU second hszU)).trans hHS
  have hYs' : bS.sudo_5Board_4home[second]'(hHomeS') = embed z := by
    have hset := settle_home_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq (hhomeS.trans hset) second hHomeS'
    rw [Array.getElem_set_ne (h := hneSeatS)] at hget
    have hszU : second < bU.sudo_5Board_4home.size := by
      rw [hhomeU, Array.size_set]; exact hHomeS
    rw [hget, idx_eq hhomeU second hszU, Array.getElem_set_ne (h := hneD2)]
    exact hYs
  have hSpH' : 6 < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
    exact hSpH
  have hSpHome' : 6 < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n mvM slides peak, Array.size_set, hhomeU,
      Array.size_set]
    exact hSpHome
  have hSpE' : bS.sudo_5Board_4held[6]'(hSpH') = false := by
    have hset := settle_held_eq bU seat hinS lane n mvM slides peak
    have hget := idx_eq (hheldS0.trans hset) 6 hSpH'
    rw [Array.getElem_set_ne (h := hneSeat6)] at hget
    have hszU : 6 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSpH
    exact (hget.trans (idx_eq hheldU 6 hszU)).trans hSpE
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
  obtain ⟨b', hok, hbench, hon, hto, hmk', htier', _hszD, hempty, _, _, _,
      hix, hctrl, hmx, hopsEq, hmv, hsl, hpk, hst, hho, hsp⟩ :=
    run_else_lane bS dst first second (mirrorTrits y) y2 z
      w h r n k mvS slS hole peak peakS bench mirror hoffS hblS hDD hHD hHeldD hHomeD
      hF' hHomeF' hHF' hArr' hS' hHomeS' hHS' hYs' hSpH' hSpHome' hSpE' h7S
      hneD1 hneD2 hne6D hne6F hne6S hpos hnb hnS (mirror_len y n hlen) hlen2 hlenz hf
      hmovesS hslidesS hpeakSboard hpeak7 hstrictS hpeakS7 hspan (mirror_trits y) hy2 hfi
      hfitM hfitS hfm hholeS hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS hsm hnsm hfitB hfold
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
    rw [hcostS0, settle_ctrl_eq bU seat hinS lane n mvM slides peak, hcU]
  have hxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    rw [hcostS0, settle_mx_eq bU seat hinS lane n mvM slides peak, hxU]
  have hmvS : mvS + 2 * pegCount (mirrorTrits y) + pegCount z + schoolMoves y2 z n n +
      foldCharge n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) mirror) =
      (moves + pegCount y + 2 * pegCount (lane.take n)) +
        2 * pegCount (mirrorTrits y) + pegCount z + schoolMoves y2 z n n +
        foldCharge n (n - k) (school n y2 z (pref (mirrorTrits y) bench n) mirror) := by
    simp [mvS, pegL]
  have hslS : slS + 2 * pegCount (mirrorTrits y) =
      slides + 2 * pegCount (lane.take n) + 2 * pegCount (mirrorTrits y) := by
    simp [slS, pegL]
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    simp [bS, markerOn]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [htier',
      show bS.sudo_5Board_1t =
        (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_1t from by
          dsimp [bS, markerOn],
      settle_tier_eq bU seat hinS lane n mvM slides peak, htierU]
  refine ⟨b', ?_, hbench, rise_lane_spec mirror n k bench y2 z y hy2 hz hlen hspan hnb,
      hon, hto, hmk'.trans hmkS, htierB, hempty, hix.trans hmS, hctrl.trans hcS,
      hmx.trans hxS, ?_, ?_, ?_⟩
  · rw [hrise, hflag]
    exact hok
  · rw [hmv, hmvS]
  · rw [hsl, hslS]
  · let schR := school n y2 z (pref (mirrorTrits y) bench n) mirror
    let laneR := laneFold n (n - k) schR
    let hole' := if hole < topIdx schR then topIdx schR else hole
    have hschLen : schR.length = bench := by
      have hnleM : n ≤ (mirrorTrits y).length := by
        rw [mirror_len y n hlen]
        exact Nat.le_refl n
      simp [schR, school_length, pref_length hnb hnleM]
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
    have hsz' : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsEq, hopsS]
      exact hszU
    have hop' : b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hsz' = Int.ofNat (cOps + 1) :=
      cell_eq_of (hopsEq.trans hopsS) hopU
    have hlenR : laneR.length = bench := by
      rw [laneFold_length n (n - k) schR (by rw [hschLen]; exact hnb), hschLen]
    have h6 : 6 < b'.sudo_5Board_4held.size := by
      rw [_hszD]
      rw [show bS.sudo_5Board_4held.size =
          (settleBoard bU seat hHU hDU lane n mvM slides peak).sudo_5Board_4held.size from by
            dsimp [bS, markerOn]]
      rw [settle_held_eq bU seat hinS lane n mvM slides peak, Array.size_set, hheldU]
      exact hSpH
    refine ⟨hole', hsz', hop', h6, hsp h6, hpeak7, hpk, hst, hhole', ?_, ?_, ?_, ?_⟩
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

end EcbsLink2.Link2
