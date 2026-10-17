/-
  The first gap line of `fform_add`: square the rise. The bench still holds
  the rise and is aimed at the up, so the multiply settles that up, copies it
  into the spare, and the bench prefix is `u²`. SPEC.md §3 R7 line 151.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformFold

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- Square the rise. `Ecbs.mul` of the gap by the up, copying the up, mirror
    off. The bench was aimed at the up, so that rise is settled first. The new
    bench prefix is `fieldMul u u`. -/
theorem gap_u2 (b : Ecbs.Board) (dst up : Nat) (u lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hH : up < b.sudo_5Board_4home.size)
    (hD : up < b.sudo_5Board_4held.size)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (up : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[up] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMs : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitSs : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hne6 : up ≠ 6)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (htake : lane.take n = u) (hlen : u.length = n)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitP : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount u))
    (hspan : 2 * (n - 1) < bench)
    (hu : allTritList u)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount u + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount u +
        n * (n + 1) + 3 * (bench - n))) :
    ∃ b' lane',
      Ecbs.mul b ((dst : Nat) : Int) ((up : Nat) : Int) ((up : Nat) : Int)
          true false false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fieldMul n k bench u u := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : up < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hH
  let hDU : up < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hD
  have hflag := off_marker_else b dst up up up lane m ctrl mx script cOps n moves slides peak
    true false hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops
    hH hD h7 hempty hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitMs hfitSs
  let pegL := pegCount (lane.take n)
  let mvS := moves + 2 * pegL
  let bS := markerOn (settleBoard bU up hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU up := ⟨hHU, hDU⟩
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨up, hDU⟩ true) 7 := by
    have hle : countHeld (bU.sudo_5Board_4held.set ⟨up, hDU⟩ true) 7 ≤ 7 :=
      countHeld_seven _
    omega
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU up hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakSboard : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      simp [bU, bumpOp, feed, markerUpFeed, hpeak]
    rw [hcostS, settle_peak_eq bU up hinS lane n moves slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS, settle_moves_eq bU up hinS lane n moves slides peak]
    dsimp [mvS, pegL]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU up ⟨hHU, hDU⟩ lane n moves slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU up hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU up hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU up hHU hDU lane n moves slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hbl]
  have hUpD : up < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU up hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hD
  have hUpH : up < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU up hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hH
  have hHeldUp : bS.sudo_5Board_4held[up]'(hUpD) = true := by
    have hset := settle_held_eq bU up hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) up hUpD
    rw [hget]
    simp [Array.getElem_set]
  have hHomeUp : bS.sudo_5Board_4home[up]'(hUpH) = embed u := by
    have hset := settle_home_eq bU up hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) up hUpH
    rw [hget]
    simp [Array.getElem_set]
    rw [htake]
  have h6D : 6 < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU up hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hSpH
  have h6H : 6 < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU up hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hSpHome
  have h6E : bS.sudo_5Board_4held[6]'(h6D) = false := by
    have hset := settle_held_eq bU up hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) 6 h6D
    rw [Array.getElem_set_ne (h := hne6)] at hget
    have h6U : 6 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSpH
    exact (hget.trans (idx_eq hheldU 6 h6U)).trans hSpE
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU up hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hn]
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hpeakS
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hhole
  have hcostEq : bS.sudo_5Board_4cost =
      (settleBoard bU up hHU hDU lane n moves slides peak).sudo_5Board_4cost := hcostS
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostEq, settle_strict_eq bU up hinS lane n moves slides peak, hstrictU]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostEq, settle_hole_eq bU up hinS lane n moves slides peak, hholeU]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hr]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU up hinS lane n moves slides peak, htierU, hk]
  obtain ⟨b', hok, hbench, hmul, _hmk, _hon, _hto, _htier, _hsl, _hpk⟩ :=
    copy_else_field bS dst up up u u w h r n k mvS hole peak peakS bench
      hoffS hblS hUpD hUpH hHeldUp hHomeUp hUpD hUpH hHeldUp hHomeUp
      h6D h6H h6E h7S hne6 hne6 hn0 hnb hnS hlen hlen hf hmovesS hpeakSboard hpeak7
      hstrictS hfitP hspan hu hfi hfm hholeS hw0 hh0 hrR hrP hnE hkLe hgap
      hwS hhS hrS hkS hsm hnsm hfitB hfold
  refine ⟨b', laneFold n (n - k) (school n u u (List.replicate bench 0) false), ?_, hbench, hmul⟩
  rw [hflag]
  exact hok

/-- The bottom times the squared rise. The bench holds `u²` and is aimed at the
    gap, so that square is settled, then `fieldMul` of the bottom by it is the
    new bench prefix. -/
theorem gap_u2z (b : Ecbs.Board) (gap bot : Nat) (u2 z lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hG : gap < b.sudo_5Board_4home.size)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hBH : bot < b.sudo_5Board_4home.size)
    (hBD : bot < b.sudo_5Board_4held.size)
    (hHeldB : b.sudo_5Board_4held[bot] = true)
    (hArrB : b.sudo_5Board_4home[bot] = embed z)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (gap : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[gap] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hne : bot ≠ gap)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (htake : lane.take n = u2) (hlenu : u2.length = n) (hlenz : z.length = n)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hz : allTritList z)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
        3 * (bench - n))) :
    ∃ b' lane',
      Ecbs.mul b ((gap : Nat) : Int) ((bot : Nat) : Int) ((gap : Nat) : Int)
          false false false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fieldMul n k bench z u2 := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : gap < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hG
  let hDU : gap < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hGD
  have hflag := off_marker_else b gap bot gap gap lane m ctrl mx script cOps n moves slides peak
    false false hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops
    hG hGD h7 hempty hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let mvS := moves + 2 * pegCount (lane.take n)
  let bS := markerOn (settleBoard bU gap hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU gap := ⟨hHU, hDU⟩
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨gap, hDU⟩ true) 7 := by
    have hle : countHeld (bU.sudo_5Board_4held.set ⟨gap, hDU⟩ true) 7 ≤ 7 :=
      countHeld_seven _
    omega
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakB : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      simp [bU, bumpOp, feed, markerUpFeed, hpeak]
    rw [hcostS, settle_peak_eq bU gap hinS lane n moves slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS, settle_moves_eq bU gap hinS lane n moves slides peak]
    dsimp [mvS]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU gap ⟨hHU, hDU⟩ lane n moves slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hbl]
  have hGapD : gap < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hGD
  have hGapH : gap < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU gap hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hG
  have hHeldG : bS.sudo_5Board_4held[gap]'(hGapD) = true := by
    have hset := settle_held_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) gap hGapD
    rw [hget]
    simp [Array.getElem_set]
  have hHomeG : bS.sudo_5Board_4home[gap]'(hGapH) = embed u2 := by
    have hset := settle_home_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) gap hGapH
    rw [hget]
    simp [Array.getElem_set]
    rw [htake]
  have hBotD : bot < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hBD
  have hBotH : bot < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU gap hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hBH
  have hHeldBot : bS.sudo_5Board_4held[bot]'(hBotD) = true := by
    have hset := settle_held_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) bot hBotD
    rw [Array.getElem_set_ne (h := Ne.symm hne)] at hget
    have hBU : bot < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hBD
    exact (hget.trans (idx_eq hheldU bot hBU)).trans hHeldB
  have hHomeBot : bS.sudo_5Board_4home[bot]'(hBotH) = embed z := by
    have hset := settle_home_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) bot hBotH
    rw [Array.getElem_set_ne (h := Ne.symm hne)] at hget
    have hBU : bot < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hBH
    exact (hget.trans (idx_eq hhomeU bot hBU)).trans hArrB
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hn]
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hpeakS
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hhole
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU gap hinS lane n moves slides peak, hstrictU]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU gap hinS lane n moves slides peak, hholeU]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hr]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hk]
  obtain ⟨b', hok, hbench, hmul⟩ := nocopy_else_field bS gap bot gap z u2
      w h r n k mvS hole peak peakS bench hoffS hblS hBotD hBotH hHeldBot hHomeBot
      hGapD hGapH hHeldG hHomeG h7S hne hn0 hnb hnS hlenz hlenu hf hmovesS
      hpeakB hstrictS hspan hz hfi hfm hholeS hw0 hh0 hrR hrP hnE hkLe hgap
      hwS hhS hrS hkS hsm hnsm hfitB hfold
  refine ⟨b', laneFold n (n - k) (school n z u2 (List.replicate bench 0) false), ?_, hbench, hmul⟩
  rw [hflag]
  exact hok

/-- Square the run into the spare. The bench holds the previous gap value and
    is aimed at the gap, so that value is settled, then the across is copied
    and squared. The bench prefix is `fieldMul v v`. -/
theorem gap_v2 (b : Ecbs.Board) (dst gap across : Nat) (v lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hG : gap < b.sudo_5Board_4home.size)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hAH : across < b.sudo_5Board_4home.size)
    (hAD : across < b.sudo_5Board_4held.size)
    (hHeldA : b.sudo_5Board_4held[across] = true)
    (hArrA : b.sudo_5Board_4home[across] = embed v)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (gap : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[gap] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hne : gap ≠ across) (hne6 : across ≠ 6) (hneG6 : gap ≠ 6)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlen : v.length = n)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitP : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v +
        n * (n + 1) + 3 * (bench - n))) :
    ∃ b' lane',
      Ecbs.mul b ((dst : Nat) : Int) ((across : Nat) : Int) ((across : Nat) : Int)
          true false false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fieldMul n k bench v v := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : gap < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hG
  let hDU : gap < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hGD
  have hflag := off_marker_else b dst across across gap lane m ctrl mx script cOps n moves slides
    peak true false hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops
    hG hGD h7 hempty hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let mvS := moves + 2 * pegCount (lane.take n)
  let bS := markerOn (settleBoard bU gap hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU gap := ⟨hHU, hDU⟩
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨gap, hDU⟩ true) 7 := by
    have hle : countHeld (bU.sudo_5Board_4held.set ⟨gap, hDU⟩ true) 7 ≤ 7 :=
      countHeld_seven _
    omega
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakB : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      simp [bU, bumpOp, feed, markerUpFeed, hpeak]
    rw [hcostS, settle_peak_eq bU gap hinS lane n moves slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS, settle_moves_eq bU gap hinS lane n moves slides peak]
    dsimp [mvS]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU gap ⟨hHU, hDU⟩ lane n moves slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU gap hHU hDU lane n moves slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hbl]
  have hAccD : across < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hAD
  have hAccH : across < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU gap hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hAH
  have hHeldA' : bS.sudo_5Board_4held[across]'(hAccD) = true := by
    have hset := settle_held_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) across hAccD
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hAU : across < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hAD
    exact (hget.trans (idx_eq hheldU across hAU)).trans hHeldA
  have hHomeA : bS.sudo_5Board_4home[across]'(hAccH) = embed v := by
    have hset := settle_home_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) across hAccH
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hAU : across < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hAH
    rw [hget]
    exact (idx_eq hhomeU across hAU).trans hArrA
  have h6D : 6 < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hSpH
  have h6H : 6 < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU gap hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hSpHome
  have h6E : bS.sudo_5Board_4held[6]'(h6D) = false := by
    have hset := settle_held_eq bU gap hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) 6 h6D
    rw [Array.getElem_set_ne (h := hneG6)] at hget
    have h6U : 6 < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSpH
    exact (hget.trans (idx_eq hheldU 6 h6U)).trans hSpE
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU gap hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hn]
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hpeakS
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hhole
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU gap hinS lane n moves slides peak, hstrictU]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU gap hinS lane n moves slides peak, hholeU]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hr]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU gap hinS lane n moves slides peak, htierU, hk]
  obtain ⟨b', hok, hbench, hmul, _, _, _, _, _, _⟩ := copy_else_field bS dst across across v v
      w h r n k mvS hole peak peakS bench hoffS hblS hAccD hAccH hHeldA' hHomeA
      hAccD hAccH hHeldA' hHomeA h6D h6H h6E h7S hne6 hne6 hn0 hnb hnS hlen hlen hf
      hmovesS hpeakB hpeak7 hstrictS hfitP hspan hv hfi hfm hholeS hw0 hh0 hrR hrP
      hnE hkLe hgap hwS hhS hrS hkS hsm hnsm hfitB hfold
  refine ⟨b', laneFold n (n - k) (school n v v (List.replicate bench 0) false), ?_, hbench, hmul⟩
  rw [hflag]
  exact hok

/-- The squared run times the bottom. The bench holds `v²` and is aimed at the
    spare, so that square is settled, then `fieldMul` of it by the bottom is
    the new bench prefix. -/
theorem gap_v2z (b : Ecbs.Board) (sp bot : Nat) (v2 z lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hS : sp < b.sudo_5Board_4home.size)
    (hSD : sp < b.sudo_5Board_4held.size)
    (hBH : bot < b.sudo_5Board_4home.size)
    (hBD : bot < b.sudo_5Board_4held.size)
    (hHeldB : b.sudo_5Board_4held[bot] = true)
    (hArrB : b.sudo_5Board_4home[bot] = embed z)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (sp : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[sp] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hne : sp ≠ bot)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (htake : lane.take n = v2) (hlenv : v2.length = n) (hlenz : z.length = n)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hv2 : allTritList v2)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
        3 * (bench - n))) :
    ∃ b' lane',
      Ecbs.mul b ((bot : Nat) : Int) ((sp : Nat) : Int) ((bot : Nat) : Int)
          false false false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fieldMul n k bench v2 z := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : sp < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hS
  let hDU : sp < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hSD
  have hflag := off_marker_else b bot sp bot sp lane m ctrl mx script cOps n moves slides peak
    false false hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops
    hS hSD h7 hempty hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let mvS := moves + 2 * pegCount (lane.take n)
  let bS := markerOn (settleBoard bU sp hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU sp := ⟨hHU, hDU⟩
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨sp, hDU⟩ true) 7 := by
    have hle : countHeld (bU.sudo_5Board_4held.set ⟨sp, hDU⟩ true) 7 ≤ 7 :=
      countHeld_seven _
    omega
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU sp hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakB : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      simp [bU, bumpOp, feed, markerUpFeed, hpeak]
    rw [hcostS, settle_peak_eq bU sp hinS lane n moves slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS, settle_moves_eq bU sp hinS lane n moves slides peak]
    dsimp [mvS]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU sp ⟨hHU, hDU⟩ lane n moves slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU sp hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU sp hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU sp hHU hDU lane n moves slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hbl]
  have hSpD : sp < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU sp hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hSD
  have hSpH : sp < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU sp hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hS
  have hHeldS : bS.sudo_5Board_4held[sp]'(hSpD) = true := by
    have hset := settle_held_eq bU sp hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) sp hSpD
    rw [hget]
    simp [Array.getElem_set]
  have hHomeS : bS.sudo_5Board_4home[sp]'(hSpH) = embed v2 := by
    have hset := settle_home_eq bU sp hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) sp hSpH
    rw [hget]
    simp [Array.getElem_set]
    rw [htake]
  have hBotD : bot < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU sp hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hBD
  have hBotH : bot < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU sp hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hBH
  have hHeldBot : bS.sudo_5Board_4held[bot]'(hBotD) = true := by
    have hset := settle_held_eq bU sp hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) bot hBotD
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hBU : bot < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hBD
    exact (hget.trans (idx_eq hheldU bot hBU)).trans hHeldB
  have hHomeBot : bS.sudo_5Board_4home[bot]'(hBotH) = embed z := by
    have hset := settle_home_eq bU sp hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) bot hBotH
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hBU : bot < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hBH
    exact (hget.trans (idx_eq hhomeU bot hBU)).trans hArrB
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU sp hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hn]
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hpeakS
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hhole
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU sp hinS lane n moves slides peak, hstrictU]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU sp hinS lane n moves slides peak, hholeU]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hr]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU sp hinS lane n moves slides peak, htierU, hk]
  obtain ⟨b', hok, hbench, hmul⟩ := nocopy_else_field bS bot sp bot v2 z
      w h r n k mvS hole peak peakS bench hoffS hblS hSpD hSpH hHeldS hHomeS
      hBotD hBotH hHeldBot hHomeBot h7S hne hn0 hnb hnS hlenv hlenz hf hmovesS
      hpeakB hstrictS hspan hv2 hfi hfm hholeS hw0 hh0 hrR hrP hnE hkLe hgap
      hwS hhS hrS hkS hsm hnsm hfitB hfold
  refine ⟨b', laneFold n (n - k) (school n v2 z (List.replicate bench 0) false), ?_, hbench, hmul⟩
  rw [hflag]
  exact hok

/-- Onto, with the bench already aimed at the destination and that home empty.
    The keep test takes the bench as the strip. Schooling the two factors onto
    it and folding is `fieldAdd` of the bench prefix and `fieldMul` of the
    factors. For the gap that prefix is `u²Z` and the product is `v³`. -/
theorem gap_keep (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat)
    (m ctrl mx script cOps n k w h r moves hole peak peakS bench : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = ((dst : Nat) : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hD : dst < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hbench : b.sudo_5Board_5bench = embed (pref home bench n))
    (hF : first < b.sudo_5Board_4held.size)
    (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs)
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    ∃ b',
      Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
          false true false = .ok b' ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n xs ys (pref home bench n) false)) ∧
      (laneFold n (n - k) (school n xs ys (pref home bench n) false)).take n =
        fieldAdd n home (fieldMul n k bench xs ys) := by
  let pad := pref home bench n
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := markerOn (bumpOp feed 0 cOps hopsF)
  have hmul : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      false true false =
      Ecbs.mulFromHeld ((n : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false bU (embed pad) := by
    rw [mul_keep_eq]
    unfold Ecbs.mulKeep
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl]
    conv =>
      lhs
      rw [atL_ofNat _ 0 hops, hop0, ok_bind,
        ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
        putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
      dsimp only
    have hbump :
        ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_3ops :=
              b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
          Ecbs.Board) = bumpOp b 0 cOps hops := by
      simp [bumpOp]
    rw [hbump]
    rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
    have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by
      simp [bumpOp, hm]
    have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
      simp [bumpOp, hc]
    have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat mx := by simp [bumpOp, hx]
    have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
      simp [bumpOp, hscript]
    rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
        hbound hfitMk hfitC hfit2]
    rw [← mul_up_bump b m ctrl mx cOps hops hmk]
    simp only [ok_bind]
    have hU : { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true } = bU := by
      simp [bU, markerOn, feed]
    rw [hU]
    have hnL : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
      simp [bU, markerOn, bumpOp, feed, markerUpFeed, hn]
    have honL : bU.sudo_5Board_8bench_on = true := by
      simp [bU, markerOn, bumpOp, feed, markerUpFeed, hon]
    have htoL : bU.sudo_5Board_8bench_to = ((dst : Nat) : Int) := by
      simp [bU, markerOn, bumpOp, feed, markerUpFeed, hto]
    have hbenchL : bU.sudo_5Board_5bench = embed pad := by
      simp [bU, markerOn, bumpOp, feed, markerUpFeed, hbench, pad]
    have hDL : dst < bU.sudo_5Board_4held.size := by
      simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hD
    have hemptyL : bU.sudo_5Board_4held[dst] = false := by
      simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hempty
    simp only [bumpOp, markerUpFeed, hn, hon, hto, hbench, pad, if_true, pure_eq_ok,
      ok_bind]
    rw [← ofNat_eq_natCast dst, atL_ofNat _ dst hD, hempty]
    simp only [ok_bind, Bool.not_false, pure_eq_ok]
    have hbeq : SudoRt.SEq.beq (Int.ofNat dst) (Int.ofNat dst) = true := by
      rw [sEq_int]
      exact decide_eq_true rfl
    rw [hbeq]
    simp
  have hpadLen : pad.length = bench := pref_length hnb (by omega)
  have hFU : first < bU.sudo_5Board_4held.size := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hF
  have hHomeU : first < bU.sudo_5Board_4home.size := by
    simpa [bU, markerOn_home, bumpOp_home, feed, markerUpFeed] using hHome
  have hHFU : bU.sudo_5Board_4held[first] = true := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hHF
  have hArrU : bU.sudo_5Board_4home[first] = embed xs := by
    simpa [bU, markerOn_home, bumpOp_home, feed, markerUpFeed] using hArr
  have hSU : second < bU.sudo_5Board_4held.size := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hS
  have hHomeSU : second < bU.sudo_5Board_4home.size := by
    simpa [bU, markerOn_home, bumpOp_home, feed, markerUpFeed] using hHomeS
  have hHSU : bU.sudo_5Board_4held[second] = true := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hHS
  have hYsU : bU.sudo_5Board_4home[second] = embed ys := by
    simpa [bU, markerOn_home, bumpOp_home, feed, markerUpFeed] using hYs
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using h7
  have hmovesU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [bU, markerOn, bumpOp_moves, feed, markerUpFeed, hmoves]
  have hpeakSU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed, hpeakS]
  have haim : bU = mulAimed bU ((dst : Nat) : Int) (embed pad) := by
    apply board_ext <;>
      simp [mulAimed, bU, markerOn, bumpOp, feed, markerUpFeed, hon, hto, hbench, pad]
  have hschool := mul_onto_school bU dst first second xs ys pad n moves peakS false
    hFU hHomeU hHFU hArrU hSU hHomeSU hHSU hYsU h7U hne hn0 hlenx hleny hf
    hmovesU hpeakSU (by rw [hpadLen]; exact hspan) hxsT
    (pref_trits home bench n hhomeT hnb (by omega)) hfi hfm
  have hma : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      false true false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bU ((dst : Nat) : Int) (embed pad) second peakS hSU hHomeSU)
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
    rw [hmul]
    conv =>
      lhs
      rw [haim]
    exact hschool
  let sch := school n xs ys pad false
  let mvN := moves + schoolMoves xs ys n n
  let bFold := withMoves
      (mulPrep bU ((dst : Nat) : Int) (embed pad) second peakS hSU hHomeSU)
      (Int.ofNat mvN)
  have hschLen : sch.length = bench := by
    simpa [sch, hpadLen] using school_length xs ys pad false n
  have hschT : allTritList sch :=
    school_trits xs ys pad false n (pref_trits home bench n hhomeT hnb (by omega))
      (by
        intro i hi
        rw [hpadLen]
        have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
        have hle : i + (n - 1) ≤ 2 * (n - 1) := by
          rw [Nat.two_mul]
          exact Nat.add_le_add_right hi' (n - 1)
        exact Nat.lt_of_le_of_lt hle hspan)
  have hmB : bFold.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvN := by
    simp [bFold, withMoves]
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bU, markerOn, bumpOp_peak, feed, markerUpFeed, hpeak]
  have hpeakB : bFold.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hpeakU]
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed, hhole]
  have hholeB : bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hholeU]
  have h7B : 7 ≤ bFold.sudo_5Board_4held.size := by
    simp [bFold, withMoves, mulPrep, mulAimed, strictBoard, Array.size_set]
    exact h7U
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed]
  have hwB : bFold.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hw]
  have hhB : bFold.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hh]
  have hrB : bFold.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hr]
  have hnB : bFold.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hn, ofNat_eq_natCast]
  have hkB : bFold.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hk]
  have hblB : bFold.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, htierU, hbl]
  have hfitF : FitsLen (mvN + 3 * (sch.length - n)) := by
    rw [hschLen]
    refine FitsLen.of_le hfold ?_
    have hsch : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
    simp only [mvN]
    omega
  have hOk := mulAfter_ok bFold sch w h r n k mvN hole bench peak
      (by rw [hschLen]; exact hfitB) hwB hhB hrB hnB hkB hblB hw0 hh0 hrR hrP hnE hkLe hgap
      hschT hmB hholeB hpeakB h7B (by rw [hschLen]; exact hsm) hnsm hfitF
      (by rw [hschLen]; exact Nat.le_refl bench) (Nat.lt_of_lt_of_le hn0 hnb)
  refine ⟨ontoFoldBoard bFold sch n k mvN peak, ?_, ?_, ?_⟩
  · rw [hma]
    simpa [bFold, sch, pad, mvN] using hOk
  · simpa [sch, pad] using ontoFoldBoard_bench bFold sch n k mvN peak
  · simpa [sch, pad] using mul_onto_add n k bench xs ys home hhomeT hlenH hspan hnb

end EcbsLink2.Link2
