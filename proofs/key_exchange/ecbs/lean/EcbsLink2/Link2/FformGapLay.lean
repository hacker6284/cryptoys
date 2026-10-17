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

end EcbsLink2.Link2
