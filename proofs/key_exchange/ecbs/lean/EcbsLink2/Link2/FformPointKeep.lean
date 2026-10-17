/-
  The new across and the new up of `fform_add`. The bench is already aimed at
  the destination and that home is empty, so the multiply keeps the bench and
  copies the second factor into the spare. SPEC.md §3 R7 lines 153 and 154.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformPointLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A list whose tail from `n` is zero is the length-`n` prefix padded to `m`. -/
theorem zeroTail_pref (xs : List Nat) (n m : Nat)
    (hlen : xs.length = m) (hn : n ≤ xs.length)
    (hz : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0) :
    xs = pref (xs.take n) m n := by
  have hm : n ≤ m := by rw [← hlen]; exact hn
  have htake : n ≤ (xs.take n).length := by
    rw [List.length_take, Nat.min_eq_left hn]
    exact Nat.le_refl n
  have hplen : (pref (xs.take n) m n).length = m := pref_length hm htake
  apply List.ext_get
  · rw [hlen, hplen]
  · intro i hi hi'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [pref, List.getElem_append, List.length_take, Nat.min_eq_left hn,
      List.getElem_take, List.getElem_replicate] at hi' ⊢
    split
    · rfl
    · exact hz i (by omega) hi

def keepSchool (n bench : Nat) (xs ys home : List Nat) (mirror : Bool) : List Nat :=
  school n xs ys (pref home bench n) mirror

def keepCharge (n k moves bench : Nat) (xs ys home : List Nat) (mirror : Bool) : Nat :=
  moves + pegCount ys + schoolMoves xs ys n n +
    foldCharge n (n - k) (keepSchool n bench xs ys home mirror)

theorem placeHeldSize (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold placeBoard
  dsimp only
  split <;> simp [Array.size_set]

theorem placeHomeSize (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  unfold placeBoard
  dsimp only
  split <;> simp [Array.size_set]

/-- Onto, copying the second home, with the bench already the destination.
    The spare is cleared. Every other home stays. The bench prefix is the
    destination plus the product, mirrored when `mir` is true. -/
structure KeepCopy
    (b b' : Ecbs.Board) (lane' home xs ys : List Nat)
    (dst first second : Nat)
    (m ctrl mx cOps n k moves slides peak peakS hole bench : Nat) (mir : Bool) : Prop where
  mul_ok : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      true true mir = .ok b'
  bench_eq : b'.sudo_5Board_5bench = embed lane'
  lane_eq : lane' = laneFold n (n - k) (keepSchool n bench xs ys home mir)
  take_eq : lane'.take n =
      if mir then fieldAdd n home (mirrorTrits (fieldMul n k bench xs ys))
      else fieldAdd n home (fieldMul n k bench xs ys)
  mon : b'.sudo_5Board_9marker_on = true
  ix : b'.sudo_5Board_6marker = Int.ofNat (m + 1)
  ctrl : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2)
  mx : b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2))
  on : b'.sudo_5Board_8bench_on = true
  to_eq : b'.sudo_5Board_8bench_to = ((dst : Nat) : Int)
  tier : b'.sudo_5Board_1t = b.sudo_5Board_1t
  moves_eq : b'.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (keepCharge n k moves bench xs ys home mir)
  slides_eq : b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  peak_eq : b'.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)
  strict_eq : b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  hole_eq : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx (keepSchool n bench xs ys home mir)))
  ops0 : ∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h = Int.ofNat (cOps + 1)
  heldSz : b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size
  homeSz : b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size
  spareH : ∀ h : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6]'h = false
  spareA : ∀ h : 6 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[6]'h = (#[] : Array Int)
  stayH : ∀ j, j ≠ 6 → ∀ hj : j < b.sudo_5Board_4held.size,
      ∀ hj' : j < b'.sudo_5Board_4held.size,
      b'.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj
  stayA : ∀ j, j ≠ 6 → ∀ hj : j < b.sudo_5Board_4home.size,
      ∀ hj' : j < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[j]'hj' = b.sudo_5Board_4home[j]'hj

theorem keep_copy (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (mir : Bool)
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
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak7 : 7 ≤ peak) (hpeakS7 : 7 ≤ peakS)
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs) (hysT : allTritList ys)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitP : FitsLen (moves + pegCount ys))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
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
    (hfold : FitsLen (moves + pegCount ys + n * (n + 1) + 3 * (bench - n))) :
    ∃ b' lane',
      KeepCopy b b' lane' home xs ys dst first second
        m ctrl mx cOps n k moves slides peak peakS hole bench mir := by
  let pad := pref home bench n
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := markerOn (bumpOp feed 0 cOps hopsF)
  have hmul : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      true true mir =
      Ecbs.mulFromHeld ((n : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true mir bU (embed pad) := by
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
    simp only [bumpOp, markerUpFeed, hn, hon, hto, hbench, pad, if_true, pure_eq_ok, ok_bind]
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
  have h6U : 6 < bU.sudo_5Board_4held.size := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hSpH
  have h6HU : 6 < bU.sudo_5Board_4home.size := by
    simpa [bU, markerOn_home, bumpOp_home, feed, markerUpFeed] using hSpHome
  have h6E : bU.sudo_5Board_4held[6] = false := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using hSpE
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, markerOn_held, bumpOp_held, feed, markerUpFeed] using h7
  have hmovesU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [bU, markerOn, bumpOp_moves, feed, markerUpFeed, hmoves]
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bU, markerOn, bumpOp_peak, feed, markerUpFeed, hpeak]
  have hpeakSU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed, hpeakS]
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed, hn]
  have haim : bU = mulAimed bU ((dst : Nat) : Int) (embed pad) := by
    apply board_ext <;>
      simp [mulAimed, bU, markerOn, bumpOp, feed, markerUpFeed, hon, hto, hbench, pad]
  have hspanP : 2 * (n - 1) < pad.length := by rw [hpadLen]; exact hspan
  have hpadT : allTritList pad := pref_trits home bench n hhomeT hnb (by omega)
  have hcopy := held_copy_school bU dst first second xs ys pad n moves peak peakS mir
      hFU hHomeU hHFU hArrU hSU hHomeSU hHSU hYsU h6U h6HU h6E h7U
      hne6F hne6S hn0 hnU hlenx hleny hf hmovesU hpeakU hpeakSU hfitP
      hspanP hxsT hpadT hfi hfm
  let mv := moves + pegCount ys
  let bPlace := placeBoard bU 6 h6HU h6U ys moves peak
  let h6P : 6 < bPlace.sudo_5Board_4held.size := by
    rw [placeHeldSize]; exact h6U
  let h6HP : 6 < bPlace.sudo_5Board_4home.size := by
    rw [placeHomeSize]; exact h6HU
  let mvN := mv + schoolMoves xs ys n n
  let bFold := withMoves
      (mulPrep bPlace ((dst : Nat) : Int) (embed pad) 6 peakS h6P h6HP)
      (Int.ofNat mvN)
  let sch := school n xs ys pad mir
  have hma : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      true true mir = mulAfter (Int.ofNat 0, (bFold, embed sch)) := by
    rw [hmul]
    conv =>
      lhs
      rw [haim]
    simpa [bFold, bPlace, sch, pad, mv, mvN] using hcopy
  have hschLen : sch.length = bench := by
    simpa [sch, hpadLen] using school_length xs ys pad mir n
  have hschT : allTritList sch :=
    school_trits xs ys pad mir n hpadT
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
  have hnoP : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨6, h6U⟩ true) 7 := by
    have hle := countHeld_seven (bU.sudo_5Board_4held.set ⟨6, h6U⟩ true)
    omega
  have hpeakPl : bPlace.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [place_peak bU 6 ⟨h6HU, h6U⟩ ys moves peak hpeakU, if_neg hnoP, ofNat_eq_natCast]
  have hpeakB : bFold.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [show bFold.sudo_5Board_4cost.sudo_5Costs_4peak =
        bPlace.sudo_5Board_4cost.sudo_5Costs_4peak from by
          rw [peak_withMoves, mulPrep_peak], hpeakPl]
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed, hhole]
  have hholePl : bPlace.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bPlace]
    unfold placeBoard
    dsimp only
    split <;> simp [hholeU]
  have hholeB : bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [show bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bPlace.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole from by
          rw [hole_withMoves, mulPrep_hole], hholePl]
  have h7B : 7 ≤ bFold.sudo_5Board_4held.size := by
    rw [show bFold.sudo_5Board_4held.size = bPlace.sudo_5Board_4held.size from by
          rw [held_withMoves, mulPrep_held_size], placeHeldSize]
    exact h7U
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed]
  have htierPl : bPlace.sudo_5Board_1t = bU.sudo_5Board_1t := by
    dsimp [bPlace]
    unfold placeBoard
    dsimp only
    split <;> rfl
  have hwB : bFold.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hw]
  have hhB : bFold.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hh]
  have hrB : bFold.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hr]
  have hnB : bFold.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hn, ofNat_eq_natCast]
  have hkB : bFold.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hk]
  have hblB : bFold.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [show bFold.sudo_5Board_1t = bPlace.sudo_5Board_1t from by
          rw [tier_withMoves, mulPrep_tier], htierPl, htierU, hbl]
  have hfitF : FitsLen (mvN + 3 * (sch.length - n)) := by
    rw [hschLen]
    refine FitsLen.of_le hfold ?_
    have hsch : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
    simp only [mvN, mv]
    omega
  have hOk := mulAfter_ok bFold sch w h r n k mvN hole bench peak
      (by rw [hschLen]; exact hfitB) hwB hhB hrB hnB hkB hblB hw0 hh0 hrR hrP hnE hkLe hgap
      hschT hmB hholeB hpeakB h7B (by rw [hschLen]; exact hsm) hnsm hfitF
      (by rw [hschLen]; exact Nat.le_refl bench) (Nat.lt_of_lt_of_le hn0 hnb)
  let bOut := ontoFoldBoard bFold sch n k mvN peak
  let lane' := laneFold n (n - k) sch
  have hhomeEq : bOut.sudo_5Board_4home = bPlace.sudo_5Board_4home.set ⟨6, h6HP⟩ #[] := by
    rw [fold_home bFold sch n k mvN peak, home_withMoves, prep_home]
  have hheldEq : bOut.sudo_5Board_4held = bPlace.sudo_5Board_4held.set ⟨6, h6P⟩ false := by
    rw [fold_held bFold sch n k mvN peak, held_withMoves, prep_held]
  have hsetHome : bPlace.sudo_5Board_4home =
      bU.sudo_5Board_4home.set ⟨6, h6HU⟩ (embed ys) := by
    dsimp [bPlace]
    unfold placeBoard
    dsimp only
    split <;> rfl
  have hsetHeld : bPlace.sudo_5Board_4held = bU.sudo_5Board_4held.set ⟨6, h6U⟩ true := by
    dsimp [bPlace]
    unfold placeBoard
    dsimp only
    split <;> rfl
  have hhomeU0 : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    simp [bU, markerOn_home, bumpOp_home, feed, markerUpFeed]
  have hheldU0 : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    simp [bU, markerOn_held, bumpOp_held, feed, markerUpFeed]
  have hnoF : ¬ peak < countHeld bFold.sudo_5Board_4held 7 := by
    have hle := countHeld_seven bFold.sudo_5Board_4held
    omega
  have hschN : sch = keepSchool n bench xs ys home mir := by
    simp [sch, pad, keepSchool]
  have hIxU : bU.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed]
  have hctrlU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed]
  have hmxU : bU.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    simp [bU, markerOn, bumpOp, feed, markerUpFeed]
  exact ⟨bOut, lane', {
    mul_ok := by rw [hma, hOk]
    bench_eq := by simpa [lane', sch] using ontoFoldBoard_bench bFold sch n k mvN peak
    lane_eq := by simp [lane', hschN]
    take_eq := by
      cases mir with
      | false =>
          simpa [lane', sch, pad, keepSchool] using
            mul_onto_add n k bench xs ys home hhomeT hlenH hspan hnb
      | true =>
          simpa [lane', sch, pad, keepSchool] using
            onto_add_mirror n k bench xs ys home hhomeT hxsT hysT hlenH hspan hnb
    mon := by
      rw [fold_marker bFold sch n k mvN peak, marker_withMoves, mulPrep_marker]
      dsimp [bPlace]
      unfold placeBoard
      dsimp only
      split <;> simp [bU, markerOn_flag]
    ix := by
      rw [fold_ix bFold sch n k mvN peak, ix_withMoves, prep_ix]
      dsimp [bPlace]
      unfold placeBoard
      dsimp only
      split <;> simp [hIxU]
    ctrl := by
      rw [fold_ctrl bFold sch n k mvN peak, ctrl_withMoves, prep_ctrl]
      dsimp [bPlace]
      unfold placeBoard
      dsimp only
      split <;> simp [hctrlU]
    mx := by
      rw [fold_mx bFold sch n k mvN peak, mx_withMoves, prep_mx]
      dsimp [bPlace]
      unfold placeBoard
      dsimp only
      split <;> simp [hmxU]
    on := by rw [fold_on bFold sch n k mvN peak, on_withMoves, prep_on]
    to_eq := by rw [fold_to bFold sch n k mvN peak, to_withMoves, prep_to]
    tier := by
      rw [fold_tier bFold sch n k mvN peak, tier_withMoves, mulPrep_tier, htierPl, htierU]
    moves_eq := by
      rw [fold_moves bFold sch n k mvN peak]
      simp [keepCharge, mvN, mv, hschN]
    slides_eq := by
      rw [fold_slides bFold sch n k mvN peak, slides_withMoves, prep_slides]
      dsimp [bPlace]
      unfold placeBoard
      dsimp only
      split <;> simp [bU, markerOn, bumpOp, feed, markerUpFeed, hslides]
    peak_eq := fold_peak bFold sch n k mvN peak hnoF
    strict_eq := by
      rw [fold_strict bFold sch n k mvN peak, strict_withMoves]
      dsimp [bFold, bPlace]
      unfold mulPrep strictBoard mulAimed raisedPeak
      have hle : countHeld bPlace.sudo_5Board_4held 7 ≤ 7 := countHeld_seven _
      have hnoS : ¬ peakS < countHeld bPlace.sudo_5Board_4held 7 := by omega
      dsimp
      simp [hnoS, ofNat_eq_natCast]
    hole_eq := by
      rw [fold_hole bFold sch n k mvN peak, hholeB, hschN]
      by_cases hlt : hole < topIdx (keepSchool n bench xs ys home mir)
      · have hdec : decide (Int.ofNat (topIdx (keepSchool n bench xs ys home mir)) >
            Int.ofNat hole) = true := by
          rw [decide_eq_true_eq]
          exact (ofNat_lt_iff hole _).mpr hlt
        rw [hdec, if_pos rfl, raisedHole, if_pos hlt]
      · have hdec : decide (Int.ofNat (topIdx (keepSchool n bench xs ys home mir)) >
            Int.ofNat hole) = false := by
          rw [decide_eq_false_iff_not]
          intro hgt
          exact hlt ((ofNat_lt_iff hole _).mp hgt)
        rw [hdec, if_neg (by decide), raisedHole, if_neg hlt]
    ops0 := by
      intro h
      have hopsEq : bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [fold_ops, ops_withMoves, prep_ops]
        dsimp [bPlace]
        unfold placeBoard
        dsimp only
        split <;> rfl
      have hget := idx_eq hopsEq 0 h
      rw [hget]
      simp [bU, markerOn, bumpOp, Array.getElem_set]
    heldSz := by
      rw [hheldEq, Array.size_set, placeHeldSize, hheldU0]
    homeSz := by
      rw [hhomeEq, Array.size_set, placeHomeSize, hhomeU0]
    spareH := by
      intro h
      have hget := idx_eq hheldEq 6 h
      rw [hget]
      simp [Array.getElem_set]
    spareA := by
      intro h
      have hget := idx_eq hhomeEq 6 h
      rw [hget]
      simp [Array.getElem_set]
    stayH := by
      intro j hneJ hj hj'
      have hget := idx_eq hheldEq j hj'
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hget
      have hSz : j < bPlace.sudo_5Board_4held.size := by
        rw [placeHeldSize, hheldU0]; exact hj
      have hread := idx_eq hsetHeld j hSz
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hread
      have hBU : j < bU.sudo_5Board_4held.size := by rw [hheldU0]; exact hj
      rw [hget, hread, idx_eq hheldU0 j hBU]
    stayA := by
      intro j hneJ hj hj'
      have hget := idx_eq hhomeEq j hj'
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hget
      have hSz : j < bPlace.sudo_5Board_4home.size := by
        rw [placeHomeSize, hhomeU0]; exact hj
      have hread := idx_eq hsetHome j hSz
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hread
      have hBU : j < bU.sudo_5Board_4home.size := by rw [hhomeU0]; exact hj
      rw [hget, hread, idx_eq hhomeU0 j hBU]
  }⟩

/-- `v·F + x₂·Z₃`, with the card's product `F·v` commuted. -/
theorem across_sum (n k bench : Nat) (x2 u v z f z3 : List Nat)
    (hfT : allTritList f) (hv : allTritList v)
    (hf : f = fformF n k bench u v z)
    (hz3 : z3 = fformBottom n k bench v z) :
    fieldAdd n (fieldMul n k bench f v) (fieldMul n k bench x2 z3) =
      fformAcross n k bench x2 u v z := by
  have hFt : allTritList (fformF n k bench u v z) := hf ▸ hfT
  rw [hf, hz3, fieldMul_comm n k bench (fformF n k bench u v z) v hFt hv]
  unfold fformAcross
  rfl

/-- White new up: both products mirrored, which is `−(u·F + y₂·Z₃)`. -/
theorem up_white (n k bench : Nat) (y2 u v z f z3 : List Nat)
    (hfT : allTritList f) (hu : allTritList u)
    (hfu : allTritList (fieldMul n k bench f u))
    (hyz : allTritList (fieldMul n k bench y2 z3))
    (hf : f = fformF n k bench u v z)
    (hz3 : z3 = fformBottom n k bench v z) :
    fieldAdd n (mirrorTrits (fieldMul n k bench f u))
        (mirrorTrits (fieldMul n k bench y2 z3)) =
      fformUp n k bench y2 u v z := by
  rw [← mirrorTrits_fieldAdd n (fieldMul n k bench f u) (fieldMul n k bench y2 z3) hfu hyz,
    fieldMul_comm n k bench f u hfT hu, hf, hz3]
  unfold fformUp
  rfl

end EcbsLink2.Link2
