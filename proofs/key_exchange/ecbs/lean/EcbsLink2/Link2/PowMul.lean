/-
  A nonzero root digit multiplies with the marker on and the cube still on
  the bench. `mul` settles that bench into the up home, then runs the
  marker-on schoolbook. The result is `powLiveBoard`: the lane fold with the
  marker flag put back, named as the record update.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowAt

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- What `marker_step` writes when the marker is already seated at `m`. -/
def markerSeat (b : Ecbs.Board) (m ctrl mx : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_6marker := Int.ofNat (m + 1)
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2)
      sudo_5Costs_17script_marker_max := Int.ofNat (max mx (m + 2)) } }

/-- Settling commutes with seating the marker. The two updates write different fields. -/
theorem settle_marker_comm (c : Ecbs.Board) (m ctrl mx home : Nat)
    (hin : HomeIn c home) (xs : List Nat) (n moves slides peak : Nat) :
    settleBoard (markerSeat c m ctrl mx) home hin.hH hin.hD xs n moves slides peak =
      markerSeat (settleBoard c home hin.hH hin.hD xs n moves slides peak) m ctrl mx := by
  by_cases hpk : peak < countHeld (c.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · rw [settle_peak (markerSeat c m ctrl mx) home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk,
      settle_peak c home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    apply board_ext
    case pos.hcost =>
      apply cost_ext <;> simp [markerSeat]
    all_goals simp [markerSeat]
  · rw [settle_keep (markerSeat c m ctrl mx) home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk,
      settle_keep c home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    apply board_ext
    case neg.hcost =>
      apply cost_ext <;> simp [markerSeat]
    all_goals simp [markerSeat]

private theorem get_eq_of_array_local {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

theorem settle_size_held (b : Ecbs.Board) (home i : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (hi : i < b.sudo_5Board_4held.size) :
    i < (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4held.size := by
  rw [settle_held_eq b home hin xs n moves slides peak, Array.size_set]
  exact hi

theorem settle_size_home (b : Ecbs.Board) (home i : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (hi : i < b.sudo_5Board_4home.size) :
    i < (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4home.size := by
  rw [settle_home_eq b home hin xs n moves slides peak, Array.size_set]
  exact hi

theorem ready_spare_held (b : Ecbs.Board) (up spare : Nat)
    (hH : up < b.sudo_5Board_4home.size) (hD : up < b.sudo_5Board_4held.size)
    (hS : spare < b.sudo_5Board_4held.size)
    (lane : List Nat) (n moves slides peak cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (m ctrl mx : Nat) :
    spare < (markerSeat (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
        (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)) m ctrl mx).sudo_5Board_4held.size := by
  simp only [markerSeat, bumpOp]
  exact settle_size_held b up spare ⟨hH, hD⟩ lane n moves slides peak hS

theorem ready_spare_home (b : Ecbs.Board) (up spare : Nat)
    (hH : up < b.sudo_5Board_4home.size) (hD : up < b.sudo_5Board_4held.size)
    (hHome : spare < b.sudo_5Board_4home.size)
    (lane : List Nat) (n moves slides peak cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (m ctrl mx : Nat) :
    spare < (markerSeat (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
        (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)) m ctrl mx).sudo_5Board_4home.size := by
  simp only [markerSeat, bumpOp]
  exact settle_size_home b up spare ⟨hH, hD⟩ lane n moves slides peak hHome

/-- Clearing the marker flag before `mulPrep` only changes that flag. -/
theorem mulPrep_flag (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size) (hHome : second < b.sudo_5Board_4home.size)
    (hS' : second < ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4held.size)
    (hHome' : second < ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4home.size)
    (hflag : b.sudo_5Board_9marker_on = true) :
    mulPrep b dst strip second peakS hS hHome =
      markerOn (mulPrep { b with sudo_5Board_9marker_on := false } dst strip second peakS
        hS' hHome') := by
  unfold mulPrep strictBoard mulAimed markerOn
  apply board_ext
  case hmon => exact hflag
  case hheld =>
    have hfin : (⟨second, hS⟩ : Fin _) = ⟨second, hS'⟩ := Fin.ext rfl
    simp [hfin]
  case hhome =>
    have hfin : (⟨second, hHome⟩ : Fin _) = ⟨second, hHome'⟩ := Fin.ext rfl
    simp [hfin]
  all_goals rfl

/-- The board the schoolbook folds. Marker off; `powLiveBoard` puts the flag back. -/
def powMulOff (bReady : Ecbs.Board) (spare peakS : Nat)
    (hS : spare < bReady.sudo_5Board_4held.size)
    (hHomeS : spare < bReady.sudo_5Board_4home.size)
    (dst mvW bench : Nat) : Ecbs.Board :=
  withMoves
    (mulPrep { bReady with sudo_5Board_9marker_on := false }
      ((dst : Nat) : Int) (embed (List.replicate bench 0)) spare peakS hS hHomeS)
    (Int.ofNat mvW)

attribute [local irreducible] settleBoard

private theorem replicate_trits_local (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

private theorem of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : i < a.size) (hs : a[i]? = some v) : a[i] = v := by
  rw [Array.getElem?_eq_getElem h] at hs
  injection hs

private theorem nat_beq_false (a b : Nat) (h : a ≠ b) :
    SudoRt.SEq.beq (a : Int) (b : Int) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b] at hEq
    exact hEq))

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

/-- `mul up up spare false false false` on a marker-on cube bench is the flagged fold. -/
theorem pow_mul_live (b : Ecbs.Board) (up spare : Nat) (lane cube factor : List Nat)
    (w h r n k moves slides peak peakS cOps m ctrl mx script bench hole : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (up : Int))
    (hH : up < b.sudo_5Board_4home.size)
    (hD : up < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[up] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hS : spare < b.sudo_5Board_4held.size)
    (hHomeS : spare < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[spare] = true)
    (hYs : b.sudo_5Board_4home[spare] = embed factor)
    (hne : up ≠ spare)
    (hn0 : 0 < n)
    (htake : lane.take n = cube)
    (hfac : factor.length = n)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hcubeT : allTritList cube)
    (hfi : FitsLen (2 * (n - 1)))
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
    (hfold : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1) + 3 * (bench - n))) :
    Ecbs.mul b ((up : Nat) : Int) ((up : Nat) : Int) ((spare : Nat) : Int)
        false false false =
      .ok (powLiveBoard
        (powMulOff
          (markerSeat (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
              (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)) m ctrl mx)
          spare peakS
          (ready_spare_held b up spare hH hD hS lane n moves slides peak cOps hops m ctrl mx)
          (ready_spare_home b up spare hH hD hHomeS lane n moves slides peak cOps hops m ctrl mx)
          up
          (moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n)
          bench)
        (school n cube factor (List.replicate bench 0) false)
        n k
        (moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n)
        (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hD⟩ true) 7))) := by
  unfold Ecbs.mul
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 0 cOps hops)
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by
    simpa [bumpOp] using hm
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hscript
  rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitMk hfitC hfit2]
  simp only [ok_bind]
  let bM := markerSeat (bumpOp b 0 cOps hops) m ctrl mx
  conv =>
    lhs
    pattern (Ecbs.settle _)
    change Ecbs.settle bM
  have hHc : up < (bumpOp b 0 cOps hops).sudo_5Board_4home.size :=
    bump_home_lt b 0 cOps up hops hH
  have hDc : up < (bumpOp b 0 cOps hops).sudo_5Board_4held.size :=
    bump_held_lt b 0 cOps up hops hD
  have hsetM := settle_refines bM up lane n moves slides peak hHc hDc h7
      (by simp [bM, markerSeat, bumpOp, hon])
      (by simp [bM, markerSeat, bumpOp, hto])
      (by simpa [bM, markerSeat, bumpOp] using hempty)
      (by simp [bM, markerSeat, bumpOp, hbench])
      (by simp [bM, markerSeat, bumpOp, hn])
      hpos hnle hzero hf hfitL
      (by simp [bM, markerSeat, bumpOp, hmoves])
      (by simp [bM, markerSeat, bumpOp, hslides])
      (by simp [bM, markerSeat, bumpOp, hpeak])
      hpeg hfitMv hfitSl
  rw [hsetM, ok_bind]
  rw [settle_marker_comm (bumpOp b 0 cOps hops) m ctrl mx up ⟨hHc, hDc⟩
      lane n moves slides peak]
  rw [settle_bump_comm b 0 cOps hops up ⟨hH, hD⟩ lane n moves slides peak]
  let bS := settleBoard b up hH hD lane n moves slides peak
  let hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak
  let bReady := markerSeat (bumpOp bS 0 cOps hopsS) m ctrl mx
  have hReady :
      markerSeat (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
        (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)) m ctrl mx = bReady := by
    rfl
  conv =>
    lhs
    rw [hReady]
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    have hget := get_eq_of_array_local (settle_ops b up ⟨hH, hD⟩ lane n moves slides peak) 0 hopsS
    exact hget.trans hop0
  let hFu : up < bS.sudo_5Board_4held.size :=
    settle_held_lt b up ⟨hH, hD⟩ lane n moves slides peak
  let hHu : up < bS.sudo_5Board_4home.size :=
    settle_home_lt b up ⟨hH, hD⟩ lane n moves slides peak
  have hHFq : bS.sudo_5Board_4held[up]? = some true := by
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  have hHF : bS.sudo_5Board_4held[up] = true := of_some _ _ _ hFu hHFq
  have hArrq : bS.sudo_5Board_4home[up]? = some (embed cube) := by
    rw [settle_home_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set, htake]
  have hArr : bS.sudo_5Board_4home[up] = embed cube := of_some _ _ _ hHu hArrq
  let hSs : spare < bS.sudo_5Board_4held.size :=
    settle_size_held b up spare ⟨hH, hD⟩ lane n moves slides peak hS
  let hHsp : spare < bS.sudo_5Board_4home.size :=
    settle_size_home b up spare ⟨hH, hD⟩ lane n moves slides peak hHomeS
  have hHSq : bS.sudo_5Board_4held[spare]? = some true := by
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_set_ne _ ⟨up, hD⟩ true hne]
    rw [Array.getElem?_eq_getElem hS, hHS]
  have hHS2 : bS.sudo_5Board_4held[spare] = true := of_some _ _ _ hSs hHSq
  have hYsq : bS.sudo_5Board_4home[spare]? = some (embed factor) := by
    rw [settle_home_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_set_ne _ ⟨up, hH⟩ (embed (lane.take n)) hne]
    rw [Array.getElem?_eq_getElem hHomeS, hYs]
  have hYs2 : bS.sudo_5Board_4home[spare] = embed factor := of_some _ _ _ hHsp hYsq
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    rw [settle_marker_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hmk
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b up ⟨hH, hD⟩ lane n moves slides peak
  have hmS : bS.sudo_5Board_6marker = Int.ofNat m := by
    rw [settle_ix_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hm
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    rw [settle_ctrl_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hc
  have hxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [settle_mx_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hx
  have hsS : bS.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    have ht := settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_1t = b.sudo_5Board_1t from ht]
    exact hscript
  let mvSet := moves + 2 * pegCount (lane.take n)
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvSet : Int) := by
    rw [settle_moves_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    simp [mvSet, ofNat_eq_natCast]
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak, Array.size_set]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hn
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    have ht := settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak
    rw [show bS.sudo_5Board_1t = b.sudo_5Board_1t from ht]
    exact hbl
  have hpeakSS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq b up ⟨hH, hD⟩ lane n moves slides peak]; exact hpeakS
  have hlenx : cube.length = n := by
    rw [← htake, List.length_take, Nat.min_eq_left hnle]
  have hfm : FitsLen (mvSet + n * (n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hblR : bReady.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp only [bReady, markerSeat, bumpOp]
    exact hblS
  have hheldR : bReady.sudo_5Board_4held = bS.sudo_5Board_4held := by
    simp [bReady, markerSeat, bumpOp]
  have hhomeR : bReady.sudo_5Board_4home = bS.sudo_5Board_4home := by
    simp [bReady, markerSeat, bumpOp]
  conv =>
    lhs
    rw [hblR, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  conv =>
    lhs
    rw [hheldR, hhomeR]
  conv =>
    lhs
    rw [← ofNat_eq_natCast up, atL_ofNat _ up hFu, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ up hHu, hArr, ok_bind]
  have hbf : SudoRt.SEq.beq (↑spare) (Int.ofNat up) = false := by
    rw [ofNat_eq_natCast up]
    exact nat_beq_false spare up hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let strip0 := embed (List.replicate bench 0)
  let bA := mulAimed bReady ((up : Nat) : Int) strip0
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by
    simpa [bA, mulAimed, hheldR] using h7S
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [bA, mulAimed, bReady, markerSeat, bumpOp, hpeakSS]
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bSt := strictBoard bA peakS
  have hheldSt : bSt.sudo_5Board_4held = bReady.sudo_5Board_4held := by
    simp [bSt, strictBoard, bA, mulAimed]
  have hhomeSt : bSt.sudo_5Board_4home = bReady.sudo_5Board_4home := by
    simp [bSt, strictBoard, bA, mulAimed]
  have hSsR : spare < bSt.sudo_5Board_4held.size := by
    rw [hheldSt, hheldR]; exact hSs
  have hHsR : spare < bSt.sudo_5Board_4home.size := by
    rw [hhomeSt, hhomeR]; exact hHsp
  have hHeldSp : bSt.sudo_5Board_4held[spare] = true := by
    simpa [bSt, strictBoard, bA, mulAimed, bReady, markerSeat, bumpOp] using hHS2
  have hHomeSp : bSt.sudo_5Board_4home[spare] = embed factor := by
    simpa [bSt, strictBoard, bA, mulAimed, bReady, markerSeat, bumpOp] using hYs2
  conv =>
    lhs
    rw [← ofNat_eq_natCast spare, atL_ofNat _ spare hSsR, hHeldSp]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ spare hHsR, hHomeSp, ok_bind]
  rw [putL_ofNat _ spare false hSsR, ok_bind]
  rw [putL_ofNat _ spare (#[] : Array Int) hHsR, ok_bind]
  have hnB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bumpOp, hn, ofNat_eq_natCast]
  rw [hnB]
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change rowStep (embed cube) (embed factor) false (Int.ofNat n) (0 : Int)
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bL := mulPrep bReady ((up : Nat) : Int) strip0 spare peakS hSsR hHsR
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, strip0))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvSet := by
    rw [show bL.sudo_5Board_4cost.sudo_5Costs_5moves =
        bReady.sudo_5Board_4cost.sudo_5Costs_5moves from by simp [bL, mulPrep_moves]]
    simp [bReady, markerSeat, bumpOp, hmovesS, mvSet, ofNat_eq_natCast]
  simp only [strip0]
  rw [school_loop_refines cube factor (List.replicate bench 0) mvSet n false bL
      mulAfter (fun r => Except.ok r) hn0
      (by rw [hlenx]; exact Nat.le_refl _)
      (by rw [hfac]; exact Nat.le_refl _)
      (by simp [size_embed, List.length_replicate]; exact hspan)
      hcubeT (replicate_trits_local _) hmL hf hfi hfm]
  rw [bind_ok_id]
  let sch := school n cube factor (List.replicate bench 0) false
  let mvW := mvSet + schoolMoves cube factor n n
  let strip := embed (List.replicate bench 0)
  let hSready : spare < bReady.sudo_5Board_4held.size :=
    ready_spare_held b up spare hH hD hS lane n moves slides peak cOps hops m ctrl mx
  let hHready : spare < bReady.sudo_5Board_4home.size :=
    ready_spare_home b up spare hH hD hHomeS lane n moves slides peak cOps hops m ctrl mx
  let bOff := powMulOff bReady spare peakS hSready hHready up mvW bench
  have hflagR : bReady.sudo_5Board_9marker_on = true := by
    simp only [bReady, markerSeat, bumpOp]
    rw [settle_marker_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hmk
  have hprep : mulPrep bReady ((up : Nat) : Int) strip0 spare peakS hSsR hHsR =
      markerOn (mulPrep { bReady with sudo_5Board_9marker_on := false }
        ((up : Nat) : Int) strip0 spare peakS hSready hHready) :=
    mulPrep_flag bReady ((up : Nat) : Int) strip0 spare peakS hSsR hHsR hSready hHready hflagR
  have hmove : withMoves (mulPrep bReady ((up : Nat) : Int) strip0 spare peakS hSsR hHsR)
      (Int.ofNat mvW) = markerOn bOff := by
    rw [hprep]
    simp only [bOff, powMulOff, withMoves_markerOn]
  rw [hmove]
  have hflagW : bOff.sudo_5Board_9marker_on = false := by
    simp [bOff, powMulOff, marker_withMoves, mulPrep_marker]
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length cube factor (List.replicate bench 0) false n
  have hfit : FitsLen sch.length := by rw [hlenS]; exact hfitB
  have hnW : bOff.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [hnS, ofNat_eq_natCast]
  have hwW : bOff.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hw
  have hhW : bOff.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hh
  have hrW : bOff.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hr
  have hkW : bOff.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hk
  have hblW : bOff.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp only [bOff, powMulOff, tier_withMoves, mulPrep_tier, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hbl
  have hmW : bOff.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvW := by
    simp [bOff, powMulOff, mvW]
  have hholeW : bOff.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp only [bOff, powMulOff, hole_withMoves, mulPrep_hole, bReady, markerSeat, bumpOp]
    rw [settle_hole_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hhole
  let pkSeat := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hD⟩ true) 7)
  have hpeakW : bOff.sudo_5Board_4cost.sudo_5Costs_4peak = (pkSeat : Int) := by
    simp only [bOff, powMulOff, peak_withMoves, mulPrep_peak, bReady, markerSeat, bumpOp]
    rw [settle_peak_eq b up ⟨hH, hD⟩ lane n moves slides peak hpeak]
    simp [pkSeat, raisedPeak, ofNat_eq_natCast]
  have h7W : 7 ≤ bOff.sudo_5Board_4held.size := by
    simp only [bOff, powMulOff, held_withMoves, mulPrep_held_size]
    simpa [bReady, markerSeat, bumpOp] using h7S
  have htri : allTritList sch := by
    simpa [sch] using school_trits cube factor (List.replicate bench 0) false n
      (replicate_trits_local _) (fun i hi => by
        rw [List.length_replicate]
        have : i + (n - 1) ≤ 2 * (n - 1) := by omega
        exact Nat.lt_of_le_of_lt this hspan)
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hposB : 0 < bench := by omega
  have hfitF : FitsLen (mvW + 3 * (sch.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hfold (by
      have := schoolMoves_bound cube factor n
      omega)
  rw [mulAfter_flag bOff sch w h r n k mvW hole bench pkSeat hflagW hfit hwW hhW hrW hnW hkW
      hblW hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hposB]
  have hAfter : mulAfter (Int.ofNat 0, (bOff, embed sch)) =
      .ok (ontoFoldBoard bOff sch n k mvW pkSeat) :=
    mulAfter_ok bOff sch w h r n k mvW hole bench pkSeat hfit hwW hhW hrW hnW hkW hblW
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmW hholeW hpeakW h7W hsmS hnsm hfitF hlen hposB
  rw [hAfter]
  exact powLive_bind bOff sch n k mvW pkSeat

end EcbsLink2.Link2
