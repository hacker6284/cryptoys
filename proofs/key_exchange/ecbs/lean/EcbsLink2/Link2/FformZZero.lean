/-
  A zero cell whose input is `zBench`. The bench holds `Z` and is aimed at
  home 2. After the lift, settling that bench is the homes cube.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformYZero

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift bottomFlag

private theorem get_of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) (hlt : i < a.size) : a[i]'hlt = v := by
  have heq := Array.getElem?_eq_getElem hlt
  rw [h] at heq
  exact Option.some.inj heq.symm

private theorem peg_le (ys : List Nat) (n : Nat) (hn : n ≤ ys.length) :
    pegCount (ys.take n) ≤ n := by
  refine Nat.le_trans (pegCount_le _) ?_
  rw [List.length_take]
  exact Nat.min_le_left _ _

private theorem z_room (moves slides peg n cube d slide : Nat)
    (hpeg : peg ≤ n)
    (hm : FitsLen (moves + 2 * n + cube + 2 * n + 3 * d))
    (hs : FitsLen (slides + 2 * n + slide)) :
    FitsLen (2 * peg) ∧
      FitsLen (moves + 2 * peg) ∧
      FitsLen (slides + 2 * peg) ∧
      FitsLen (moves + 2 * peg + cube + 2 * n + 3 * d) ∧
      FitsLen (slides + 2 * peg + slide) := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  refine ⟨FitsLen.of_le hm ?_, FitsLen.of_le hm ?_, FitsLen.of_le hs ?_,
      FitsLen.of_le hm ?_, FitsLen.of_le hs ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega

/-- The settled `zBench`. Home 2 receives `Z`. Homes 0 and 1 stay. -/
structure ZSeen
    (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY xP yP zP ys : List Nat)
    (moves slides pk peakS hole cOps ctrl mx : Nat) : Type where
  h2H : 2 < b.sudo_5Board_4home.size
  h2D : 2 < b.sudo_5Board_4held.size
  movesS : Nat
  slidesS : Nat
  hmovesS : movesS = moves + 2 * pegCount (ys.take t.n)
  hslidesS : slidesS = slides + 2 * pegCount (ys.take t.n)
  peakT : Nat
  hRoomS : FitsLen (movesS + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n))
  hSlS : FitsLen (slidesS + slideCharge t.n)
  frS : FrameAt (settleBoard b 2 h2H h2D ys t.n moves slides pk) t baseX baseY
  seen : AcrossSeen (settleBoard b 2 h2H h2D ys t.n moves slides pk)
      xP yP zP t.n t.k t.w t.h t.r t.benchlen t.combgap
      peakT peakS movesS slidesS hole cOps ctrl mx t.script t baseX baseY

noncomputable def zbench_seen
    (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY xP yP zP ys : List Nat)
    (fr : FrameAt b t baseX baseY)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hm : b.sudo_5Board_6marker < 0)
    (moves slides ctrl mx pk peakS hole cOps cMul : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopMul : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMul = Int.ofNat cMul)
    (htake : ys.take t.n = zP)
    (hCtrl : FitsLen (ctrl + 5)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n)) :
    ZSeen t b baseX baseY xP yP zP ys moves slides pk peakS hole cOps ctrl mx := by
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [fr.szH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [fr.szD]; decide
  have frS := settle_frame t b baseX baseY ys fr 2 h2H h2D t.n moves slides pk
    (by decide) (by decide)
  let bS := settleBoard b 2 h2H h2D ys t.n moves slides pk
  let movesS := moves + 2 * pegCount (ys.take t.n)
  let slidesS := slides + 2 * pegCount (ys.take t.n)
  let peakT :=
    if pk < countHeld (b.sudo_5Board_4held.set ⟨2, h2D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨2, h2D⟩ true) 7 else pk
  have h0S : bS.sudo_5Board_4home[0]'(by rw [frS.szH]; decide) = embed xP := by
    have h? : bS.sudo_5Board_4home[0]? = some (embed xP) := by
      rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 0)]
      rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
      exact congrArg some h0
    exact get_of_some _ 0 _ h? (by rw [frS.szH]; decide)
  have h1S : bS.sudo_5Board_4home[1]'(by rw [frS.szH]; decide) = embed yP := by
    have h? : bS.sudo_5Board_4home[1]? = some (embed yP) := by
      rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 1)]
      rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
      exact congrArg some h1
    exact get_of_some _ 1 _ h? (by rw [frS.szH]; decide)
  have h2S : bS.sudo_5Board_4home[2]'(by rw [frS.szH]; decide) = embed zP := by
    have h? : bS.sudo_5Board_4home[2]? = some (embed (ys.take t.n)) := by
      rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_eq]
    rw [htake] at h?
    exact get_of_some _ 2 _ h? (by rw [frS.szH]; decide)
  have hd0S : bS.sudo_5Board_4held[0]'(by rw [frS.szD]; decide) = true := by
    have h? : bS.sudo_5Board_4held[0]? = some true := by
      rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 0)]
      rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
      exact congrArg some hd0
    exact get_of_some _ 0 _ h? (by rw [frS.szD]; decide)
  have hd1S : bS.sudo_5Board_4held[1]'(by rw [frS.szD]; decide) = true := by
    have h? : bS.sudo_5Board_4held[1]? = some true := by
      rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 1)]
      rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
      exact congrArg some hd1
    exact get_of_some _ 1 _ h? (by rw [frS.szD]; decide)
  have hd2S : bS.sudo_5Board_4held[2]'(by rw [frS.szD]; decide) = true := by
    have h? : bS.sudo_5Board_4held[2]? = some true := by
      rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_set_eq]
    exact get_of_some _ 2 _ h? (by rw [frS.szD]; decide)
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesS := by
    simpa [movesS] using settle_moves_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesS := by
    simpa [slidesS] using settle_slides_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakT := by
    simpa [peakT] using settle_peak_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk hpk
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    rw [settle_ctrl_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hc
  have hmxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [settle_mx_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hmx
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS := by
    rw [settle_strict_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hstrict
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hhole
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 2 hops ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    have hopArr := settle_ops b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
    exact (at_eq hopArr hopsS hops).trans hop1
  have hMulS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [settle_ops b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    exact hMul
  have hopMulS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMulS = Int.ofNat cMul := by
    have hopArr := settle_ops b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
    exact (at_eq hopArr hMulS hMul).trans hopMul
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    rw [settle_marker_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hmk
  have hmS : bS.sudo_5Board_6marker < 0 := by
    rw [settle_ix_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hm
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hRoomS : FitsLen (movesS + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    simpa [movesS] using hRoom
  have hSlS : FitsLen (slidesS + slideCharge t.n) := by
    simpa [slidesS] using hSl
  exact {
    h2H
    h2D
    movesS
    slidesS
    hmovesS := rfl
    hslidesS := rfl
    peakT
    hRoomS
    hSlS
    frS
    seen := lifted_across t bS baseX baseY xP yP zP frS hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT h0S h1S h2S hd0S hd1S hd2S hmkS hoffS hmS
      movesS slidesS ctrl mx peakT peakS hole cOps cMul
      hmvS hslS hcS hmxS hpkS hstrictS hholeS hopsS hopS hMulS hopMulS
      hCtrl hOps hRoomS hSlS
  }

/-- The lifted `zBench` board and the comb it settles into are the same
    `frobenius_point`. -/
theorem zbench_comb_eq
    (t : Spec.Tier) (b bZ : Ecbs.Board) (xP yP zP ys : List Nat)
    (baseX baseY : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hm : b.sudo_5Board_6marker < 0)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (moves slides ctrl mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (ctrl + 5)) (hOps : FitsLen (cOps + 3))
    (hpeg : FitsLen (2 * pegCount (ys.take t.n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take t.n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take t.n)))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n))
    (pack : ZSeen t b baseX baseY xP yP zP ys moves slides pk peakS hole cOps ctrl mx)
    (hfrob : Ecbs.frobenius_point b = .ok bZ) :
    bZ = bottomFlag pack.seen.a zP := by
  have hn0 : 0 < t.n := hOk.n_pos
  have hposY : 0 < ys.length := Nat.lt_of_lt_of_le hn0 hnle
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have htierS :=
    settle_tier_eq b 2 ⟨pack.h2H, pack.h2D⟩ ys t.n moves slides pk
  have htier : b.sudo_5Board_1t = embTier t := htierS.symm.trans pack.frS.tier
  have hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [htier]; rfl
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; simp [embTier, ofNat_eq_natCast]
  have hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [htier]; rfl
  have hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [htier]; rfl
  have hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [htier]; rfl
  have hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [htier]; rfl
  have hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    rw [htier]; rfl
  have hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    rw [htier]; rfl
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hfm : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hlink := frobenius_lifted_bench b 2 xP ys t.w t.h t.r t.n t.k
    moves slides hole t.benchlen pk peakS cOps t.combgap ctrl mx t.script
    hmk hon hm hc hmx hscript (by have h := hsh.script_ge; omega)
    (FitsLen.of_le hCtrl (by omega)) hops hop1 (FitsLen.of_le hOps (by omega))
    (by decide) h0D h0H hd0 h0 pack.h2D pack.h2H h7 hto hd2
    hbench hstrict hpk hn0 hn hxL hposY hnle hzero hnFit (lane_fit t hship hcap) hmv hsl hpeg hfitMv hfitSl
    hbl hcg hspan h3 hfm hhole hxT hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap
    hw hh hr hk hsm hnsm hbenchFit hfold
  have hMv : FitsLen (pack.movesS + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le pack.hRoomS (by omega)
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ pack.seen.a.laneX.length := by rw [pack.seen.a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  obtain ⟨hpegU, hfitMvU, hfitSlU⟩ := up_settle_fit pack.seen.a hMv pack.hSlS
  obtain ⟨_, hMu, _⟩ := up_out_le pack.seen.a
  have hleM : upMv2 pack.seen.a +
      2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) + 2 * t.n ≤
      pack.movesS + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hleF : upMv2 pack.seen.a +
      2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) + 2 * t.n +
      3 * (t.benchlen - t.n) ≤
      pack.movesS + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hfmU : FitsLen (upMv2 pack.seen.a +
      2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) + 2 * t.n) :=
    FitsLen.of_le pack.hRoomS hleM
  have hfoldU : FitsLen (upMv2 pack.seen.a +
      2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) + 2 * t.n +
      3 * (t.benchlen - t.n)) :=
    FitsLen.of_le pack.hRoomS hleF
  have hflag := frobenius_is_flag pack.seen.a zP hyT hyL pack.seen.hH2 pack.seen.h2
    hzL hzT hn0 hnbL hnb hgap0 hs1 hs2
    (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
    hCtrl hOps hspan h3 hnFit hbenchFit hpegU hfitMvU hfitSlU hfmU hfoldU
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  exact Except.ok.inj (hfrob.symm.trans (hlink.trans hflag))

/-- The lifted `zBench` board, the settled across cube, and `bZ = bottomFlag`. -/
structure ZOpen
    (t : Spec.Tier) (b bZ : Ecbs.Board)
    (baseX baseY xP yP zP ys : List Nat) : Type where
  moves : Nat
  slides : Nat
  ctrl : Nat
  mx : Nat
  pk : Nat
  peakS : Nat
  hole : Nat
  c1 : Nat
  c0 : Nat
  hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int)
  hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0)
  bRec : Ecbs.Board
  hopsEq : bRec.sudo_5Board_4cost.sudo_5Costs_3ops =
    b.sudo_5Board_4cost.sudo_5Costs_3ops
  heldEq : bRec.sudo_5Board_4held = b.sudo_5Board_4held
  pack : ZSeen t bRec baseX baseY xP yP zP ys moves slides pk peakS hole c1 (ctrl + 1) mx
  hZ : bZ = bottomFlag pack.seen.a zP

theorem zbench_open_exists
    (t : Spec.Tier) (b bL bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
    (hlift : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_point bL = .ok bZ) :
    Nonempty (ZOpen t b bZ baseX baseY xP yP zP ys) := by
  rcases hAt with ⟨hmk, htier, _, _, _, _, _, _, _, _, _, _,
      h3, h4, hH3, hH4, _, hscript, hszH', hszD', _, hrest⟩
  rcases hrest with ⟨moves, slides, ctrl, mark, mx, pk, peakS, hole, c1, c0,
      hmv, hsl, hc0, hmark, hmx, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, _, hfitMv, hfitSl, _, _, _⟩
  have fr : FrameAt b t baseX baseY := {
    tier := htier
    szH := hszH'
    szD := hszD'
    home3 := h3
    held3 := hH3
    home4 := h4
    held4 := hH4
  }
  let bRec := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }
  have href := marker_lift_refines b mark ctrl hmark hc0 (FitsLen.of_le hfitCtrl (by omega))
  have he : bL = bRec := Except.ok.inj (hlift.symm.trans href)
  have frL := lift_frame t b bRec baseX baseY fr mark ctrl hmark hc0
    (FitsLen.of_le hfitCtrl (by omega)) href
  have hop1 := get_of_some _ 1 _ hop1? hops
  have hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans Nat.zero_lt_one hops
  have hopMul := get_of_some _ 0 _ hop0? hMul
  have hOps := cube_slack_cell c1 t.cells done hc1 hpos
  have hCtrlL : FitsLen ((ctrl + 1) + 5) := FitsLen.of_le hfitCtrl (by omega)
  have hpegN := peg_le ys t.n hnle
  obtain ⟨hpeg, hfitMvS, hfitSlS, hRoom, hSl⟩ :=
    z_room moves slides (pegCount (ys.take t.n)) t.n
      (cubeCharge t.n t.benchlen) (t.benchlen - t.n) (slideCharge t.n)
      hpegN hfitMv hfitSl
  have harrH : bRec.sudo_5Board_4home = b.sudo_5Board_4home := rfl
  have harrD : bRec.sudo_5Board_4held = b.sudo_5Board_4held := rfl
  have h0L : bRec.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP :=
    (at_eq harrH (by rw [hszH]; decide) (by rw [hszH]; decide)).trans h0
  have h1L : bRec.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP :=
    (at_eq harrH (by rw [hszH]; decide) (by rw [hszH]; decide)).trans h1
  have hd0L : bRec.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true :=
    (at_eq harrD (by rw [hszD]; decide) (by rw [hszD]; decide)).trans hd0
  have hd1L : bRec.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true :=
    (at_eq harrD (by rw [hszD]; decide) (by rw [hszD]; decide)).trans hd1
  have hd2L : bRec.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false :=
    (at_eq harrD (by rw [hszD]; decide) (by rw [hszD]; decide)).trans hd2
  have hmL : bRec.sudo_5Board_6marker < 0 := by
    have hmEq : bRec.sudo_5Board_6marker = -1 := rfl
    rw [hmEq]
    decide
  have hcL : bRec.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) := rfl
  have hopsL : 1 < bRec.sudo_5Board_4cost.sudo_5Costs_3ops.size := hops
  have hopL : bRec.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsL = (c1 : Int) := hop1
  have hMulL : 0 < bRec.sudo_5Board_4cost.sudo_5Costs_3ops.size := hMul
  have hopMulL : bRec.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMulL = Int.ofNat c0 := hopMul
  let pack := zbench_seen t bRec baseX baseY xP yP zP ys frL hsh hOk sat hscript
    hxL hyL hzL hxT hyT hzT hszH hszD h0L h1L hd0L hd1L hd2L hmk hmL
    moves slides (ctrl + 1) mx pk peakS hole c1 c0
    hmv hsl hcL hmx hpk hstrict hhole hopsL hopL hMulL hopMulL htake
    hCtrlL hOps hRoom hSl
  have hfrobR : Ecbs.frobenius_point bRec = .ok bZ := by
    simpa [he] using hfrob
  have hZ := zbench_comb_eq t bRec bZ xP yP zP ys baseX baseY hsh hOk sat hscript
    hxL hyL hzL hxT hyT hzT hszH hszD h0L hd0L hd2L hmk hon hto hmL
    hbench hnle hzero hcap hship moves slides (ctrl + 1) mx pk peakS hole c1
    hmv hsl hcL hmx hpk hstrict hhole hopsL hopL hCtrlL hOps hpeg hfitMvS hfitSlS
    hRoom hSl pack hfrobR
  exact ⟨{
    moves
    slides
    ctrl
    mx
    pk
    peakS
    hole
    c1
    c0
    hmv
    hsl
    hc0
    hmx
    hop1 := hop1?
    hop0 := hop0?
    bRec
    hopsEq := rfl
    heldEq := rfl
    pack
    hZ
  }⟩

noncomputable def zbench_open
    (t : Spec.Tier) (b bL bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
    (hlift : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_point bL = .ok bZ) :
    ZOpen t b bZ baseX baseY xP yP zP ys :=
  Classical.choice (zbench_open_exists t b bL bZ baseX baseY px py xP yP zP ys done
    hAt hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto
    hbench htake hnle hzero hcap hship hpos hlift hfrob)

/-- A zero cell that starts in `zBench`. Homes 3 and 4 survive the lift, the
    settle of `Z` into home 2, and the comb. -/
theorem zbench_zero_frame
    (t : Spec.Tier) (b bL bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
    (hlift : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_point bL = .ok bZ) :
    FrameAt bZ t baseX baseY := by
  let o := zbench_open t b bL bZ baseX baseY px py xP yP zP ys done hAt hsh hOk sat
    hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto hbench htake hnle hzero
    hcap hship hpos hlift hfrob
  exact frame_of_seen o.pack.seen.a t baseX baseY zP o.pack.frS o.pack.seen.hops
    o.pack.seen.a.h0D o.pack.seen.a.h0H o.pack.seen.hOn o.pack.seen.h3 o.pack.seen.h4
    o.pack.seen.hH3 o.pack.seen.hH4 bZ o.hZ

private theorem move_cast (out s m peg cube n d : Nat)
    (hs : s = m + 2 * peg) (h : out ≤ s + cube + 2 * n + 3 * d) :
    out ≤ m + 2 * peg + cube + 2 * n + 3 * d := by
  subst hs
  exact h

private theorem slide_cast (out s slides peg n : Nat)
    (hs : s = slides + 2 * peg) (hpeg : peg ≤ n) (h : out ≤ s + 4 * n) :
    out ≤ slides + 6 * n := by
  subst hs
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  omega

/-- Moves, slides, control, marker, and the two op slots after a `zBench` zero cell. -/
theorem zbench_zero_counts
    (t : Spec.Tier) (b bL bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
    (hlift : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_point bL = .ok bZ) :
    ∃ (moves slides ctrl mx c1 c0 moves' slides' pk' peakS' hole' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      bZ.sudo_5Board_9marker_on = true ∧
      (∀ h : 0 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[0] = true) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max (max mx 1) 2) 3) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole' ∧
      1 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((c1 + 3 : Nat) : Int) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      moves' ≤ moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n) ∧
      slides' ≤ slides + 6 * t.n ∧
      bZ.sudo_5Board_4held[5]? = some false ∧
      bZ.sudo_5Board_4held[6]? = some false ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[4]? =
        b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? := by
  let o := zbench_open t b bL bZ baseX baseY px py xP yP zP ys done hAt hsh hOk sat
    hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto hbench htake hnle hzero
    hcap hship hpos hlift hfrob
  let a := o.pack.seen.a
  have hZ := o.hZ
  have hmon : bZ.sudo_5Board_9marker_on = true :=
    (congrArg (fun brd => brd.sudo_5Board_9marker_on) hZ).trans (bottomFlag_mon a zP)
  have hH0 : ∀ h : 0 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[0] = true := by
    intro h
    have hheld := congrArg (fun brd => brd.sudo_5Board_4held) hZ
    exact (at_eq hheld h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held0 a zP)
  have hmvZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_5moves) hZ).trans
      (bottomFlag_moves a zP)
  have hslZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_6slides) hZ).trans
      (bottomFlag_slides a zP)
  have hctrlZ : bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (o.ctrl + 6) := by
    have h :=
      (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_4ctrl) hZ).trans
        (bottomFlag_ctrl a zP)
    have hnat : (o.ctrl + 1) + 5 = o.ctrl + 6 := by omega
    simpa [hnat] using h
  have hmarkZ :=
    (congrArg (fun brd => brd.sudo_5Board_6marker) hZ).trans (bottomFlag_mark a zP)
  have hmxZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) hZ).trans
      (bottomFlag_mx a zP)
  have hpkZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_4peak) hZ).trans
      (bottomFlag_peak a zP)
  have hstZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hZ).trans
      (bottomFlag_strict a zP)
  have hholeZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hZ).trans
      (bottomFlag_hole a zP)
  have hopsZ : 1 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hZ]
    exact bottomFlag_ops a zP
  have hopZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some ((o.c1 + 3 : Nat) : Int) := by
    have hflag := bottomFlag_op a zP
    have h? : (bottomFlag a zP).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
        some (Int.ofNat (o.c1 + 3)) := by
      rw [Array.getElem?_eq_getElem (bottomFlag_ops a zP)]
      exact congrArg some hflag
    exact (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) hZ).trans h?
  have hop0Z : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat o.c0) := by
    let bS := settleBoard o.bRec 2 o.pack.h2H o.pack.h2D ys t.n o.moves o.slides o.pk
    have hopArr := settle_ops o.bRec 2 ⟨o.pack.h2H, o.pack.h2D⟩ ys t.n o.moves o.slides o.pk
    have hMulS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      Nat.lt_trans Nat.zero_lt_one o.pack.seen.hops
    have hsrc : 0 < o.bRec.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hsz := congrArg Array.size hopArr
      rw [← hsz]
      exact hMulS
    have hget : o.bRec.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hsrc = Int.ofNat o.c0 := by
      have h := o.hop0
      rw [← o.hopsEq] at h
      rw [Array.getElem?_eq_getElem hsrc] at h
      exact Option.some.inj h
    have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMulS = Int.ofNat o.c0 :=
      (at_eq hopArr hMulS hsrc).trans hget
    have h0f := comb_ops0_from bS o.c0 a zP hMulS hop0S o.pack.seen.hops
      a.h0D a.h0H o.pack.seen.hOn
    exact (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[0]?) hZ).trans h0f
  have hleM := comb_moves_le a zP
  have hleS := comb_slides_le a
  have hpegN := peg_le ys t.n hnle
  obtain ⟨h5, h6, hopsN⟩ := fform_open t b baseX baseY px py done hAt
  have h5R : o.bRec.sudo_5Board_4held[5]? = some false := by
    rw [o.heldEq]; exact h5
  have h6R : o.bRec.sudo_5Board_4held[6]? = some false := by
    rw [o.heldEq]; exact h6
  have hopsR : o.bRec.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
    rw [o.hopsEq]; exact hopsN
  have hszR : o.bRec.sudo_5Board_4held.size = 8 := by
    rw [o.heldEq, hszD]
  obtain ⟨h5F, h6F, hopsF⟩ :=
    settle_comb_kept o.bRec 2 ⟨o.pack.h2H, o.pack.h2D⟩ ys t.n o.moves o.slides o.pk
      (by decide) (by decide) a zP o.peakS o.pack.seen.hops o.pack.seen.hOn
      hszR h5R h6R hopsR
  have h5Z := (congrArg (fun brd => brd.sudo_5Board_4held[5]?) o.hZ).trans h5F
  have h6Z := (congrArg (fun brd => brd.sudo_5Board_4held[6]?) o.hZ).trans h6F
  have hopsZ5 :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops.size) o.hZ).trans hopsF
  obtain ⟨c4, hopIn4, _⟩ := fform_fadd t b baseX baseY px py done hAt
  let bS4 := settleBoard o.bRec 2 o.pack.h2H o.pack.h2D ys t.n o.moves o.slides o.pk
  have hopS4 : bS4.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat c4) := by
    rw [settle_ops o.bRec 2 ⟨o.pack.h2H, o.pack.h2D⟩ ys t.n o.moves o.slides o.pk, o.hopsEq]
    exact hopIn4
  have h4S : 4 < bS4.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [settle_ops o.bRec 2 ⟨o.pack.h2H, o.pack.h2D⟩ ys t.n o.moves o.slides o.pk,
      o.hopsEq, hopsN]
    decide
  have hflag4 := comb_ops4 a zP o.peakS (Int.ofNat c4) o.pack.seen.hops h4S
    o.pack.seen.hOn hopS4
  have hkeep4 : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[4]? =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? :=
    ((congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[4]?) o.hZ).trans
      hflag4).trans hopIn4.symm
  refine ⟨o.moves, o.slides, o.ctrl, o.mx, o.c1, o.c0, _, _, _, _, _,
      o.hmv, o.hsl, o.hc0, o.hmx, o.hop1, o.hop0, hmon, hH0, hmvZ, hslZ, hctrlZ,
      hmarkZ, hmxZ, hpkZ, hstZ, hholeZ, ?_, hopZ, hop0Z, ?_, ?_, h5Z, h6Z, hopsZ5,
      hkeep4⟩
  · exact hopsZ
  · exact move_cast _ o.pack.movesS o.moves (pegCount (ys.take t.n))
      (cubeCharge t.n t.benchlen) t.n (t.benchlen - t.n) o.pack.hmovesS hleM
  · exact slide_cast _ o.pack.slidesS o.slides (pegCount (ys.take t.n)) t.n
      o.pack.hslidesS hpegN hleS

/-- Held 1 and 2 on the comb a `zBench` cell leaves. Home 1 keeps the cubed up,
    and the bottom cube clears home 2. -/
theorem zbench_held12
    (t : Spec.Tier) (b bL bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hcap : ys.length ≤ t.benchlen)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
    (hlift : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_point bL = .ok bZ) :
    (∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true) ∧
      (∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false) := by
  let o := zbench_open t b bL bZ baseX baseY px py xP yP zP ys done hAt hsh hOk sat
    hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto hbench htake hnle hzero
    hcap hship hpos hlift hfrob
  refine ⟨?_, ?_⟩
  · intro h
    have harr := congrArg (fun brd => brd.sudo_5Board_4held) o.hZ
    exact (at_eq harr h (by rw [bottomFlag_szD o.pack.seen.a zP]; decide)).trans
      (bottomFlag_held1 o.pack.seen.a zP)
  · intro h
    have harr := congrArg (fun brd => brd.sudo_5Board_4held) o.hZ
    exact (at_eq harr h (by rw [bottomFlag_szD o.pack.seen.a zP]; decide)).trans
      (bottomFlag_held2 o.pack.seen.a zP)

end EcbsLink2.Link2
