/-
  The board `frobenius_point` returns, on the homes layout, has marker `2`.
  A live F-form cell then has room for `comb_u2z`'s script check whenever
  `fformScript < script`. Demo is outside that bound (`demo_not_fform`,
  `DEMO_SCRIPT.md`).
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformFrob
import EcbsLink2.Link2.FformCount
import EcbsLink2.Link2.WalkScope

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem elem_cast {α : Type} (a : Array α) (i : Nat)
    (h1 h2 : i < a.size) {v : α} (h : a[i]'h1 = v) : a[i]'h2 = v := by
  cases proof_irrel h1 h2
  exact h

/-- `m = 2` meets `comb_u2z`'s `m + 8 < script` once one live cell fits. -/
theorem comb_script_at_two (script : Nat) (h : fformScript < script) : 2 + 8 < script := by
  unfold fformScript at h
  omega

/-- Homes layout. After the cell's lift, `frobenius_point` is the flagged comb
    and the marker is `2`. -/
theorem frobenius_marker_two
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 := by
  obtain ⟨bL, a, hlift, hhome?, hheld?⟩ :=
    fform_homes_across t b baseX baseY px py xP yP zP done hAt hsh hOk sat
      hxL hyL hxT hyT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0 mark mx
      pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1 hCtrl hOps
      hRoom hSl
  have hn0 : 0 < t.n := hOk.n_pos
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le hRoom (by omega)
  obtain ⟨hpeg, hfitMv, hfitSl⟩ := up_settle_fit a hMv hSl
  obtain ⟨_, hMu, _⟩ := up_out_le a
  have hleF : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n) ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hleM : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n) := FitsLen.of_le hRoom hleM
  have hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n)) := FitsLen.of_le hRoom hleF
  have hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed zP := by
    have hsz : 2 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
    have h := hhome?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszHOn]; decide) (Option.some.inj h)
  have hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true := by
    have hsz : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
    have h := hheld?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszDOn]; decide) (Option.some.inj h)
  have hflag := frobenius_is_flag a zP hyT hyL hheld2 hhome2 hzL hzT hn0 hnbL hnb hgap0
    hs1 hs2 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
    hCtrl hOps hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfm hfold
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  exact ⟨bL, bottomFlag a zP, hlift, hflag, bottomFlag_mark a zP⟩

end EcbsLink2.Link2
