/-
  The comb `comb_u2z` reads, past the multiply counter. The bench prefix is
  `fieldCube` of the bottom, aimed at home 2, and held 2 is clear.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformComb

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem comb_held2
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4held[2]? = some false := by
  have hsz : 2 < (bottomFlag a z).sudo_5Board_4held.size := by
    rw [bottomFlag_szD a z]; decide
  have h := bottomFlag_held2 a z
  exact (Array.getElem?_eq_getElem hsz).trans (congrArg some h)

theorem comb_bench
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done cMul : Nat)
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
    (hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopMul : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMul = Int.ofNat cMul)
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ (bL : Ecbs.Board)
      (a : DownAcross bL xP yP t.n t.k t.w t.h t.r t.benchlen t.combgap
            pk moves slides hole cOps (c0 + 1) mx t.script)
      (lane : List Nat),
      Ecbs.frobenius_point bL = .ok (bottomFlag a zP) ∧
      (bottomFlag a zP).sudo_5Board_5bench = embed lane ∧
      lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
      (∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
      (bottomFlag a zP).sudo_5Board_8bench_on = true ∧
      (bottomFlag a zP).sudo_5Board_8bench_to = (2 : Int) ∧
      (bottomFlag a zP).sudo_5Board_4held[2]? = some false := by
  obtain ⟨bL, a, _, hlift, hflag, _, _⟩ :=
    comb_entry t b baseX baseY px py xP yP zP done cMul hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0
      mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1
      hMul hopMul hCtrl hOps hRoom hSl
  obtain ⟨bL2, bZ, hlift2, hfrob, _, hbon, hto, lane, hbench, htake, hzero, _, _⟩ :=
    frobenius_fform_homes t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0
      mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1
      hCtrl hOps hRoom hSl
  have hb : bL2 = bL := Except.ok.inj (hlift2.symm.trans hlift)
  have hbZ : bZ = bottomFlag a zP := by
    rw [hb] at hfrob
    exact Except.ok.inj (hfrob.symm.trans hflag)
  refine ⟨bL, a, lane, hflag, ?_, ?_, ?_, ?_, ?_, comb_held2 a zP⟩
  · rw [← hbZ]; exact hbench
  · exact htake
  · exact hzero
  · rw [← hbZ]; exact hbon
  · rw [← hbZ]; exact hto

end EcbsLink2.Link2
