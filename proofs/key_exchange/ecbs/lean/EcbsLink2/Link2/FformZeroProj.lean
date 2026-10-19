/-
  The zero cell's projective point. The comb counters stay in `FformZeroAt`,
  and the cube algebra stays in `FformZeroLay`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformZeroAt
import EcbsLink2.Link2.FformZeroLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The zero cell cubes the projective point and leaves it in the `zBench` layout. -/
theorem zero_cell_proj
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
    (hSl : FitsLen (slides + slideCharge t.n))
    (cells : List Nat) (i : Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hfitI : FitsLen (i + 1)) :
    ∃ (bL : Ecbs.Board) (bZ : Ecbs.Board),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      FrameAt bZ t baseX baseY ∧
      ProjOn t bZ (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) := by
  obtain ⟨bL, bZ, hlift, hfrob, hfr, hH1, hH2, hbon, hto,
      lane, hbench, htake, hzero, hhome0, hhome1⟩ :=
    zero_bZ_lay t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl cells i hpos hi hlen hc hfitI
  exact ⟨bL, bZ, hlift, hfrob, hfr,
    zero_zbench t b bZ baseX baseY px py xP yP zP done hAt hsh hOk sat
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd2 hoff hH1 hH2 hbon hto
      lane hbench htake hzero hhome0 hhome1⟩

end EcbsLink2.Link2
