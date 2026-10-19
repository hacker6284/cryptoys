/-
  A zero cell of `hframe` on `yBench` or `zBench`. The emitted step is
  `cell_walk_step`, and the board is the next `FformAt`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformYPack
import EcbsLink2.Link2.FformZPack
import EcbsLink2.Link2.FformCellWalk
import EcbsLink2.Link2.WalkFformStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift

private theorem step_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hle : i + 1 ≤ t.cells + 1 := by omega
  have hone : 1 ≤ cellOpsCharge t := hpos
  exact Nat.le_trans hle (by simpa using Nat.mul_le_mul_left (t.cells + 1) hone)

private abbrev StepEx :=
  Except SudoRt.Trap
    (SudoRt.Flow (Int × (Ecbs.Board × Bool)) ((Bool × Bool) × Ecbs.Board))

private def stepOn (i toN : Nat) (sb : Ecbs.Board) : StepEx :=
  if i = toN then
    Except.ok (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat i, (sb, true)))
  else
    Except.ok (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat (i + 1), (sb, true)))

private theorem pair_board {i : Int} {sb b : Ecbs.Board}
    (h : (i, (sb, true)) = (i, (b, true))) : sb = b := by
  injection h with _ hp
  injection hp with hsb _

private theorem step_board (i toN : Nat) (sb b : Ecbs.Board)
    (h : stepOn i toN sb = stepOn i toN b) : sb = b := by
  by_cases hlast : i = toN
  · unfold stepOn at h
    rw [if_pos hlast, if_pos hlast] at h
    exact pair_board (SudoRt.Flow.brk.inj (Except.ok.inj h))
  · unfold stepOn at h
    rw [if_neg hlast, if_neg hlast] at h
    exact pair_board (SudoRt.Flow.cont.inj (Except.ok.inj h))

/-- `yBench`, colour 0. The emitted step lands on the next `FformAt`. -/
theorem ybench_zero_step
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (i : Nat)
    (ax' ay' : List Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (tw : TierWalk t)
    (hstep : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < ys.length, ys[j] = 0)
    (hfitY : FitsLen ys.length)
    (cells : List Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py)
        (cells[i]'(by omega)) = some (true, (ax', ay'))) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hposI : i < t.cells := by omega
  obtain ⟨bL, bZ, hlift, hfrob, hAtZ⟩ :=
    ybench_zero_cell_at t b baseX baseY px py xP yP zP ys i hAt hsh hOk sat tw
      hstep h12 h46 hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto
      hbench htake hnle hzero hfitY hposI
  have hwalk0 : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) 0 =
      some (true, (ax', ay')) := by
    simpa [hc] using hwalk
  have hfit := step_fit t tw i (by omega)
  have hnone : (0 : Nat) ≠ 0 →
      Ecbs.fform_add bZ (decide ((0 : Nat) = 2)) = .ok (true, bZ) := by
    intro h
    exact absurd rfl h
  obtain ⟨sb, hst⟩ :=
    cell_walk_step t cells i 0 b bL bZ bZ (baseX, baseY) px py ax' ay'
      hpos hi hlen hc hwalk0 hlift hfrob hnone hfit
  have hpt :=
    fformStep_point cells i (t.cells - 1) b bL bZ hi (by omega) hc hlift hfrob hfit
  have hsb : sb = bZ :=
    step_board i (t.cells - 1) sb bZ (by simpa [stepOn] using hst.symm.trans hpt)
  have hcubes :=
    walk_zero_cubes t.n t.k t.benchlen (baseX, baseY) px py ax' ay' hwalk0
  have hAt' : FformAt t bZ baseX baseY ax' ay' (i + 1) := by
    rw [← hcubes.1, ← hcubes.2] at hAtZ
    exact hAtZ
  refine ⟨bZ, ?_, hAt'⟩
  simpa [hsb] using hst

/-- `zBench`, colour 0. The emitted step lands on the next `FformAt`. -/
theorem zbench_zero_step
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (i : Nat)
    (ax' ay' : List Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (tw : TierWalk t)
    (hstep : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
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
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < ys.length, ys[j] = 0)
    (hfitY : FitsLen ys.length)
    (cells : List Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py)
        (cells[i]'(by omega)) = some (true, (ax', ay'))) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hposI : i < t.cells := by omega
  obtain ⟨bL, bZ, hlift, hfrob, hAtZ⟩ :=
    zbench_zero_cell_at t b baseX baseY px py xP yP zP ys i hAt hsh hOk sat tw
      hstep h12 h46 hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto
      hbench htake hnle hzero hfitY hposI
  have hwalk0 : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) 0 =
      some (true, (ax', ay')) := by
    simpa [hc] using hwalk
  have hfit := step_fit t tw i (by omega)
  have hnone : (0 : Nat) ≠ 0 →
      Ecbs.fform_add bZ (decide ((0 : Nat) = 2)) = .ok (true, bZ) := by
    intro h
    exact absurd rfl h
  obtain ⟨sb, hst⟩ :=
    cell_walk_step t cells i 0 b bL bZ bZ (baseX, baseY) px py ax' ay'
      hpos hi hlen hc hwalk0 hlift hfrob hnone hfit
  have hpt :=
    fformStep_point cells i (t.cells - 1) b bL bZ hi (by omega) hc hlift hfrob hfit
  have hsb : sb = bZ :=
    step_board i (t.cells - 1) sb bZ (by simpa [stepOn] using hst.symm.trans hpt)
  have hcubes :=
    walk_zero_cubes t.n t.k t.benchlen (baseX, baseY) px py ax' ay' hwalk0
  have hAt' : FformAt t bZ baseX baseY ax' ay' (i + 1) := by
    rw [← hcubes.1, ← hcubes.2] at hAtZ
    exact hAtZ
  refine ⟨bZ, ?_, hAt'⟩
  simpa [hsb] using hst

end EcbsLink2.Link2
