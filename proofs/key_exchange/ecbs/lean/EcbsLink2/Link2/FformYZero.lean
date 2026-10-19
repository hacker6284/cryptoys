/-
  A zero cell whose input is `yBench`. The lift keeps homes 3 and 4.
  Settling `yP` into home 1 keeps them too. The comb after that settle is
  the lifted homes cube, so `flag_keeps_base` finishes `FrameAt`, and the
  counters are the comb's plus the settle's two peg-counts.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformFrob
import EcbsLink2.Link2.FformFrame
import EcbsLink2.Link2.FformKept
import EcbsLink2.Link2.FformCount
import EcbsLink2.Link2.FformComb
import EcbsLink2.Link2.FformSumRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift

private theorem elem_cast {α : Type} (a : Array α) (i : Nat) (h1 h2 : i < a.size)
    {v : α} (h : a[i]'h1 = v) : a[i]'h2 = v := by
  cases proof_irrel h1 h2
  exact h

private theorem six_le_cube (n : Nat) : 6 * n ≤ 8 * n * (n + 1) := by
  have h : 6 ≤ 8 * (n + 1) := by omega
  calc
    6 * n = n * 6 := Nat.mul_comm _ _
    _ ≤ n * (8 * (n + 1)) := Nat.mul_le_mul_left n h
    _ = 8 * n * (n + 1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm n 8, Nat.mul_assoc]

/-- Two cube spends, the settle's `2 * n`, and one more `2 * n`. -/
theorem ybench_move_room (n bench : Nat) :
    2 * (cubeCharge n bench + 2 * n + 3 * (bench - n)) + 4 * n ≤
      8 * stepBudget n bench := by
  unfold cubeCharge stepBudget
  generalize hd : bench - n = d
  have h8 : 8 * n ≤ 8 * (n * (n + 1)) := by
    have hone : 1 ≤ n + 1 := by omega
    have hmul : n * 1 ≤ n * (n + 1) := Nat.mul_le_mul_left n hone
    have h := Nat.mul_le_mul_left 8 (by simpa using hmul)
    simpa [Nat.mul_assoc, Nat.mul_comm n 8] using h
  have hmain : 24 * n + 18 * d ≤ 16 * n + 8 * (n * (n + 1)) + 24 * d := by
    have hleft : 24 * n + 18 * d = 16 * n + (8 * n + 18 * d) := by omega
    have hrest : 8 * n + 18 * d ≤ 8 * (n * (n + 1)) + 24 * d := by
      have h18 : 18 * d ≤ 24 * d := by omega
      exact Nat.add_le_add h8 h18
    omega
  have hL : 2 * (8 * n + 6 * d + 2 * n + 3 * d) + 4 * n = 24 * n + 18 * d := by omega
  have hR : 8 * (2 * n + n * (n + 1) + 3 * d) =
      16 * n + 8 * (n * (n + 1)) + 24 * d := by omega
  rw [hL, hR]
  exact hmain

/-- The marker lift rewrites the marker and the control counter. Homes 3 and 4
    stay, with their held flags, and the tier stays. -/
theorem lift_frame (t : Spec.Tier) (b bL : Ecbs.Board) (baseX baseY : List Nat)
    (fr : FrameAt b t baseX baseY) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1))
    (hL : Ecbs.marker_lift b = .ok bL) :
    FrameAt bL t baseX baseY := by
  have href := marker_lift_refines b marker ctrl hm hc hfit
  have he : bL = { b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } } :=
    Except.ok.inj (hL.symm.trans href)
  have hhome : bL.sudo_5Board_4home = b.sudo_5Board_4home := by rw [he]
  have hheld : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [he]
  have htier : bL.sudo_5Board_1t = b.sudo_5Board_1t := by rw [he]
  exact {
    tier := htier.trans fr.tier
    szH := (congrArg Array.size hhome).trans fr.szH
    szD := (congrArg Array.size hheld).trans fr.szD
    home3 := fun h =>
      (at_eq hhome h (by rw [fr.szH]; decide)).trans (fr.home3 (by rw [fr.szH]; decide))
    held3 := fun h =>
      (at_eq hheld h (by rw [fr.szD]; decide)).trans (fr.held3 (by rw [fr.szD]; decide))
    home4 := fun h =>
      (at_eq hhome h (by rw [fr.szH]; decide)).trans (fr.home4 (by rw [fr.szH]; decide))
    held4 := fun h =>
      (at_eq hheld h (by rw [fr.szD]; decide)).trans (fr.held4 (by rw [fr.szD]; decide))
  }

private theorem settle_read_home (b : Ecbs.Board) (home i : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (ys : List Nat) (n moves slides pk : Nat) (hne : home ≠ i)
    (hi : i < b.sudo_5Board_4home.size) :
    (settleBoard b home hH hD ys n moves slides pk).sudo_5Board_4home[i]? =
      b.sudo_5Board_4home[i]? := by
  rw [settle_home_eq b home ⟨hH, hD⟩ ys n moves slides pk]
  exact Array.getElem?_set_ne _ _ _ hne

private theorem settle_read_held (b : Ecbs.Board) (home i : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (ys : List Nat) (n moves slides pk : Nat) (hne : home ≠ i)
    (hi : i < b.sudo_5Board_4held.size) :
    (settleBoard b home hH hD ys n moves slides pk).sudo_5Board_4held[i]? =
      b.sudo_5Board_4held[i]? := by
  rw [settle_held_eq b home ⟨hH, hD⟩ ys n moves slides pk]
  exact Array.getElem?_set_ne _ _ _ hne

/-- Settling a bench into `home` writes that home. Homes 3 and 4 stay when
    `home` is 1 or 2, and so do their held flags. The tier stays. -/
theorem settle_frame (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY ys : List Nat)
    (fr : FrameAt b t baseX baseY) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (n moves slides pk : Nat) (h3 : home ≠ 3) (h4 : home ≠ 4) :
    FrameAt (settleBoard b home hH hD ys n moves slides pk) t baseX baseY := by
  let bS := settleBoard b home hH hD ys n moves slides pk
  have hszH : bS.sudo_5Board_4home.size = 8 := by
    rw [settle_home_eq b home ⟨hH, hD⟩ ys n moves slides pk, Array.size_set, fr.szH]
  have hszD : bS.sudo_5Board_4held.size = 8 := by
    rw [settle_held_eq b home ⟨hH, hD⟩ ys n moves slides pk, Array.size_set, fr.szD]
  have home_at (i : Nat) (v : Array Int) (hne : home ≠ i) (hi : i < 8)
      (h : b.sudo_5Board_4home[i]'(by rw [fr.szH]; exact hi) = v) :
      bS.sudo_5Board_4home[i]'(by rw [hszH]; exact hi) = v := by
    have h? := settle_read_home b home i hH hD ys n moves slides pk hne
      (by rw [fr.szH]; exact hi)
    have hb? : b.sudo_5Board_4home[i]? = some v := by
      rw [Array.getElem?_eq_getElem (by rw [fr.szH]; exact hi)]
      exact congrArg some h
    rw [hb?] at h?
    have hsz : i < bS.sudo_5Board_4home.size := by rw [hszH]; exact hi
    rw [Array.getElem?_eq_getElem hsz] at h?
    exact Option.some.inj h?
  have held_at (i : Nat) (hne : home ≠ i) (hi : i < 8)
      (h : b.sudo_5Board_4held[i]'(by rw [fr.szD]; exact hi) = true) :
      bS.sudo_5Board_4held[i]'(by rw [hszD]; exact hi) = true := by
    have h? := settle_read_held b home i hH hD ys n moves slides pk hne
      (by rw [fr.szD]; exact hi)
    have hb? : b.sudo_5Board_4held[i]? = some true := by
      rw [Array.getElem?_eq_getElem (by rw [fr.szD]; exact hi)]
      exact congrArg some h
    rw [hb?] at h?
    have hsz : i < bS.sudo_5Board_4held.size := by rw [hszD]; exact hi
    rw [Array.getElem?_eq_getElem hsz] at h?
    exact Option.some.inj h?
  exact {
    tier := (settle_tier_eq b home ⟨hH, hD⟩ ys n moves slides pk).trans fr.tier
    szH := hszH
    szD := hszD
    home3 := fun _ => home_at 3 (embed baseX) h3 (by decide) (fr.home3 _)
    held3 := fun _ => held_at 3 h3 (by decide) (fr.held3 _)
    home4 := fun _ => home_at 4 (embed baseY) h4 (by decide) (fr.home4 _)
    held4 := fun _ => held_at 4 h4 (by decide) (fr.held4 _)
  }

/-- Homes 3 and 4 on the across cube are the homes of the lifted board. -/
theorem across_base
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk peakS moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (t : Spec.Tier) (baseX baseY : List Nat)
    (fr : FrameAt b t baseX baseY)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (h0D : 0 < b.sudo_5Board_4held.size) (h0H : 0 < b.sudo_5Board_4home.size)
    (hOn : a.b1On = acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H) :
    a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX ∧
      a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY ∧
      a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true ∧
      a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hi : 3 < 8 := by decide
    have hiL : 3 < b.sudo_5Board_4home.size := by rw [fr.szH]; exact hi
    have hAc := across_home_ne b x 3 n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H (by decide) hiL
    have hhome : a.b1On.sudo_5Board_4home =
        (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
          hops h0D h0H).sudo_5Board_4home := by rw [hOn]
    have hget := at_eq hhome (by rw [a.hszHOn]; exact hi)
      (by rw [raw_home, Array.size_set, feed_home]; exact hiL)
    exact hget.trans (hAc.trans (fr.home3 (by rw [fr.szH]; exact hi)))
  · have hi : 4 < 8 := by decide
    have hiL : 4 < b.sudo_5Board_4home.size := by rw [fr.szH]; exact hi
    have hAc := across_home_ne b x 4 n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H (by decide) hiL
    have hhome : a.b1On.sudo_5Board_4home =
        (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
          hops h0D h0H).sudo_5Board_4home := by rw [hOn]
    have hget := at_eq hhome (by rw [a.hszHOn]; exact hi)
      (by rw [raw_home, Array.size_set, feed_home]; exact hiL)
    exact hget.trans (hAc.trans (fr.home4 (by rw [fr.szH]; exact hi)))
  · have hi : 3 < 8 := by decide
    have hiL : 3 < b.sudo_5Board_4held.size := by rw [fr.szD]; exact hi
    have hAc := across_held_ne b x 3 n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H (by decide) hiL
    have hheld : a.b1On.sudo_5Board_4held =
        (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
          hops h0D h0H).sudo_5Board_4held := by rw [hOn]
    have hget := at_eq hheld (by rw [a.hszDOn]; exact hi)
      (by rw [raw_held, Array.size_set, feed_held]; exact hiL)
    exact hget.trans (hAc.trans (fr.held3 (by rw [fr.szD]; exact hi)))
  · have hi : 4 < 8 := by decide
    have hiL : 4 < b.sudo_5Board_4held.size := by rw [fr.szD]; exact hi
    have hAc := across_held_ne b x 4 n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H (by decide) hiL
    have hheld : a.b1On.sudo_5Board_4held =
        (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
          hops h0D h0H).sudo_5Board_4held := by rw [hOn]
    have hget := at_eq hheld (by rw [a.hszDOn]; exact hi)
      (by rw [raw_held, Array.size_set, feed_held]; exact hiL)
    exact hget.trans (hAc.trans (fr.held4 (by rw [fr.szD]; exact hi)))

/-- The bottom cube keeps the across cube's homes 3 and 4, so the comb board
    is `FrameAt`. -/
theorem flag_frame
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk peakS moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (t : Spec.Tier) (baseX baseY z : List Nat)
    (fr : FrameAt b t baseX baseY)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (h0D : 0 < b.sudo_5Board_4held.size) (h0H : 0 < b.sudo_5Board_4home.size)
    (hOn : a.b1On = acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
      hops h0D h0H)
    (h3 : a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX)
    (h4 : a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY)
    (hH3 : a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true)
    (hH4 : a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true) :
    ∃ bZ, FrameAt bZ t baseX baseY := by
  have hkeep := flag_keeps_base a z baseX baseY h3 h4 hH3 hH4
  let bZ := bottomFlag a z
  have hcube := cube_off_tier (markerDownFeed b ctrl mx) 0 0 x n k moves holeN bench pk
    peakS cOps hops h0D h0H
  have hOnTier : a.b1On.sudo_5Board_1t = b.sudo_5Board_1t := by
    have hwrap : (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
        hops h0D h0H).sudo_5Board_1t =
        (cubeOffBoard (markerDownFeed b ctrl mx) 0 0 x n k moves holeN bench pk peakS
          cOps hops h0D h0H).sudo_5Board_1t := by
      unfold acrossBoard
      rfl
    exact (congrArg (fun brd => brd.sudo_5Board_1t) hOn).trans (hwrap.trans hcube)
  have htierZ : bZ.sudo_5Board_1t = b.sudo_5Board_1t :=
    (bottomFlag_tier a z).trans hOnTier
  exact ⟨bZ, {
    tier := htierZ.trans fr.tier
    szH := hkeep.2.2.2.2.1
    szD := hkeep.2.2.2.2.2
    home3 := fun h =>
      (at_eq rfl h (by rw [bottomFlag_sz a z]; decide)).trans hkeep.1
    held3 := fun h =>
      (at_eq rfl h (by rw [bottomFlag_szD a z]; decide)).trans hkeep.2.2.1
    home4 := fun h =>
      (at_eq rfl h (by rw [bottomFlag_sz a z]; decide)).trans hkeep.2.1
    held4 := fun h =>
      (at_eq rfl h (by rw [bottomFlag_szD a z]; decide)).trans hkeep.2.2.2.1
  }⟩

end EcbsLink2.Link2

