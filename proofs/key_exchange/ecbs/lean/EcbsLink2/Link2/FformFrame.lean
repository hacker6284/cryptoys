/-
  The frame a nonzero F-form cell keeps. Homes 3 and 4 stay the original base
  point, the home arrays stay length 8, and the tier stays `embTier`.
  The name is `FformFrame` because `CellFrame` is the affine cell.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellStep
import EcbsLink2.Link2.FformHold
import EcbsLink2.Link2.FformCount

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have hxs := embed_beq xs ys
  rw [h] at hxs
  rw [embed_beq ys ys] at hxs
  exact of_decide_eq_true (by simpa using hxs)

/-- What `FformAt` asks of the tier and the base homes. -/
structure FrameAt (b : Ecbs.Board) (t : Spec.Tier) (baseX baseY : List Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  home3 : ∀ h : 3 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[3]'h = embed baseX
  held3 : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3]'h = true
  home4 : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4]'h = embed baseY
  held4 : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4]'h = true

/-- The bottom cube keeps homes 3 and 4. `bottomFlag_later` is the off step
    plus the settle chain; `bottomFlag_held3` and `bottomFlag_held4` are the flags. -/
theorem flag_keeps_base
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z baseX baseY : List Nat)
    (h3 : a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX)
    (h4 : a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY)
    (hH3 : a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true)
    (hH4 : a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true) :
    (bottomFlag a z).sudo_5Board_4home[3]'(by rw [bottomFlag_sz a z]; decide) = embed baseX ∧
    (bottomFlag a z).sudo_5Board_4home[4]'(by rw [bottomFlag_sz a z]; decide) = embed baseY ∧
    (bottomFlag a z).sudo_5Board_4held[3]'(by rw [bottomFlag_szD a z]; decide) = true ∧
    (bottomFlag a z).sudo_5Board_4held[4]'(by rw [bottomFlag_szD a z]; decide) = true ∧
    (bottomFlag a z).sudo_5Board_4home.size = 8 ∧
    (bottomFlag a z).sudo_5Board_4held.size = 8 := by
  refine ⟨?_, ?_, bottomFlag_held3 a z hH3, bottomFlag_held4 a z hH4,
      bottomFlag_sz a z, bottomFlag_szD a z⟩
  · rw [bottomFlag_later a z 3 (by decide) (by decide) (by decide) (by decide), h3]
  · rw [bottomFlag_later a z 4 (by decide) (by decide) (by decide) (by decide), h4]

/-- The cell's tail still holds those homes, and the tier is `embTier`.
    `flag_keeps_base` is the cube: its home 3 is `baseX`, and the tail reports
    that same list as `x2`. -/
theorem cell_frame (t : Spec.Tier) (b : Ecbs.Board) (lane : List Nat)
    (n k bench : Nat) (v z x2 y2 x3 yUp : List Nat)
    (tier : Ecbs.Tier) (szHome szHeld : Nat) (baseX baseY : List Nat)
    (c : CellAt b lane n k bench v z x2 y2 x3 yUp tier szHome szHeld)
    {b0 : Ecbs.Board} {x y : List Nat}
    {w h r cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b0 x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h3 : a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX)
    (h4 : a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY)
    (hH3 : a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true)
    (hH4 : a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true)
    (hLink3 : (bottomFlag a z).sudo_5Board_4home[3]'(by rw [bottomFlag_sz a z]; decide) = embed x2)
    (hLink4 : (bottomFlag a z).sudo_5Board_4home[4]'(by rw [bottomFlag_sz a z]; decide) = embed y2)
    (hTier : tier = embTier t) (hszH : szHome = 8) (hszD : szHeld = 8) :
    FrameAt b t baseX baseY := by
  have hflag := flag_keeps_base a z baseX baseY h3 h4 hH3 hH4
  have hx : x2 = baseX := embed_inj (hLink3.symm.trans hflag.1)
  have hy : y2 = baseY := embed_inj (hLink4.symm.trans hflag.2.1)
  exact {
    tier := c.tierEq.trans hTier
    szH := c.szH.trans hszH
    szD := c.szD.trans hszD
    home3 := fun h => (c.home3 h).trans (congrArg embed hx)
    held3 := c.held3
    home4 := fun h => (c.home4 h).trans (congrArg embed hy)
    held4 := c.held4
  }

end EcbsLink2.Link2
