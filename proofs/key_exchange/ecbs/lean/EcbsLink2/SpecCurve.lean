/-
  The curve equation from SPEC.md, as a predicate on peg lists.
-/
import EcbsLink2.Spec

namespace EcbsLink2.Spec

/-- Coefficient-wise sum in GF(3). Hole `i` is `xs[i] + ys[i]` mod 3, and a
    missing hole is empty. -/
def fieldAdd (n : Nat) (xs ys : List Nat) : List Nat :=
  (List.range n).map fun i => tritAdd (coeff xs i) (coeff ys i)

/-- SPEC.md line 3: **E: y² = x³ − x² + 1 over GF(3ⁿ)**. SPEC.md §8 line 321
    names the same constants (`a₂ = −1`, `a₆ = 1`) as "y squared is x cubed,
    minus x squared, plus one". SPEC.md §5.3 line 222 is that test on the
    board: the up times itself, against the across cubed, take away the across
    times itself, plus a white peg in hole 0.

    `x` and `y` are peg lists in the same basis as `fieldMul` (hole 0 first,
    empty/white/red = 0/1/2). Minus is the colour flip, which is multiplication
    by 2 in GF(3). Plus one is `fieldAdd` with a white peg in hole 0. -/
def onCurve (n k bench : Nat) (x y : List Nat) : Bool :=
  let y2 := fieldMul n k bench y y
  let x2 := fieldMul n k bench x x
  let x3 := fieldCube n k bench x
  let rhs := fieldAdd n (fieldAdd n x3 (mirrorTrits x2))
    (1 :: List.replicate (n - 1) 0)
  decide (y2 = rhs)

/-- SPEC.md §5.1 line 198, Demo base point, hole 0 first: x = `.RWR.WW`,
    y = `R..RRWR`. -/
theorem demo_base_onCurve :
    onCurve demo.n demo.k demo.benchlen
      [0, 2, 1, 2, 0, 1, 1] [2, 0, 0, 2, 2, 1, 2] = true := by
  decide

end EcbsLink2.Spec
