/-
  The base point from SPEC.md §5.1, as a function on peg lists.
  Not a claim that the emitted `base_point` agrees with it yet.
-/
import EcbsLink2.SpecCurve

namespace EcbsLink2.Spec

/-- A white peg in hole 0 and empty elsewhere. SPEC.md §5.1 line 193
    ("a white peg in hole 0 of the up") and §5.3 line 222 (the plus one). -/
def whiteHole0 (n : Nat) : List Nat :=
  1 :: List.replicate (n - 1) 0

/-- `e_j`: a white peg in hole `j`, every other hole empty. SPEC.md §5.1 line 193
    starts the search with that peg in hole 1. -/
def basisPeg (n j : Nat) : List Nat :=
  (List.replicate n 0).set j 1

/-- The curve side `x³ − x² + 1`. SPEC.md line 3 and §5.1 line 193
    ("its curve side in the bottom"). Minus is the colour flip. -/
def curveSide (n k bench : Nat) (x : List Nat) : List Nat :=
  fieldAdd n (fieldAdd n (fieldCube n k bench x) (mirrorTrits (fieldMul n k bench x x)))
    (whiteHole0 n)

/-- SPEC.md §5.1 line 195: the root exponent `(3^n + 1) / 4`.
    The same line says `3^n ≡ 3 (mod 4)`, so this divides when `n` is odd. -/
def rootExpNat (n : Nat) : Nat :=
  (3 ^ n + 1) / 4

/-- One trit of that exponent, hole 0 first (the highest power).
    SPEC.md §5.1 lines 193 and 195: `n − 1` digits, "red, empty, red, empty …,
    ending red, white". Red/empty/white = 2/0/1. The last of the `n − 1` holes
    is white; every earlier even hole is red; the odd holes between them are empty.
    That sentence names two final digits, so it describes `n ≥ 3`. -/
def rootDigit (n i : Nat) : Nat :=
  if i + 2 = n then 1 else if i % 2 = 0 then 2 else 0

/-- The `n − 1` trits. Hole `n − 1` is the "one hole short" and is not a digit. -/
def rootDigits (n : Nat) : List Nat :=
  (List.range (n - 1)).map (rootDigit n)

/-- Hole 0 is the highest power of 3. -/
def digitsValue (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * 3 + d) 0

/-- One cube-and-multiply step. SPEC.md §5.1 line 193: cube the up, then on red
    (`2`) multiply by the gap (`rhs²`), on white (`1`) by the bottom (`rhs`).
    A zero trit only cubes. Hole 0 is read first, so this is MSB-first. -/
def powStep (n k bench : Nat) (rhs acc : List Nat) (d : Nat) : List Nat :=
  let cubed := fieldCube n k bench acc
  if d = 2 then fieldMul n k bench cubed (fieldMul n k bench rhs rhs)
  else if d = 1 then fieldMul n k bench cubed rhs
  else cubed

/-- `rhs` raised to the root exponent, by those trits, starting from 1. -/
def fieldPowDigits (n k bench : Nat) (rhs : List Nat) (digits : List Nat) : List Nat :=
  digits.foldl (powStep n k bench rhs) (whiteHole0 n)

/-- The square root the card builds: `rhs ^ ((3^n + 1) / 4)`. -/
def rootY (n k bench : Nat) (x : List Nat) : List Nat :=
  fieldPowDigits n k bench (curveSide n k bench x) (rootDigits n)

/-- `y² = rhs` for that root. SPEC.md §5.1 line 193: "Not the bottom?" clears
    and moves on; a match is a hit. -/
def rootHit (n k bench : Nat) (x : List Nat) : Bool :=
  fieldMul n k bench (rootY n k bench x) (rootY n k bench x) == curveSide n k bench x

/-- The first hit at hole `j`, starting at hole 1 and moving one hole on
    (SPEC.md §5.1 line 193). `fuel` is how many holes remain to try; the
    search stops at hole `n`. Structural in `fuel`, so the kernel can evaluate it. -/
def searchRoot (n k bench fuel j : Nat) : Option (List Nat × List Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if j < n then
      let x := basisPeg n j
      if rootHit n k bench x then some (x, rootY n k bench x)
      else searchRoot n k bench fuel (j + 1)
    else none

/-- The halving ladder, structural in the fuel so the kernel can evaluate it.
    `specRungs c` is `rungList c` (R6). -/
def specRungsGo : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, c =>
    if c ≤ 1 then [] else rungColour c :: specRungsGo fuel (c / 2)

def specRungs (c : Nat) : List Nat :=
  specRungsGo (c + 1) c

/-- R6 on a rung list: the gap `invert` leaves before the hole-0 mirror. -/
def invGapOf (n k bench : Nat) (x rungs : List Nat) : List Nat :=
  fieldCube n k bench (invClimb n k bench x (x, 1) rungs.reverse).1

/-- R6, including the quadratic-character mirror. `none` when the product is
    not a single peg in hole 0. Uses `specRungs` so evaluation does not depend
    on the well-founded `rungList`. -/
def specInv (n k bench : Nat) (x : List Nat) : Option (List Nat) :=
  let g := invGapOf n k bench x (specRungs (n - 1))
  let v := fieldMul n k bench g x
  if v = whiteHole0 n then some g
  else if v = 2 :: List.replicate (n - 1) 0 then some (mirrorTrits g)
  else none

/-- Subtract in the peg basis: `a − b` is `a` plus the colour flip of `b`. -/
def fieldSub (n : Nat) (a b : List Nat) : List Nat :=
  fieldAdd n a (mirrorTrits b)

/-- Chord addition of two affine points. SPEC.md §3 R7 lines 156–157:
    slope = rise over run, run inverted first; new x = slope² + 1 + first x − run;
    new y = slope · (first x − new x) − first y. The first point is `p`, the
    second is `q`, and the run is `q.x − p.x`, which is what makes
    "first x − run" equal minus both x's (`−2 = 1` in GF(3), the same line).
    An empty run is `none` (the secant is not defined). This is not a tangent
    formula; SPEC.md does not give one. -/
def chordAdd (n k bench : Nat) (p q : List Nat × List Nat) : Option (List Nat × List Nat) :=
  let run := fieldSub n q.1 p.1
  match specInv n k bench run with
  | none => none
  | some inv =>
    let rise := fieldSub n q.2 p.2
    let slope := fieldMul n k bench rise inv
    let slope2 := fieldMul n k bench slope slope
    let x3 := fieldAdd n (fieldAdd n (fieldAdd n slope2 (whiteHole0 n)) p.1) (mirrorTrits run)
    let y3 := fieldSub n (fieldMul n k bench slope (fieldSub n p.1 x3)) p.2
    some (x3, y3)

/-- Frobenius on an affine point: cube each coordinate. SPEC.md §3 R5 line 138. -/
def pointCube (n k bench : Nat) (p : List Nat × List Nat) : List Nat × List Nat :=
  (fieldCube n k bench p.1, fieldCube n k bench p.2)

/-- SPEC.md §3 R8 lines 158–159, one key cell.
    While the accumulator is empty, Frobenius is skipped and the first non-empty
    cell copies the base point (mirrored when the cell is red). After that, every
    cell cubes the accumulator, and a white cell adds the base point, a red cell
    adds its negative. Any other trit is `none`. -/
def walkStep (n k bench : Nat) (base : List Nat × List Nat) (live : Bool)
    (acc : List Nat × List Nat) (c : Nat) : Option (Bool × (List Nat × List Nat)) :=
  let acc := if live then pointCube n k bench acc else acc
  if c = 0 then some (live, acc)
  else if c ≠ 1 ∧ c ≠ 2 then none
  else
    let y := if c = 2 then mirrorTrits base.2 else base.2
    let addend := (base.1, y)
    if live then
      match chordAdd n k bench acc addend with
      | none => none
      | some s => some (true, s)
    else some (true, addend)

/-- The cells of one walk, reading order, hole 0 first. -/
def walkGo (n k bench : Nat) (base : List Nat × List Nat) :
    Bool → List Nat × List Nat → List Nat → Option (List Nat × List Nat)
  | _, acc, [] => some acc
  | live, acc, c :: cs =>
    match walkStep n k bench base live acc c with
    | none => none
    | some (live', acc') => walkGo n k bench base live' acc' cs

/-- White, red, white, red. SPEC.md §5.1 lines 193 and 196:
    `τ³ − τ² + τ − 1 = 5`. The first cell is the `τ³` term. -/
def cofactorCells : List Nat := [1, 2, 1, 2]

/-- That walk on the root `R`, which SPEC.md §5.1 line 196 calls `5R`.
    Demo performs it by the chord rule and the other tiers by the F-form
    (SPEC.md §3 R7 lines 147–156) and then clears the denominator
    (SPEC.md §3 R8 line 159). Both are this affine result. -/
def cofactorWalk (n k bench : Nat) (root : List Nat × List Nat) : Option (List Nat × List Nat) :=
  walkGo n k bench root false (whiteHole0 n, whiteHole0 n) cofactorCells

/-- SPEC.md §5.1 lines 191–198. `some (x, y)` is the base point; `none` means
    no hole from 1 to `n − 1` hit, or the cofactor walk's run was empty. -/
def basePoint (t : Tier) : Option (List Nat × List Nat) :=
  match searchRoot t.n t.k t.benchlen t.n 1 with
  | none => none
  | some root => cofactorWalk t.n t.k t.benchlen root

/-- On every published tier the card's trit list is `(3^n + 1) / 4`
    (SPEC.md §5.1 line 195). Kernel evaluation, not a search. -/
theorem demo_rootDigits : digitsValue (rootDigits 7) = rootExpNat 7 := by decide

theorem toy_rootDigits : digitsValue (rootDigits 23) = rootExpNat 23 := by decide

theorem hobby_rootDigits : digitsValue (rootDigits 59) = rootExpNat 59 := by decide

theorem specRungsGo_eq (fuel c : Nat) (h : c ≤ fuel) :
    specRungsGo fuel c = rungList c := by
  induction fuel using Nat.strongRecOn generalizing c with
  | ind fuel ih =>
    cases fuel with
    | zero =>
      have hc : c = 0 := Nat.eq_zero_of_le_zero h
      subst hc
      unfold specRungsGo
      exact (rungList_le (Nat.zero_le 1)).symm
    | succ fuel =>
      unfold specRungsGo
      by_cases hc : c ≤ 1
      · rw [if_pos hc, rungList_le hc]
      · have hlt : 1 < c := by omega
        rw [if_neg hc, rungList_gt hlt]
        apply congrArg (fun t => rungColour c :: t)
        apply ih fuel (Nat.lt_succ_self fuel) (c / 2)
        have hdiv : c / 2 < c := Nat.div_lt_self (by omega) (by decide)
        omega

theorem specRungs_eq (c : Nat) : specRungs c = rungList c :=
  specRungsGo_eq (c + 1) c (Nat.le_succ c)

/-- The evaluating inverse is R6 (`fieldInv`). -/
theorem specInv_eq (n k bench : Nat) (x : List Nat) :
    specInv n k bench x = fieldInv n k bench x := by
  unfold specInv fieldInv invGapOf invGap whiteHole0
  rw [specRungs_eq]

theorem searchRoot_zero (n k bench j : Nat) : searchRoot n k bench 0 j = none := rfl

/-- A hit at the hole under test is the first hit. Later holes are not read. -/
theorem searchRoot_hit (n k bench fuel j : Nat) (hj : j < n)
    (hh : rootHit n k bench (basisPeg n j) = true) :
    searchRoot n k bench (fuel + 1) j =
      some (basisPeg n j, rootY n k bench (basisPeg n j)) := by
  unfold searchRoot
  rw [if_pos hj]
  dsimp only
  rw [if_pos hh]

/-- A miss moves the white peg one hole on. SPEC.md §5.1 line 193. -/
theorem searchRoot_miss (n k bench fuel j : Nat) (hj : j < n)
    (hh : rootHit n k bench (basisPeg n j) = false) :
    searchRoot n k bench (fuel + 1) j = searchRoot n k bench fuel (j + 1) := by
  have hne : ¬ rootHit n k bench (basisPeg n j) = true := by
    rw [hh]
    decide
  have hdef : searchRoot n k bench (fuel + 1) j =
      (if j < n then
        let x := basisPeg n j
        if rootHit n k bench x then some (x, rootY n k bench x)
        else searchRoot n k bench fuel (j + 1)
      else none) := rfl
  rw [hdef, if_pos hj]
  dsimp only
  rw [if_neg hne]

theorem searchRoot_past (n k bench fuel j : Nat) (hj : ¬ j < n) :
    searchRoot n k bench (fuel + 1) j = none := by
  unfold searchRoot
  rw [if_neg hj]

/-- Hole 1 is the first hole the search tries. A hit there is the root,
    and the base point is the cofactor walk of that root. -/
theorem basePoint_at1 (t : Tier) (hn : 1 < t.n)
    (hh : rootHit t.n t.k t.benchlen (basisPeg t.n 1) = true) :
    basePoint t =
      cofactorWalk t.n t.k t.benchlen
        (basisPeg t.n 1, rootY t.n t.k t.benchlen (basisPeg t.n 1)) := by
  have hsr := searchRoot_hit t.n t.k t.benchlen (t.n - 1) 1 hn hh
  have hfuel : (t.n - 1) + 1 = t.n := by omega
  simp only [hfuel] at hsr
  unfold basePoint
  rw [hsr]

/-- SPEC.md §3 R7 line 149. The run `v = x₂Z − X`. -/
def fformRun (n k bench : Nat) (x2 z x : List Nat) : List Nat :=
  fieldAdd n (mirrorTrits x) (fieldMul n k bench x2 z)

/-- SPEC.md §3 R7 line 150. The rise `u = y₂Z − Y`. A red cell passes `−y₂`. -/
def fformRise (n k bench : Nat) (y2 z y : List Nat) : List Nat :=
  fieldAdd n (mirrorTrits y) (fieldMul n k bench y2 z)

/-- SPEC.md §3 R7 line 151. The gap `F = u²Z + v²(v + Z)`. -/
def fformF (n k bench : Nat) (u v z : List Nat) : List Nat :=
  let u2 := fieldMul n k bench u u
  let v2 := fieldMul n k bench v v
  fieldAdd n (fieldMul n k bench u2 z)
    (fieldMul n k bench v2 (fieldAdd n v z))

/-- SPEC.md §3 R7 line 152. The new bottom `v · (v²Z)`. -/
def fformBottom (n k bench : Nat) (v z : List Nat) : List Nat :=
  fieldMul n k bench v (fieldMul n k bench (fieldMul n k bench v v) z)

/-- SPEC.md §3 R7 line 153. The new across `v·F + x₂·Z₃`. -/
def fformAcross (n k bench : Nat) (x2 u v z : List Nat) : List Nat :=
  fieldAdd n (fieldMul n k bench v (fformF n k bench u v z))
    (fieldMul n k bench x2 (fformBottom n k bench v z))

/-- SPEC.md §3 R7 line 154. The new up `−(u·F + y₂·Z₃)`. -/
def fformUp (n k bench : Nat) (y2 u v z : List Nat) : List Nat :=
  mirrorTrits (fieldAdd n
    (fieldMul n k bench u (fformF n k bench u v z))
    (fieldMul n k bench y2 (fformBottom n k bench v z)))

end EcbsLink2.Spec

