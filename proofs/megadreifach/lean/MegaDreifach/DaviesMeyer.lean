/-
  M6 — Davies–Meyer algebra and the LOCKED 3-solve invariant.
  Software: `h' = compose h (E_m h)`.
  Hand: puzzles A=h, B=h⁻¹, C=id restore (A,B,C)=(h', h'⁻¹, id).
  Zero sorry. No native_decide.
-/
import MegaDreifach.Group

namespace MegaDreifach

/-- Software DM: `h' = h ∘ E_m(h) = compose h e`. -/
def daviesMeyer (h e : Position) : Position := compose h e

theorem daviesMeyer_def (h e : Position) : daviesMeyer h e = compose h e := rfl

/-- Pair of mutual inverses (DoubleDeal-style: hypothesized bijections). -/
def isInverse (g inv : Position) : Prop :=
  compose g inv = identity ∧ compose inv g = identity

theorem isInverse_symm {g inv : Position} (h : isInverse g inv) : isInverse inv g :=
  ⟨h.2, h.1⟩

/-- Between-block 3-puzzle state. -/
structure Triple where
  A : Position
  B : Position
  C : Position

/-- Invariant: `(A,B,C) = (h, h⁻¹, id)`. -/
def tripleInvariant (t : Triple) (h hInv : Position) : Prop :=
  t.A = h ∧ t.B = hInv ∧ t.C = identity ∧ isInverse h hInv

/-- Start of a block: A holds `h`, B holds `h⁻¹`, C is solved. -/
def startTriple (h hInv : Position) : Triple :=
  { A := h, B := hInv, C := identity }

theorem startTriple_invariant (h hInv : Position) (hinv : isInverse h hInv) :
    tripleInvariant (startTriple h hInv) h hInv :=
  ⟨rfl, rfl, rfl, hinv⟩

/--
  LOCKED 3-solve schedule (HAND.md), algebraic form:

  1. Run `E_m` on A. Now A holds `e = E_m(h)`.
  2. Solve B (moves = left-multiply by `h`, since B = `h⁻¹`), copy onto A.
     A becomes `compose h e = h'`. B becomes identity.
  3. Solve A (moves = left-multiply by `h'⁻¹`), copy onto B and C.
     A becomes identity; B and C hold `h'⁻¹`.
  4. Solve C (moves = left-multiply by `h'`), copy onto A.
     `(A,B,C) = (h', h'⁻¹, id)`.
-/
def threeSolve (h hInv e hPrimeInv : Position) : Triple :=
  -- step 1
  let A1 := e
  let B1 := hInv
  let C1 := identity
  -- step 2: solve B onto A  (inverse of B is h)
  let A2 := compose h A1
  let B2 := compose h B1
  let C2 := C1
  -- step 3: solve A onto B and C  (inverse of A2 is hPrimeInv)
  let A3 := compose hPrimeInv A2
  let B3 := compose hPrimeInv B2
  let C3 := compose hPrimeInv C2
  -- step 4: solve C onto A  (inverse of C3 is h' = compose h e)
  let h' := compose h e
  let A4 := compose h' A3
  let B4 := B3
  let C4 := compose h' C3
  { A := A4, B := B4, C := C4 }

/-- M6: after the 3-solve, `(A,B,C) = (h', h'⁻¹, id)`. -/
theorem threeSolve_restores (h hInv e hPrimeInv : Position)
    (hinv : isInverse h hInv)
    (h'inv : isInverse (compose h e) hPrimeInv) :
    let h' := compose h e
    tripleInvariant (threeSolve h hInv e hPrimeInv) h' hPrimeInv := by
  -- Expand the schedule and rewrite with the inverse hypotheses.
  have h_hInv : compose h hInv = identity := hinv.1
  have h'_hPrimeInv : compose (compose h e) hPrimeInv = identity := h'inv.1
  have hPrimeInv_h' : compose hPrimeInv (compose h e) = identity := h'inv.2
  -- B2 = compose h hInv = id
  -- A2 = compose h e = h'
  -- A3 = compose hPrimeInv h' = id
  -- B3 = compose hPrimeInv id = hPrimeInv
  -- C3 = compose hPrimeInv id = hPrimeInv
  -- A4 = compose h' id = h'
  -- C4 = compose h' hPrimeInv = id
  constructor
  · -- A = h'
    simp [threeSolve, compose_id_right, compose_assoc, hPrimeInv_h']
  constructor
  · -- B = hPrimeInv
    simp [threeSolve, h_hInv, compose_id_right]
  constructor
  · -- C = id
    simp [threeSolve, compose_id_right, h'_hPrimeInv]
  · exact h'inv

/-- Software DM agrees with the A-register after step 2 of the hand schedule. -/
theorem daviesMeyer_eq_step2 (h e : Position) :
    daviesMeyer h e = compose h e := rfl

end MegaDreifach
