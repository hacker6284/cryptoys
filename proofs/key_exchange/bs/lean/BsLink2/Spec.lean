/-
  BS: a hand-written model of the arithmetic of `primitives/key_exchange/bs/SPEC.md`
  (§2.3 parameters, §3 registers, B3 multiply, B5 tidy), written from the SPEC and not
  from `bs.sudo`. Numbers are `Nat`; a register is a `List Nat` of trits, hole 0 first,
  hole `i` worth `3^i` (§3). Nothing here is a security claim.
-/

namespace BsLink2.Spec

/-- §3. The value of a register: hole `i` is worth `3^i` (0 empty, 1 white, 2 red). -/
def value : List Nat → Nat
  | [] => 0
  | t :: ts => t + 3 * value ts

/-- §3. A register of `n` holes: `n` trits. -/
def IsReg (n : Nat) (x : List Nat) : Prop := x.length = n ∧ ∀ t ∈ x, t ≤ 2

/-- The register of `n` holes holding `v` (its `n` low base-3 digits, hole 0 first). -/
def toReg : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 3 :: toReg n (v / 3)

/-- §2.3. A field `p = 3^n − c`; the toll `c` is given as a register, hole 0 first. -/
structure Field where
  n : Nat
  toll : List Nat

/-- §2.3. The toll `c`. -/
def Field.c (F : Field) : Nat := value F.toll

/-- §2.3. The modulus `p = 3^n − c`. -/
def Field.p (F : Field) : Nat := 3 ^ F.n - F.c

/-- §2.3 / B4. The domain the recipes are stated for: the toll is a non-empty trit
    register of fewer than `n` trits (so `c < 3^(n−1)`; SPEC §2.3 "Every toll has fewer
    than n trits"). Primality of `p` is not assumed anywhere below. -/
structure Field.Wf (F : Field) : Prop where
  toll_trits : ∀ t ∈ F.toll, t ≤ 2
  toll_pos : 0 < F.toll.length
  toll_lt : F.toll.length < F.n

/-- B5. The tidy answer (canonical form) of a register: its value reduced mod `p`, as a
    register of `n` holes. -/
def tidy (F : Field) (x : List Nat) : List Nat := toReg F.n (value x % F.p)

/-- B3. What a product must be. The SPEC's fold (B4) fixes one representative below
    `3^n` of `A · B · 3^nudge` mod `p`, but not by a closed formula, so the model of
    `multiply` is this relation: a register of `n` trits, below `3^n`, congruent to
    `A · B · 3^nudge` mod `p`. -/
def MulResult (F : Field) (a b : List Nat) (nudge : Nat) (out : List Nat) : Prop :=
  IsReg F.n out ∧ value out < 3 ^ F.n ∧ value out % F.p = value a * value b * 3 ^ nudge % F.p

/-- §2.3 tier T1 (skiff): `p = 3^18 − 3^2 − 1`, toll white at holes 0 and 2. -/
def T1 : Field := ⟨18, [1, 0, 1]⟩

/-- §2.3 tier T2 (frigate): `p = 3^35 − 3^29 − 1`, toll white at holes 0 and 29. -/
def T2 : Field := ⟨35, [1] ++ List.replicate 28 0 ++ [1]⟩

/-- The SPEC §2.3 table's values of `p` for T1 and T2. -/
theorem T1_p : T1.p = 387420479 := by decide
theorem T2_p : T2.p = 49962914721634823 := by decide
theorem T1_p_formula : T1.p = 3 ^ 18 - 3 ^ 2 - 1 := by decide
theorem T2_p_formula : T2.p = 3 ^ 35 - 3 ^ 29 - 1 := by decide
theorem T1_wf : T1.Wf := ⟨by decide, by decide, by decide⟩
theorem T2_wf : T2.Wf := ⟨by decide, by decide, by decide⟩

end BsLink2.Spec

namespace BsLink2.Spec

/-- §3.1. The sender's answer to a called hole. -/
inductive Shot where
  | hit
  | miss
  | misfire
  deriving DecidableEq, Repr

/-- §3.1: red "Hit!", white "Miss!", empty "Misfire!". -/
def answer : Nat → Shot
  | 2 => .hit
  | 1 => .miss
  | _ => .misfire

/-- §3.1. Sending a public value `x`: the receiver calls every hole from 0 to `n − 1`
    (a fixed `n` calls) and copies each answer into the same hole of a cleared Y, so the
    answers are `x`'s holes read as shots and Y ends up holding `x`. -/
def sendPublicValue (x : List Nat) : List Shot × List Nat := (x.map answer, x)

end BsLink2.Spec

namespace BsLink2.Spec

/-- B7. The exponent a cell string encodes: the cells read as a base-3 number, first
    cell most significant (cells before the first white or red one contribute nothing). -/
def expOf (cells : List Nat) : Nat := cells.foldl (fun e c => 3 * e + c) 0

/-- B7, public phase: the tidy answer of the walk with `g = 3` over `cells`, i.e. the
    register holding `3^e mod p`. -/
def publicValue (F : Field) (cells : List Nat) : List Nat := toReg F.n (3 ^ expOf cells % F.p)

/-- B7, shared phase: the tidy answer of the walk with base `C` over `cells`, i.e. the
    register holding `C^e mod p`. -/
def sharedSecret (F : Field) (base cells : List Nat) : List Nat :=
  toReg F.n (value base ^ expOf cells % F.p)

end BsLink2.Spec
