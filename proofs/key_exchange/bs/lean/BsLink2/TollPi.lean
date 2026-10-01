/-
  §2.3: the T6 toll against the ternary digits of π.

  SPEC §2.3: a long toll is `c = π_t + j`, where `π_t` is the integer whose base-3 digits
  are the first `t` ternary digits of π, and T6 has `c = π₅₀ + 4383`. Since
  π = 10.0102…₃ has two digits before the point, `π₅₀ = ⌊π · 3^48⌋`.

  What is checked here, by `decide` on natural numbers (no `native_decide`):
  * `T6.toll` is the 50-hole register of `pi50 + 4383` (`T6_toll_eq`);
  * `pi50 ≤ 3^48 · L` and `3^48 · U < pi50 + 1`, for two explicit rationals `L < U`
    (`pi50_le_lower`, `upper_lt_pi50_succ`), so every real in `[L, U]` has
    `⌊x · 3^48⌋ = pi50`;
  * the leading digits of `pi50` are those SPEC §2.3 quotes, 1 0 0 1 0 2 1 1 0 1 2 2.

  `L` and `U` are Machin's formula `π = 16·arctan(1/5) − 4·arctan(1/239)` with each
  arctan replaced by a partial sum of its Gregory series `Σ (−1)^i / ((2i+1)·x^(2i+1))`:
  `L` takes 16 terms for 1/5 (a lower bound) and 17 for 1/239 (an upper bound), `U` the
  other way round. **That `L ≤ π ≤ U` is cited, not proved**: core Lean has no real
  numbers, so Machin's identity and the alternating-series bound are classical facts this
  file relies on in its prose only. No hypothesis or axiom about π enters any theorem.

  Not checked: that `j = 4383` is the *smallest* offset making `p` a safe prime
  (`reference/bsparams.py` does that search).
-/
import BsLink2.Spec

namespace BsLink2.Spec.TollPi

/-- A non-negative rational `num / den`. -/
structure Q where
  num : Nat
  den : Nat

def Q.add (a b : Q) : Q := ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

def Q.scale (k : Nat) (a : Q) : Q := ⟨k * a.num, a.den⟩

/-- The `i`-th Gregory term of `arctan(1/x)` without its sign: `1 / ((2i+1)·x^(2i+1))`. -/
def term (x i : Nat) : Q := ⟨1, (2 * i + 1) * x ^ (2 * i + 1)⟩

/-- The first `k` Gregory terms of `arctan(1/x)`, split into the sum of the positive terms
    (even `i`) and the sum of the negative ones (odd `i`). -/
def gregory (x : Nat) : Nat → Q × Q
  | 0 => (⟨0, 1⟩, ⟨0, 1⟩)
  | k + 1 =>
    let pn := gregory x k
    if k % 2 = 0 then (pn.1.add (term x k), pn.2) else (pn.1, pn.2.add (term x k))

/-- The lower Machin bound `L = A − B`: 16 terms for 1/5, 17 for 1/239. -/
def lowerA : Q := ((gregory 5 16).1.scale 16).add ((gregory 239 17).2.scale 4)
def lowerB : Q := ((gregory 5 16).2.scale 16).add ((gregory 239 17).1.scale 4)

/-- The upper Machin bound `U = A − B`: 17 terms for 1/5, 16 for 1/239. -/
def upperA : Q := ((gregory 5 17).1.scale 16).add ((gregory 239 16).2.scale 4)
def upperB : Q := ((gregory 5 17).2.scale 16).add ((gregory 239 16).1.scale 4)

/-- `π₅₀` as SPEC §2.3 defines it: T6's toll value minus the offset 4383. -/
def pi50 : Nat := 250593671573291099987359

/-- T6's toll is the 50-hole register of `π₅₀ + 4383` (hole 0 least significant). -/
theorem T6_toll_eq : T6.toll = toReg 50 (pi50 + 4383) := by decide

theorem T6_toll_value : value T6.toll = pi50 + 4383 := by decide

/-- `π₅₀ / 3^48 ≤ L`, i.e. `π₅₀ · A.den · B.den + B.num · A.den · 3^48 ≤ A.num · B.den · 3^48`
    for `L = A − B`. -/
theorem pi50_le_lower :
    pi50 * lowerA.den * lowerB.den + lowerB.num * lowerA.den * 3 ^ 48 ≤
      lowerA.num * lowerB.den * 3 ^ 48 := by decide

/-- `U < (π₅₀ + 1) / 3^48`, for `U = A − B`. -/
theorem upper_lt_pi50_succ :
    upperA.num * upperB.den * 3 ^ 48 <
      (pi50 + 1) * upperA.den * upperB.den + upperB.num * upperA.den * 3 ^ 48 := by decide

/-- The bracket is non-trivial: `L < U`. -/
theorem lower_lt_upper :
    lowerA.num * lowerB.den * (upperA.den * upperB.den) +
        upperB.num * upperA.den * (lowerA.den * lowerB.den) <
      upperA.num * upperB.den * (lowerA.den * lowerB.den) +
        lowerB.num * lowerA.den * (upperA.den * upperB.den) := by decide

/-- The first twelve ternary digits of `π₅₀`, most significant first, are SPEC §2.3's
    `π = 10.0102110122…₃`. -/
theorem pi50_leading_digits :
    ((toReg 50 pi50).reverse.take 12) = [1, 0, 0, 1, 0, 2, 1, 1, 0, 1, 2, 2] := by decide

/-- `π₅₀` has exactly 50 ternary digits (its top digit is not 0). -/
theorem pi50_bounds : 3 ^ 49 ≤ pi50 ∧ pi50 < 3 ^ 50 := by decide

end BsLink2.Spec.TollPi
