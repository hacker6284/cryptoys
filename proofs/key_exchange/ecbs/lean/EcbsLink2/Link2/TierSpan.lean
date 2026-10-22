/-
  Room for a schoolbook product and for a comb on each shipped tier.
  `2 * (n - 1) < bench` is the reach `fieldMul` folds. `3 * (n - 1) < bench`
  is the reach `fieldCube` uses to lay peg `i` at hole `3 * i`. Both are
  tier parameters, discharged by `decide`. Proof-only. Not a security claim.
-/
import EcbsLink2.Spec

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem demo_mul_span : 2 * (demo.n - 1) < demo.benchlen := by decide
theorem demo_cube_span : 3 * (demo.n - 1) < demo.benchlen := by decide

theorem toy_mul_span : 2 * (toy.n - 1) < toy.benchlen := by decide
theorem toy_cube_span : 3 * (toy.n - 1) < toy.benchlen := by decide

theorem hobby_mul_span : 2 * (hobby.n - 1) < hobby.benchlen := by decide
theorem hobby_cube_span : 3 * (hobby.n - 1) < hobby.benchlen := by decide

theorem serious_mul_span : 2 * (serious.n - 1) < serious.benchlen := by decide
theorem serious_cube_span : 3 * (serious.n - 1) < serious.benchlen := by decide

end EcbsLink2.Link2
