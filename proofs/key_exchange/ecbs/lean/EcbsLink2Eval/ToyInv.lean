/-
  The run's inverse on the first Toy chord. One kernel evaluation of R6.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Spec

theorem toy_run_inv :
    specInv 23 15 72
        [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
      some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0] := by
  set_option maxRecDepth 8192 in decide

end EcbsLink2.Spec
