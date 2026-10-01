/-
  Axiom audit of the Scramble Link 2 package. Run by the shared gate
  `python3 ../../doubledeal/check_axioms.py scramble` (after `lake build`). Prints the
  axioms of EVERY theorem declared in a `ScrambleV2.*` module, private ones included,
  then `audited N`. The checker allows only propext, Classical.choice and Quot.sound;
  anything else (sorryAx, Lean.ofReduceBool from native_decide, a user axiom), an
  `axiom` declared in the package, or an unimported module fails.

  The MegaDreifach Link 2 runtime lemmas this package re-checks (library
  `MegaDreifachLink`, sources `../../megadreifach/lean/MegaDreifach/Link2/{Embed,Sudo,Loop}`)
  are not under this root; their own gate is `check_axioms.py megadreifach`.
  `#print axioms` is transitive, so every MegaDreifach lemma a `ScrambleV2` theorem uses
  is still in its report.
-/
import ScrambleV2
import AuditAll

#audit_all ScrambleV2
