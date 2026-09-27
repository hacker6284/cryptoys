# DoubleDeal security theorems (draft)

Separate Lake package so the refinement package (`../lean`) and `Generated/`
stay dependency-free. Requires Mathlib `v4.14.0` (rev `4bbdccd9`, pinned in
`lake-manifest.json`, matching `leanprover/lean4:v4.14.0`) and `../lean` as a
path dependency.

    lake exe cache get      # prebuilt Mathlib; never build Mathlib from source
    lake build
    python3 check_axioms.py # fails while any listed theorem uses sorryAx
    python3 checks/selftest.py && python3 checks/check_relabel.py

Two libraries:

- `DoubleDealSecurity` (Mathlib): T1 relabellings `σ : Equiv.Perm (Fin 52)`
  against Compose, ShiftRows, SumRanks, GridCycle, rounds, encrypt; the
  proof-only v8 model and its fidelity to the frozen v8 vectors (`V8Vectors`).
- `DoubleDealSecurityLink` (no Mathlib): the Link 2 transfer to the emitted
  `Doubledeal.encrypt`. It imports `DoubleDeal.Concrete`/`Link2`, whose
  `PassKey.lean` declares root `Function.LeftInverse`/`RightInverse` shims that
  clash with Mathlib, so it cannot share an environment with the Mathlib side.
  Its statements take any cell map `f` with `CardMap f`; `σ.app` is one
  (`Relabel.app_cardMap`).

T1 is a draft: `DRAFT-SORRY` marks statements that are checked numerically but
not yet proved. Link 1 (sudo = Generated) remains open.
