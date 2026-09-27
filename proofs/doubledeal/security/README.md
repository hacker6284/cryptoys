# DoubleDeal security theorems (draft)

Separate Lake package so the refinement package (`../lean`) and `Generated/`
stay dependency-free. Requires Mathlib `v4.14.0` (rev `4bbdccd9`, pinned in
`lake-manifest.json`, matching `leanprover/lean4:v4.14.0`) and `../lean` as a
path dependency.

    lake exe cache get      # prebuilt Mathlib; never build Mathlib from source
    lake build
    python3 check_axioms.py # standard axioms only; KNOWN_SORRY allowlist by name
    python3 checks/scan_sorry.py # sorry only in the allowlisted conjecture
    python3 checks/selftest.py && python3 checks/check_relabel.py

One library, `DoubleDealSecurity`: T1 relabellings `σ : Equiv.Perm (Fin 52)`
against Compose, ShiftRows, SumRanks, GridCycle, rounds and encrypt
(`Relabel.lean`, with the chooser-generic GridCycle walk in `Walk.lean`); the Link 2 transfer to the emitted `Doubledeal.encrypt`
(`Link.lean`); the proof-only v8 model checked against the frozen v8 vectors
(`V8Vectors.lean`).

T1 is a draft: `DRAFT-SORRY` marks statements that are checked numerically but
not yet proved (currently only the round/encrypt conjectures
`fullRound_commutes_iff_id` and `encrypt6_commutes_iff_id`). CI (`proofs.yml`,
job `doubledeal-security`) allows `sorry` only in `fullRound_commutes_iff_id`
and `sorryAx` only in that theorem and `encrypt6_commutes_iff_id`, by exact
name; any new sorry fails. A green run means the listed theorems check; it is
not a security claim.
`checks/measure_v9sym.py` (log committed) measures the v9Sym relabellings
against GridCycle, one round and the full cipher. Link 1 (sudo = Generated) remains open.
