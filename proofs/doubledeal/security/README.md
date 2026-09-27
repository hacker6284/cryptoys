# DoubleDeal security theorems (draft)

Separate Lake package so the refinement package (`../lean`) and `Generated/`
stay dependency-free. Requires Mathlib `v4.14.0` (rev `4bbdccd9`, pinned in
`lake-manifest.json`, matching `leanprover/lean4:v4.14.0`) and `../lean` as a
path dependency.

    lake exe cache get                  # prebuilt Mathlib; never build Mathlib from source
    lake build
    python3 ../check_axioms.py security # audits EVERY DoubleDealSecurity theorem
    lake build DoubleDealSecurityHeavy DoubleDealSecurity.Audit   # heavy witnesses, ~2–3 min
    python3 ../check_axioms.py security-heavy                      # audits EVERY heavy theorem
    python3 checks/scan_sorry.py --selftest && python3 checks/scan_sorry.py  # no admit/native_decide/sorryAx/axiom; sorry only in the conjecture
    python3 checks/selftest.py && python3 checks/check_relabel.py && python3 checks/check_covariant.py

## Layout

Two libraries about relabellings `σ : Equiv.Perm (Fin 52)` of card values:
`DoubleDealSecurity` (the default target) and `DoubleDealSecurityHeavy`
(kernel witnesses taking minutes; not a default target, so a plain `lake build`
skips it).

| Module | Content |
|---|---|
| `Decks` | named cards, witness decks, the cell-map interface |
| `Relabel` | relabellings, decks, commuting/covariance notions |
| `SumRanks` | SumRanks commutes iff σ is a constant weight shift; v8 rank-preserving; the 52-element v9 group `v9Sym` |
| `Walk` | the GridCycle seat walk, generic in the seat chooser |
| `GridCycle` | GridCycle commutes only with σ = 1 (v9 and the frozen v8 model) |
| `Rounds` | lifting to rounds/encrypt; stem onto decks; the conjecture; degenerate-key side lemma |
| `PermKeys` | encrypt with permutation round keys reduces to the conjecture |
| `Link` | Link 2 transfer to the emitted `Doubledeal.encrypt`, K♣↔K♦ witness |
| `V8Vectors` | frozen v8 vectors checked against the v8 model (generated, `--check`) |
| `RealKey` | commuting relabellings closed under powers; every nontrivial `v9Sym` has a power `v9Sym 0 2` or `v9Sym 1 0`; pull-back from the emitted `encrypt` |
| `Audit` | the `#audit_all Root` command used by `Axioms.lean` / `AxiomsHeavy.lean` |
| `DoubleDealSecurityHeavy.RealKey` | three `decide!` encryptions under the identity master key; `generated_encrypt_realKey_not_v9Sym_equivariant` |

Generic list/rotation lemmas live in the Mathlib-free core package
(`../lean/DoubleDeal/SumRanks.lean`, `Rotate.lean`).

## Status and gates

`generated_encrypt_realKey_not_v9Sym_equivariant` (heavy library): under ONE
master key, the identity deck expanded by the real PassKey chain, no nontrivial
`v9Sym` commutes with the emitted `encrypt`. Read it narrowly: one atypical key;
the breaking message is shown to exist, not named; the key is never relabelled;
it excludes exact symmetry only, not near-symmetries or statistical
distinguishers (v8 fell to one); it is not the open per-key statement.

T1 is a draft. The only open statement is the covariant round conjecture
`roundBody_covariant_iff_id` (marked `DRAFT-SORRY`, checked numerically by
`checks/check_covariant.py`); `fullRound_commutes_iff_id` and the
permutation-key `encrypt6_commutes_iff_id` rest on it.

CI (`proofs.yml`, job `doubledeal-security`) enforces, by exact name:
- `checks/scan_sorry.py`: `sorry` only in `roundBody_covariant_iff_id`; no
  `admit`, `admitGoal`, `native_decide`, `sorryAx` or `axiom` declarations anywhere. A sorry
  counts for its top-level declaration (inside `have` too); `let rec` and `where`
  items count under their own name `top.f`, as Lean and the axiom gate name them.
  `--selftest` checks these cases.
- `../check_axioms.py security` runs `Axioms.lean`, whose `#audit_all` reports
  the axioms of every theorem declared in a `DoubleDealSecurity.*` module. Only
  propext, Classical.choice and Quot.sound are allowed, except `sorryAx` for
  the three KNOWN_SORRY theorems above. Any axiom declared in the package fails,
  and so does a stale KNOWN_SORRY entry. It does not import the heavy library, but it fails if the `HEAVY_THEOREMS`
  registry and the theorems declared in `DoubleDealSecurityHeavy/` disagree.
  `#audit_all` also prints every module under its root that Lean actually loaded,
  and each mode fails if a file under its library directory (`DoubleDealSecurity/`
  here, `DoubleDealSecurityHeavy/` in the heavy mode) was not loaded, since the
  audit never saw it. Lean decides what is imported, so commented-out imports
  cannot fool it. A private and a public theorem with the same user name also fail.

CI (`proofs-heavy.yml`, job `doubledeal-security-heavy`) builds the heavy library
and runs `../check_axioms.py security-heavy` (same rules, no KNOWN_SORRY; every
registered theorem must be reported) plus `scan_sorry.py`. It runs on PRs that
touch the security sources, the core/Generated Lean, `check_axioms.py` or the
doubledeal sudo spec; on pushes to main; weekly; and on `workflow_dispatch`.

So any new sorry, and any new theorem built on the conjecture, fails CI. A
green run means the theorems check as stated; it is not a security claim.
Link 1 (sudo = Generated) remains open.

## Notes

- The kernel `decide!` in `Link.lean` (the K♣↔K♦ witness on the emitted
  `encrypt`) takes about 50–80 s depending on the machine. Keep it `decide!`: do not switch it to
  `native_decide`, which would add `Lean.ofReduceBool` to the trusted base
  (and the gate rejects it).
- `checks/*.log` are committed snapshots of seeded runs, not CI-checked:
  `check_relabel.log` and `check_covariant.log` (seconds to rerun; CI reruns
  both scripts, and `check_covariant.py` exits non-zero if any sampled σ is
  covariant) and
  `measure_v9sym.log` (minutes; measurement only).
