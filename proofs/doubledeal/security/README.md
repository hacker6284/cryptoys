# DoubleDeal security theorems (draft)

Separate Lake package so the refinement package (`../lean`) and `Generated/`
stay dependency-free. Requires Mathlib `v4.14.0` (rev `4bbdccd9`, pinned in
`lake-manifest.json`, matching `leanprover/lean4:v4.14.0`) and `../lean` as a
path dependency.

    lake exe cache get                  # prebuilt Mathlib; never build Mathlib from source
    lake build
    python3 ../check_axioms.py security # audits EVERY DoubleDealSecurity theorem
    python3 checks/scan_sorry.py --selftest && python3 checks/scan_sorry.py  # no admit/native_decide/sorryAx/axiom; sorry only in the conjecture
    python3 checks/selftest.py && python3 checks/check_relabel.py && python3 checks/check_covariant.py

## Layout

One library, `DoubleDealSecurity`. Most of it is about relabellings
`σ : Equiv.Perm (Fin 52)` of card values. `BranchNumber` is separate: the
trivial branch-number floor on decks, and the GridCycle tail swap that attains it.

| Module | Content |
|---|---|
| `Decks` | named cards, witness decks, the cell-map interface |
| `Relabel` | relabellings, decks, commuting/covariance notions |
| `SumRanks` | SumRanks commutes iff σ is a constant weight shift; v8 rank-preserving; the 52-element v9 group `v9Sym` |
| `Walk` | the GridCycle seat walk, generic in the seat chooser |
| `GridCycle` | GridCycle commutes only with σ = 1 (v9 and the frozen v8 model) |
| `BranchNumber` | trivial branch-number floor (`≥ 4` for any deck bijection); GridCycle attains it by swapping walk cards 50 and 51 (v9 and the frozen v8 model). Not a wide-trail bound |
| `Rounds` | lifting to rounds/encrypt; stem onto decks; the conjecture; degenerate-key side lemma |
| `PermKeys` | encrypt with permutation round keys reduces to the conjecture |
| `Link` | Link 2 transfer to the emitted `Doubledeal.encrypt`, K♣↔K♦ witness |
| `V8Vectors` | frozen v8 vectors checked against the v8 model (generated, `--check`) |

Generic list/rotation lemmas live in the Mathlib-free core package
(`../lean/DoubleDeal/SumRanks.lean`, `Rotate.lean`).

## Status and gates

T1 is a draft. The only open statement is the covariant round conjecture
`roundBody_covariant_iff_id` (marked `DRAFT-SORRY`, checked numerically by
`checks/check_covariant.py`); `fullRound_commutes_iff_id` and the
permutation-key `encrypt6_commutes_iff_id` rest on it.

CI (`proofs.yml`, job `doubledeal-security`) enforces, by exact name:
- `checks/scan_sorry.py`: `sorry` only in `roundBody_covariant_iff_id`; no
  `admit`, `native_decide`, `sorryAx` or `axiom` declarations anywhere. A sorry
  counts for its top-level declaration (inside `have` too); `let rec` and `where`
  items count under their own name `top.f`, as Lean and the axiom gate name them.
  `--selftest` checks these cases.
- `../check_axioms.py security` runs `Axioms.lean`, whose `#audit_all` reports
  the axioms of every theorem declared in a `DoubleDealSecurity.*` module. Only
  propext, Classical.choice and Quot.sound are allowed, except `sorryAx` for
  the three KNOWN_SORRY theorems above. Any axiom declared in the package fails,
  and so does a stale KNOWN_SORRY entry.

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
