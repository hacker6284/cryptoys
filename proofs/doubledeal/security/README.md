# DoubleDeal security theorems (draft)

Separate Lake package so the refinement package (`../lean`) and `Generated/`
stay dependency-free. Requires Mathlib `v4.14.0` (rev `4bbdccd9`, pinned in
`lake-manifest.json`, matching `leanprover/lean4:v4.14.0`) and `../lean` as a
path dependency.

    lake exe cache get                  # prebuilt Mathlib; never build Mathlib from source
    lake build
    python3 ../check_axioms.py security # audits EVERY DoubleDealSecurity theorem
    lake build DoubleDealSecurityHeavy AuditAll                   # heavy witnesses, ~10 min (five decide! encryptions + GridCycle survival checks)
    python3 ../check_axioms.py security-heavy                      # audits EVERY heavy theorem
    python3 checks/scan_sorry.py --selftest && python3 checks/scan_sorry.py  # no admit/native_decide/sorryAx/axiom; sorry only in the conjecture
    python3 checks/selftest.py && python3 checks/check_relabel.py && python3 checks/check_covariant.py

## Layout

Two libraries: `DoubleDealSecurity` (the default target) and
`DoubleDealSecurityHeavy` (kernel witnesses taking minutes; not a default target,
so a plain `lake build` skips it). Most of the code is about relabellings
`σ : Equiv.Perm (Fin 52)` of card values. `BranchNumber` is separate: the
trivial branch-number floor on decks, and the GridCycle tail swap that attains it.

| Module | Content |
|---|---|
| `Decks` | named cards, witness decks, the cell-map interface |
| `Relabel` | relabellings, decks, commuting/covariance notions |
| `SumRanks` | **deprecated v8/v9 models.** Two-weight SumRanks commutes iff σ is a constant weight shift; v8 rank-preserving; the 52-element v9 group `v9Sym` |
| `SumRanksV10` | v10 SumRanks commutes with every `v10Sym a x` (rank + a mod 13, GF(4) suit label ⊕ x; 52 elements, ℤ/13 × (ℤ/2)², not cyclic): `sumRanksV10_commutes_v10Sym` ("if", on every card-valued grid) |
| `SumRanksV10Iff` | the converse and the full characterisation `sumRanksV10_commutes_iff`: σ commutes with v10 SumRanks on every deck iff σ = `v10Sym a x` for some a, x. Proof: the chained steps are one row rotation then one column rotation (`sumRanksChain_eq`); commuting on a deck forces equal amounts; two decks differing in the last card of row 0 force a constant rank shift mod 13, and two differing in the top card of column 1 force a constant suit-label shift. Like v9's `sumRanks_commutes_iff` |
| `Walk` | the GridCycle seat walk, generic in the seat chooser |
| `GridCycle` | GridCycle commutes only with σ = 1 (live v11 walk, kept in v12, re-checked after the v11 GridCycle change; earlier proved for v9/v10 and still for the frozen v8 model) |
| `BranchNumber` | trivial branch-number floor (`≥ 4` for any deck bijection); GridCycle attains it by swapping walk cards 50 and 51 (live v11 GridCycle and the frozen v8 model; the tail argument uses only that the chooser picks a free seat). Not a wide-trail bound |
| `Rounds` | lifting to rounds/encrypt (hypotheses now `CommutesG σ sumRanksV10`); stem onto decks; the conjecture; degenerate-key side lemma |
| `PermKeys` | encrypt with permutation round keys reduces to the conjecture; `encrypt6_not_commutes_v10Sym` (was `…_v9Sym`) |
| `Link` | Link 2 transfer to the emitted `Doubledeal.encrypt` (v12), K♣↔K♦ witness (re-checked on v10, v11 and v12) |
| `V8Vectors` | frozen v8 vectors checked against the v8 model (generated, `--check`) |
| `RealKey` | commuting relabellings closed under powers; every nontrivial `v10Sym a x` has a power equal to one of four witnesses `v10Sym 1 0`, `v10Sym 0 1`, `v10Sym 0 2`, `v10Sym 0 3` (v9 needed two; `v10Sym` is not cyclic); pull-back from the emitted `encrypt` |
| `SumRanksDP.Standalone`, `SumRanksDP.Decomp`, `SumRanksDP.Main` | **v10 SumRanks survival bound** `sumRanksV10_survival_le` (and `…'`): every relabelling outside `v10Sym` commutes with v10 SumRanks on at most `52!/64` of the `52!` decks. SumRanks alone, one layer; not a statement about keyed rounds or the cipher. Counting proof (row/column chains, Cases A and B, hypergeometric counts, tables A and B by kernel `decide!`, each ≤ ~1.5 s). Lemma map: `SUMRANKS_DP.md`; paper proof: `sumranks-dp-paper/PROOF.md` |
| `GridCycleSurvival` | **GridCycle relabelling survival** (roadmap milestone M1, see [Roadmap](#roadmap); `../analysis/v12-diffusion/NOTES.md`): τ survives GridCycle at deck π iff `mixColumns (τ·π) = τ·mixColumns π`. Proved for every τ: `52 · #survivors ≤ #gcExc τ · 52!` (first-card argument; `gcExc` = fixed points plus K♣/K♠); fixed-point-free τ ≤ `52!/26`; 50 of the 51 nontrivial `v10Sym` survive on no deck; `v10Sym 0 3` ≤ `52!/26`, and ≤ `52!/4420` **given** the two finite checks `Check3 KC LKC`, `Check3 KS LKS` as hypotheses (`…_of_check`). GridCycle alone, one layer; not a trail bound for τ outside `v10Sym`, and not a statement about the cipher |
| `TrailBound` | **multi-round characteristic bound under INDEPENDENT UNIFORM round keys** (roadmap milestone M2; `../analysis/v12-trail/NOTES.md`). `Trail σ R y K`: in every one of R rounds (Compose with `K i`, then the unkeyed round), SumRanks and GridCycle both commute with σ. Counting over all `(52!)^R` key tuples, from every deck y: `trail_card_le_26` (σ ≠ 1, unconditional) `26^R · # ≤ (52!)^R`; `trail_card_le_64_of_not_v10Sym` `64^R`; `trail_card_le_64_of_check` (σ ≠ 1, given the GridCycle checks) `64^R`. One characteristic, not a differential. Says nothing about the real PassKey schedule. No final no-mix round |
| `SwapMechanism` | deck-by-deck SumRanks commutation; a swap of two cards with equal (rank + suit) mod 4 commutes with v9 SumRanks on every deck where they share a row (the mechanism of the K♣↔Q♥ distinguisher, `proofs/deprecated/doubledeal-v9/`). **Deprecated-v9 model**; kept as the proof of the v9 mechanism, not a statement about v10 |
| `DoubleDealSecurityHeavy.RealKey` | five `decide!` encryptions of the emitted v12 `encrypt` under the identity master key (expected values regenerated for v12, whose key schedule changed) (the message and its images under the four witnesses); `generated_encrypt_realKey_not_v10Sym_equivariant` |
| `DoubleDealSecurityHeavy.GridCycleSurvival` | kernel `decide!` of `Check3 KC LKC` / `Check3 KS LKS` (8 chunks of 13 × 52 first-three-seat evaluations, ~30 s each), hence unconditional `gc_survival_v10Sym03_le` / `gc_survival_v10Sym_le`: every nontrivial `v10Sym a x` survives GridCycle on at most `52!/4420` decks |
| `DoubleDealSecurityHeavy.TrailBound` | unconditional `trail_card_le_64` (every σ ≠ 1) and `trail_card_le_4420_v10Sym`, from the kernel-checked GridCycle checks; same model and caveats as `TrailBound` |

Generic list/rotation lemmas live in the Mathlib-free core package
(`../lean/DoubleDeal/SumRanks.lean`, `SumRanksV10.lean`, `Rotate.lean`).

## Roadmap

The AES-style argument (SPEC.md §6, row S15), as milestones. "Proved" means a Lean
theorem in this package, audited as above; no item is a security claim.

| Milestone | Status | Where |
|---|---|---|
| M1. GridCycle relabelling survival (the diffusion notion) | **Done.** Proved: 50 of the 51 nontrivial `v10Sym` survive GridCycle on no deck; `v10Sym 0 3` on ≤ 1/26 (default library) and ≤ 1/4420 (heavy library; default library given the two finite checks). The Hamming branch number is the trivial floor 4 | `GridCycleSurvival`, `DoubleDealSecurityHeavy.GridCycleSurvival`, `../analysis/v12-diffusion/NOTES.md` |
| M2. Multi-round trail bound | **Done, in the independent-uniform-round-key model only.** The constant-σ characteristic through R mix rounds has probability ≤ (1/64)^R for every σ ≠ 1 (heavy library; default library (1/26)^R, and (1/64)^R given the two finite checks). One characteristic, not a differential; no final no-mix round; not linked to `encryptN` | `TrailBound`, `DoubleDealSecurityHeavy.TrailBound`, `../analysis/v12-trail/NOTES.md` |
| M3. Linear-analogue note | **Note only, no Lean.** No linear analogue is defined; the note argues that no direct analogue exists for permutation-valued state and proposes Fourier analysis on `S_52`; one sampled single-card position statistic, at the noise level of its control | `../analysis/v12-linear/NOTES.md` |
| M4. Covariant round conjecture `roundBody_covariant_iff_id` | **In progress.** Open (`DRAFT-SORRY`); checked numerically by `checks/check_covariant.py` | `Rounds` |

Open, with no milestone yet:
- the real PassKey schedule (dependent round keys): nothing is proved about it;
- the full differential (the sum over characteristics, including σ → β for β ≠ σ);
- a whole-walk GridCycle bound for small-support relabellings (the proved first-card bound is ≈ 1 for them);
- the link from `rounds` to `encryptN`, and the final no-mix round.

## Status and gates

`generated_encrypt_realKey_not_v10Sym_equivariant` (heavy library; v9 had
`…_not_v9Sym_equivariant`): under ONE master key, the identity deck expanded
by the real PassKey chain, no nontrivial `v10Sym` commutes with the emitted
`encrypt`. Read it narrowly: one atypical key; the breaking message is shown
to exist, not named; the key is never relabelled; it excludes exact symmetry
only, not near-symmetries or statistical distinguishers (v8 and v9 each fell
to one); it is not the open per-key statement.
Measured near-symmetries of v10 SumRanks alone (empirical, not proved) are in
`../analysis/v10-sumranks/sbox-search/`: the worst measured non-symmetry
relabelling is a same-suit 3-cycle at exactly 9/1105 ≈ 1/123; the same-suit
swap is 1/221. Proved (`sumRanksV10_survival_le`, `SumRanksDP/Main.lean`): no
non-symmetry relabelling survives v10 SumRanks alone on more than 1/64 of the
decks. Also proved (`sumRanksV10_survival_threeCycle`,
`SumRanksDP/ThreeCycle.lean`): the one 3-cycle A♣→2♣→3♣ survives on exactly
9/1105 of the decks, so the 1/64 constant is within a factor 2 of tight
(`sumRanksV10_survival_lower`). That 9/1105 is the maximum over all
non-symmetries is computer-assisted (`sumranks-dp-paper/PROOF.md` §5b) and not
formalised.

Branch number and GridCycle survival (roadmap milestone M1, v12;
`../analysis/v12-diffusion/NOTES.md`). The Hamming branch number of GridCycle is
exactly the trivial floor 4 (proved, below), so no wide-trail bound comes from
it. The notion used instead is relabelling survival. Proved: the 50 nontrivial
`v10Sym` other than `v10Sym 0 3` never survive GridCycle, and `v10Sym 0 3`
survives on at most 1/4420 of the decks (heavy library; the default library
states it conditional on the finite check). Only measured: full GridCycle survival
(0 in 60000 sampled decks for `v10Sym 0 3` given its prefix; mean ≈ 0.0035 over
swaps). For relabellings outside `v10Sym`, the only proved GridCycle bound is the
first-card one, which is weak (≈ 1) for small-support relabellings.

Multi-round (roadmap milestone M2, `TrailBound`, `../analysis/v12-trail/NOTES.md`).
**Conditional on the model**: independent uniform round keys (built into the
counting over all key tuples), one constant-σ characteristic, and no final no-mix
round. In that model the characteristic has probability ≤ (1/64)^R for every
σ ≠ 1 (heavy library; the default library proves (1/26)^R unconditionally and
(1/64)^R given the finite check). Not proved: anything about the real PassKey
schedule, the differential (sum over characteristics), and σ → β for β ≠ σ.

Linear analogue (roadmap milestone M3): none is defined. Permutation-valued state
has no masks, and the note `../analysis/v12-linear/NOTES.md` explains why and
proposes Fourier analysis on `S_52` (the standard representation first). There are
no Lean statements for it.

`BranchNumber` has no `sorry`. Distinct decks differ in at least two seats, so
any map that sends decks to decks and separates them has branch number at
least 4. The live v11 GridCycle (as v9/v10 before it) and the frozen v8 model attain 4: swapping walk cards
50 and 51 changes exactly two output seats. That is the trivial floor, not a
bound above 4, and not a statement about SumRanks or keyed rounds.

T1 is a draft. The only open statement is the covariant round conjecture
`roundBody_covariant_iff_id` (marked `DRAFT-SORRY`, checked numerically by
`checks/check_covariant.py`); `fullRound_commutes_iff_id` and the
permutation-key `encrypt6_commutes_iff_id` rest on it.

CI (`proofs.yml`, job `doubledeal-security`) enforces, by exact name:
- `checks/scan_sorry.py`: `sorry` only in `roundBody_covariant_iff_id`; no
  `admit`, `admitGoal`, `native_decide`, `sorryAx`, `initialize` or `axiom` declarations anywhere. A sorry
  counts for its top-level declaration (inside `have` too); `let rec` and `where`
  items count under their own name `top.f`, as Lean and the axiom gate name them.
  `--selftest` checks these cases.
- `../check_axioms.py security` runs `Axioms.lean`, whose `#audit_all` (from the shared
  core-only package `../../audit`, required by path; MegaDreifach uses the same one) reports
  the axioms of every theorem declared in a `DoubleDealSecurity.*` module. Only
  propext, Classical.choice and Quot.sound are allowed, except `sorryAx` for
  the three KNOWN_SORRY theorems above. Any axiom declared in the package fails,
  and so does a stale KNOWN_SORRY entry. It does not import the heavy library, but it fails if the `HEAVY_THEOREMS`
  registry and the theorems declared in `DoubleDealSecurityHeavy/` disagree.
  The audit itself (`#audit_all`, in Lean) raises an error when a `.lean` file
  under its library directory (`DoubleDealSecurity/` here, `DoubleDealSecurityHeavy/`
  in the heavy mode) was not loaded by the environment, since the audit never saw
  it; any Lean error fails `check_axioms.py`. Lean decides what is imported, so
  commented-out imports cannot fool it. A private and a public theorem with the same user name also fail.
  The audit also raises `DUP n` for any non-private name declared under its root that
  more than one module declares, including an identical redeclaration of a Mathlib or
  core name (Lean 4.14 merges identical imported theorems silently). Reserved
  (auto-generated) names are skipped. `checks/audit_dup_selftest.py` (CI) builds
  throwaway modules (in a temporary copy of the packages, not the source tree) and requires exactly two DUPs (an identical `isDeck_mixColumns`, and
  a user-declared `zfxH.eq_1`) and none for the on-demand reserved `zfxF.eq_unfold` /
  `zfxF.induct`.

CI (`proofs-heavy.yml`, job `doubledeal-security-heavy`) builds the heavy library
and runs `../check_axioms.py security-heavy` (same rules, no KNOWN_SORRY; every
registered theorem must be reported) plus `scan_sorry.py`. It runs on PRs that
touch the security sources, the core/Generated Lean, `check_axioms.py`, `proofs/audit` or the
doubledeal sudo spec; on pushes to main; weekly; and on `workflow_dispatch`.

Both jobs (`doubledeal-security` and `doubledeal-security-heavy`) must be green
before merge (not enforced by branch protection): each audit checks only its own
library, so a stray module can fail just one of them.

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
  `measure_v9sym.log` (minutes; measurement only; v9).
- `checks/realkeys/v10sym_subgroup.py` re-checks the v10 witness reduction, SumRanks v10
  commutation on random decks and the heavy witness outputs (Python, seconds).
- `checks/branchnum/` holds the branch-number measurements (analysis only; see its
  `NOTES.md`). Runtimes on 8 cores: `measure.py` about 3-5 min, `structural.py` about
  2.5 min, the time-budgeted searches (`search.py`, `trail_search.py`) about 1 h wall
  time in total. CI only re-verifies the committed witnesses: `witnesses.py` must
  reproduce `witnesses.json` exactly.
