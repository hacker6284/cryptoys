# DoubleDeal v12: GridCycle diffusion (roadmap milestone M1)

Roadmap: [`security/README.md`, section "Roadmap"](../../security/README.md#roadmap).

Scope. GridCycle (`mix_columns`, the v11 walk, unchanged in v12) **alone**, one layer.
Labels used below: **PROVED** = Lean, audited by `check_axioms.py`; **EXACT
(enumeration)** = exhaustive Python enumeration, not formalised; **MEASURED** =
random sampling with a fixed seed. Nothing here is a security or bit-security claim,
nothing proposes a change to the cipher, and a green build is not a security claim.

## 1. Which "diffusion" notion?

Two notions were considered. Only the second is useful to a trail argument.

### 1a. Hamming branch number (seat weight). Weak: equals the trivial floor 4.

`wt(d, d')` = number of seats where two decks differ; `B(F) = min over d ≠ d' of
wt(d, d') + wt(F d, F d')`. Two distinct decks differ in at least 2 seats, so
`B(F) ≥ 4` for every deck bijection F.

* **PROVED** (`DoubleDealSecurity/BranchNumber.lean`, since PR #84, re-checked for
  v11 and so for v12): the floor, and GridCycle attains it. Swapping walk cards 50
  and 51 changes exactly two output seats (`mixColumns_tail_branch`). So
  **B(GridCycle) = 4 exactly.**
* This is the weak minimum case: the branch number is the trivial floor. It is
  **not** a break. Every layer of DoubleDeal only moves cards, so weight 1 cannot
  occur and the AES scale does not transfer. Earlier measurements
  (`../../security/checks/branchnum/NOTES.md`, for v8/v9) found weight-2 → weight-2
  pairs for every layer and for one keyed round.
  So this line stops here: no Lean bound above 4 exists to prove.

### 1b. Relabelling (value-difference) survival. This is the notion the trail argument needs.

Write a deck as a permutation `π` (card `π k` at walk position `k`), and a
difference as a relabelling `τ` of the 52 card values (the pair is `(π, τ·π)`).
Say **τ survives layer F at π** iff `F(τ·π) = τ·F(π)`, i.e. the pair leaves F with
the same value difference τ. Then:

* Compose (the only keyed layer), ShiftRows and lay/scoop only move seats, so they
  commute with every τ on every deck (survival probability 1).
* SumRanks v10: τ ∈ `v10Sym` (52 elements) survives on every deck. Every τ ∉ `v10Sym`
  survives on at most `52!/64` decks (**PROVED**, `sumRanksV10_survival_le`, PR #93).
* GridCycle: τ survives at π iff the seat walk of `τ·π` equals that of `π`
  (**PROVED**, `mixColumns_rel_iff_walk`). The seat of walk card n depends only on
  the cards before it.

So the SumRanks bound fails exactly on the 51 nontrivial `v10Sym`. The question for
GridCycle is how rarely *those* survive. The answer is below.

## 2. What was enumerated (EXACT) — `prefix_survival.py`, log `prefix_survival.log`

`A_k(τ) = P_π[seat_n(τ·π) = seat_n(π) for all n < k]` over uniform π. Seat n depends
only on cards 0..n-1, so `A_k` is computed **exactly** by enumerating all
`52·51·…·(52-k+2)` ordered prefixes. Survival ≤ `A_k(τ)` for every k. The walker is
checked against `ddport.walk_v11` on 300 random decks (selfcheck).

Enumerated: the 51 nontrivial `v10Sym a x` (A_2, A_3; and A_4 for `v10Sym 0 3`), and
all 1326 value transpositions (A_2, A_3). Results:

| τ | A_2 | A_3 | A_4 |
|---|---|---|---|
| 50 nontrivial v10Sym other than `v10Sym 0 3` | 0 | 0 | – |
| `v10Sym 0 3` (♣↔♠, ♥↔♦, same rank) | 1/26 | 25/663 | **1/4420** (30 of 132600 triples) |
| transpositions (all 1326) | 25/26 … 1 (1 for K♣↔K♠) | 1225/1326 … 413/442 ≈ 0.934 | – |

The prefix bound is only strong for relabellings with few fixed points (the
v10Sym). For small-support τ such as transpositions it is close to 1. Those are
the τ that SumRanks' 1/64 already covers.

## 3. What was proved (PROVED) — `security/DoubleDealSecurity/GridCycleSurvival.lean`

Namespace `DoubleDeal.Security.GridCycleSurvival`. `GCSurvives τ π :=
mixColumns (rel τ (permDeck π)) = rel τ (mixColumns (permDeck π))`, and
`gcSurvivors τ` is the set of such π in `Equiv.Perm (Fin 52)`.

* `gcSurvivors_card_le τ : 52 * (gcSurvivors τ).card ≤ (gcExc τ).card * 52!`
  (`gcExc τ` = fixed points of τ, plus K♣/K♠ if τ exchanges them).
* `gc_survival_le_fixfree τ (h : ∀ c, τ c ≠ c) : 26 * (gcSurvivors τ).card ≤ 52!`.
* `gcSurvivors_v10Sym_eq_empty a x (hne : ¬(a = 0 ∧ x = 0)) (h03 : ¬(a = 0 ∧ x = 3)) :
  gcSurvivors (v10Sym a x) = ∅`.
* `gc_survival_v10Sym03 : 26 * (gcSurvivors (v10Sym 0 3)).card ≤ 52!`.
* Default library, **conditional** on two finite checks as hypotheses:
  `gc_survival_v10Sym03_le_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS) :
  4420 * (gcSurvivors (v10Sym 0 3)).card ≤ 52!`, and `gc_survival_v10Sym_le_of_check`
  (same bound for every nontrivial `v10Sym a x`).
* Heavy library (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`, kernel `decide!`
  in 8 chunks of ~30 s, ~2 min per check, ~4 min for the module in CI): `check3_KC`, `check3_KS`, and so, **unconditionally**,
  `gc_survival_v10Sym03_le : 4420 * (gcSurvivors (v10Sym 0 3)).card ≤ 52!` and
  `gc_survival_v10Sym_le a x hne : 4420 * (gcSurvivors (v10Sym a x)).card ≤ 52!`.
  The lists `LKC`/`LKS` (the 30 triples; `T03` is built from them) are generated
  from this enumeration into `DoubleDealSecurity/GridCycleSurvivalLists.lean` by
  `prefix_survival.py --lean`, and CI runs `prefix_survival.py --check`. The kernel
  re-checks them, so a wrong list fails the heavy build.

The Lean bounds match the EXACT values A_2 = 0, A_2 = 1/26 and A_4 = 1/4420 above.
They are upper bounds from a prefix of the walk. The true full survival is smaller
(next section).

## 4. Sampled full survival (MEASURED)

* `conditional_survival.py` → `conditional_survival.log`: for `v10Sym 0 3`, 2000
  random completions of each of the 30 surviving triples (60000 decks, seed
  20260929). **0 full survivals**; rule-of-three 95% bound 5e-5 on
  `P[full survival | prefix in T03]`. Every deck is tested two ways (equal walks,
  and `mix_columns` commutation in the v12 port), and the two must agree.
* `transposition_survival.py` → `transposition_survival.log`: all 1326 value
  transpositions on the same 2000 random decks. Mean full survival 0.0035, and the
  largest sampled estimate is 0.0085 (5♦↔8♦; the maximum of 1326 noisy estimates, so
  biased upwards: at 2000 decks one estimate near 0.005 has standard error ≈ 0.0016,
  so the largest of 1326 such estimates landing near 0.0085 is what noise alone
  would give). For comparison, the v11 selection measurement in `../v10-gridcycle/`
  reports a worst swap survival ≈ 0.0049. That is consistent with this run, but the
  two samplers were not reconciled here. These are **not** bounds and no theorem
  uses them.

## 5. Findings

* **Hamming branch number = 4 (trivial floor), attained.** Already proved (§1a).
  This is a weakness of the *notion* for card-moving layers, not an attack.
* **No GridCycle break found for the relabelling notion.** Every nontrivial SumRanks
  symmetry survives GridCycle with probability ≤ 1/4420 (PROVED, heavy). 50 of the 51
  survive with probability 0 (PROVED, default library).
* **Gap (honest):** for relabellings outside `v10Sym`, the only *proved* GridCycle
  statement is the 1-step bound `#gcExc/52`, which is ~1 for small-support τ. Any
  multi-round statement for those τ has to take its per-round factor from SumRanks'
  1/64, not from GridCycle. A better proved GridCycle bound for small-support τ
  (sampled ≈ 0.0035–0.0085 for swaps) would need a whole-walk argument. That is not
  attempted here.

## Reproduce

    python3 prefix_survival.py            # ~1 min; --quick for A_2 only
    python3 prefix_survival.py --lean     # regenerate GridCycleSurvivalLists.lean (--check: compare, CI)
    python3 conditional_survival.py       # ~8 s
    python3 transposition_survival.py     # ~80 s
    cd ../../security && lake build DoubleDealSecurityHeavy.GridCycleSurvival   # decide!: ~2 min per check, ~4 min in CI
