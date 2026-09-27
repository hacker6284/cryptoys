# security-wip: work in progress, not built or checked by CI

This directory holds the Lean formalisation, still in progress, of the v10
SumRanks survival bound:

> every relabelling `τ ∉ v10Sym` commutes with `sumRanksV10` on at most
> `52!/64` of the `52!` decks (`sumRanksV10_survival_le`).

The paper proof (bound `0.012768 · 52!`, exact supremum `9/1105`) is
`PROOF.md` of the sumranks-dp working notes. The Lean target is the weaker
`1/64`.

* `DoubleDealSecurityWIP/SumRanksDP/Standalone.lean` imports only Mathlib. It holds
  the self-contained combinatorics and numerics: Lemma 2, the GF(4) column
  table, the fibre bound, the hypergeometric counts, and tables A and B.
* `DoubleDealSecurityWIP/SumRanksDP/Main.lean` imports `DoubleDealSecurity.SumRanksV10Iff`
  and the standalone file. It holds the per-deck reduction, the row and column
  chains, Cases A and B, and the main theorem.
* `LEMMAS.md` lists every open (`sorry`) lemma with its statement, dependencies
  and difficulty, and says whether it can be handed out on its own.
* `check_tables.py` checks tables A and B exactly in rational arithmetic, using
  the same definitions as the Lean code.

## Status

The files contain `sorry`, which is why they live outside
`proofs/doubledeal/security/`. There, `checks/scan_sorry.py` and `Audit.lean`
would reject them. The library is declared in `../security/lakefile.toml` as a
non-default `lean_lib` (`srcDir = "../security-wip"`), so neither the default
`lake build` nor any CI job builds it. Build it explicitly:

```
cd proofs/doubledeal/security
lake build DoubleDealSecurityWIP
```

Repo rules still apply: no `native_decide`, kernel `decide` only. A kernel check
that takes more than a few seconds (tables A and B, Lemma 4) moves to
`DoubleDealSecurityHeavy` when this is promoted.
Once every `sorry` is gone, the files move into `DoubleDealSecurity/` (the
light parts) and `DoubleDealSecurityHeavy/` (the heavy tables), and this
directory is deleted.
