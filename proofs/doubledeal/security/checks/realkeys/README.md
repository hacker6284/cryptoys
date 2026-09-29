<!-- Owns: scoping notes and empirical results for the real-key-schedule relabelling witnesses. Maintenance rules: ../../../../../DOCS.md. -->
# Real-schedule relabelling: scoping notes (analysis only)

What the key schedule is:
- `Doubledeal.encrypt m K` computes `expand_keys K = [K0..K6]`, where K0 = K and K(r+1) = passkey(Kr).
- It whitens with K0, runs full rounds 1–5 with K1..K5, and runs the final round (no GridCycle) with K6.
- The model `encryptDeckFn` / `encryptDeck` uses exactly this schedule (`passKeyIter`), and
  `Link2.encrypt_refines` transfers it to the generated code under `Perm52 K`.
- Valid master keys are decks (SPEC §2). A key with a missing card makes `index_of` hit
  `sudoAssert false` and trap.

Empirical results (`emp.py`, `structured.py`; both run the v9 Python port, `ddport.encrypt(m, k, 9)`, against `v9Sym`). No commuting instance was found:
- The identity master key with the identity message (or `firstDeck 51`) breaks all 51 nontrivial v9Sym.
- 12,300 random master keys, one random message each:
  - 627,300 (key, v9Sym σ) pairs: 0 commute.
  - 123,000 random σ (transpositions and uniform permutations): 0 commute.
- 62 structured keys × 6 structured messages × 51 v9Sym: 0 commute.

Cost: one real-schedule `encryptDeck` evaluation takes about 46 s of kernel time with `decide!`.
`v9sym_subgroup.py` shows that two witnesses (v9Sym 0 2 and v9Sym 1 0) cover all 51
nontrivial elements, because the σ that commute with a fixed E_K form a subgroup.

v10 and later: `v10sym_subgroup.py` reduces the 51 nontrivial `v10Sym` to four witnesses and re-checks the heavy witness outputs; `realkey_to_lean.py` writes the five expected ciphertexts of `DoubleDealSecurityHeavy/RealKey.lean` from the v12 Python port (`--check` in CI). See [`../../README.md`](../../README.md) (`RealKey` rows).
