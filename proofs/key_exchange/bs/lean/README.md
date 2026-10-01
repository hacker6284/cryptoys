<!-- Owns: the scope of the BS Link 2 proofs (proofs/key_exchange/bs/lean) and their export table. Maintenance rules: ../../../../DOCS.md. -->
# BS Link 2: the emitted arithmetic and exchange against a hand-written model

Status: **a milestone, not the whole of BS.** The Lean below proves that the code `sudoc` emits from [`bs.sudo`](../../../../primitives/key_exchange/bs/bs.sudo) (in [`Generated/`](Generated/README.md)) computes what a hand-written model of [SPEC](../../../../primitives/key_exchange/bs/SPEC.md) §2.3, §3, §3.1 and B3 to B9 says, for every input in the stated domain. It is **correctness of the emitted code, not a security claim**: nothing here says discrete logs in these fields are hard, that `p` is prime, or that a key has any entropy. The key reader and the key build (§4) are **not** covered (see the table).

Build and audit (Lean 4.14.0, no Mathlib):

```sh
cd proofs/key_exchange/bs/lean
lake build                                       # BsLink2 (and the emitted Generated/)
python3 ../../../doubledeal/check_axioms.py bs   # every BsLink2 theorem: propext, Classical.choice, Quot.sound only
python3 ../../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
```

No `sorry`, no `native_decide`, no `axiom`. The tier facts use `decide` and `decide!` (kernel evaluation, no extra axiom).

## Generated Lean

[`Generated/`](Generated/README.md) is emitted from `bs.sudo` by `proofs/emit_lean.sh bs` under the terminates gate (`sudoc emit-ir --require terminates`), which `bs.sudo` passes since its loops became bounded `for` loops (#160). Its TAP runs every sudo `test` in `bs.sudo`: **26/26 pass** (`cd Generated && lake build && ./.lake/build/bin/bs_test`; CI job `bs-generated`). That is evidence the emitter ran, not a theorem.

## The model

[`BsLink2/Spec.lean`](BsLink2/Spec.lean), written from the SPEC, not from `bs.sudo`. A register is a `List Nat` of trits, hole 0 first, hole `i` worth `3^i`; a field is `n` and the toll register, `p = 3^n − c`.

- `Spec.Field.Wf`: the domain. The toll is a non-empty trit register of **fewer than n trits** (SPEC §2.3, the bound `pay_toll` asserts since #160). Primality of `p` is not assumed.
- `Spec.tidy`: the register holding `value x mod p`.
- `Spec.MulResult`: what a product must be: `n` trits, below `3^n`, congruent to `A·B·3^nudge` mod `p`. The SPEC's fold fixes one representative but not by a closed formula, so the model of `multiply` is this relation, not a function.
- `Spec.sendPublicValue`: the answers are the holes read as shots, and Y ends up holding the value.
- `Spec.expOf`: the cells read as a base-3 number, first cell most significant. `Spec.publicValue` is `3^e mod p`, `Spec.sharedSecret` is `C^e mod p`, `Spec.exchangeKey` is `3^(2ab) mod p`.
- `Spec.checkReceived`: exactly `n` trits, else reject; `C = R·R mod p`; reject `C = 0` or `C = 1`; otherwise `C`.
- T1 and T2 are written out from the §2.3 table, with `T1_p` and `T2_p` checking `p` against the table's values (`decide`).

`emb` sends a model field to the emitted `Bs.Field`; registers go through MegaDreifach's `embed` (a `List Nat` as an `Array Int`).

## Emitted functions

Every `export func` of `bs.sudo` has a row; `check_axioms.py --selftest` checks this column against the sudo. "Given `read_key`" means the theorem takes the key reader's output as a hypothesis (`Bs.read_key key = .ok (embed cells)`, with the cells trits, a hit among them, and their count fitting `i64`); nothing is claimed about `read_key` itself yet.

| Emitted function | Theorem | What it says |
| --- | --- | --- |
| `tier` | `tier_T1_refines`, `tier_T2_refines`, `tier_T6_wf` | `tier "T1"` and `tier "T2"` are the model's T1 and T2 (and so have the §2.3 `p`). `tier "T6"` is a well-formed field with `n = 100` and a 50-trit toll; its digits are not checked against π here. |
| `multiply` | `multiply_refines` | On a well-formed field, registers of `n` trits and a nudge of 0 to 2, `multiply` succeeds with a register satisfying `Spec.MulResult`. |
| `tidy` | `tidy_refines` | On a register of `n` trits, `tidy` returns exactly `Spec.tidy`. |
| `check_received` | `check_received_refines` | For **any** received list of naturals (any length, any digits), `check_received` returns exactly `Spec.checkReceived`. |
| `send_public_value` | `send_public_value_refines` | Sending a register gives the model's shots, in call order, and a Y equal to the value. |
| `public_value` | `public_value_refines` | Given `read_key`: the register holding `3^e mod p`. |
| `shared_secret` | `shared_secret_refines` | Given `read_key`, for a base register `C` of `n` trits: the register holding `C^e mod p`. |
| `exchange` | `exchange_agree` | Given `read_key` for both keys, and if neither received square is 0 or 1 mod `p`: `exchange` succeeds, publishes `3^a mod p` and `3^b mod p`, and both secrets are `3^(2ab) mod p`. The failure branches (a rejected square) are not stated. |
| `read_key` | none | Not claimed. The walk theorems take its output as a hypothesis. |
| `dice` | none | Not claimed. |
| `build_key_grid` | none | Not claimed. |
| `build_letting_go` | none | Not claimed. |

The `FitsLen` hypotheses (that `n + 1`, `2n + 2` or the cell count fits `i64`) hold by far in every tier. `public_value_refines` and `exchange_agree` also assume `n ≥ 3`, because a red first hit starts the public accumulator as a white at hole 2 (B7); every tier has `n ≥ 18`.

## The peg recipes underneath

These are the lemmas the headlines are built from, each about one emitted function on `Array Int`:

- `drop_spec` (B2): dropping a colour at a hole adds `c·3^hole`, with the carries.
- `lay_spec` (B3): laying a register at hole `s` adds `A·3^s`.
- `pay_toll_spec` (B4): folding the overflow leaves a register of `n` trits below `3^n` that differs from the input by a multiple of `p`. Its proof carries the **4-lift bound** of SPEC B4: because the toll has fewer than `n` trits, four lifts always clear a hole, so `pay_toll`'s `assert strip[h] == 0` after its `for lift = 1 to 4` never fails on this domain.
- `multiply_spec` (B3), `slide_spec`, `tidy_spec` (B5), `cube_spec` (B6).
- `walk_public_spec`, `walk_shared_spec` (B7): the walk's accumulator stays congruent to `3^(e so far)` or `C^(e so far)` mod `p`, and the final tidy makes it exact.
- `call_the_shots_spec` (§3.1), `is_trits_spec`, `is_empty_spec`, `is_lone_white_spec` (B8).
- `eq_embed_toReg`: a trit array is determined by its size and value; this turns the congruences into equalities with the model's registers.

## Dice and the tray-die assumption

No theorem here is about probability, and none is about the key build. The let-go list of `build_letting_go` would be an **arbitrary input** to any statement about it: nothing assumes how or when a builder lets go. The entropy figures of SPEC §4 rest on the **tray-die assumption** (A4 and §4.2: every let-go is chosen without regard to the unread dice in the tray). If a later theorem states a probability, that assumption must appear in it as a named `Prop` hypothesis, never as an `axiom`. None does yet.

## Remaining work

- `read_key` (§4.3): that it returns trits starting with the start marker, which would discharge the walk hypotheses.
- `dice`, `build_key_grid`, `build_letting_go` (§4.2), with the let-go list arbitrary.
- `exchange` when a square is rejected (the two error branches).
- `tier "T6"` toll digits against π.
- Known-answer vectors (`vectors/bs_vectors.json`) run through the emitted Lean. Today CI runs the emitted sudo tests only ([`Generated/`](Generated/README.md), TAP).
