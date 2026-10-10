<!-- Owns: the scope of the BS Link 2 proofs (proofs/key_exchange/bs/lean) and their export table. Maintenance rules: ../../../../DOCS.md. -->
# BS Link 2: the emitted arithmetic, key and exchange against a hand-written model

Status: **a milestone, not the whole of BS.** The Lean below proves that the code `sudoc` emits from [`bs.sudo`](../../../../primitives/key_exchange/bs/bs.sudo) (in [`Generated/`](Generated/README.md)) computes what a hand-written arithmetic model (values mod p) of [SPEC](../../../../primitives/key_exchange/bs/SPEC.md) §2.3, §3, §3.1, B3 to B9, the key build §4.2 and the key reader §4.3 say, for every input in the stated domain. The model tracks register values only: the peg recipes (how pegs are dropped, laid and lifted), what B6 leaves in the registers besides their values, and the public-phase nudges as hole shifts are not modelled; the theorems reach them only through the emitted code. It is **correctness of the emitted code, not a security claim**: nothing here says discrete logs in these fields are hard, that `p` is prime, or that a key has any entropy. The key reader (§4.3) is covered, so the walk and exchange theorems start from the key's pages. The key build (§4.2, `build_key_grid`) is covered for any dice whose face lists fit `i64`, and every grid it returns is a well-formed page. A key grid is built in one sitting (SPEC §4.2: nobody lets go), so the build has no let-go input. No statement is about how likely a grid is (see "Dice and probability").

Build and audit (Lean 4.14.0, no Mathlib):

```sh
cd proofs/key_exchange/bs/lean
lake build                                       # BsLink2 (and the emitted Generated/)
python3 ../../../doubledeal/check_axioms.py bs   # every BsLink2 theorem: propext, Classical.choice, Quot.sound only
python3 ../../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
```

No `sorry`, no `native_decide`, no `axiom`. The tier facts use `decide` and `decide!` (kernel evaluation, no extra axiom).

## Generated Lean

[`Generated/`](Generated/README.md) is emitted from `bs.sudo` by `proofs/emit_lean.sh bs` under the terminates gate (`sudoc emit-ir --require terminates`), which `bs.sudo` passes since its loops became bounded `for` loops (#160). Its TAP runs every sudo `test` in `bs.sudo`: **32/32 pass** (`cd Generated && lake build && ./.lake/build/bin/bs_test`; CI job `bs-generated`). That is evidence the emitter ran, not a theorem.

## The model

[`BsLink2/Spec.lean`](BsLink2/Spec.lean), written from the SPEC, not from `bs.sudo`. A register is a `List Nat` of trits, hole 0 first, hole `i` worth `3^i`; a field is `n` and the toll register, `p = 3^n − c`.

- `Spec.Field.Wf`: the domain. The toll is a non-empty trit register of **fewer than n trits** (SPEC §2.3, the bound `pay_toll` asserts since #160). Primality of `p` is not assumed.
- `Spec.tidy`: the register holding `value x mod p`.
- `Spec.MulResult`: what a product must be: `n` trits, below `3^n`, congruent to `A·B·3^nudge` mod `p`. The SPEC's fold fixes one representative but not by a closed formula, so the model of `multiply` is this relation, not a function.
- `Spec.sendPublicValue`: the answers are the holes read as shots, and Y ends up holding the value.
- `Spec.expOf`: the cells read as a base-3 number, first cell most significant. `Spec.publicValue` is `3^e mod p`, `Spec.sharedSecret` is `C^e mod p`, `Spec.exchangeKey` is `3^(2ab) mod p`.
- `Spec.checkReceived`: exactly `n` trits, else reject; `C = R·R mod p`; reject `C = 0` or `C = 1`; otherwise `C`.
- T1 and T2 are written out from the §2.3 table, with `T1_p` and `T2_p` checking `p` against the table's values (`decide`). `Spec.T6` copies T6's 50-trit toll from `bs.sudo`; [`BsLink2/TollPi.lean`](BsLink2/TollPi.lean) checks it against π as far as core Lean can (below).
- §4.1 / §4.3, the key: `Spec.Ship` (kind, down or across, row and column of its first hole, bow at the last hole or not), `Spec.Grid` (ships and 100 pegs), and `Spec.Grid.Wf`: every ship on the 10 × 10 grid, no two ships sharing a hole, 100 pegs that are trits. `Spec.KeyWf pages`: one or more well-formed pages. `Spec.readKey`: the start marker (a white cell), then each page's ship pass (`Spec.shipPass`, one hole at a time: a ship's first hole white across / red down, its last hole white back / red on plus a plain cell for a Sub and a white one for a Cruiser, every other hole plain) and peg pass (`Spec.pegPass`).
- B9: `Spec.exchange` reads both keys, publishes, sends, checks (Alice's check of Bob's value first) and returns either `Spec.aliceRejects`, `Spec.bobRejects` (the two `bs.sudo` error texts) or the record of both publics, shots, received values, bases and secrets.
- §4.2: `Spec.Dice`, the three face streams (d12, d6, d10) as arbitrary integers and how many of each have been read; `Spec.dice` is fresh dice.
- §4.2 BUILD, in one sitting (no letting go). The dice: `Spec.rollHole` (d12, 1–12), `Spec.rollD6`, `Spec.throwD10` (a row-cup d10 thrown until it shows 1–9), `Spec.throwRowCup` (five of them). The pieces: `Spec.hasRoom`, `Spec.growLoop` / `Spec.pieceOf` / `Spec.layShip` / `Spec.growUntilItBumps` (step 1), `Spec.keypadFirst` / `Spec.keypadSecond` (step 2). `Spec.holeStep` is one hole: the row cup at a row's first hole (`Spec.rowCupAt`), grow (`Spec.growAt`), peg (`Spec.pegAt`). `Spec.build` walks the 100 holes from an empty grid; `Spec.buildKeyGrid` returns the grid and the read counts. Every step that reads a die fails (`none`) when its stream has run out or the face is off the die.

`emb` sends a model field to the emitted `Bs.Field`; registers go through MegaDreifach's `embed` (a `List Nat` as an `Array Int`).

## Emitted functions

Every `export func` of `bs.sudo` has a row; `check_axioms.py --selftest` checks this column against the sudo. Keys are `embKey pages` for model pages with `Spec.KeyWf pages`; no headline theorem takes the key reader's output as a hypothesis; the `*_of_read` / `exchange_cells_refines` lemmas keep the cells form.

| Emitted function | Theorem | What it says |
| --- | --- | --- |
| `tier` | `tier_T1_refines`, `tier_T2_refines`, `tier_T6_wf` | `tier "T1"` and `tier "T2"` are the model's T1 and T2 (and so have the §2.3 `p`). `tier "T6"` is `Spec.T6`, a well-formed field with `n = 100` and a 50-trit toll; for its digits against π see "The T6 toll and π". |
| `multiply` | `multiply_refines` | On a well-formed field, registers of `n` trits and a nudge of 0 to 2, `multiply` succeeds with a register satisfying `Spec.MulResult`. |
| `tidy` | `tidy_refines` | On a register of `n` trits, `tidy` returns exactly `Spec.tidy`. |
| `check_received` | `check_received_refines` | For **any** received list of naturals (any length, any digits), `check_received` returns exactly `Spec.checkReceived`. |
| `send_public_value` | `send_public_value_refines` | Sending a register gives the model's shots, in call order, and a Y equal to the value. |
| `public_value` | `public_value_refines` | For a key of well-formed pages: the register holding `3^e mod p`, where `e` is `Spec.readKey` of the key read as a base-3 number. |
| `shared_secret` | `shared_secret_refines` | For a key of well-formed pages and a base register `C` of `n` trits: the register holding `C^e mod p`. |
| `exchange` | `exchange_refines`, `exchange_alice_rejects`, `exchange_bob_rejects`, `exchange_agree_of_accepted` | For two keys of well-formed pages, `exchange` returns exactly `Spec.exchange`'s outcome in all three branches. Corollaries: if `3^(2b) mod p` is 0 or 1 it returns the error "B8: Alice rejects Bob's value" (whatever `a` is); if not, but `3^(2a) mod p` is 0 or 1, the error "B8: Bob rejects Alice's value"; if neither, it succeeds, publishes `3^a mod p` and `3^b mod p`, and both secrets are `3^(2ab) mod p`. |
| `read_key` | `read_key_spec` | For a key of well-formed pages, `read_key` returns `Spec.readKey`: the start marker, then each page's ship pass and peg pass. With `readKey_trits`, `expOf_readKey_pos` (the start marker makes the exponent non-zero; `expOf_readKey_ge`: at least `3^(cells − 1)`) and `length_readKey_le` (at most `300·pages + 1` cells) this discharges what the walk lemmas assume. |
| `dice` | `dice_refines` | For any three face streams, `dice` is `Spec.dice` (nothing read yet). |
| `build_key_grid` | `build_key_grid_refines`, `build_key_grid_dice`, `build_key_grid_wf` | For any model dice whose three face lists fit `i64`, `build_key_grid` succeeds exactly when `Spec.buildKeyGrid` does and returns its grid and read counts, and traps exactly when the model fails; `build_key_grid_dice` starts from `dice d12 d6 d10`. Whatever grid it returns is `embGrid` of a page `g` with `Spec.KeyWf [g]`, so the one-page key `#[grid]` meets the key hypotheses of `public_value_refines` and the walk and exchange theorems (`Spec.KeyWf [g]`, and `FitsLen 301` holds outright). Their other hypotheses, `F.Wf`, `3 ≤ n` and `FitsLen (2n + 2)`, are about the tier and remain. |

The `FitsLen` hypotheses (that `2n + 2`, or `300·pages + 1` for a key of `pages` pages, or a face list's length, fits `i64`) hold by far in every tier and every key that could be built. `public_value_refines` and the `exchange` theorems also assume `n ≥ 3`, because a red first hit starts the public accumulator as a white at hole 2 (B7); every tier has `n ≥ 18`.

## The T6 toll and π

SPEC §2.3 says T6's toll is `π₅₀ + 4383`, where `π₅₀` is the integer whose base-3 digits are the first 50 ternary digits of π, i.e. `⌊π·3^48⌋`. Core Lean has no real numbers, so [`TollPi.lean`](BsLink2/TollPi.lean) checks on naturals (each check by `decide`; `floor_eq_pi50` is proved from them, not by `decide`):

- `T6_toll_eq`: `Spec.T6`'s toll is the 50-hole register of `pi50 + 4383` for an explicit `pi50`;
- `pi50_le_lower`, `upper_lt_pi50_succ`, `lower_lt_upper`: for two explicit rationals `L < U`, `pi50 ≤ 3^48·L` and `3^48·U < pi50 + 1` (endpoint checks);
- `floor_eq_pi50`, proved from those endpoint checks: every rational `x = a/b` with `L ≤ x ≤ U` has `⌊x·3^48⌋ = a·3^48 / b = pi50`. Core Lean has no `ℚ`, so `x` is a pair of naturals and the comparisons are cross-multiplied (`LowerLe`, `LeUpper`); `lower_in_bracket` shows the bracket is not empty;
- `pi50_leading_digits`: its first twelve ternary digits are the 1 0 0 1 0 2 1 1 0 1 2 2 that §2.3 quotes.

`L` and `U` are Machin's `16·arctan(1/5) − 4·arctan(1/239)` with each arctan cut to 16 or 17 terms of its Gregory series. **That `L ≤ π ≤ U` is cited (Machin's identity and the alternating-series bound), not proved**, and so is the last step to the real π: from `L ≤ π ≤ U` and `⌊·⌋` being monotone, `⌊L·3^48⌋ ≤ ⌊π·3^48⌋ ≤ ⌊U·3^48⌋`, and `floor_eq_pi50` makes both ends `pi50`; no hypothesis or axiom about π enters a theorem. Not checked either: that 4383 is the smallest offset making `p` a safe prime.

## The peg recipes underneath

These are the lemmas the headlines are built from, each about one emitted function on `Array Int`:

- `drop_spec` (B1): dropping a colour at a hole adds `c·3^hole`, with the carries; the carry loop stops at the first hole that does not carry, and `drop`'s final `assert clicks == 0` holds whenever the sum fits the strip.
- `lay_spec` (B2): laying a register at hole `s` adds `A·3^s`.
- `pay_toll_spec` (B4): folding the overflow leaves a register of `n` trits below `3^n` that differs from the input by a multiple of `p`. Its proof carries the **4-lift bound** of SPEC B4: because the toll has fewer than `n` trits, four lifts always clear a hole, so `pay_toll`'s `assert strip[h] == 0` after its `for lift = 1 to lifts_per_hole` (4) never fails on this domain.
- `multiply_spec` (B3), `slide_spec`, `tidy_spec` (B5), `cube_spec` (B6).
- `walk_public_spec`, `walk_shared_spec` (B7): the walk's accumulator stays congruent to `3^(e so far)` or `C^(e so far)` mod `p`, and the final tidy makes it exact.
- `call_the_shots_spec` (§3.1), `is_trits_spec`, `is_empty_spec`, `is_lone_white_spec` (B8).
- `eq_embed_toReg`: a trit array is determined by its size and value; this turns the congruences into equalities with the model's registers.
- `ship_holes_spec`, `ship_pass_spec`, `peg_pass_spec` (§4.3): a ship on the grid gets its holes; a page's ship pass (four 100-hole tables built ship by ship, then one hole at a time) is `Spec.shipPass` when no two ships share a hole; its peg pass is its pegs.
- `exchange_cells_refines` (B9) and `public_value_refines_of_read`, `shared_secret_refines_of_read` (B7): the same statements from the cells `read_key` returned; the headlines above discharge that with `read_key_spec`.
- `build_spec` (§4.2): the emitted `build` is `Spec.build`, traps included. Underneath, `hole_step_spec` and `row_step_spec` (one step of `build`'s column and row loops, against `Spec.holeStep` and `Spec.rowStep`), `throw_row_cup_spec` and `grow_until_it_bumps_spec`. The loop bodies are copied from `Generated/Bs.lean` into `Build.lean` (up to named loop steps and `_`-prefixed unused binders; `rfl` is the check): `holeStepE`, its body `holeInnerE` and the stages `stageBE`, `stageCE` and `stageEE` under it, `rowStepE`, `buildE`, and `grow_until_it_bumps`'s `growStepE` / `growAfterE`. They are a proof device: `build_eq` (by `rfl`) ties them to the emitted `build`, so a change in the emitted code breaks the proof instead of going unnoticed.
- `build_wf` (§4.1 / §4.2): every grid `Spec.build` returns is `Spec.Grid.Wf`. A ship is laid only from an uncovered hole and grows only into holes with room (`growUntilItBumps_room`), so it never overlaps a ship already laid; pegs come off the keypad, so they are trits.

## Dice and probability

No theorem here is about probability. The build theorems say what grid given dice faces produce, for each dice separately, not how likely a grid is; `dice_refines` only says what the fresh dice record holds. A key grid is built in one sitting (SPEC §4.2: nobody lets go), so the build has no let-go input and the emitted code has no let-go path. The entropy figures of SPEC §4 assume fair dice and the rule followed exactly (A4). If a later theorem states a probability, that assumption must appear in it as a named `Prop` hypothesis, never as an `axiom`. None does yet.

## Remaining work

- One statement from dice to the exchange (the pieces are here: `build_key_grid_wf` gives the key that `exchange_refines` takes). Keys of more than one page are built one page at a time; nothing here composes the pages.
- No probability statement is planned for the build; if one is ever stated, A4 (fair dice, the rule followed exactly) goes in as a named `Prop` hypothesis.
- Known-answer vectors (`vectors/bs_vectors.json`) run through the emitted Lean. Today CI runs the emitted sudo tests only ([`Generated/`](Generated/README.md), TAP).
- π itself in Lean (Machin's identity and the series bound, e.g. with Mathlib in a heavy package), which would turn the cited bracket into a theorem.
