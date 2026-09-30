<!-- Owns: the Link 1 (sudo text = emitted Lean) feasibility assessment and proof plan. Status rows stay in ANTI_DRIFT.md. Maintenance rules: ../DOCS.md. -->
# Link 1: sudo text = generated Lean (scope only)

Status: **OPEN** ([`ANTI_DRIFT.md`](ANTI_DRIFT.md)). This file is a feasibility assessment and a plan. Nothing here is proved. The target is MegaDreifach v2 ([`megadreifach.sudo`](../primitives/hash/megadreifach/megadreifach.sudo)). The same plan applies to the other emitted targets.

## What is trusted today

```text
megadreifach.sudo --sudoc (Rust, front end)--> protocol-4 JSON IR --backends/lean/emit.py--> Generated/Megadreifach.lean + SudoRt.lean
```

- `sudoc` and the Lean backend come from sudocode at the pin in [`SUDOCODE_PIN`](SUDOCODE_PIN). At that pin `backends/lean/emit.py` is about 3,100 lines of Python.
- The only semantics of sudo is informal prose (sudocode `spec/language.md`). No machine-readable semantics exists to prove against.
- Link 2 starts at the emitted Lean: everything proved about `Generated.v_Hash` / `v_HashDeck` is about that output, not about the `.sudo` text.
- Evidence, not proof: Generated TAP (the sudo test blocks, run as compiled Lean) and the 8 KAT theorems.

## Options

| Option | Result | Cost | Verdict |
| --- | --- | --- | --- |
| Verified emitter: prove `emit.py` correct, or rewrite it in Lean and prove that | Emitter drops out of the TCB for every program | Needs a formal sudo semantics first, plus a compiler proof over the whole IR | Not feasible short-term |
| **Translation validation** per program: a Lean deep embedding of the IR plus an interpreter, then `Generated.f = eval ir f` for each emitted function | Emitter drops out of the TCB for MegaDreifach | Weeks; see below | Recommended |
| Differential testing (more KATs, random sudo-vs-Lean runs) | Evidence only | Days | Already partly done (TAP, KATs); does not close Link 1 |

## Plan (translation validation)

1. **IR embedding.** A Lean inductive for the protocol-4 IR subset that `megadreifach.sudo` uses: i64 arithmetic with traps, lists with value semantics, records, `for` over bounded ranges, `break`, asserts, calls. The emitted MegaDreifach code uses a small runtime surface (`SudoRt`: checked `addI` / `subI` / `mulI` / `divI` / `modI` / `negI`, `atL` / `putL` / `appendL` / `filledL` / `listLen`, `runLoopOn`, `Flow`, `Trap`), so the subset is small.
2. **Reference interpreter** `eval : Program → Fn → List Value → Except Trap Value`, written against `language.md` and reviewed line by line against it. This interpreter becomes the new trusted artefact, in place of `emit.py`. It is much smaller and has no code generation.
3. **IR import.** Dump the IR with `sudoc emit-ir` at the pin, then turn the JSON into a Lean term with a generator checked in CI, in the same style as `vectors/json_to_lean.py --check`.
4. **Per-template lemmas.** One lemma for each `emit.py` template (statement forms, loop lowering to `runLoopOn`, trap propagation): the emitted shape equals `eval` of the IR node. These are generic over the node's children.
5. **Per-function theorems** `Generated.f args = eval ir "f" args` for the MegaDreifach functions (the emitted file has about 140 definitions, including loop bodies), by unfolding and the template lemmas. The existing Link 2 lemmas are not needed here, but the proof style (`chain_loop`, fuel-total loops) carries over.
6. **Glue.** Compose with Link 2, so that on `PadWf` the interpreter's `Hash` equals the algebraic `vhashAlg`.

**What remains trusted afterwards:** `sudoc`'s front end (parser and type checker, `.sudo` → IR) and the faithfulness of the interpreter to `language.md`.

## Cost and risks

- Steps 1–3 take about a week. Steps 4–5 dominate: several weeks, because `emit.py`'s control-flow lowering (`Flow`, fuel loops) needs care and the per-function proofs must go through `decide`-free unfolding without blowing up elaboration time (the Link 2 files already see heavy elaboration on `em_block`).
- Pin bumps: the IR import and template lemmas are tied to the pin. Each bump re-runs the proofs and may need template lemmas redone.
- Partial credit is real: once steps 1–3 exist, each per-function theorem is useful alone (for example `pad_message`, `phi_chunk`).

Not attempted in this change: it is not cheap.
