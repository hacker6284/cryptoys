# Link 2: algebraic Lean ≃ Generated Lean

Link 2 is a **refinement** goal: on the well-formed domain, the
handwritten algebraic ledger (`proofs/*/lean/<Name>/`) equals the
emitted implementation (`proofs/*/lean/Generated/`). Algebraic
theorems then transfer to Generated — and to sudo — **modulo emitter
bugs**.

This is **not** Link 1. Link 1 (sudo → Generated via `emit`) stays
**trusted-not-proved**. `proofs/emit_lean.sh --check` is the living
alarm. A green Link 2 theorem is not emitter soundness, not a KAT/TAP
substitute, and not bit-security / MDS / collision-resistance / AEAD
security.

Sudo remains normative. Never hand-edit `lean/Generated/`.

## Why a bridge

`Generated/` is a standalone Lake package. Emitted functions are
fuel-total `Except SudoRt.Trap` over `Array Int`. Stones are `Fin` /
`List Nat` algebra. Those types do not match. The bridge interprets
one side into the other **without editing Generated sources**.

Well-formedness is the domain where Trap does not fire and the
`Array Int` value is in the image of the algebraic embedding (Nats
that fit the i64 index arithmetic the emitter uses). PassKey does not
need the Fin-52 packet; encrypt will.

```text
List Nat  --embed-->  Array Int
   |                      |
   | algebraic            | Generated (Except Trap)
   v                      v
List Nat  <--decode--  Array Int     (on success, no Trap)
```

## This drop (DoubleDeal passkey induction)

Builds on the first slice (embed/decode, `suit_of` / `rank_of`,
`drop_front` / `push_front`, `passkey` on length ≤ 1).

| Item | Status |
| --- | --- |
| Scaffolding + well-formedness + embed/decode | Landed (`DoubleDeal/Link2/Embed.lean`) |
| `suit_of` / `rank_of` refine the stones | Landed |
| `Generated.drop_front` ≃ algebraic `uncons` (nonempty, `FitsLen`) | Landed |
| `Generated.push_front` ≃ algebraic `cons` (`FitsLen`) | Landed |
| `Generated.left_rotate` ≃ algebraic `rotL` (`FitsLen`) | This PR (`Link2/Rotate.lean`) |
| One generated PassKey body ≃ `passKeyStep` (rotate / cut / push) | This PR (`maybeRotate_refines`, `maybeCut_push_refines`, `passKeyStep_refines`) |
| Twin `runLoopOn` inducts to `passKeyGoN` on every well-formed list | This PR (`passkey_loop_refines`, `passkey_twin_refines`) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on length ≤ 1 | Landed (`passkey_nil`, `passkey_singleton`) |
| `Generated.passkey` residual stepper = `passkeyStepGen` (all lists) | **NEXT** (do-elaboration / nested suit-rotate; not a second algorithm) |
| `Generated.encrypt` ≃ `encryptDeck` / `encrypt6` | **NEXT** (statement sketched in `DoubleDeal/Link2.lean`) |
| `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` | OPEN |
| S2/S3/S4 transfer onto `Except Trap` (injectivity of emitted passkey, …) | OPEN |
| MegaDreifach / Scramble algebraic ≃ Generated | OPEN (Scramble has little ledger; MD Hash is M13) |
| DoubleDeal-CBC-HMAC algebraic ≃ Generated | OPEN. Generated TAP exists (`#22`); no algebraic ledger. Not AEAD security. |
| sudo text = generated Lean (deep embedding) | OPEN — Link 1, not this file |
| Bit-security, MDS, collision-resistance, AEAD | Not a Link 2 claim |

## What stays trusted-not-proved

- The Lean emitter (`backends/lean/emit.py` at the pin in
  [`ANTI_DRIFT.md`](ANTI_DRIFT.md)).
- Generated TAP and JSON KATs as **evidence**, not Link 2 theorems.

Edit `.sudo` and regenerate `Generated/` to change the algorithm.
Edit stones / `Link2/` to change the ledger or the refinement.
