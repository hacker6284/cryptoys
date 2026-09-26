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
need the Fin-52 packet; encrypt uses `CardBound` and `Perm52`
(`encrypt_refines`).

```text
List Nat  --embed-->  Array Int
   |                      |
   | algebraic            | Generated (Except Trap)
   v                      v
List Nat  <--decode--  Array Int     (on success, no Trap)
```

## This drop (DoubleDeal S3/S4 on Except Trap)

Builds on #26/#28/#30 (`passkey_refines`, `passkey_inv_refines`, twin
`runLoopOn`) and #32 (`encrypt_refines`). On the well-formed domain —
`FitsLen` lists, and `WellFormed` for emitted `Array Int` — algebraic
S3/S4 hold for `Doubledeal.passkey` and `Doubledeal.passkey_inv`
(`Except SudoRt.Trap`): card multiset (`List.Perm`), `passkey_inv`
after `passkey` is the identity, `passkey` after `passkey_inv` is the
identity, and both are injective. The proofs are the two passkey glues
plus the list algebra. They do not re-induct on `runLoopOn`. Algebraic
Link 2 only — not bit-security, not emitter soundness.

| Item | Status |
| --- | --- |
| Scaffolding + well-formedness + embed/decode | Landed (`DoubleDeal/Link2/Embed.lean`) |
| `suit_of` / `rank_of` refine the stones | Landed |
| `Generated.drop_front` ≃ algebraic `uncons` (nonempty, `FitsLen`) | Landed |
| `Generated.push_front` ≃ algebraic `cons` (`FitsLen`) | Landed |
| `Generated.left_rotate` ≃ algebraic `rotL` (`FitsLen`) | Landed (`Link2/Rotate.lean`) |
| `Generated.right_rotate` ≃ algebraic `rotR` (`FitsLen`) | Landed (`right_rotate_refines`; via `left_rotate` + `rotR_eq_rotL`) |
| One generated PassKey body ≃ `passKeyStep` (rotate / cut / push) | Landed (`maybeRotate_refines`, `maybeCut_push_refines`, `passKeyStep_refines`) |
| Twin `runLoopOn` inducts to `passKeyGoN` on every well-formed list | Landed (`passkey_loop_refines`, `passkey_twin_refines`) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on length ≤ 1 | Landed (`passkey_nil`, `passkey_singleton`) |
| Residual stepper of `Doubledeal.passkey` = `passkeyStepGen` | **CLOSED** (`passkey_step_eq`, `passkey_inlined_cut_eq`; nested suit-rotate / do-elaboration, not a second algorithm) |
| `Generated.passkey` ≃ `passToKeyCutFallback` on every well-formed list | **CLOSED** (`passkey_eq_twin_loop`, `passkey_refines`) |
| One generated inverse body ≃ `invPassKeyStep` | Landed (`maybeCutInv_refines`, `maybeRotateInv_refines`, `invPassKeyStep_refines`) |
| Twin inverse `runLoopOn` inducts to `passKeyInvGoN` | Landed (`passkey_inv_loop_refines`, `passkey_inv_twin_refines`) |
| Residual stepper of `Doubledeal.passkey_inv` = `passkeyInvStepGen` | **CLOSED** (`passkey_inv_step_eq`, `passkey_inv_eq_twin_loop`; nested undo-cut / do-elaboration, not a second algorithm) |
| `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list | **CLOSED** (`passkey_inv_refines`) |
| `Generated.encrypt` ≃ `encryptDeck` / `encrypt6` | **CLOSED** (`encrypt_refines`; `CardBound` message, `Perm52` key, length 52) |
| `mix_columns` ≃ `mixColumns` | **CLOSED** (`mix_columns_refines`) |
| `full_round` / `final_round` ≃ `fullRound` / `fullRoundNoMix` | **CLOSED** (`full_round_refines`, `final_round_refines`) |
| S3/S4 transfer onto `Except Trap` (multiset, inverse, injectivity) | **CLOSED** (`passkey_perm`, `passkey_inv_perm`, `passkey_leftInverse`, `passkey_rightInverse`, `passkey_injective`, `passkey_inv_injective`, and the `WellFormed` Array forms in `Link2/PassKeyTransfer.lean`) |
| MegaDreifach `pad_message` ≃ algebraic `pad` | **CLOSED** (`pad_message_refines`, `pad_message_refines_array`, `pad_z_refines`). Domain `PadWf`: bytes `≤ 255` and `8 * length` fits in an i64. Not `v_Hash`. |
| MegaDreifach `compose` ≃ algebraic `compose` | **CLOSED** (`compose_refines`, `compose_refines_array`). Domain `PosWf`: lengths 20/20/30/30, nonnegative in-range indices, orientations `< 3` / `< 2` (trap-free, i64-safe). Not `v_Hash`. |
| MegaDreifach `require_permutation` ≃ algebraic `requirePermutation` | **CLOSED** (`require_permutation_refines`, `require_permutation_refines_array`). Domain `DealWf` / `isPermutation52`: length 52, nonnegative card ids `< 52`, no duplicates (trap-free, i64-safe). Not `v_Hash`. |
| MegaDreifach `pack_ori2` ≃ algebraic `packOri2` | **CLOSED** (`pack_ori2_refines`, `pack_ori2_refines_array`). Domain `Ori2Wf`: length 30, entries `< 2`. Horner value `< 2^29`, one limb, trap-free i64 arithmetic. Not `v_Hash`. |
| MegaDreifach `pack_ori3` ≃ algebraic `packOri3` | **CLOSED** (`pack_ori3_refines`, `pack_ori3_refines_array`). Domain `Ori3Wf`: length 20, entries `< 3`. Horner value `< 3^19`, at most two base-10^9 limbs, trap-free i64 arithmetic. Not `v_Hash`. |
| MegaDreifach full `v_Hash` / Scramble algebraic ≃ Generated | **OPEN** (`v_Hash` is M13; Scramble has little ledger). The pad, compose, `require_permutation`, `pack_ori2`, and `pack_ori3` slices are closed. `phi_chunk` / `phi_inv` are still open. |
| DoubleDeal-CBC-HMAC algebraic ≃ Generated | OPEN. Generated TAP exists (`#22`); no algebraic ledger. Not AEAD security. |
| sudo text = generated Lean (deep embedding) | OPEN — Link 1, not this file |
| Bit-security, MDS, collision-resistance, AEAD | Not a Link 2 claim |

## What stays trusted-not-proved

- The Lean emitter (`backends/lean/emit.py` at the pin in
  [`ANTI_DRIFT.md`](ANTI_DRIFT.md)).
- Generated TAP and JSON KATs as **evidence**, not Link 2 theorems.

Edit `.sudo` and regenerate `Generated/` to change the algorithm.
Edit stones / `Link2/` to change the ledger or the refinement.
