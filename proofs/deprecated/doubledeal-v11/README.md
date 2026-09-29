# DoubleDeal v11: PassKey suit+rank collision (SUPERSEDED, not attacked)

**Kind:** a superseded version, frozen next to its artifacts (see the [`proofs/README.md`](../../README.md) taxonomy). **It is not a vulnerability proof and there is no attack on v11.** The finding is a related-key property of the key schedule. On the 6-round cipher it gave no measurable effect. This folder freezes DoubleDeal v11 at [`primitives/cipher/doubledeal/v11/`](../../../primitives/cipher/doubledeal/v11/), following the v8/v9/v10 layout. **The successor is v12.** v12 changes one step of the PassKey \(F\) (the suit cut becomes "deal suit + 2 cards under the hand, or under the key pile if they do not fit"). The analysis that found the property and measured the candidate rules is [`proofs/doubledeal/analysis/passkey-related-key/`](../../doubledeal/analysis/passkey-related-key/). Nothing here is a security claim, and there are no bit-security claims in either direction.

## Why supersede

In each step of v11 PassKey \(F\) (v11 SPEC §3.7), the controller C cuts the hand by suit(C) mod n and then, if rank(C) < n, cuts the hand again by rank(C). Two cuts of the same pile add, so when the rank fits, the move is a single rotation of the hand by (suit + rank) mod n, and C matters only through suit + rank. Take two cards with the same suit + rank, such as 2♥ (1 + 2) and A♠ (2 + 1). Swap them in a key K (τ = 2♥↔A♠). Whenever both act at steps where their ranks fit, every move of \(F\) is the same on K and on τK. So \(F(\tau K) = \tau F(K)\).

| Claim | Status |
| --- | --- |
| 68 swaps (the pairs with equal suit + rank) satisfy \(P[F(\tau K) = \tau F(K)] \ge e(e-1)/2652\) with \(e = 51 - \text{larger rank}\); worst 196/221 ≈ 0.887 (2♣↔A♥, 2♥↔A♠, 2♠↔A♦), down to 703/1326 ≈ 0.530 for pairs with a King | **Closed form**, hand-checkable (analysis README §1–2, `colliders.py` enumerates the moves exactly). The measured rates agree to about 1e-3 (`logs/pass.log`). Not a Lean theorem. |
| Every other swap passes one \(F\) at below 1/64 (worst measured 9♥↔9♦ 0.0028) | **Measured** (50k keys per swap, all 1326). |
| Through the real key schedule (six passes), K and τK give six round keys that all differ by exactly τ for 48.14% ± 0.04% of keys (2♥↔A♠); from 0.02 to 0.48 over the 68 pairs | **Measured** (`logs/sched_top.log`, 5M keys per swap; `logs/sched_all68.log`). |
| On the full 6-round v11 cipher, \(E_{\tau K}(P) = E_K(P)\), \(E_{\tau K}(P) = E_K(P)\circ\sigma\) and \(E_{\tau K}(\tau P) = \tau E_K(P)\) never held; ciphertext agreement matched unrelated decks (0.9999 ± 0.0006 equal seats against 1) | **Measured**: 0 hits in 10M related-key samples for 2♥↔A♠ (95% upper bound 3e-7), 2M each for more pairs and controls (`logs/rk_main.log`, `logs/rk_more.log`). |

**What this is not.**
* Not a single-key attack. \(F\) is a bijection, so there are no equivalent keys and the key space is not reduced.
* Not a related-plaintext distinguisher, the model of the v8/v9 breaks.
* Not a related-key distinguisher on the 6-round cipher at 10M samples. A τ-related round key enters the state through Compose as a swap of two *seats*, not of two labels, and the next unkeyed round spreads it. It buys about one round of six.

v11 is superseded because the repo holds each layer to a per-layer bar, and PassKey is the one place where a clean, closed-form collision was left. It is not superseded because of a demonstrated break. The decision and the choice of rule are the maintainer's.

## The v12 rule (for reference)

At each step, pop C; the hand has n cards and the key pile i = 51 − n. With d = suit(C) + 2 (♣0 ♥1 ♠2 ♦3):
* if d < n, deal d cards one at a time off the top of the hand (so they come out reversed) and put the packet under the hand;
* else if d < i, do the same on the key pile;
* else skip. This cannot happen in a 52-card pass; it is written so the rule is total.

Then comes the unchanged rank cut with key-pile fallback, then C on top of the key pile. Measured for this rule (analysis README §9): the worst swap through one pass is 2♣↔A♥ at 0.00198 ≈ 1/506. No two cards ever make the same move at the same step (exact bound 0). Six passes: 0 in 200k for the worst pair. Round trips: 0 failures in 200k each way. These are measurements, not a security claim.

## Files

| Path | What |
| --- | --- |
| `vectors/` | Frozen v11 vectors. `proofs/doubledeal/vectors/regen.sh v11 --check` rebuilds them from `v11/doubledeal_v11.sudo` through the sudoc JS target (CI: `generated-fresh`). They are the v11 vectors that were live before v12, unchanged. |
| `lean/Generated/` | Emitted Lean of the frozen v11 sudo (`proofs/emit_lean.sh doubledeal-v11`; do not edit) and its TAP test of the sudo tests (CI: the `doubledeal-v11-generated` entry of the `generated` matrix in `proofs.yml`). There is no witness package, because there is no attack to witness. |

The v11 Lean proofs (PassKey inverse, Link 2 refinement, GridCycle, security package) are not copied here. They stay in git history at the v11 heads (#96, #99 and the latest main before v12).

## Reproduce

```sh
proofs/doubledeal/vectors/regen.sh v11 --check
proofs/emit_lean.sh --check doubledeal-v11
(cd proofs/deprecated/doubledeal-v11/lean/Generated && lake build && ./.lake/build/bin/doubledeal_v11_test)
proofs/doubledeal/analysis/passkey-related-key/run_all.sh   # slow (~25 min on 8 cores), optional
```
