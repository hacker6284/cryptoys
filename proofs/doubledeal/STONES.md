# DoubleDeal stones (SPEC §6)

Checklist for [`primitives/cipher/doubledeal/SPEC.md`](../../primitives/cipher/doubledeal/SPEC.md) §6. Tags match the SPEC: **Lean**, **property-test**, **cryptanalysis script**, **TLA**. Mark **proof** vs **evidence**. This file only claims **correctness** where Lean is green.

| # | Stone | Proof / evidence | Lean coverage | Notes |
| --- | --- | --- | --- | --- |
| S1 | Layer bijections: lay/scoop cm & rm; SumRanks; ShiftRows; GridCycle; Compose | **Proof** | `lean/DoubleDeal/Grid.lean` (`scoop_lay_columnMajor`, `lay_scoop_columnMajor`, `scoop_lay_rowMajor`, `lay_scoop_rowMajor`); `SumRanks.lean` (`invSumRanks_sumRanks`, `sumRanks_invSumRanks`); `ShiftRows.lean` (`invShiftRows_shiftRows`, `shiftRows_invShiftRows`); `GridCycle.lean` (`invMixColumns_mixColumns`); `Compose.lean` (`compose_mutual_inverses`, `compose_mutual_inverses_52`) | GridCycle inverse is `invMix ∘ Mix`. The other composition on arbitrary packets is open. Property-test evidence also in `doubledeal.sudo` self_test. |
| S2 | Round-trip: `inv_full_round ∘ full_round`, `inv_final ∘ final`, `decrypt ∘ encrypt` | **Proof** (abstract keys + algebraic schedule) | `lean/DoubleDeal/Round.lean`: `invUnkeyedWithMix_rt`, `encrypt1WithMix_rt`, `encryptNoMix_rt`, `invFullRound_fullRound`, `invFullRoundNoMix_fullRoundNoMix`, `encryptN_rt`, `encrypt6_rt`. `Concrete.lean`: `encryptDeckFn_rt`, `encryptDeckFn_rt_range`, `encryptDeck_eq_encryptDeckFn`, `decryptDeck_eq_decryptDeckFn` | Proof-only skeleton. Algorithm is `Generated.encrypt`. OPEN that they are equal. Generated TAP (12/12) is the sudo-test oracle. |
| S3 | PassKey determinism + content-preservation | **Proof** | `lean/DoubleDeal/PassKey.lean`: `passToKeyCutFallback_perm` | Determinism is the function definition. Content = `List.Perm`. |
| S4 | PassKey injectivity on lists / \(S_{52}\) | **Proof** | `PassKey.lean`: `invPassKeyStep_passKeyStep`, `passKeyStep_invPassKeyStep`, `passKey_leftInverse`, `passKey_rightInverse`, `passKey_injective` | Constructive inverse. Cycle structure / orbit lengths stay **evidence only**. Land with PR #3 so SPEC §3.7 / S4 point at these names. |
| S5 | CTR factoradic unranking bijection \(\mathbb{Z}/13!\mathbb{Z} \leftrightarrow S_{13}\) | **Partial proof** | `lean/DoubleDeal/Factoradic.lean`: `unrankPerm_perm`, `unrankPerm_inj_3` | Permutation of items is proved. Injectivity is kernel `decide` on `Fin 3!` only. |
| S6 | CTR merge: `counter_deck` is length 52; consecutive counters agree on seats 0..38 | **Proof** | `Factoradic.lean`: `counterDeck_length`, `counterDeck_nonce_prefix`, `diamondPerm_nodup` | Length 52 assumes a 39-card nonce. Prefix stability is `List.take`. |
| S7 | Hand↔math refinement | Open | none | SPEC / player-sheet audit; not Lean in this drop. |
| S8 | Differential toy search; avalanche vs \(N_r\) | **Evidence** only | none | Do not promote to a security result. |
| S9 | Slide probes | **Evidence** only | none | A zero-hit sample is not a proof. |
| S10 | Permutation / seat-Hamming stats | **Evidence** only | none | Toy metrics. |
| S11 | ECB identical-block leak; CTR KP recovery under nonce reuse | **Proof** (Compose algebra) | `Compose.lean` (`compose_kp_unique`, `compose_kp_unique_52`); `Modes.lean` (`ctr_kp_unique_52`, `ctr_nonce_prefix_stable`, `compose_ecb_equal_blocks`) | Algebra of Compose, not an end-to-end demo script. |
| S12 | Unkeyed peel: `full_round = Compose(unkeyed(M), K)` | **Proof** | `Round.lean`: `fullRound_peel`, `fullRoundNoMix_peel` | Definitional. |
| S13 | §5.3 bytes ↔ deck; `0x80` pad strips uniquely | **Evidence** | none in Lean | `primitives/cipher/doubledeal/encoding.test.mjs` and `demos/doubledeal/cards.js`. Same digit convention as §5.2. |

**Suggested order:** S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7. Keep S8–S10 as evidence notebooks. Cycle structure of PassKey stays evidence.
