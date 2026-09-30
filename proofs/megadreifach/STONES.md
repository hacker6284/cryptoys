# MegaDreifach — Lean stone throws (correctness only)

Product: **MegaDreifach** (three-megaminx MD hash; name locked 2026-09-24).
Taxonomy: follow `proofs/README.md`. **Correctness** stones only. No collision-resistance, no bit-security slogans, no promoting pressure tables to theorems.
Length extension on bare Hash is **accepted by design** (SHA-2-shaped) — do not “prove away” LE; the pad theorems show injectivity and length recovery, which is exactly why classic MD length-extension still applies.

A green Lean build is not a security claim.

**Every stone below is about MegaDreifach v2 (C36)**, the current version (`primitives/hash/megadreifach/SPEC.md`, `megadreifach.sudo`): `Generated/` is emitted from that sudo and the KAT stones use the v2 KAT file. The frozen v1 weakness proofs are in `proofs/deprecated/megadreifach-v1/` (its README).

## Must-ship

| ID | Claim | Status | Lean coverage |
|----|--------|--------|---------------|
| M1 | Megaminx **position** model + legality predicates (even cp, co parity, even ep, eo parity as in SPEC.md) | **Proved** | `lean/MegaDreifach/Position.lean`: `Position`, `isLegal`, `identity_isLegal`, `legal_*`, `listOf_inj`, `listOfOri_inj` |
| M2 | Face turns / left-multiply action; **compose** associative; **inverse** round-trip | **Proved** | `Group.lean`: `compose_assoc`, `compose_left_inv`, `compose_right_inv`, `compose_inverse_rt`, `leftMul_cancel`. Inverse takes hypothesized `icp`/`iep` (DoubleDeal-style). **Open:** discharging those hypotheses for the concrete `Em.inverse` / `permInv` (pigeonhole on `Fin n`); `inverse_refines` (Link 2) only relates `permInv` to Generated `inverse`. |
| M3 | `rank_position` / 29-byte digest encoding of legal G into `[0, \|G\|)` | **Injectivity proved; surjectivity / unrank OPEN** | `Rank.lean`: `evenComplete_even`, `evenComplete_unique`, `packOri3_inj`, `packOri2_inj`, `last_ori3_unique`, `rankLists_components_eq`, `positionToBytes_rank_inj`, `groupOrder_lt_digest`, `packOri*_unpack`. `Position.listOf_inj`. `Link2/VHash.lean`: `positionToBytes_components_eq` (for `InjPos` positions, equal digests give equal component ranks). `Link2/PosBytesGen.lean`: `rankPosition_lt_group` (`InjPos` → rank `< \|G\|`). **Glue done:** `Security/DigestInj.lean`: `evenRank_inj` (`evenRank` injective on even permutations of `0..n-1`: Lehmer prefix + even completion), `positionToBytes_inj_legal` (29-byte digest injective on `isLegal` positions), `positionToBytes_inj_reachable` (on every chaining value reachable from IV-COOK12). `Security/Parity.lean`: the DM parity invariant `isLegal_chR` / `isLegal_chainMsg` (every reachable chaining value is legal). Independent of the grip rule. Surjectivity onto `[0, \|G\|)` and a computable inverse (unrank) are OPEN. |
| M4 | Factoradic / Lehmer **φ**: injective for `n < 2^224` → 52-card permutations | **Proved** | `Factoradic.lean`: `lehmerUnrank_inj`, `phiUnrank_inj`, `phiUnrank_perm`, `two_pow_224_lt_fact_52` (kernel `decide`). Round trip φ(φ⁻¹(deal)) = deal on permutations of `0..51`: `Link2/VHashDeck.lean`: `lehmerUnrank_lehmerRank`, `phiUnrank_lehmerRank` |
| M5 | Pad **B=28** SHA-2-style: injective on messages; length field recovers bit length | **Proved** | `Pad.lean`: `pad_length_mod`, `pad_recovers_bitlen`, `unpad_pad`, `pad_injective` |
| M6 | Davies–Meyer algebra: software `h' = compose(h, E_m(h))`; hand 3-solve restores `(A,B,C)=(h', h'⁻¹, id)` | **Proved** | `DaviesMeyer.lean`: `daviesMeyer`, `threeSolve_restores`, `startTriple_invariant` |
| M7 | `HashDeckBody` domain: reject non-permutations (`require_permutation`) | **Proved** | `Domain.lean`: `requirePermutation_iff`, `requirePermutation_reject`, `requirePermutation_isSome_iff` |
| M8 | One-card G2: **card ↦ φ_card(g,o)** injective for fixed `(g,o)` (G2_PROOF Theorem A) (g injective, o `GripOk`, cards `< 52`) | **Proved for the v2 nets** | `G2.lean`: `phiCard_inj_of_distinct_nets`, `kingUpAmount_ne_ace`, `two_card_net_eq_of_state_eq`, `no_same_first_two_card_of_nets` (reductions). `G2Nets.lean`: `nets_nodup` (60 kernel `decide!` checks, one per grip), `net2_ne`, `g2Step_fst_ne`, `g2Step_ne`, `phiCard_net2_ne`. See below. |
| M9 | Abs-G2 **L2 mid-block**: no 2-card local collision under the v2 grip rule (2-card window, `InjPos` W) | **PARTIAL** | `G2Nets.lean`: `twoCard_same_first_ne` (same first card; `InjPos`, `GripOk`, cards `< 52`), `twoCard_collision_nets` (reduction to net products). Different first cards: exhaustive Python search, computational evidence, not a proof ([`m9/README.md`](m9/README.md)). |

## Strongly want

| ID | Claim | Status | Lean coverage |
|----|--------|--------|---------------|
| M10 | F3 blank rounds are pure group ops (t=36) — well-defined, deterministic | **Proved** (algebraic) | `IV.lean`: `f3Tail` (= `f3Iter step 36`, `f3Tail_eq_iterate`), `f3Iter_deterministic`. Concrete Up+1 face-turn is an argument, not a cubie table. **Open:** instantiating M10 with the real F3 step, which acts on `Position × Grip` and the round number (`Em.f3Step` / `Em.f3Run`), not `Position → Position`. |
| M11 | IV-COOK12 is a fixed legal position | **Proved** (list predicates) | `IV.lean`: `ivCook12Of_legal`, `ivCook12_lists_legal` (kernel `decide` on the COOK12 arrays). Face-turn generator is hypothesized. `Link2/EmIv.lean`: `ivCook12_isLegal` gives legality of the concrete IV directly (no hypothesized generator), `ivCook12_eq_of` shows it is `ivCook12Of` at the algebraic unit turn, `iv_cook12_refines` links it to Generated. A general `hpres` (face turns preserve `isLegal`) is still open. |
| M12 | MD chaining: multi-block compose of DM; digest of final `h` | **Proved** (algebraic) **and linked to Generated** | `Chain.lean`: `mdChain`, `hashBlocks_eq_digest_of_final`, `digestOf_length`. `Link2/VHash.lean`: `v_Hash_eq_hashBlocks` instantiates `dm := fun h b => Em.dmStep h (phiUnrank b)`, `rank := rankPosition`, `iv := Em.ivCook12`, blocks = `fromBE` of the 28-byte chunks of `pad msg`. Hypothesis: `PadWf msg`. Trusts Link 1 (sudo → Generated emit). |
| M13 | Vector agreement: proof-package digests of exported KATs match `kats/megaminx_hash_kats_v2.json` | **Proved** (8/8) | `lean/MegaDreifachHeavy/Kat.lean` (non-default lean_lib `MegaDreifachHeavy`, CI job `megadreifach-heavy`): `kat_empty`, `kat_short_abc`, `kat_short_one`, `kat_edge_27`, `kat_edge_28`, `kat_edge_29`, `kat_multi_56`, `kat_multi_100`, each stated once as `Megadreifach.v_Hash (embed (hexBytes Vectors.vec_<name>.msgHex)) = .ok (embed (hexBytes Vectors.vec_<name>.digestHex))` on the generated `Vectors.lean` (`vectors/json_to_lean.py --check` ties it to `primitives/hash/megadreifach/kats/megaminx_hash_kats_v2.json`; the generated `KatSpecCheck.lean` pins each statement to the real constants and rejects `[init]` hooks, after a heavy build from deleted outputs, CI job `megadreifach-heavy`; planted shadows and hooks: `vectors/katspec_negatives.py`, CI job `megadreifach-lean`). Algebraic side (`alg_<name>`) by kernel `decide!` (no `native_decide`). About 12 min of kernel time. Algorithm is still `Generated.v_Hash`; no handwritten `Hash`. |

## Security layer (not correctness stones)

`lean/MegaDreifach/Security/` (imported by `MegaDreifach.lean`, audited by the default gate) proves reductions and grip-rule-independent lemmas, never security. Report and scripts: `security/REPORT.md`. Summary in the README, section "Security status".

- Independent of the grip rule (all of it): MD reduction (`extract_collision_comp`, `v_Hash_collision_comp`), pad suffix-freeness (`pad_suffix_free`), steps as left multiplications by face-move words (`StepWord.lean`), digest injectivity (M3 glue above), ideal-cipher counting cores (`dm_forward_bad_count`, `dm_inverse_bad_count`).
- No Lean result about the v2 grip rule's strength or weakness, beyond the local one-card injectivity lemmas and the same-first-card two-card lemma in `G2Nets.lean` (M8, M9 same-first-card half). The v1 weaknesses (`CornerDriven`, `FreeStart`, `SwapCollision`) are proofs about v1 only and live, frozen, in `proofs/deprecated/megadreifach-v1/`.

## Explicitly out of scope (do not claim)

- Ideal-cipher-on-G / PRF of `E_m` (under v1 it is false: `MegaDreifachV1.Security.emBlock_word`)
- Collision resistance of full Hash (v2: free-start pseudo-collisions are easy, SPEC §8; v1: false, see the frozen v1 package)
- IV-anchored Hash collision resistance (v2: empirically untested beyond SPEC §8; v1: collisions from the standard IV are practical, one pair kernel-checked in the frozen v1 package)
- Free-start L3 absence (L3 **exists**; free-start `HashDeckBody` is broken)
- Birthday ≈ 2^113 as a theorem (SPEC honesty only)
- Relative reorient recipes (disproved in research; abs only)
- PRESSURE.md attack tables as theorems

## M8 — what shipped vs the informal Theorem A

G2_PROOF Theorem A: for every fixed `(g,o)`, `card ↦ φ_card(g,o)` is injective, because the 52 face-turn nets `T_card(o)` are pairwise distinct and left-multiply.

**Shipped (sorry-free):**

1. Left-multiplication cancels when `g.cp` / `g.ep` are injective (`leftMul_cancel`).
2. Therefore distinct nets ⇒ distinct one-card states (`phiCard_inj_of_distinct_nets`).
3. King-up amount `−k` differs from Ace `+k` for every legal `k` (`kingUpAmount_ne_ace`) — the soft-lock reason King is not Ace.
4. Same-first-card 2-card states differ once the second-card nets differ (`no_same_first_two_card_of_nets`) — G2_PROOF §3 corollary as a reduction.
5. **v2 nets (`G2Nets.lean`).** `net2 o card` is the G2 step from the identity; every card step is `compose (net2 o card) g` (`g2Step_fst_net`). For each grip `rotAt s` (`s < 60`), `nets_nodup_<s>` checks by kernel `decide!` that the 52 corner permutations `listOf (net2 (rotAt s) c).cp` are pairwise distinct. The checks are split per grip: one check over all 60 grips at once runs out of memory. `nets_nodup` collects them, and `net2_ne` gives distinct nets on every `GripOk` grip. With `leftMul_cancel` this makes one card step injective in the card from any position with injective `cp` / `ep` (`g2Step_fst_ne`, `g2Step_ne`; every `InjPos` chaining value qualifies). Scope: one card, fixed grip. The v1 nets are not covered.

## M9 — two-card windows (PARTIAL)

Shipped in `G2Nets.lean`: the same-first-card half (`twoCard_same_first_ne`, M8 at the intermediate grip) and the reduction of a different-first-card position collision to an equality of net products (`twoCard_collision_nets`). The different-first-card half is exhaustive computational evidence (`m9/m9_search.py`), not a proof. Its numbers, the argument, the obstacle to a kernel proof and the limits (2-card window only, not block-level) are in [`m9/README.md`](m9/README.md). M9 stays PARTIAL.

Do **not** claim M9 from the Python scan. Relative recipes are **disproved** (do not “prove” their L2-safety). L3 abs collisions **exist** (do not prove L3 absence).

## Layout

```text
proofs/megadreifach/
  README.md
  STONES.md
  lean/                 # Lake project (toolchain 4.14.0, no Mathlib)
                        #   MegaDreifach (default lib), MegaDreifachHeavy (KATs, non-default)
  vectors/              # KAT copy; json_to_lean.py generates lean/MegaDreifach/Vectors.lean
  m9/                   # M9 two-card window search (v2; Python 3, stdlib only) + write-up
  security/             # REPORT.md + attack scripts (v1 grip rule; Python 3, stdlib only; suit_blind_collision.py = practical v1 collisions)
proofs/audit/          # shared `#audit_all` package (core-only)
proofs/doubledeal/check_axioms.py   # the shared axiom gate (modes megadreifach, megadreifach-heavy, megadreifach-v1-deprecated)
primitives/hash/megadreifach/   # the primitive: v2 SPEC + megadreifach.sudo (what this package models) + kats/ (v1 and v2 KAT files)
primitives/hash/megadreifach/v1/  # frozen, deprecated v1: SPEC.md + megadreifach.sudo
proofs/deprecated/megadreifach-v1/ # frozen v1 Lean: the v1 weakness proofs + their closure (MegaDreifachV1)
```

Hand-written Lean is not a proof that `megadreifach.sudo` equals this model. Link 2 (`Generated.v_Hash` = the algebraic fold on `PadWf`) is proved; Link 1 (sudo text = emitted Lean) is trusted, not proved ([`../LINK1.md`](../LINK1.md)). M9 is PARTIAL.
