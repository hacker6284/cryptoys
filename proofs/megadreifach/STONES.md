# MegaDreifach — Lean stone throws (correctness only)

Product: **MegaDreifach** (three-megaminx MD hash; name locked 2026-09-24).
Taxonomy: follow `proofs/README.md`. **Correctness** stones only. No collision-resistance, no bit-security slogans, no promoting pressure tables to theorems.
Length extension on bare Hash is **accepted by design** (SHA-2-shaped) — do not “prove away” LE; the pad theorems show injectivity and length recovery, which is exactly why classic MD length-extension still applies.

A green Lean build is not a security claim.

## Must-ship

| ID | Claim | Status | Lean coverage |
|----|--------|--------|---------------|
| M1 | Megaminx **position** model + legality predicates (even cp, co parity, even ep, eo parity as in `megaminx.py`) | **Proved** | `lean/MegaDreifach/Position.lean`: `Position`, `isLegal`, `identity_isLegal`, `legal_*`, `listOf_inj`, `listOfOri_inj` |
| M2 | Face turns / left-multiply action; **compose** associative; **inverse** round-trip | **Proved** | `Group.lean`: `compose_assoc`, `compose_left_inv`, `compose_right_inv`, `compose_inverse_rt`, `leftMul_cancel`. Inverse takes hypothesized `icp`/`iep` (TwoDeck-style). |
| M3 | `rank_position` / 29-byte digest **bijection** on legal G ↔ `[0, \|G\|)` | **Proved at packing layer** | `Rank.lean`: `evenComplete_even`, `evenComplete_unique`, `packOri3_inj`, `packOri2_inj`, `last_ori3_unique`, `rankLists_components_eq`, `positionToBytes_rank_inj`, `groupOrder_lt_digest`, `packOri*_unpack`. `Position.listOf_inj`. **Open glue:** `evenRank` injectivity on even `S_n` as one theorem (Lehmer prefix + even completion). No `sorry` stand-in. |
| M4 | Factoradic / Lehmer **φ**: injective for `n < 2^224` → 52-card permutations | **Proved** | `Factoradic.lean`: `lehmerUnrank_inj`, `phiUnrank_inj`, `phiUnrank_perm`, `two_pow_224_lt_fact_52` (kernel `decide`) |
| M5 | Pad **B=28** SHA-2-style: injective on messages; length field recovers bit length | **Proved** | `Pad.lean`: `pad_length_mod`, `pad_recovers_bitlen`, `unpad_pad`, `pad_injective` |
| M6 | Davies–Meyer algebra: software `h' = compose(h, E_m(h))`; hand 3-solve restores `(A,B,C)=(h', h'⁻¹, id)` | **Proved** | `DaviesMeyer.lean`: `daviesMeyer`, `threeSolve_restores`, `startTriple_invariant` |
| M7 | `HashDeckBody` domain: reject non-permutations (`require_permutation`) | **Proved** | `Domain.lean`: `requirePermutation_iff`, `requirePermutation_reject`, `requirePermutation_isSome_iff` |
| M8 | One-card G2: **card ↦ φ_card(g,o)** injective for fixed `(g,o)` (G2_PROOF Theorem A) | **Reduction proved; nets OPEN** | `G2.lean`: `phiCard_inj_of_distinct_nets`, `kingUpAmount_ne_ace`, `two_card_net_eq_of_state_eq`, `no_same_first_two_card_of_nets`. Does **not** enumerate the 60×52 concrete nets. |
| M9 | Abs-G2 **L2 mid-block**: no 2-card local collision under Recipe A | **OPEN** | Structure only. See plan below. Do not ship a `sorry` theorem. |

## Strongly want

| ID | Claim | Status | Lean coverage |
|----|--------|--------|---------------|
| M10 | F3 blank rounds are pure group ops (t=12) — well-defined, deterministic | **Proved** (algebraic) | `IV.lean`: `f3_12`, `f3Iter_deterministic`. Concrete Up+1 face-turn is an argument, not a cubie table. |
| M11 | IV-COOK12 is a fixed legal position | **Proved** (list predicates) | `IV.lean`: `ivCook12Of_legal`, `ivCook12_lists_legal` (kernel `decide` on the COOK12 arrays). Face-turn generator is hypothesized. |
| M12 | MD chaining: multi-block compose of DM; digest of final `h` | **Proved** (algebraic) | `Chain.lean`: `mdChain`, `hashBlocks_eq_digest_of_final`, `digestOf_length` |
| M13 | Vector agreement: Lean digests of exported KATs match `kats/megaminx_hash_kats.json` | **OPEN** (metadata only) | `Vectors.lean` / `VectorCheck.lean`: pad lengths, block counts, digest width, `\|G\|`. Full Hash needs `E_m` (`em_spike_r4`). |

## Explicitly out of scope (do not claim)

- Ideal-cipher-on-G / PRF of `E_m`
- Collision resistance of full Hash
- IV-anchored Hash collision (empirically open; not a Lean target)
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

**OPEN (no `sorry` theorem):** pairwise distinctness of the 60×52 concrete nets. Research check: `g2_proof_core.prove_one_card` reports 0 collisions. That scan is too large for kernel `decide` and is not `native_decide` (forbidden in this tree). Follow-up options: a structured face/noon/Front case split, or a checked-in finite table with a kernel-small certificate — not this PR.

## M9 — abs-G2 L2 plan (OPEN)

Informal proof: G2_PROOF.md §3–4. Sketch for a later Lean file, **not** shipped:

1. Same-first-card 2-card collisions reduce to M8 nets (`no_same_first_two_card_of_nets`). Already a reduction here.
2. Distinct first cards: `g''` collides iff the two-card nets `T(o₁,b)∘T(o,a) = T(o₁',d)∘T(o,c)` *and* final grips match.
3. Absolute Recipe A: matching final grips forces the same second-read R3 element `r`. Same `r` on different second-card faces needs the same corner cubie in two slots after the net — the research scan reports this obstruction on every same-net / diff-first candidate (`second_cons_ok = 0`).
4. Lean needs: a grip/read model, the Recipe A update, and that cubie-slot obstruction as a lemma. The 60-grip × 2704-word scan stays a computer-checked certificate unless a uniform slot argument replaces it.

Do **not** claim M9 from the Python scan. Relative recipes are **disproved** (do not “prove” their L2-safety). L3 abs collisions **exist** (do not prove L3 absence).

## Layout

```text
proofs/megadreifach/
  README.md
  STONES.md
  lean/                 # Lake project (toolchain 4.14.0, no Mathlib)
  vectors/              # KAT export for metadata agreement
primitives/hash/megadreifach/   # megaminx group + pad/φ/domain/IV front end
                                # E_m / hash_bytes: follow-up (needs abs-G2 runner)
```
