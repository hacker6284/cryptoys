<!-- Owns: the MegaDreifach proof ledger (what is proved, what is open, the security status of the v1 grip rule, how to build and check it). Maintenance rules: ../../DOCS.md. This file is checked by check_axioms.py --selftest, see DOCS.md. -->
# MegaDreifach proofs

Normative product name: **MegaDreifach**. The puzzle/group library stays **megaminx**.

> **Pinned to MegaDreifach v1 (deprecated).** This package models the frozen v1, [`v1/SPEC.md`](../../primitives/hash/megadreifach/v1/SPEC.md) plus [`v1/megadreifach.sudo`](../../primitives/hash/megadreifach/v1/megadreifach.sudo), not the current v2. `lean/Generated/` is emitted from that sudo (`proofs/emit_lean.sh` target `megadreifach`), `vectors/` and `MegaDreifachHeavy/Kat.lean` use the v1 KAT file [`kats/megaminx_hash_kats_v1.json`](../../primitives/hash/megadreifach/kats/megaminx_hash_kats_v1.json), and the model, Link 2 and `Security/` are about the v1 grip rule. **No theorem here is about v2** until the package is ported. Why v1 is deprecated: the [`v1/SPEC.md`](../../primitives/hash/megadreifach/v1/SPEC.md) banner. Below, "sudo" and "Hash" mean the v1 ones.

Sudo is normative. Emitted Lean under `lean/Generated/` is the algorithm (`v_Hash`). `lean/MegaDreifach/` is the obligation ledger for algebraic stones sudo does not express. It is not a second `Hash`. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

MegaDreifach is a toy Merkle–Damgård hash on the megaminx group. The Lean package below proves **correctness / algebraic** facts (position legality, group law, encodings, pad injectivity, DM algebra). It does **not** prove collision resistance, ideal-cipher-on-G, or AES-class security. A green `lake build` is not a security claim. The `MegaDreifach.Security` modules add an MD reduction and proved *weaknesses* of the v1 grip rule, including a kernel-checked IV-anchored `Hash` collision; see [Security status](#security-status).

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Do not read the pad theorems as “LE is gone.”

## Three layers (be honest)

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the proof-only model** | Position legality, compose/inverse, rank packing, φ injectivity, pad injectivity, DM / 3-solve algebra, `require_permutation`, G2 one-card *reduction*. | Lean kernel. `lake build` of the proof package. **Not** Hash. |
| **(b) Generated TAP** | `proofs/emit_lean.sh` → `lake` → `megadreifach_test` (11/11). | Compiled emitted Lean. **Not** a sudo=Lean theorem. |
| **(c) KAT metadata + KAT theorems** | Pad lengths, block counts, digest width, `\|G\|` in `vectors/` via `lake exe megadreifach`. All 8 exported KATs are also kernel-checked theorems about `Generated.v_Hash` (M13; `MegaDreifachHeavy/Kat.lean`, non-default lean_lib, ~8 min of kernel `decide!`). | Compiled Lean evaluation (metadata); Lean kernel (KAT theorems, `lake build MegaDreifachHeavy`). |
| **(d) Equivalence** | sudo text = generated Lean, or `hashBlocks` = `Generated.v_Hash`. | **`hashBlocks` = `Generated.v_Hash` PROVED on `PadWf`** (`v_Hash_eq_hashBlocks`). Sudo text ↔ generated Lean (Link 1) is still OPEN: the emitter is trusted. |

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| M1 | Position model + legality predicates | Proved |
| M2 | Compose associative; inverse round-trip (hypothesized perm inverses) | Proved |
| M3 | Digest rank packing: mixed-radix components, even last-pair, 29-byte inj, `listOf` inj; digest encoding injective on legal and on reachable positions | Injectivity proved; surjectivity / unrank open (see below). Packing layer in `Rank.lean`. The glue is done: `evenRank_inj` (even permutations), `positionToBytes_inj_legal`, `positionToBytes_inj_reachable` (`Security/DigestInj.lean`), with the DM parity invariant `isLegal_chR` / `isLegal_chainMsg` (`Security/Parity.lean`) |
| M4 | Factoradic φ injective for `n < 2^{224}` | Proved |
| M5 | Pad B=28 injective; length field recovers bit length | Proved |
| M6 | DM `h' = compose h e`; 3-solve restores `(h', h'⁻¹, id)` | Proved |
| M7 | `HashDeckBody` rejects non-permutations | Proved |
| M8 | One-card G2 injectivity | Reduction proved; 60×52 net distinctness OPEN |
| M10 | F3 t=12 is a well-defined iterate | Proved (algebraic) |
| M11 | IV-COOK12 arrays satisfy legality predicates | Proved (kernel `decide` on the lists) |
| M12 | MD chain is the fold of DM; digest of the final `h` | Proved (algebraic) |
| Link 2 | `pad_message` ≃ algebraic `pad` on `PadWf` (bytes `≤ 255`, `8 * length` fits in an i64) | Proved (`pad_message_refines`, `pad_message_refines_array`, `pad_z_refines`). Not collision resistance. Not `v_Hash`. |
| Link 2 | `compose` ≃ algebraic `compose` on `PosWf` (lengths 20/20/30/30, in-range indices, orientations `< 3` / `< 2`) | Proved (`compose_refines`, `compose_refines_array`). Trap-free i64 indices. Not `v_Hash`. |
| Link 2 | `require_permutation` ≃ algebraic `requirePermutation` on `DealWf` (length 52, nonnegative ids `< 52`, no duplicates) | Proved (`require_permutation_refines`, `require_permutation_refines_array`). Trap-free i64 indices. Not `v_Hash`. |
| Link 2 | `pack_ori2` ≃ algebraic `packOri2` on `Ori2Wf` (length 30, entries `< 2`) | Proved (`pack_ori2_refines`, `pack_ori2_refines_array`). Value `< 2^29`, one limb. Not `v_Hash`. |
| Link 2 | `pack_ori3` ≃ algebraic `packOri3` on `Ori3Wf` (length 20, entries `< 3`) | Proved (`pack_ori3_refines`, `pack_ori3_refines_array`). Value `< 3^19`, at most two limbs. Not `v_Hash`. |
| Link 2 | `even_perm_rank_big` ≃ algebraic `evenRank` on `Rank20Wf` (length 20, permutation of `0..19`, rank `< 2·10^9`) | Proved (`even_perm_rank_big_refines`, `even_perm_rank_big_refines_array`). One-limb multiply, two-limb sum. Superseded by the general row below (`even_perm_rank_big_refines_gen`: every length-20 / length-30 permutation). Not M3 injectivity. |
| Link 2 | `position_to_bytes` ≃ algebraic `positionToBytes` on `PosBytesWf` (corner rank 0, corner-ori pack 0, edge prefix `0..27`, any `Ori2Wf` edge ori) | Proved (`position_to_bytes_refines`, `position_to_bytes_refines_array`). Digest is `toBE 29 (packOri2 eo)`. `even30` = `30!/2` on a zero accumulator. Superseded by the general row below (`position_to_bytes_refines_gen`: every `InjPos` position). |
| Link 2 | `big_from_be` on `k` zero bytes (`k` fits in an i64, including the 28-byte pad block) ≃ `fromBE = 0` | Proved (`big_from_be_zeros`, `big_from_be_zeros_fromBE`, `big_from_be_zero_pad`). Empty limb list. Not a general pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 13`, and `peel_leading` of zero ≃ `(0, 0)` on that domain | Proved (`big_factorial_refines`, `peel_leading_zero`, `peel_leading_zero_digit`). `12!` is one limb; `13!` is the last one-limb×one-limb product. Digit `0 / d!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_from_be` ≃ `fromBE` on `BeShortWf` (length `≤ 3`, bytes `≤ 255`) | Proved (`big_from_be_short`, `big_from_be_short_array`, `big_from_be_byte`). Value `< 256^3 < 10^9`, one limb. Not length 4. Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_from_be` ≃ `fromBE` on `BeLimb2Wf` (length `≤ 7`, bytes `≤ 255`) | Proved (`big_from_be_limb2`, `big_from_be_limb2_array`, `big_add_byte`). Value `< 256^7 < 10^18`, at most two limbs. Not length 8. Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ factoradic digit on one limb (`d ≤ 12`, `n < 10^9`) | Proved (`peel_leading_limb`, `peel_leading_factorial`). Pair is `(n % d!, n / d!)`. Digit `1` on `d!` itself. Not `d ≥ 13`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 19`, and `peel_leading` of zero for `d ≤ 19` | Proved (`big_factorial_two`, `big_mul_two`, `peel_leading_zero_two`). `13!`–`19!` are two limbs (`19! < 10^18`); `20!` is three limbs. Zero digit `0 / d!`. Not a positive two-limb peel. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `d!` ≃ digit `1` for `d ≤ 19` | Proved (`peel_leading_factorial_two`, `divmod_sq`, `big_mul_one`). Remainder `0`. Two-limb division of values below `10^18`. Not an arbitrary positive rank. Not `20!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 20` | Proved (`big_factorial_three`, `big_mul_three`). `20! = 19! · 20` is three limbs (`10^18 ≤ 20! < 10^27`). Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 26` | Proved (`big_factorial_acc3`, `big_mul_acc3`). `21!`–`26!` multiply a three-limb accumulator by `i ≤ 26` and stay below `10^27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `d!` ≃ digit `1` for `d ≤ 26` | Proved (`peel_leading_factorial_three`, `divmod_cube`, `big_mul_one_three`). Remainder `0`. For `d ≥ 20`, `d!` is three limbs (`26! < 10^27`). Not an arbitrary positive rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of zero ≃ `(0, 0)` for `d ≤ 26` | Proved (`peel_leading_zero_three`, `peel_leading_zero_digit_three`). Digit `0 / d!`. For `d ≥ 20`, `d!` is three limbs; the closing multiply is the zero coefficient. Not a positive rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n < d!` ≃ `(n, 0)` for `d ≤ 26` | Proved (`peel_leading_below`, `peel_leading_below_digit`). Digit `0`. Positive two-limb ranks for `13 ≤ d` and three-limb ranks for `20 ≤ d`, strictly below `d!`. Not `d!` itself. Not a positive digit. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n` in `[d!, 2·d!)` ≃ digit `1` for `d ≤ 19` | Proved (`peel_leading_one`, `peel_leading_one_digit`). Remainder `n - d!`, which may be positive. For `13 ≤ d` the rank is two limbs (`2·19! < 10^18`). Not `d ≥ 20`. Not a digit `q ≥ 2`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n` in `[d!, 2·d!)` ≃ digit `1` for `d ≤ 26` | Proved (`peel_leading_one_three`, `peel_leading_one_three_digit`, `mag_sub_three_le`). Remainder `n - d!`, which may be positive. For `20 ≤ d` the rank is three limbs (`2·26! < 10^27`). Not a digit `q ≥ 2`. Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ `(n % d!, n / d!)` for `d ≤ 26` and `n < limbCap d` | Proved (`peel_leading_cap`, `peel_leading_cube`, `peel_leading_sq`). Every digit, including `q ≥ 2`. Cap is `10^9` / `10^18` / `10^27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_divmod_small` ≃ `n / d` on any width, divisor one limb | Proved (`big_divmod_small_refines`, `big_divmod_nat`). Not `big_mul`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_mul` of a wide left factor by one limb ≃ `natLimbs (q · n)` | Proved (`big_mul_wide_refines`, `big_mul_nat`). Accumulator on the left. Not `v_Hash`. |
| Link 2 | `big_mul` of one limb on the left by a wide digit string ≃ `natLimbs (q · n)` | Proved (`big_mul_left_refines`, `big_mul_left_nat`). Digit times a wide factorial, the orientation `peel_leading` emits. Not `mag_sub`. Not `peel_leading` for `d > 26`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 51` | Proved (`big_factorial_51`). `51! < 10^72`, at most eight limbs. Not `peel_leading` for `d > 26`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `mag_sub` ≃ `n - m` on canonical limbs, any width, `m ≤ n` | Proved (`mag_sub_nat`). Trimmed digits are `natLimbs (n - m)`. Not `v_Hash`. |
| Link 2 | `mag_add` / `big_add` ≃ `n + m` on canonical limbs, any width | Proved (`mag_add_limbs`, `mag_add_nat`, `big_add_nat`). Trimmed digits are `natLimbs (n + m)`. `FitsLen` of the longer string plus one covers the final carry. Not the 28-byte `big_from_be`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_from_be` ≃ `fromBE` on `BePadWf` (length `≤ 28`, bytes `≤ 255`) | Proved (`big_from_be_pad`, `big_from_be_pad_array`, `fromBE_pad_lt_limb8`). `256^28 < 10^72 = limbBase^8`, at most eight limbs; value is `bigOf (natLimbs (fromBE bs))`. Each step `acc * 256 + b` is `big_mul_nat` then `big_add_nat`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ `(n % d!, n / d!)` for `d ≤ 51` and `n / d! < 10^9` | Proved (`peel_leading_51`). One-limb digit. `n < 10^81`. Not a 28-byte `big_from_be`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `phi_chunk` ≃ `phiUnrank (fromBE bs)` on `PhiChunkWf` (length 28, bytes `≤ 255`) | Proved (`phi_chunk_refines`, `phi_chunk_refines_array`, `phiChunkStep_lt`, `phiChunkStep_51`). Outer `chain_loop` runs `phiState` from `0` to `51`, peeling `(rank % d!, rank / d!)` and erasing the drawn card; the last step breaks at `phiState rank 52` with `out = embed (phiUnrank rank)`. Not `phi_inv`. Not `v_Hash` on its own (see the `v_Hash` row below). |
| Link 2 | `v_Hash` ≃ algebraic MD hash on `PadWf` (bytes `≤ 255`, `8·len` fits in an i64) | Proved (`v_Hash_refines`, `v_Hash_refines_array`, `v_MegaDreifach_refines`, `v_Hash_eq_hashBlocks`; `Link2/VHash.lean`). The spec `vhashAlg msg` is `positionToBytes` of `foldl (fun h blk => Em.dmStep h (phiUnrank (fromBE blk))) Em.ivCook12` over the 28-byte blocks of `pad msg`. No traps on `PadWf`. `v_Hash` never calls `phi_inv`. Not `v_HashDeck`. Not collision resistance. Link 1 (sudo = Generated) still trusted. |
| Link 2 | All 8 hash KATs as theorems about `Generated.v_Hash` | Proved (`MegaDreifachHeavy/Kat.lean`: `kat_empty`, …, `kat_multi_100`). Each is stated once, `v_Hash (embed (hexBytes Vectors.vec_<name>.msgHex)) = .ok (embed (hexBytes Vectors.vec_<name>.digestHex))`, on the strings of `Vectors.lean`, which `vectors/json_to_lean.py` generates from the v1 KAT JSON (`--check` in CI). The generated `KatSpecCheck.lean` (a program run after a clean heavy build) pins each `kat_<name>` type to an `Expr` over the real `v_Hash` / `embed` / `hexBytes` / `vec_<name>` and rejects any `[init]` / `[builtin_init]` in the package, so a local shadow or an import-time hook fails the heavy job (planted negatives: `vectors/katspec_negatives.py`, CI job `megadreifach-lean`). Kernel `decide!` (no `native_decide`) through per-block literal chaining values. Non-default lean_lib `MegaDreifachHeavy` (~8 min), CI job `megadreifach-heavy`. |
| Link 2 | `em_block` ≃ `Em.emBlock` (the whole E_m, a typed transliteration of the sudo) for any deal of length `≥ 52` | Proved (`em_block_refines`, `dm_step_refines`, `body_from_refines`; `Link2/EmBlock.lean`). Typed transliteration of E_m (tables copied verbatim) in `Em.lean`. Also `face_turn`, `inverse`, `noon_phys`, `spin_about_up`, `abs_reorient`, `corner_slot`, `colour_on`, `colours_at`, `recipe_a`, `g2_step`, `f3_step`, `iv_cook12` (`Link2/{FaceTurn,Inverse,EmHelpers,EmCorner,EmRecipe,EmSpin,EmStep,EmInv,EmIv}.lean`). The `recipe_a` trap branches are unreachable via the `GripOk` invariant. |
| Link 2 | `position_to_bytes` ≃ `positionToBytes` on every `InjPos` position (injective `cp` / `ep` tables) | Proved (`position_to_bytes_refines_gen`; `Link2/PosBytesGen.lean`). Multi-limb (`< 10^72`) bigint pipeline, `big_to_be_gen`. Supersedes the `PosBytesWf` row. |
| Link 2 | `even_perm_rank_big` ≃ `evenRank` on every length-20 / length-30 permutation (`PermNWf`) | Proved (`even_perm_rank_big_refines_gen`, `even_perm_rank_big_refines_20`, `_30`; `Link2/EvenRankGen.lean`). Multi-limb ranks via `big_mul_nat_gen`. Supersedes the `Rank20Wf` row. |
| Link 2 | `big_mul` ≃ Nat product on arbitrary normalised limb lists (`FitsLen` of the total length) | Proved (`big_mul_gen_refines`, `big_mul_nat_gen`; `Link2/MulGen.lean`, `Link2/MulGenMath.lean`). |
| Link 2 | `big_to_be` ≃ `toBE w v` for `v < 10^72`, `v < 256^w` | Proved (`big_to_be_gen`). |
| Link 2 | Invariant `InjPos`: holds at `ivCook12`, preserved by compose, faceMove, faceTurn, g2Step, f3Step, emBlock, dmStep | Proved (`Link2/InjInv.lean`). |
| Link 2 | `body_from` / `v_HashDeckBody` refined to digest bytes | Proved (`body_from_refines_full`, `v_HashDeckBody_refines`). `v_HashDeck` itself is not (`phi_inv` is closed separately). |
| Link 2 | `phi_inv` ≃ `toBE 28 (lehmerRank deal)` on `PhiInvWf` (length 52, permutation of `0..51`, `lehmerRank < 2^224`) | Proved (`phi_inv_refines`, `phi_inv_refines_array`, `phiInvStep_lt`, `phiInvStep_51`, `phiInvFind_breaks`, `mag_cmp_eq`, `magCmp_lt_natLimbs`, `ToBePad.big_to_be_pad`). Outer `chain_loop` runs `phiState` from `0` to `51`, folding `n := n * (52 - i) + idx` (`big_from_int` / `big_mul` / `big_add`), erasing `idx`, asserting `n < 2^224` (`mag_cmp` on canonical limbs), and emitting `big_to_be n 28`. Result is `embed (toBE 28 (lehmerRank deal))`. Not `v_HashDeck`. |

## What is open or not claimed

| Stone | Claim | Status |
| --- | --- | --- |
| M3 (unrank) | Surjectivity of the digest encoding onto `[0, \|G\|)`; a computable `rankPosition` inverse (unrank) | **OPEN.** Injectivity is proved (see M3 above: `evenRank_inj`, `positionToBytes_inj_legal`, `positionToBytes_inj_reachable`, `isLegal_chR`); surjectivity and unrank are not. |
| M8 (nets) | Pairwise distinctness of the 60×52 concrete face-turn nets | OPEN. Too large for kernel `decide`. Not a blocker. |
| M9 | Abs-G2 L2 mid-block: no 2-card local collision | OPEN (sketch in [STONES.md](STONES.md)). Informal proof in research `G2_PROOF.md`. Not a blocker. |
| — | sudo text equals generated Lean (Link 1) | OPEN; the emitter is trusted. The algebraic fold = `Generated.v_Hash` half is proved on `PadWf` (`v_Hash_eq_hashBlocks`). See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). |
| — | `Generated.v_HashDeck` refinement; Scramble algebraic ≃ Generated | OPEN. Pad, `compose`, `require_permutation`, `pack_ori2`, `pack_ori3`, length-20 `even_perm_rank_big` (`Rank20Wf`), zero-rank `position_to_bytes` (`PosBytesWf`), zero-byte `big_from_be`, short, two-limb, and 28-byte `big_from_be` (`BePadWf`, length `≤ 28`), `big_factorial` (`n ≤ 51`), `peel_leading` below `limbCap d` for `d ≤ 26`, `peel_leading` for `d ≤ 51` when `n / d! < 10^9` (`peel_leading_51`), arbitrary-width `mag_sub` (`mag_sub_nat`), arbitrary-width `mag_add` / `big_add` (`mag_add_limbs`, `mag_add_nat`, `big_add_nat`), arbitrary-width `big_divmod_small`, wide-by-small `big_mul`, one-limb-times-wide `big_mul` (`big_mul_left_nat`), 28-byte `phi_chunk` (`PhiChunkWf`, length `≤ 28`), and `phi_inv` on 52-card deals (`PhiInvWf`, `lehmerRank < 2^224`, `toBE 28`) are closed, and so is full `v_Hash` on `PadWf` (`v_Hash_refines`). Still open: `v_HashDeck` (it calls `phi_inv`; the `phi_inv` refinement itself is closed). Not collision resistance. |
| — | Collision resistance of Hash; IV-anchored collision resistance | Not claimed, and **false for v1**: IV-anchored `Hash` collisions are practical (3-card local collisions from swapping two same-rank cards two apart, ≈2^12–2^13 compressions; a concrete pair is kernel-checked, `SwapCollision.v_Hash_swap_collision`, and measured by `security/suit_blind_collision.py`). Free-start `HashDeckBody` is broken; L3 collisions **exist**, and occur at a practical rate in real blocks. Under the v1 grip rule the compression function also has pseudo-collisions (reduction to a squaring collision proved, `dmStep_pseudo_collision`; pairs demonstrated on the real function); see [Security status](#security-status) |
| — | Ideal-cipher-on-G / PRF of `E_m` | Not claimed. Under the v1 grip rule `E_m` is not an ideal cipher (`emBlock_word`, a 2-query distinguisher) |
| — | Birthday ≈ 2^113 as a theorem | SPEC honesty only |
| — | Relative reorient L2-safety | Disproved in research; abs only. Not a Lean target |
| — | PRESSURE.md attack tables | Evidence / research. Never theorems |

## Security status

Scope: MegaDreifach v1. Its E_m uses the v1 **Recipe A grip rule**, called "v1 of the grip rule" here (the v1 SPEC's "Public v1 Body" API name is unrelated). Recipe A re-grips by reading one corner cubie, after the card's held-face, noon and Front turns. Lean files: `lean/MegaDreifach/Security/`. Report, scripts and recorded logs: [`security/REPORT.md`](security/REPORT.md). None of this is a security claim.

| Result | Status | Grip rule |
| --- | --- | --- |
| MD reduction: a `v_Hash` collision or second preimage on `PadWf` messages yields a compression (`dmBlock`) collision; the pad is suffix-free (MD strengthening) | Proved (`md_collision`, `pad_suffix_free`, `blocks_suffix_free`, `extract_collision_comp`, `extract_second_preimage_comp`, `v_Hash_collision_comp`, `v_Hash_second_preimage_comp`) | Independent |
| Digest encoding injective on reachable chaining values (M3 glue) | Proved (`evenRank_inj`, `isLegal_chR`, `isLegal_chainMsg`, `positionToBytes_inj_legal`, `positionToBytes_inj_reachable`). Surjectivity / unrank is open | Independent |
| Ideal-cipher counting cores (BRS Davies–Meyer) | Proved (`dm_forward_bad_count`, `dm_inverse_bad_count`). The probabilistic bound is on paper only, and it does **not** apply to v1 (E_m is not an ideal cipher) | Independent |
| E_m is corner-driven: same corners ⇒ same left-multiplying word; the corner chain is its own ≈90.2-bit MD hash and fixes the top ≈90.2 digest bits | Proved (`emBlock_word`, `dmStep_word`, `foldl_dmBlock_sameCorners`, `digest_top_collision`) | **v1 only** (corner-only read) |
| Pseudo-collisions of the compression function for every block and corner part | Reduction proved: same corners and `(hW)² = (h'W)²` ⇒ equal `dm` outputs (`dmStep_collision_of_sq`, `dmStep_pseudo_collision`). That such pairs exist for every block and corner part is argued on paper (two edge involutions) and demonstrated on the real function (`security/pseudo_collision.py`, 50/50); it is not a Lean theorem | **v1 only** (corner-only read) |
| **Practical IV-anchored `Hash` collisions.** The Recipe A read comes after the noon turn, so for ≈71.5% of cards the new grip ignores the suit. Swapping two same-rank cards two apart is then a 3-card local collision about once in 2,800 tries (three apart ≈1/16,000; adjacent 0/224,315, so M9 stays open). That is ≈2^12–2^13 compressions per collision | **Measured on the real hash** (`security/suit_blind_collision.py`, per-distance rates with 95% intervals, committed logs; the pre-noon control removes them, see below). One 28-byte pair (digest `0084d6d1…c34e82`) is kernel-checked for the generated `v_Hash` (`SwapCollision.v_Hash_swap_collision`; only 7-card prefixes are evaluated, so it is in the default library) | **v1 only** (read after the noon turn) |
| **Practical second preimages of long targets**, by the same swaps: found for 65/100 random 1,000-block (28 KB) targets and 30/30 3,000-block targets, ≈2^12–2^12.6 compressions per target; ≈1 vulnerable block in 900. Also a related-key distinguisher of E_m (≈1/2,800 vs ≈2^−226) | **Measured** (same script and logs) | **v1 only** (read after the noon turn) |
| Preimage, and second preimage of short targets: ≈2^93–2^96 | **Estimate** extrapolated from toy-scale runs (F4); not run at full size | **v1 only** (corner-only read) |

The v1 results come from two separate causes, and a new grip rule should fix both:
* **the corner-only read** (`CornerDriven.lean`, `FreeStart.lean`; the F4 estimate): the grip must also depend on edges;
* **the read after the noon turn** (`SwapCollision.lean`, the measured collisions and second preimages): every re-grip must depend on the suit, e.g. by reading right after the held-face turn.

In-tree control (`security/suit_blind_collision.py --variant pre-noon`, log `security/logs/suit_blind_collision_pre_noon.log`; REPORT §3.5): keeping Recipe A and moving only the read to right after the held-face turn removes the swap collisions. On the same 12,000 IV blocks, distance 2 goes from 15/35,175 to 0/35,175 (distances 1–4: 17/139,490 → 0/139,490), and the suit-blind fraction from 0.715 to 0. That an edge-reading rule which still reads after the noon turn keeps the collisions is out-of-tree evidence only (see the report), so "fixing A alone does not fix F5" is expected but not shown here. The rule-independent files, including `StepWord.lean`, which holds the `Em` step lemmas, still need the local repairs listed in the report (§1.5) if E_m changes, mainly `StepWord` and `MDReduction.injPos_chR_from`.

## Lean packages

Two Lake packages, toolchain **4.14.0**, no Mathlib — same pin as DoubleDeal.

**Generated (algorithm).** Do not edit:

```sh
proofs/emit_lean.sh megadreifach
cd proofs/megadreifach/lean/Generated && lake build && ./.lake/build/bin/megadreifach_test
```

**Proof-only.** From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/megadreifach/lean
lake build
```

`lake exe megadreifach` prints a one-line summary **and** runs the KAT metadata checks. The library target is `MegaDreifach`. `python3 ../../doubledeal/check_axioms.py megadreifach` (the one shared axiom gate; `#audit_all` comes from the core-only package [`proofs/audit`](../audit/README.md)) audits every theorem of the library (only `propext`, `Classical.choice`, `Quot.sound`). `python3 ../vectors/json_to_lean.py --check` checks `MegaDreifach/Vectors.lean` against the v1 KAT JSON.

The 8 KAT theorems (M13) are in the separate, non-default library `MegaDreifachHeavy` (about 8 min of kernel evaluation):

```sh
lake build MegaDreifach MegaDreifachHeavy
lake env lean --run KatSpecCheck.lean   # no [init] hooks; KAT statements exact
python3 ../../doubledeal/check_axioms.py megadreifach-heavy
```

CI builds and audits it in the `megadreifach-heavy` job ([`.github/workflows/proofs-heavy.yml`](../../.github/workflows/proofs-heavy.yml)).

Shipped theorems contain no `sorry` and no `native_decide`. Kernel `decide` / `decide!` is used on closed numerals and finite tables (`2^224 < 52!`, `|G| < 256^29`, IV-COOK12 list predicates, the E_m SPEC tables, the KAT evaluations). CI also emits Lean from [`v1/megadreifach.sudo`](../../primitives/hash/megadreifach/v1/megadreifach.sudo) and runs Generated TAP.

## Reading order

M1 → M2 → M4 → M5 → M7 → M3 (packing) → M6 → M10/M11/M12 → M8 reduction → Link 2 (`Link2.lean`, then `Link2/VHash.lean`) → Security (`Security.lean`; imports follow use: MDGeneric → MDReduction; StepWord (the `Em` step lemmas); MDReduction + StepWord → Parity → DigestInj; MDReduction → IdealCount; the v1 weaknesses MDReduction + StepWord → CornerDriven, CornerDriven + Parity → FreeStart, and SwapCollision on Link 2 alone). Leave M8 nets and M9 OPEN. `hashBlocks` equals `Generated.v_Hash` only on `PadWf` and only through `v_Hash_eq_hashBlocks`; the sudo → Generated emit is still trusted. Do not promote pressure tables or L3-absence slogans.
