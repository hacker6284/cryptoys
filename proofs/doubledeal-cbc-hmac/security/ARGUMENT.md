<!-- Owns: the full security argument behind DoubleDeal-CBC-Sandwich v2 SPEC §8. Maintenance rules: ../../../DOCS.md. -->
# DoubleDeal-CBC-Sandwich v2: the security argument

This is the argument that [SPEC §8](../../../primitives/aead/doubledeal-cbc-hmac/SPEC.md#8-security-honesty) summarises. The SPEC is normative; if the two disagree, this file is wrong. Nothing here is machine-checked unless it is tagged PROVED, and nothing here is a security claim for the instance. Every bound is relative to assumptions on MegaDreifach v3 and DoubleDeal that are HEURISTIC.

**Tags.** These are the tags of SPEC §8.
- **PROVED**: a named sudo test in `doubledeal_cbc_hmac.sudo` checks the claim.
- **LITERATURE**: a published theorem, used as its authors state it and not re-checked here.
- **ARGUED**: a pen-and-paper argument in this file, not machine-checked.
- **COMPUTED**: a number from a committed log in [`logs/`](logs/), produced by [`sandwich_v3_stats.mjs`](sandwich_v3_stats.mjs).
- **HEURISTIC**: an unproven assumption.
- **OUT-OF-TREE**: a number from code that is not in this repository.

Every ± is a 95% half-width (1.96 standard errors).

**Model and notation.** k_enc and k_mac are independent and uniform on S₅₂. Positions multiply as permutations. f(h, D) = h·W·h is one MegaDreifach v3 Davies–Meyer step (the v3 sudo's `dm_step`): W is the face-turn word the card phase builds from the deck D read against h. f* chains f over a list of decks. The MAC is

  tag = digest(f*(IV-COOK12, [K] ‖ S ‖ [K∘ρ])),  where K = k_mac and (K∘ρ)[i] = K[51 − i] is K turned over.

## 1. The framing is injective (ARGUED)

S = VERSION_DECK ‖ AAD decks ‖ IV ‖ C_0 ‖ … ‖ C_{n−1} ‖ LENGTH_DECK(|aad|) (SPEC §5). The map from (aad, IV, C_0..C_{n−1}) to S is injective:
- The last deck is unrank(|aad|). Since rank ∘ unrank is the identity on [0, 52!), it gives |aad|, and so the number a = ⌈|aad|/28⌉ of AAD decks.
- The a decks after VERSION_DECK rank back to 28·a bytes, the AAD zero-filled. Truncating them to |aad| gives the AAD; the length deck is what separates AADs that differ only in trailing zero bytes.
- The next deck is the IV, and the decks up to the last are C_0..C_{n−1}.

The sudo test "the MAC input: version deck first, length deck last, zero-filled AAD kept apart" checks examples of this. It does not check injectivity in general, so this stays ARGUED. The framing is not prefix-free; §4 shows what that costs.

## 2. Theorem S: Yasuda's Sandwich theorem, mapped onto whole decks

### 2.1 The source, as read (LITERATURE, partly unverified)

K. Yasuda, "'Sandwich' Is Indeed Secure: How to Authenticate a Message with Just One Hashing", ACISP 2007, LNCS 4586, pp. 355–369. §§1–7 were read, up to the end of the proof of Lemma 2. **Lemmas 3–4 (the cAU step) and §§8–10 (the optimised filling and padding variants) were not available and are unverified.** The f̌ term of the theorem comes from Lemmas 3–4.

- **Setting.** The compression is f : {0,1}^{n+d} → {0,1}^n, and h is Merkle–Damgård with strengthening π(λ).
- **Scheme.** τ = h(K ‖ 0^p ‖ M ‖ 10^ν ‖ K), with |K| = k and **p = d − k > 0**. The key fills part of a block, and the last block is K ‖ π(λ). The 10^ν padding makes the final key start a fresh block.
- **Assumptions** (a "dual family", §3 of the paper):
  - f′_K(v ‖ z) = f(v ‖ K ‖ z) is keyed through the data block. It must be a PRF against **q + 1** queries at chaining values the adversary chooses.
  - f̌_Ǩ(m) = f(Ǩ ‖ m) is keyed through the chaining value. It must be a PRF against **2** queries.
  - No related-key notion is used: the first and last key blocks are two distinct inputs of **one** PRF f′_K.
- **Side condition.** π(λ) ≠ 0^p for every λ, so the last key block never equals the first.
- **Theorem 1.** Adv^prf_S(t, q, μ) ≤ Adv^prf_{f′}(t, q+1) + C(q,2)·[2·(⌈μ/d⌉+1)·Adv^prf_{f̌}(t′, 2) + 1/2^n], with t′ = (4⌈μ/d⌉+1)·T_f.
- **Proof structure.**
  - Lemma 2 (read): f′ PRF and F̄ cAU imply that S is a PRF, with loss Adv_{f′}(q+1) + C(q,2)·Adv^au_{F̄}.
  - Lemmas 3–4 (*unverified*): f̌ PRF implies F̄ cAU.
  - π(λ) is used in one place only, the step "Game G ≡ G′". Because π(λ) ≠ 0^p, the final f′ call is never at the key-derivation input IV ‖ 0^p, so K̂ = f′(IV ‖ 0^p) is independent of all the answers.
  - F̄ is cAU on arbitrary distinct messages, so prefix-freeness is not needed.
- **The paper's own comparison with HMAC.** f′ must resist q + 1 adversary-influenced queries in Sandwich, against 2 constant queries in HMAC, so the Sandwich assumption is the stronger one.

### 2.2 The mapping

| Yasuda | Here | Tag |
| --- | --- | --- |
| chaining value in {0,1}^n | megaminx position in G, \|G\| = 2^225.90 | ARGUED (arithmetic) |
| data block in {0,1}^d | one whole deck, S₅₂, 52! = 2^225.58 | ARGUED (arithmetic) |
| f(v ‖ m) | f(v, D) = h·W·h, the v3 `dm_step` | definition |
| K ∈ {0,1}^k with p = d − k > 0 | K ∈ S₅₂ fills the **whole** block: p = 0 | **deviation 1** (one of the two the proof needs) |
| first key block K ‖ 0^p | K as it lies | |
| last key block K ‖ π(λ), π(λ) ≠ 0^p | K∘ρ, K turned over | **deviation 2**, §2.3 (the other the proof needs) |
| M ‖ 10^ν (injective padding) | S, already whole decks, injective by §1 | ARGUED (§1); see §2.4 item 3 |
| MD strengthening π(λ) | none; LENGTH_DECK is the AAD length, inside S, for framing | see §2.4 item 4; harmless (π is used only for ≠ 0^p) |
| ⌈μ/d⌉ + 1 | ℓ = number of decks of S = a + n + 3 | |
| 1/2^n | 1/\|G\| = 2^−225.90 | |

### 2.3 The reversal tweak replaces π(λ) ≠ 0^p (ARGUED)

With p = 0 there is no room for a padding field. Instead, define one keyed family with a one-bit tweak: f′_K(v, b) = f(v, K∘ρ^b), b ∈ {0, 1}.
- The MAC's first call is f′_K(IV-COOK12, 0) = f(IV-COOK12, K). Every last call is f′_K(v, 1) = f(v, K∘ρ).
- (v, 1) ≠ (IV, 0) for every K and v, because the tweak differs. Also, K∘ρ differs from K in every seat (PROVED: sudo test "turning the key over moves every card to a new seat"). The test runs on one deck, but turning over only moves seats (seat i to seat 51 − i), so a deck of 52 distinct cards with no fixed seat shows that no seat is fixed for any deck.
- So in Game G the random function f′ is never queried at (IV, 0) after key derivation, and K̂ is independent. Yasuda's G ≡ G′ step then goes through unchanged, as far as can be checked by reading the proof of Lemma 2.
- The collision event E ("F̄(M_i) ‖ π_i = F̄(M_j) ‖ π_j") reduces to F̄(M_i) = F̄(M_j), as in the paper, because the tweak is constant.

The cost: A1 below is a statement about a two-map family {K, K∘ρ}, a related-key shape with the fixed, public, key-independent class Φ = {id, ·∘ρ}. The paper needs no related-key assumption, because its two key blocks are two inputs of one key.

**Turned over, against the same key at both ends (ARGUED).** With the same K at both ends, the first and last calls are f(IV, K) and f(v, K). G ≡ G′ then needs v ≠ IV-COOK12 for every query. That is a probabilistic event (about q/|G| for a random-looking F̄), and cAU does not bound it, because cAU is about pairs of messages, not about hitting a fixed point. Turned over, the separation holds for every key and every v, deterministically. It also gives a hand player two visibly different key blocks.

### 2.4 Deviations from the paper (same numbering as §2.2)

1. p = 0: the key fills the whole block (§2.2). Yasuda needs p > 0. The proof needs this.
2. Reversal tweak: the last key block is K∘ρ instead of K ‖ π(λ) with π(λ) ≠ 0^p (§2.2, §2.3). The proof needs this.
3. The "padding" is deck framing, injective by §1, with the AAD length deck at the end instead of 10^ν. That is enough, because cAU needs only distinct block strings. This rests on the *unverified* Yasuda Lemmas 3–4.
4. No MD strengthening in the final block. That is harmless for the PRF proof (§2.1).
5. The key space is S₅₂ and the chaining space is G, not bit-string spaces. Nothing in the proof of Lemma 2 uses bit strings. 52!/|G| = 0.80, so k ≈ n, but the key space is not the chaining space.
6. The paper's §§8–10 variants are not used (and are *unverified*).

### 2.5 The statement

**Theorem S (LITERATURE, partly unverified, applied with the deviations above; the mapping is ARGUED; the assumptions are HEURISTIC).** With ℓ the maximum number of decks in S,

  Adv^prf_Sandwich(t, q, ℓ) ≤ Adv^prf_{f′}(t, q+1) + C(q,2)·[2ℓ·Adv^prf_{f̌}(t′, 2) + 1/|G|],  t′ ≈ (4ℓ+1)·T_f.

- **A1 (f′ is a PRF, keyed by the key deck; HEURISTIC).** (v, b) ↦ f(v, K∘ρ^b), for uniform K ∈ S₅₂, is indistinguishable from a random function G × {0,1} → G. The reduction uses 1 query with b = 0 (at IV-COOK12) and q queries with b = 1, at chaining values the distinguisher chooses.
- **A2 (f̌ is a PRF, keyed by the chaining value; HEURISTIC).** D ↦ f(h, D), for uniform secret h ∈ G, is a PRF against 2 queries. This is the interface of `HashDeckBodyFrom` with h secret. The MegaDreifach SPEC calls that interface broken when the attacker chooses h.

## 3. Testing A1 and A2

### 3.1 The A1 test (two queries)

The oracle O is either f′(v) = f(v, K∘ρ) for a uniform secret key deck K, or a random function G → G. The test uses only b = 1, so it applies unchanged to the same-key variant.
1. Pick a uniform position h and ask for y₁ = O(h).
2. Compute W := (h⁻¹·y₁)·h⁻¹. If O = f′, this is the block's face-turn word for (h, K∘ρ), because y₁ = h·W·h.
3. Let h′ be h with the orientations of two random edge slots flipped. This is a legal position, and h′ ≠ h. Ask for y₂ = O(h′).
4. Accept iff y₂ = h′·W·h′.

**Why it works on v2 (ARGUED).** W is the product of the face turns the block chooses, and on v2 each choice depends only on the piece values the block reads. A piece of h that the block never reads (on average 6.71 edges per C36 block, MegaDreifach v2 SPEC §8) never influences any read. So flipping two unread edges leaves W unchanged, and then y₂ = h′·W·h′ exactly. By cancellation in G, the test accepts iff the word for (h′, K∘ρ) equals W. The key deck is never needed, because W is read off y₁.

**Why it should fail on v3 (ARGUED, not a proof of A1).** v3's card phase reads all 50 pieces in every block (MegaDreifach v3 SPEC §5.8: the v3 sudo test "coverage: the 48 non-King cards name all 30 edges and all 20 corners", and a deal holds each card once). So no piece is ever unread, and the structural reason for the v2 acceptances is gone. Whether a flip still leaves W unchanged by chance is what §3.3 measures. None of this rules out other distinguishers.

**Against a random function (ARGUED).** h′ ≠ h, so y₂ is uniform on G and independent of y₁. The test therefore accepts with probability exactly 1/|G| = 2^−225.90.

### 3.2 The A2 test and E3

At a uniform secret h, query a uniform deck D and D′ = D with its cards 51 and 52 swapped. Then count the edge slots (fixE) and corner slots (fixC) that z = f(h, D)⁻¹·f(h, D′) leaves fixed. For a uniform group element, the edge permutation of z is a uniform even permutation of 30 edges, and P(fixE ≥ 2) = 0.264241; the same value holds for 20 corners (ARGUED; the harness computes the value exactly). E3 runs the same comparison on the whole Sandwich: t = f*(IV-COOK12, [K, D, L, K∘ρ]) against D′, with K and D uniform and L a fixed stand-in for the length deck.

### 3.3 Results (COMPUTED; logs in [`logs/`](logs/))

| Test | v2 build (positive control) | v3 build |
| --- | --- | --- |
| A1 | 213/4,000 accepted, 5.3% (95% CI 4.67–6.06%) | 0/100,000; one-sided 95% upper bound 3.0·10⁻⁵ on this test's per-game acceptance |
| A2 (E1) | fixE advantage +0.0704 ± 0.0119 (6,000 pairs) | 120,000 pairs: P(fixE ≥ 2) = 0.2629 [0.2604, 0.2654], advantage −0.0014 ± 0.0025; fixC +0.0002 ± 0.0025; 0 equal outputs |
| E3 | not run | 40,000 pairs: fixE −0.0016 ± 0.0043, fixC −0.0033 ± 0.0043; 0 equal tags |

**What the runs could have seen (hand-derived, not harness output).**
- A1: a per-game rate r = 2.3·10⁻⁵ gives at least one acceptance in 100,000 games with probability 1 − (1 − r)^100000 ≈ 0.90.
- A2 and E3: at the 5% level with 90% power, the detectable advantage is about (1.96 + 1.28)·√(p(1 − p)/n) with p = 0.264241. That is 0.0041 at n = 120,000 and 0.0071 at n = 40,000 (a normal approximation).

The A1 bound is on one test's acceptance probability. It is not a bound on Adv^prf_{f′}, and no finite set of tests can give one. Both assumptions on v3 stay HEURISTIC.

**Consequence for v2 (ARGUED from the COMPUTED rate).** Adv_{f′}(q+1) is non-decreasing in q, so on v2 the first term of Theorem S was at least about 0.05 already at q = 1. The theorem gave no meaningful bound there, and the INT-CTXT and IND-CCA bounds of §5 inherited that. This is why the MAC moved to v3.

### 3.4 Does the A1 test reach the real MAC? (ARGUED; open beyond that)

- **Not as stated.** The test needs two f′ inputs that the adversary knows and that differ by a known flip. In the MAC, every f′(·, 1) input is the chaining value v = F̄(K̂, S), with K̂ = f(IV-COOK12, K) secret. The single f′(·, 0) call is at the fixed IV and is never repeated. The tag reveals f′(v, 1) as a full position (a bijective 29-byte encoding, no truncation), not v.
- **Making two secret chaining values differ by a known flip (HEURISTIC).** The adversary controls only the blocks. It would need blocks L, L′ such that f(u, L) and f(u, L′) differ by a flip for an unknown u. That is a statement about f̌ (A2). No way to do it is known.
- **No MAC forgery or distinguisher is known (HEURISTIC).** Beyond §3 and the v3 statistics in `proofs/megadreifach/security/v3/`, no systematic search was made.

## 4. The generic birthday limit (ARGUED; numbers by arithmetic)

- The collision term C(q,2)/|G| is 2^−26.9 at q = 2^100 tags, 2^−2.9 at q = 2^112, and of order 1 by about 2^113. With the ℓ factor, security is gone at about 2^113/√ℓ.
- The framing is not prefix-free, so a generic length-extension forgery matches this. Suppose S and S′ reach the same internal chaining value before the final key block, and have the same AAD length (so they share the same length deck L). Then S ‖ [X, L] and S′ ‖ [X, L] have equal tags. Both extended sequences are valid framings: the old length deck becomes a ciphertext deck.
- So no argument can give more than about 2^112 for this MAC. The tag-guessing term q_v/|G| is separate.

## 5. Encrypt-then-MAC and deck-CBC

**Composition (LITERATURE: M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", ASIACRYPT 2000, and J. Cryptology 21(4), 2008).** For Encrypt-then-MAC with independent keys, INT-CTXT ≤ Adv^suf-cma_MAC, and IND-CCA ≤ 2·Adv^suf-cma_MAC + Adv^ind-cpa_Enc.

**The hypotheses hold here (ARGUED, with the named sudo tests where they exist).**
- *Encoding.* The blob determines (IV, C, tag) by fixed offsets, and rank29 is a bijection onto [0, 52!). So distinct accepted (aad, blob) pairs give distinct (S, tag) pairs (§1 plus fixed offsets). The key-free public parse is not an oracle. The sudo test "a blob number that is not a deck is rejected by the public parse" checks one case.
- *SUF-CMA = UF-CMA.* The MAC is deterministic and verification recomputes it, so SUF-CMA equals UF-CMA, and Adv^suf-cma ≤ Adv^prf_Sandwich + q_v/|G|.
- *Separate keys.* `aead_seal` and `aead_open` reject k_enc = k_mac (PROVED: sudo test "the two key decks must differ").
- *Coverage and order.* The MAC covers version, AAD, IV and C; verification comes first, over the full 29 bytes; there is one reject symbol (SPEC §7). The sudo test "aead_seal then aead_open round-trips and every tamper rejects" checks the tampers it lists. That is examples, not a proof of the order.

**IND-CPA of deck-CBC (ARGUED, relative to a HEURISTIC PRP assumption on DoubleDeal).** Adv ≤ 2·Adv^prp_DoubleDeal(σ) + 2σ²/52! + 2qσ·p_max. With uniform IVs (p_max = 1/52!) this is at most 2·Adv^prp + 4σ²/52!. The 4σ²/52! term reaches 1 at σ ≈ 2^111.8 (and 2σ²/52! at σ ≈ 2^112.3); the SPEC rounds that to about 2^112 blocks. This is the standard CBC argument (M. Bellare, A. Desai, E. Jokipii, P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", FOCS 1997) with XOR replaced by Compose. It uses only one fact: for a fixed deck D, Compose(D, ·) is a bijection of S₅₂, so Compose(D, R) is uniform when R is uniform (Haar invariance). Then every DoubleDeal input is uniform until two inputs collide.

**The IV (ARGUED).** Only the IV's min-entropy enters, through p_max. A **predictable IV is broken**: the adversary Composes its guess so that it cancels the IV. **Uniqueness is not enough.**

**Keys.**
- With user-supplied decks, the bounds hold as stated if the decks are uniform and independent.
- With the optional KDF, add Adv^prf_KDF + 2·2^−228.27 (ARGUED). 2^−228.27 is the statistical distance of (d_a·|G| + d_b) mod 52! from uniform for uniform d_a, d_b: exactly r(52! − r)/(52!·|G|²) with r = |G|² mod 52!. That the digests are uniform is a random-oracle-style HEURISTIC on MegaDreifach v3.

## 6. Parity (sign) leak: no bound

- **The identity (ARGUED).** sgn is a homomorphism, so it passes through Compose exactly. A passive observer of (C_{i−1}, C_i) sees sgn(D_i) with correlation κ_K, which is DoubleDeal's own full-cipher sign correlation.
- **There is no proved bound on κ.** Learning one bit needs about 1/κ² encryptions of one block. A nonzero κ is itself a PRP distinguisher, so this sits inside the HEURISTIC PRP assumption, but deck-CBC makes it ciphertext-only.
- **OUT-OF-TREE.** An earlier review measured |κ| < 3·10⁻⁴ (key-independent part, 3 standard deviations, 10⁸ samples) with a hand-written C port of DoubleDeal, validated on the KATs. That port is not in this repository, and nothing in the tree reproduces the number.

## 7. What stays heuristic or open

- A1 and A2 on MegaDreifach v3 (HEURISTIC; §3 is evidence against two tests only), and the PRP assumption on DoubleDeal.
- Yasuda's Lemmas 3–4, which give the f̌ term, are unverified (§2.1).
- No Lean security theorem. Everything in this file is on paper.
- Hand play: without the MAC, deck-CBC is malleable (moving seats of C_{i−1} moves seats of D_i), and the rank and pad checks become oracles.

## 8. Where this came from

This file replaces the "Security argument" section of the description of PR #151 (hacker6284/cryptoys#151), written when the MAC was on MegaDreifach v2 (C36). That text is superseded:
- Its statements that the bounds are "not meaningful for C36" are about v2 and appear here only as the v2 consequence in §3.3.
- Its v2 A1 numbers (5,105 of 100,000 games; key-independence and repetition runs; the C76 coverage comparison) came from a Python experiment that is no longer in the tree. They are replaced by the in-tree v2-build positive control in §3.3, and are not used.
- Its tags followed an older convention, with PROVED used for pen-and-paper steps. Here, PROVED is used only where a named sudo test checks the claim.
