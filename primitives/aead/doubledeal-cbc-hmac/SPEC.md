# DoubleDeal-CBC-Sandwich v2

This document is the normative specification. `doubledeal_cbc_hmac.sudo` is the conformance implementation of the whole construction: deck-CBC, the Sandwich MAC, the optional key derivation, the byte ⇄ deck edge, the blob format and the decrypt order. `aead.mjs` is only a host wrapper: it draws the IV and calls the sudo. A mismatch is a bug in the implementation.

The product name is **DoubleDeal-CBC-Sandwich**, version **v2**. It replaces DoubleDeal-CBC-HMAC v1, which is frozen and superseded at [`v1/`](v1/SPEC.md). v2 has no HMAC; the name says which MAC it is (Yasuda's "Sandwich", §6). **The directory and file names still say `doubledeal-cbc-hmac`.** They will be renamed in a separate pull request, a pure `git mv`, after #182 and #151 land.

**MegaDreifach version.** The MAC and the optional key derivation use **MegaDreifach v3** (ZP26, [`primitives/hash/megadreifach/v3/`](../../hash/megadreifach/v3/SPEC.md)), the current version. Drafts of this v2 before the move used MegaDreifach v2, now deprecated. Moving to v3 changed every tag, every derived key and every KAT. It did not change the version label `DoubleDeal-CBC-Sandwich/v2`, `VERSION_DECK` or the key-derivation labels. The label stays /v2 because it versions the construction, and the hash is a parameter of the construction.

DoubleDeal-CBC-Sandwich is a toy Encrypt-then-MAC construction. It makes no cryptographic security claim. It is not for protecting anything. Nothing in it uses XOR.

---

# 1. Scope and non-goals

## In scope

- Deck-CBC of DoubleDeal: each plaintext deck is **Composed** with the previous ciphertext deck (the IV for the first block), then DoubleDeal-encrypted.
- A **Sandwich MAC** on one MegaDreifach chain: the MAC key deck, then the message decks, then the MAC key deck turned over. The tag is the finished position.
- Two **user-supplied key decks**: `k_enc` for DoubleDeal and `k_mac` for the MAC. An optional software key derivation makes both from a byte secret.
- An AEAD API with AAD in the MAC, a fresh truly shuffled IV deck per message, and tag checking before any decryption.
- A hand procedure for everything except the byte ⇄ deck edge and the AAD (both software only).

## Non-goals

- No AES-class security and no proved PRF, MAC or AEAD bound for this instance. The security argument is relative to assumptions on MegaDreifach v3 and DoubleDeal that are heuristic and unproven (§8). Two of them failed for MegaDreifach v2; the same tests detect nothing on v3, which is evidence, not a proof.
- No nonce-misuse resistance. A repeated or predictable IV is a break (§4).
- No constant-time claim.
- No CFB, OFB, SCM or SMAC.

---

# 2. Parameters (locked)

| Item | Value |
| --- | --- |
| Cipher | DoubleDeal (`primitives/cipher/doubledeal/`), one key deck `k_enc` |
| MAC | Sandwich on MegaDreifach v3 (ZP26) whole-deck compressions, one key deck `k_mac` |
| Hash (MAC and key derivation) | MegaDreifach v3, `primitives/hash/megadreifach/v3/megadreifach.sudo` (`HashDecksBody`, `Hash`) |
| Plaintext block | **28 bytes** = one deck (every 28-byte value is below 2^224 < 52!) |
| Ciphertext block, IV, tag | **29 bytes** each (the IV and ciphertext blocks are deck ranks below 52!; the tag is a megaminx digest below the group order) |
| Padding | `0x80`, then `0x00` to a multiple of 28 |
| Version | **v2**, carried by `VERSION_DECK` (§5) and the KDF labels (§3.2); kept through the move to MegaDreifach v3, because the label versions the construction and the hash is a parameter |
| Key-derivation labels | `DoubleDeal-CBC-Sandwich/v2/enc`, `DoubleDeal-CBC-Sandwich/v2/mac` |

**Decks.** A deck is a list of the 52 card ids 0..51 in DoubleDeal's CHaSeD numbering (13·suit + rank; clubs, hearts, spades, diamonds). The top card is seat 0. New-deck order is A♣ on top and K♦ at the bottom. `rank` and `unrank` are DoubleDeal's factoradic (DoubleDeal SPEC §5.3). `rank29(D)` is the 29-byte big-endian rank. A 28-byte block `P` is the deck `unrank(P)`.

**Compose.** DoubleDeal SPEC §3.6: `Compose(M, K)[j] = M[position of card j in K]` and `InverseCompose(C, K)[position of card j in K] = C[j]`. The two undo each other.

---

# 3. Keys

## 3.1 User-supplied key decks (the normal case)

`k_enc` and `k_mac` are two full decks. **Security assumes each is uniformly random and the two are independent**, however they were made. So shuffle each one truly (the IV recipe of §4.1 is the recipe to use) and keep them apart. `aead_seal` and `aead_open` reject a key that is not a deck and reject `k_enc = k_mac`.

## 3.2 Optional derivation from a byte secret (software only)

For software users who hold a byte secret MK (at least one byte):

```
d_j   = MegaDreifach_v3.Hash( u16be(|label|) ‖ label ‖ [j] ‖ u64be(|MK|) ‖ MK )    # 29 bytes, read as an integer below |G|
k_enc = unrank( (d_0·|G| + d_1) mod 52! )     with label = "DoubleDeal-CBC-Sandwich/v2/enc"
k_mac = unrank( (d_2·|G| + d_3) mod 52! )     with label = "DoubleDeal-CBC-Sandwich/v2/mac"
```

`|G|` is the megaminx group order (MegaDreifach v3 SPEC §4, the same group as v2). If the digests were uniform, each key would be within statistical distance about 2^-228.27 of a uniform deck. That "if" is a heuristic (random-oracle style) on MegaDreifach. The derivation is optional; it is not a password hash and adds no security beyond MK's entropy.

---

# 4. Deck-CBC

Let `P_0 … P_{n-1}` be the padded 28-byte blocks (n ≥ 1; the empty plaintext is one block) and `D_i = unrank(P_i)`.

```
chain = IV
for i in 0..n-1:
    X_i   = Compose(D_i, chain)          # PLACE
    C_i   = DoubleDeal.encrypt(X_i, k_enc)
    chain = C_i
```

Decrypt, block by block (only after the tag has verified, §7):

```
chain = IV
for i in 0..n-1:
    D_i   = InverseCompose(DoubleDeal.decrypt(C_i, k_enc), chain)   # COLLECT
    reject unless rank(D_i) < 2^224
    P_i   = the 28 low bytes of rank(D_i)
    chain = C_i
```

## 4.1 The IV

**The IV is a full deck, freshly and truly shuffled for every message.** It is not secret and travels as the first 29 bytes of the blob. A unique IV is **not** enough: a counter IV, the previous message's last ciphertext deck, or any IV the attacker can predict before choosing a plaintext lets them test guesses of plaintext blocks (the deck analogue of the CBC predictable-IV attack). In software the host draws it with a CSPRNG and rejection sampling (`randomDeck()` in `aead.mjs`); the sudo cannot draw randomness, so `aead_seal` takes the IV as an argument and trusts the host.

*Hand recipe: "Wash a minute, riffle seven, better twelve."* Take a separate deck. Spread it face down and swirl it with both flat hands for at least a minute. Gather it and riffle-shuffle at least 7 times, preferably 12 or more, splitting it roughly in half each time. Cut once. Shuffle out of sight, after the plaintext is fixed, and never reuse a deck anyone has seen. No overhand shuffles. The IV is exactly as good as this shuffle.

## 4.2 Hand recipes for the chain

*Equipment.* One spare deck with a different back, laid face up in a 4×13 grid in new-deck order (clubs A→K on the top row, then hearts, spades, diamonds). Each grid card marks the home of its twin. "Across the rows" means top row left to right, then the next row.

*Keeping order.* When you go through a deck card by card and must keep it, turn each card face up onto a pile, then turn the pile over at the end.

**PLACE (encrypt): "each plaintext card goes to the home of its chain card."** Hold the plaintext deck and the chain deck (the IV, or the last ciphertext deck) face down. Fifty-two times: turn up the top card of each, lay the plaintext card on the grid twin of the chain card, and keep the chain card in order. Gather the plaintext cards across the rows. That deck is `Compose(D, chain)`; DoubleDeal-encrypt it. The ciphertext deck goes out and is also the next chain. The chain deck is unchanged, so nothing is copied.

**COLLECT (decrypt): "deal across, pick up in chain order."** Deal the DoubleDeal-decrypted deck face up across the rows, one card on each grid card. Go through the chain deck in order; for each chain card, pick up the card lying on its grid twin. The picked-up pile is `InverseCompose(Y, chain)`. Decrypt from the last block backwards, so every chain deck is still intact when you need it.

---

# 5. The MAC input S

S is a list of whole decks:

```
S = VERSION_DECK ‖ AAD decks ‖ IV ‖ C_0 ‖ … ‖ C_{n-1} ‖ LENGTH_DECK(|aad|)
```

- **VERSION_DECK** (v2): new-deck order with the top two cards swapped (2♣ on top, then A♣). *By hand: "sorted, swap the top two".*
- **AAD decks** (software only): the AAD bytes zero-filled to a multiple of 28, each 28-byte chunk unranked to a deck. No decks for empty AAD.
- **IV** and **C_i**: the decks exactly as they lie; no ranking into bytes.
- **LENGTH_DECK(n)** = `unrank(n)` for the AAD length n in bytes. With no AAD it is a sorted deck. *By hand: lay a sorted deck last.*

The framing is injective (ARGUED, [`ARGUMENT.md`](../../../proofs/doubledeal-cbc-hmac/security/ARGUMENT.md) §1): S determines the AAD, the IV and the ciphertext decks. The length deck is what separates AADs that differ only in trailing zero bytes. The framing is not prefix-free, and does not need to be.

---

# 6. The Sandwich MAC

Let `f(h, D)` be one MegaDreifach v3 (ZP26) Davies–Meyer compression of the whole deck D from position h (MegaDreifach v3 SPEC §5: `f(h, D) = compose(h, E_D(h)) = h·W·h`, where W is the face-turn word the ZP26 card phase builds from D read against h, the cards dealt top first; the sudo's `dm_step`). Let `f*` chain `f` over a list of decks. Then

```
tag = digest( f*( IV-COOK12, [k_mac as it lies] ‖ S ‖ [k_mac turned over] ) )
```

"Turned over" means the old bottom card is on top: `turned_over(K)[i] = K[51 - i]`. The digest is the 29-byte position rank (MegaDreifach v3 SPEC §6). There is no padding, no length block and no second pass: every block is a whole deck. In software this is MegaDreifach v3's `HashDecksBody` (one `dm_step` per deck) on the decks with the card ids mapped to MegaDreifach's numbering (4·rank + suit, the same physical cards).

*Hand recipe: one puzzle, three stages; "key, message, key turned over."*
1. Set up IV-COOK12 (MegaDreifach v3 SPEC §5.7).
2. **Key as it lies.** Deal the MAC key deck into the puzzle, top card first, as one block.
3. **Message.** Deal in each deck of S in order, one block each: the version deck, the IV, every ciphertext deck, the length deck (a sorted deck when there is no AAD).
4. **Key turned over.** Turn the MAC key deck over and deal it in as the last block.
5. **The finished puzzle is the tag.** The verifier rebuilds the same puzzle from the received decks and its own key deck and compares the two puzzles piece by piece. Any difference means reject.

"One puzzle" is the hash puzzle of a single MegaDreifach chain; each block's Davies–Meyer step uses MegaDreifach's two helper puzzles as its hand procedure says (MegaDreifach v3 SPEC §5.4–§5.7). In software the tag is the finished position's 29-byte digest.

**Why the key turned over.** The first and the last key blocks must differ for every key. Turning a deck over moves every card to a new seat (PROVED: sudo test "turning the key over moves every card to a new seat"; seat i goes to seat 51 − i, never i, since 52 is even). So the key block that closes the MAC is never the block that opened it. That separation stands in for Yasuda's padding condition (§8; ARGUED).

---

# 7. AEAD API

```
aead_seal(plaintext, k_enc, k_mac, aad, iv) -> blob
aead_open(blob, k_enc, k_mac, aad)          -> (true, plaintext) | (false, [])
```

- `blob = rank29(IV) ‖ rank29(C_0) ‖ … ‖ rank29(C_{n-1}) ‖ tag`, 29·(n+2) bytes with n ≥ 1.
- Hosts expose `encrypt(pt, k_enc, k_mac, aad)`, which draws a fresh IV itself. `encryptWithIv` exists for known-answer tests only.
- Sudocode has no optional parameters: pass an empty list for no AAD.

**Decrypt order (MUST).**
1. Public parse, no key: the length is at least 87 and a multiple of 29, and every 29-byte number before the tag is below 52!. Unrank them to the IV and the ciphertext decks.
2. Rebuild the tag over those decks and compare all 29 bytes. On mismatch, reject and do nothing else. DoubleDeal is not called.
3. Deck-CBC decrypt (§4), rejecting any deck with rank ≥ 2^224.
4. Unpad: the stream must end in `0x80` followed only by `0x00`, with the marker in the last block.

Every failure is the same `(false, [])`. The host wrapper turns it into one exception, "reject".

---

# 8. Security honesty

**Tags.** **PROVED**: a named sudo test checks the claim. **LITERATURE**: a published theorem, used as its authors state it and not re-checked here. **ARGUED**: a pen-and-paper argument in this repository, not machine-checked. **COMPUTED**: a number from an in-tree harness whose logs are committed. **HEURISTIC**: an unproven assumption. **OUT-OF-TREE**: a number from code that is not in this repository. Every ± below is a 95% half-width (1.96 standard errors). The full argument, step by step with the same tags, is in [`proofs/doubledeal-cbc-hmac/security/ARGUMENT.md`](../../../proofs/doubledeal-cbc-hmac/security/ARGUMENT.md).

- **Toy.** DoubleDeal and MegaDreifach are toy primitives with no security proof. Every statement below is relative to named assumptions on them, and those assumptions are **heuristic**.
- **Confidentiality (ARGUED, relative to a HEURISTIC PRP assumption on DoubleDeal; the standard CBC argument carried over to decks, ARGUMENT.md §5).** With a uniform fresh IV per message, the deck chain is IND-CPA up to 2·(DoubleDeal PRP advantage) + 4σ²/52! for σ blocks: the birthday bound, reached at about 2^112 blocks. A predictable IV is broken; uniqueness is not enough.
- **Composition (LITERATURE: Bellare–Namprempre, ASIACRYPT 2000, Encrypt-then-MAC; that this construction meets its hypotheses is ARGUED, ARGUMENT.md §5).** INT-CTXT is at most the MAC's strong-unforgeability advantage, and IND-CCA is at most twice that plus the IND-CPA advantage, provided the two key decks are independent and uniform and the decrypt order of §7 is kept.
- **The MAC: its security rests on unproven (heuristic) assumptions on MegaDreifach v3.**
  - *Theorem S (LITERATURE, partly unverified, applied with two deviations).* The source is Yasuda, ACISP 2007, Theorem 1. Only his Lemma 2 (f′ PRF and F̄ cAU imply a PRF) was read. His Lemmas 3–4, which give the f̌ term, are unverified here. The deviations: here the key fills the whole block (p = 0; Yasuda needs p > 0). The last key block is separated from the first by turning the key over (a reversal tweak) instead of by his padding π(λ) ≠ 0^p. That his Lemma 2 proof survives both is ARGUED (ARGUMENT.md §2). The statement: Adv^prf ≤ Adv^prf_{f′}(q+1) + C(q,2)·[2ℓ·Adv^prf_{f̌}(2) + 1/|G|], for q tagged messages of at most ℓ decks of S each. Here f′(v) = f(v, key deck) is the compression keyed through the key block at chaining values the adversary chooses, and f̌ is the compression keyed through a secret chaining value.
  - *Both assumptions failed for MegaDreifach v2 (COMPUTED; why the test works is ARGUED).* **A1 (f′).** Query y₁ = f′(h) at a uniform h and solve W = (h⁻¹·y₁)·h⁻¹. Then query y₂ = f′(h′), where h′ is h with two random edges flipped, and accept iff y₂ = h′·W·h′. On v2 a block's face-turn word W depended only on the pieces of h the block read. So the test accepted 213 of 4,000 games (5.3%, 95% CI 4.7–6.1%) against f′ with a uniform secret key deck. Against a random function it accepts with probability exactly 1/|G| = 2^-225.9 (ARGUED). **A2 (f̌, two queries).** At a uniform secret chaining value h, query a uniform deck D and D with its last two cards swapped, and count the edge slots that z = f(h, D)⁻¹·f(h, D′) leaves fixed. On v2, P(at least 2 fixed edges) exceeded the uniform-group value 0.264241 by +0.070 ± 0.012 (6,000 pairs). Both numbers come from this repository's harness, run as a positive control on a sudoc build of the deprecated v2 sudo (logs below).
  - *On MegaDreifach v3 neither test detects anything (COMPUTED).* The same harness on the sudoc build of the v3 sudo:
    - A1: **0 of 100,000** games accepted (v2: 5.3%). The exact one-sided 95% upper bound, 3.0·10⁻⁵, is on this test's per-game acceptance probability. It is not a bound on Adv^prf_{f′}.
    - A2: 120,000 pairs. P(fixE ≥ 2) = 0.2629 (95% CI 0.2604–0.2654) against 0.264241, advantage −0.0014 ± 0.0025; for corners +0.0002 ± 0.0025; no two outputs equal.
    - E3, the whole Sandwich: t = f*(IV-COOK12, [K, D, L, K turned over]) against the same with D's last two cards swapped (K and D uniform, L a fixed stand-in for the length deck). 40,000 pairs; fixE advantage −0.0016 ± 0.0043, fixC −0.0033 ± 0.0043; no two tags equal.
    - What the runs could have seen (hand-derived, not harness output). An A1 acceptance rate of 2.3·10⁻⁵ gives at least one acceptance in 100,000 games with probability 90%. An A2 advantage of about 0.004, or an E3 advantage of about 0.007, would be detected at the 5% level with 90% power (normal approximation). The v2 effects (5.3% and +0.070) are far above these limits.

    Harness and logs: [`proofs/doubledeal-cbc-hmac/security/`](../../../proofs/doubledeal-cbc-hmac/security/README.md). The harness calls only functions of the sudoc build. `tools/generate-demos.sh` re-runs a fixed-seed slice with `--check`; that checks reproducibility, not statistics.
  - *The assumptions are still unproven (HEURISTIC).* Two tests that find nothing are not a proof. The f′ and f̌ PRF assumptions on MegaDreifach v3 are unproven, and v3 itself has no security proof (MegaDreifach v3 SPEC §8). **So the security of the Sandwich theorem for this instance is conditional.** Theorem S bounds the MAC by the PRF advantages of f′ and f̌ on v3, and those advantages are assumed small, not shown. INT-CTXT and IND-CCA inherit the same condition. Beyond these tests and the v3 statistics in `proofs/megadreifach/security/v3/`, no other distinguisher was searched for.
  - *Consequence for v2 (ARGUED from the COMPUTED rate).* With MegaDreifach v2 the A1 test is an f′ distinguisher with advantage about 0.05 from two queries. So the first term of Theorem S was at least about 0.05 for one message, and the theorem gave no meaningful bound. That is why the MAC moved to v3.
  - *Generic limit (ARGUED).* The generic birthday forgery needs about 2^113 tags, so no argument could give more than about 2^112.
- **Parity (sign) leak (ARGUED; no bound).** The sign of a permutation passes through Compose exactly. So a passive observer of two consecutive ciphertext decks sees the plaintext deck's sign with correlation κ, DoubleDeal's own sign correlation. **There is no proved bound on κ**, and about 1/κ² encryptions of one block would reveal that bit. *OUT-OF-TREE:* an earlier review measured |κ| < 3·10⁻⁴ (10⁸ samples) with a hand-written C port of DoubleDeal that is not in this repository. Nothing in the tree reproduces that number.
- **Hand play.** The hand MAC (§6) is complete, but it is slow, and a mistake at any step gives a wrong tag. Deck-CBC without the MAC is malleable: moving seats of a ciphertext deck moves seats of the next plaintext deck.
- **Comparison is not constant-time.**

---

# 9. Test vectors

`kats/doubledeal_cbc_hmac_kats.json` (product `DoubleDeal-CBC-Sandwich`, version `v2`, on MegaDreifach v3) holds a byte master `"cryptoy-master"`, the key decks it derives (§3.2), a fixed IV deck `unrank(Hash("DoubleDeal-CBC-Sandwich/v2 KAT IV") mod 52!)` (MegaDreifach v3 `Hash`) and five vectors: `empty`, `abc`, `abc_aad` (AAD `"hdr"`), `exact_28` and `forty` (40 bytes of plaintext, 30 bytes of AAD). `mac_version_only` is the tag of `S = [VERSION_DECK]` alone. `kats/regen.mjs` computes every output, the IV deck included, from the sudoc build of the sudo (`--check` compares); `aead.test.mjs` checks the file against the build; `kats/check.py` checks its structure. There is no independent second implementation: one outside the sudo would be a hand-written copy of the algorithm, which this repository does not keep.

---

# 10. How to run tests

From the repository root, with `sudoc` built:

```sh
sudoc emit-ir --require terminates -I primitives/hash/megadreifach/v3 -I primitives/cipher/doubledeal \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null
sudoc build --target js --tests -o /tmp/ddch -I primitives/hash/megadreifach/v3 -I primitives/cipher/doubledeal \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch/_doubledeal_cbc_hmac_impl.mjs
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs --check
python3 primitives/aead/doubledeal-cbc-hmac/kats/check.py
sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
MD_OUT=/tmp/megadreifach-v3 node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs --check proofs/doubledeal-cbc-hmac/security/logs/ci_slice.log ci 85000000
```

`tools/generate-demos.sh` runs all of these, and the frozen v1 sudo tests.

---

# 11. In this repository

| Artifact | Path | Role |
| --- | --- | --- |
| This specification | `primitives/aead/doubledeal-cbc-hmac/SPEC.md` | Normative rules for v2 |
| Conformance sudo | `primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo` | The whole construction |
| Host wrapper | `primitives/aead/doubledeal-cbc-hmac/aead.mjs` | Fresh IV decks, `encrypt` / `decrypt` |
| KATs | `primitives/aead/doubledeal-cbc-hmac/kats/` | Vectors, regeneration, structure check |
| Generated Lean | `proofs/doubledeal-cbc-hmac/lean/Generated/` | Emitted v2 Lean (with the imported MegaDreifach v3 and DoubleDeal) and its sudo tests (TAP). No Link 2 yet; the Lean proofs lag v2, and MegaDreifach v3 has no Lean model. |
| Security argument and evidence | `proofs/doubledeal-cbc-hmac/security/` | `ARGUMENT.md`, the full §8 argument; the §8 tests on MegaDreifach v3 and the v2 positive control: harness and logs |
| Frozen v1 | `primitives/aead/doubledeal-cbc-hmac/v1/`, `proofs/deprecated/doubledeal-cbc-hmac-v1/` | DoubleDeal-CBC-HMAC v1 and its Link 2 proofs, superseded |
| DoubleDeal | `primitives/cipher/doubledeal/doubledeal.sudo` | `encrypt` / `decrypt` |
| MegaDreifach v3 | `primitives/hash/megadreifach/v3/megadreifach.sudo` | `HashDecksBody`, `Hash` |

---

*Toy teaching AEAD. No security claim.*
