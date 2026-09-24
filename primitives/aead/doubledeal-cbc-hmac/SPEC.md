# DoubleDeal-CBC-HMAC

This document is the normative specification. `doubledeal_cbc_hmac.sudo` is the conformance implementation of HMAC-MegaDreifach, the key schedule, CBC byte helpers, ISO/IEC 7816-4 padding, and the Encrypt-then-MAC input. Byte-domain CBC that must rank a deck uses the §5.3 encoding in `demos/doubledeal/cards.js` (same limitation DoubleDeal records: `52!` does not fit in a sudocode `int`). A mismatch is a bug in the implementation.

The product name **DoubleDeal-CBC-HMAC** is locked. DoubleDeal-SCM and SMAC are not this primitive and stay later.

DoubleDeal-CBC-HMAC is a toy Encrypt-then-MAC construction. It makes no cryptographic security claim. It is not for protecting anything.

---

# 1. Scope and non-goals

## In scope

- Byte-domain **CBC** of DoubleDeal on the §5.3 28-byte injective message encoding.
- **Encrypt-then-MAC** with a real **HMAC** whose underlying hash is **MegaDreifach** (not SHA-256, not Scramble).
- A split key schedule from one master secret into an encryption deck and an HMAC key.
- An AEAD API: `encrypt` / `decrypt` with optional AAD in the MAC, tag check before plaintext is released.

## Non-goals

- No AES-class security, no PRF/MAC advantage bounds, no nonce-misuse resistance.
- No claim that MegaDreifach is collision-resistant or that HMAC-MegaDreifach is a PRF. The MAC inherits the toy hash. HMAC is still implemented as HMAC.
- No DoubleDeal-SCM / SMAC. Those names stay reserved for a later construction.
- No CFB / OFB.
- No constant-time claim. Tag compare is a full-length equality; this is a toy.
- Link-2 refinement proofs and Generated Lean for this module are out of scope here.

---

# 2. Parameters (locked)

| Item | Value |
| --- | --- |
| Construction | DoubleDeal in CBC, then Encrypt-then-MAC |
| Hash | MegaDreifach `Hash` (`primitives/hash/megadreifach/`) |
| HMAC block size \(B\) | **28** (MegaDreifach pad / compression block) |
| HMAC tag | full MegaDreifach digest, **29 bytes** |
| CBC message block | **28 bytes** (§5.3 injective capacity) |
| CBC ciphertext block | **29 bytes** (ranked deck; every deck is representable) |
| IV | **28 bytes** |
| Padding | same as DoubleDeal ECB: `0x80` then `0x00` to a multiple of 28 |
| Version label | `DoubleDeal-CBC-HMAC/v1` (ASCII) |

HMAC’s \(B = 28\) is the hash’s input block, not its digest length. MegaDreifach has \(L = 29 > B\). SHA-family HMAC never hits \(L > B\). The extra rule below is the honest extension of RFC 2104 / FIPS 198-1 for that case.

---

# 3. CBC (byte domain)

AES-spirit CBC XORs in the cipher’s message domain. DoubleDeal’s message encoding is 28 bytes; `encrypt` returns a deck whose factoradic rank need not fit in 28 bytes, so the wire ciphertext block is the 29-byte rank. XOR therefore stays on 28-byte strings. Compose-CBC on decks is rejected: XOR of two permutations is not a permutation, and it would not match AES-spirit CBC plus §5.3.

## 3.1 Pad

Identical to DoubleDeal SPEC §5.3 ECB byte streams:

1. Append `0x80`.
2. Append `0x00` until the length is a multiple of 28.

A plaintext whose length is already a multiple of 28 gains a whole extra block. The empty plaintext becomes one block (`0x80` and 27 zero bytes). Unpad requires a recovered 28-byte stream that ends in `0x80` followed only by `0x00`, and strips that suffix. Any other ending is rejected.

## 3.2 IV

The IV is 28 bytes. It is not secret. Under a given encryption key it **must be unique**. A uniformly random IV is the recommended way to get uniqueness. Reusing \((K_{\mathrm{enc}}, \mathrm{IV})\) is classic CBC misuse: the first plaintext blocks leak via XOR of the first ciphertext decks’ preimages.

The IV is an argument to `encrypt` / `decrypt`. It is not concatenated onto the default ciphertext‖tag output. It **is** included in the MAC.

## 3.3 Encrypt

Let \(P_0,\ldots,P_{n-1}\) be the padded 28-byte blocks. Let \(\mathrm{chain}_0 = \mathrm{IV}\).

```
for i in 0..n-1:
    x_i      = P_i XOR chain_i          # 28-byte XOR
    D_i      = unrank_52(x_i)           # §5.3 28-byte → deck
    E_i      = DoubleDeal.encrypt(D_i, K_enc)
    C_i      = rank_52_29(E_i)          # 29-byte big-endian rank
    chain_{i+1} = C_i[1..28]            # drop the most-significant byte
```

The ciphertext body is \(C = C_0 \mathbin{+\mskip-4mu+} \cdots \mathbin{+\mskip-4mu+} C_{n-1}\) (29\(n\) bytes).

**Why the last 28 bytes of the rank.** \(52! \approx 2^{225.58}\), so a 29-byte big-endian rank uses a little more than 225 bits. Dropping the most-significant byte keeps the 224 least-significant bits of the rank as the next CBC state. Two different decks can collide on that 28-byte view (ranks congruent modulo \(2^{224}\)). That is weaker than AES-CBC, where \(|C_i|\) equals the XOR block. It is the AES-spirit choice that stays in the 28-byte encoding without inventing a second hash inside CBC.

## 3.4 Decrypt

```
for i in 0..n-1:
    E_i      = unrank_52_29(C_i)        # reject if n ≥ 52!
    D_i      = DoubleDeal.decrypt(E_i, K_enc)
    x_i      = rank_52_28(D_i)          # reject if n ≥ 2^224
    P_i      = x_i XOR chain_i
    chain_{i+1} = C_i[1..28]
```

Honest encryption only unranks 28-byte strings, so a well-formed ciphertext decrypts to decks with rank \(< 2^{224}\). A decrypted deck outside that range is rejected.

Then unpad. Bad padding is rejected.

## 3.5 Padding oracles

Unpad runs only after a successful tag check. A padding oracle against this implementation therefore needs a forged tag (or a broken MAC). If the MAC is ignored or the hash is broken, CBC padding oracles apply exactly as they do for AES-CBC with this pad. Do not treat “toy” as a reason to skip the tag check.

---

# 4. HMAC-MegaDreifach

Standard HMAC (RFC 2104 / FIPS 198-1) with MegaDreifach as \(H\).

\[
\begin{aligned}
B &= 28, \qquad L = 29, \\
\mathrm{ipad} &= 0\mathrm{x}36^{B}, \qquad \mathrm{opad} = 0\mathrm{x}5c^{B}.
\end{aligned}
\]

## 4.1 Key normalization

Let \(K\) be a byte string.

1. If \(|K| > B\), replace \(K\) with \(H(K)\) (29 bytes).
2. If \(|K| > B\) still (this is the \(L > B\) case), replace \(K\) with the first \(B\) bytes of that digest.
3. If \(|K| < B\), append \(0\mathrm{x}00\) until \(|K| = B\).

Empty \(K\) is allowed for bare HMAC (it becomes 28 zero bytes). The AEAD master-secret schedule below rejects an empty master key.

## 4.2 Tag

\[
\mathrm{HMAC}(K, m) = H\bigl((K' \oplus \mathrm{opad}) \mathbin{\| } H\bigl((K' \oplus \mathrm{ipad}) \mathbin{\| } m\bigr)\bigr).
\]

The tag is the full 29-byte digest. No truncation in v1.

`HMAC` and `HMAC_MegaDreifach` are the same function.

Sudo has no bitwise XOR operator. `xor_byte` is an 8-step bit loop (bounded `for`). That is XOR, not a substitute.

---

# 5. Key schedule

One master secret \(\mathrm{MK}\) (one or more bytes) is split. The encryption deck and the HMAC key are **not** the same bytes.

Length-delimit every field so labels and \(\mathrm{MK}\) cannot slide into each other.

```
enc_label = "DoubleDeal-CBC-HMAC/v1/enc"
mac_label = "DoubleDeal-CBC-HMAC/v1/mac"

K_enc_bytes = Hash( u16be(|enc_label|) ‖ enc_label ‖ u64be(|MK|) ‖ MK )[0..27]
K_mac       = Hash( u16be(|mac_label|) ‖ mac_label ‖ u64be(|MK|) ‖ MK )
K_enc       = unrank_52(K_enc_bytes)     # one DoubleDeal master deck
```

`K_mac` is 29 bytes; HMAC’s normalizer hashes it once more and takes 28 bytes.

This is domain-separated Hash, not HKDF. Length extension on bare Hash is accepted by MegaDreifach; the labels and length prefixes are still the honest way to derive two keys from one secret without “use the same key for both.” Empty \(\mathrm{MK}\) is rejected.

`u16be` / `u64be` are big-endian. Label lengths fit in 16 bits.

---

# 6. AEAD API

Sudocode has no optional parameters. AAD is always passed; use an empty list for “no AAD.”

```
encrypt(plaintext, key, iv, aad) -> ciphertext ‖ tag
decrypt(ciphertext ‖ tag, key, iv, aad) -> plaintext | FAIL
```

- `key` is the master secret \(\mathrm{MK}\).
- `iv` is exactly 28 bytes.
- `ciphertext` is \(29n\) bytes for \(n \ge 1\) (the empty plaintext still produces one CBC block).
- `tag` is 29 bytes.
- Default wire blob is `ciphertext ‖ tag` (last 29 bytes are the tag). IV is a separate argument.

## 6.1 MAC input (Encrypt-then-MAC, length-delimited AAD)

```
mac_data =
    u16be(|version|) ‖ version ‖
    u64be(|aad|)     ‖ aad     ‖
    u64be(|iv|)      ‖ iv      ‖
    u64be(|C|)       ‖ C
tag = HMAC(K_mac, mac_data)
```

`version` is `DoubleDeal-CBC-HMAC/v1`. AAD is in the MAC. IV is in the MAC. Length prefixes stop AAD / IV / C from being ambiguous.

## 6.2 Encrypt

1. Reject empty `key`, IV not 28 bytes, or any non-byte.
2. Derive \(K_{\mathrm{enc}}, K_{\mathrm{mac}}\).
3. Pad plaintext; CBC-encrypt under \(K_{\mathrm{enc}}\) and IV.
4. `tag = HMAC(K_mac, mac_data)`.
5. Return \(C \mathbin{\|} \mathrm{tag}\).

## 6.3 Decrypt

1. Reject a blob shorter than \(29 + 29\) bytes, or whose \(C\) length is not a positive multiple of 29.
2. Split `tag` as the last 29 bytes.
3. Derive keys. Recompute `tag' = HMAC(K_mac, mac_data)`.
4. Compare `tag` and `tag'` over the full 29 bytes. On mismatch, **reject and do not decrypt**.
5. Only then CBC-decrypt, unpad, and return the plaintext.

A failed tag, a 29-byte integer \(\ge 52!\), a decrypted deck with rank \(\ge 2^{224}\), or a bad pad is a failure. Failures are not distinguished to the caller beyond “reject.”

---

# 7. Security honesty

- Not AES. Not AES-GCM. Not “authenticated encryption” in the reduction sense.
- MegaDreifach is a toy hash. HMAC-MegaDreifach is a correctly wired HMAC over that hash. It does not inherit SHA-2’s assumed PRF properties.
- CBC leaks via IV reuse and via identical first-block XOR relations.
- The 28-byte chain is a truncation of the 29-byte rank. Chain collisions are possible.
- Padding oracles exist if the tag check is skipped or the MAC is broken.
- IV/nonce misuse is on the caller.
- Comparison is not claimed constant-time.

---

# 8. Test vectors

`kats/doubledeal_cbc_hmac_kats.json` is generated from the conformance sudo plus the §5.3 encoding. JS tests assert round-trips and negative tag / AAD / IV / ciphertext tampers.

---

# 9. How to run tests

With `sudoc` on the path, from the repository root:

```sh
sudoc emit-ir --require terminates -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null

sudoc build --target js --tests -o /tmp/ddch \
    -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch/_doubledeal_cbc_hmac_impl.mjs

# Byte-domain AEAD (needs DoubleDeal JS from tools/build.sh as well)
export SUDOC=/path/to/sudoc
sh tools/build.sh
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
```

`sudoc emit-ir --require terminates` must exit 0 on this module (and on the MegaDreifach publics it imports). New loops are bounded `for`.

---

# 10. In this repository

| Artifact | Path | Role |
| --- | --- | --- |
| This specification | `primitives/aead/doubledeal-cbc-hmac/SPEC.md` | Normative AEAD rules |
| Conformance sudo | `primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo` | HMAC, KDF, pad, MAC input, CBC byte helpers |
| Byte-domain AEAD | `primitives/aead/doubledeal-cbc-hmac/aead.mjs` | CBC over §5.3 + sudo HMAC |
| KATs | `primitives/aead/doubledeal-cbc-hmac/kats/doubledeal_cbc_hmac_kats.json` | Published vectors |
| DoubleDeal rounds | `primitives/cipher/doubledeal/doubledeal.sudo` | `encrypt` / `decrypt` |
| MegaDreifach | `primitives/hash/megadreifach/megadreifach.sudo` | `Hash` |
| §5.3 encoding | `demos/doubledeal/cards.js` | 28-byte / 29-byte ranks |

---

*Toy teaching AEAD. No security claim. SCM stays later.*
