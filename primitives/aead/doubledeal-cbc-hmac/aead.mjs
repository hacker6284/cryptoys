// Byte-domain DoubleDeal-CBC-HMAC. SPEC.md is normative.
// HMAC / KDF / pad / MAC input come from doubledeal_cbc_hmac.sudo.
// 28-byte / 29-byte ranks are DoubleDeal §5.3 (cards.js): 52! is not a sudo int.

export function createAead({
    HMAC,
    derive_keys,
    pad_iso7816,
    unpad_iso7816,
    mac_input,
    xor_bytes,
    cbc_chain_from_cipher_block,
    tags_equal,
    encrypt,
    decrypt,
    bytesToDeck,
    deckToMessageBytes,
    deckToCipherBytes,
    cipherBytesToDeck,
}) {
    function requireBytes(name, xs, length) {
        if (!Array.isArray(xs) && !(xs instanceof Uint8Array)) {
            throw new Error(`${name} must be bytes.`);
        }
        const out = [...xs];
        if (length !== undefined && out.length !== length) {
            throw new Error(`${name} must be ${length} bytes.`);
        }
        for (const byte of out) {
            if (!Number.isInteger(byte) || byte < 0 || byte > 255) {
                throw new Error(`${name} contains a non-byte.`);
            }
        }
        return out;
    }

    function splitBlob(blob) {
        const bytes = requireBytes("blob", blob);
        if (bytes.length < 58 || (bytes.length - 29) % 29 !== 0) {
            throw new Error("The blob is ciphertext blocks of 29 bytes, then a 29-byte tag.");
        }
        return { ciphertext: bytes.slice(0, -29), tag: bytes.slice(-29) };
    }

    function cbcEncrypt(padded, iv, keyDeck) {
        const ciphertext = [];
        let chain = iv;
        for (let i = 0; i < padded.length; i += 28) {
            const block = padded.slice(i, i + 28);
            const xored = xor_bytes(block, chain);
            const deck = bytesToDeck(xored);
            const cipherDeck = encrypt(deck, keyDeck);
            const ranked = deckToCipherBytes(cipherDeck);
            ciphertext.push(...ranked);
            chain = cbc_chain_from_cipher_block(ranked);
        }
        return ciphertext;
    }

    function cbcDecrypt(ciphertext, iv, keyDeck) {
        if (ciphertext.length === 0 || ciphertext.length % 29 !== 0) {
            throw new Error("CBC ciphertext is a positive multiple of 29 bytes.");
        }
        const padded = [];
        let chain = iv;
        for (let i = 0; i < ciphertext.length; i += 29) {
            const ranked = ciphertext.slice(i, i + 29);
            const cipherDeck = cipherBytesToDeck(ranked);
            const plainDeck = decrypt(cipherDeck, keyDeck);
            const xored = deckToMessageBytes(plainDeck);
            padded.push(...xor_bytes(xored, chain));
            chain = cbc_chain_from_cipher_block(ranked);
        }
        return padded;
    }

    function encryptAead(plaintext, key, iv, aad = []) {
        const pt = requireBytes("plaintext", plaintext);
        const master = requireBytes("key", key);
        const ivb = requireBytes("iv", iv, 28);
        const aadb = requireBytes("aad", aad);
        if (master.length === 0) throw new Error("The master key is empty.");
        const [encBytes, macKey] = derive_keys(master);
        const keyDeck = bytesToDeck(encBytes);
        const padded = pad_iso7816(pt);
        const ciphertext = cbcEncrypt(padded, ivb, keyDeck);
        const tag = HMAC(macKey, mac_input(aadb, ivb, ciphertext));
        return ciphertext.concat(tag);
    }

    function decryptAead(blob, key, iv, aad = []) {
        const master = requireBytes("key", key);
        const ivb = requireBytes("iv", iv, 28);
        const aadb = requireBytes("aad", aad);
        if (master.length === 0) throw new Error("The master key is empty.");
        const { ciphertext, tag } = splitBlob(blob);
        const [encBytes, macKey] = derive_keys(master);
        const expected = HMAC(macKey, mac_input(aadb, ivb, ciphertext));
        if (!tags_equal(tag, expected)) {
            throw new Error("The tag is not valid.");
        }
        const keyDeck = bytesToDeck(encBytes);
        const padded = cbcDecrypt(ciphertext, ivb, keyDeck);
        return unpad_iso7816(padded);
    }

    return { encrypt: encryptAead, decrypt: decryptAead, splitBlob };
}
