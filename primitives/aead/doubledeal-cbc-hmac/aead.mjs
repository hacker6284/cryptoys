// Host wrapper for DoubleDeal-CBC-Sandwich v2. SPEC.md is normative and
// doubledeal_cbc_hmac.sudo is the whole algorithm (aead_seal / aead_open / mac_tag /
// derive_key_decks). This file only adds what sudo cannot do: draw a fresh,
// uniformly shuffled IV deck from the platform CSPRNG, and turn aead_open's
// (false, []) into one error. It does not re-implement any step.

// A uniform deck: Fisher-Yates driven by crypto.getRandomValues, with rejection
// so every index is exactly uniform (the software stand-in for a true shuffle).
export function randomDeck(randomValues = (a) => globalThis.crypto.getRandomValues(a)) {
    const deck = Array.from({ length: 52 }, (_, i) => i);
    const word = new Uint32Array(1);
    for (let i = 51; i > 0; i--) {
        const n = i + 1;
        const limit = Math.floor(0x100000000 / n) * n;
        let x;
        do {
            randomValues(word);
            x = word[0];
        } while (x >= limit);
        const j = x % n;
        [deck[i], deck[j]] = [deck[j], deck[i]];
    }
    return deck;
}

export function createAead({ seal, open, derive_key_decks }) {
    // The only public encrypt: a fresh IV deck for every message.
    function encrypt(plaintext, kEnc, kMac, aad = []) {
        return seal([...plaintext], [...kEnc], [...kMac], [...aad], randomDeck());
    }

    // Deterministic entry point for KATs and tests only. The IV MUST be a freshly and
    // truly shuffled deck in real use; a unique or predictable IV is not enough.
    function encryptWithIv(plaintext, kEnc, kMac, aad, iv) {
        return seal([...plaintext], [...kEnc], [...kMac], [...aad], [...iv]);
    }

    function decrypt(blob, kEnc, kMac, aad = []) {
        const [ok, plaintext] = open([...blob], [...kEnc], [...kMac], [...aad]);
        if (!ok) throw new Error("reject");
        return plaintext;
    }

    // Optional: two key decks from a byte master secret (software only). Security
    // assumes uniformly random key decks, however they are obtained.
    function deriveKeyDecks(master) {
        return derive_key_decks([...master]);
    }

    return { encrypt, encryptWithIv, decrypt, deriveKeyDecks };
}
