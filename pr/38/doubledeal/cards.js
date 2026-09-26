// §5.3 byte encoding. Outside encrypt/decrypt. 52! does not fit in a
// sudocode int, so this is the software copy of the §5.2 factoradic loop
// for a 52-card deck. It does not reduce the rank modulo 52!.

const FACT = [1n];
for (let n = 1; n <= 52; n++) FACT[n] = FACT[n - 1] * BigInt(n);

const TWO_224 = 1n << 224n;

function bytesToInt(bytes) {
    let value = 0n;
    for (const byte of bytes) value = (value << 8n) | BigInt(byte);
    return value;
}

function intToBytes(value, length) {
    const out = new Array(length);
    let rest = value;
    for (let i = length - 1; i >= 0; i--) {
        out[i] = Number(rest & 0xffn);
        rest >>= 8n;
    }
    if (rest !== 0n) throw new Error(`This integer does not fit in ${length} bytes.`);
    return out;
}

function unrank(count, rank) {
    if (rank < 0n || rank >= FACT[count]) throw new Error(`This rank does not name a permutation of ${count}.`);
    const items = Array.from({ length: count }, (_, i) => i);
    const out = [];
    let rest = rank;
    for (let k = count; k >= 1; k--) {
        const unit = FACT[k - 1];
        const index = Number(rest / unit);
        rest %= unit;
        out.push(items.splice(index, 1)[0]);
    }
    return out;
}

function rankPerm(perm) {
    const items = Array.from({ length: perm.length }, (_, i) => i);
    let value = 0n;
    for (const card of perm) {
        const index = items.indexOf(card);
        if (index < 0) throw new Error("This deck is not a permutation.");
        value += BigInt(index) * FACT[items.length - 1];
        items.splice(index, 1);
    }
    return value;
}

function isPermutation(cards, count) {
    if (cards.length !== count) return false;
    const seen = new Set(cards);
    if (seen.size !== count) return false;
    for (const card of cards) {
        if (!Number.isInteger(card) || card < 0 || card >= count) return false;
    }
    return true;
}

export function padMessage(bytes) {
    const out = [...bytes, 0x80];
    while (out.length % 28 !== 0) out.push(0);
    return out;
}

export function unpadMessage(bytes) {
    if (bytes.length === 0 || bytes.length % 28 !== 0) {
        throw new Error("Padded plaintext is a multiple of 28 bytes.");
    }
    let end = bytes.length - 1;
    while (end >= 0 && bytes[end] === 0) end -= 1;
    if (end < 0 || bytes[end] !== 0x80) throw new Error("The padding is not 0x80 followed by zeros.");
    return bytes.slice(0, end);
}

export function bytesToDeck(bytes) {
    if (bytes.length !== 28) throw new Error("A message block is 28 bytes.");
    return unrank(52, bytesToInt(bytes));
}

export function deckToMessageBytes(deck) {
    if (!isPermutation(deck, 52)) throw new Error("This deck is not a permutation.");
    const rank = rankPerm(deck);
    if (rank >= TWO_224) throw new Error("This deck's rank does not fit in 28 bytes.");
    return intToBytes(rank, 28);
}

export function deckToCipherBytes(deck) {
    if (!isPermutation(deck, 52)) throw new Error("This deck is not a permutation.");
    return intToBytes(rankPerm(deck), 29);
}

export function cipherBytesToDeck(bytes) {
    if (bytes.length !== 29) throw new Error("A ciphertext block is 29 bytes.");
    return unrank(52, bytesToInt(bytes));
}

export function deckToWire(deck) {
    if (!isPermutation(deck, 52)) throw new Error("A wire deck is 52 distinct card ids.");
    return [...deck];
}

export function wireToDeck(bytes) {
    if (!isPermutation([...bytes], 52)) throw new Error("A wire deck is 52 distinct card ids.");
    return [...bytes];
}

// A box is the characters typed, as UTF-8. A leading 0x means the rest is hex.
export function boxToBytes(text) {
    const trimmed = text.trim();
    if (!/^0x/i.test(trimmed)) return [...new TextEncoder().encode(trimmed)];
    const hex = trimmed
        .split(/\s+/)
        .filter(Boolean)
        .map((part) => part.replace(/^0x/i, ""))
        .join("");
    if (hex.length === 0) throw new Error("There are no hex digits after 0x.");
    if (!/^[0-9a-fA-F]+$/.test(hex)) throw new Error("Hex after 0x can only be digits and a–f.");
    if (hex.length % 2 !== 0) throw new Error("Hex after 0x needs an even number of digits.");
    const bytes = [];
    for (let i = 0; i < hex.length; i += 2) bytes.push(Number.parseInt(hex.slice(i, i + 2), 16));
    return bytes;
}

export function textToDecks(text) {
    const padded = padMessage(boxToBytes(text));
    const decks = [];
    for (let i = 0; i < padded.length; i += 28) decks.push(bytesToDeck(padded.slice(i, i + 28)));
    return decks;
}

export function decksToText(decks) {
    const bytes = [];
    for (const deck of decks) bytes.push(...deckToMessageBytes(deck));
    let raw;
    try {
        raw = unpadMessage(bytes);
    } catch (err) {
        throw new Error(err instanceof Error ? err.message : "The padding is not 0x80 followed by zeros.");
    }
    try {
        return new TextDecoder("utf-8", { fatal: true }).decode(new Uint8Array(raw));
    } catch {
        return "0x" + raw.map((byte) => byte.toString(16).padStart(2, "0")).join("");
    }
}

export function textToKey(text) {
    const bytes = boxToBytes(text);
    if (bytes.length === 0) throw new Error("The key is empty.");
    if (bytes.length > 28) throw new Error(`A key is one deck, so this page takes at most 28 bytes. This one is ${bytes.length}.`);
    const block = bytes.length === 28 ? bytes : padMessage(bytes);
    return bytesToDeck(block);
}

export function textToNonce(text) {
    const bytes = boxToBytes(text);
    if (bytes.length === 0) throw new Error("CTR needs a nonce.");
    if (bytes.length > 19) throw new Error(`A nonce on this page is at most 19 bytes. This one is ${bytes.length}.`);
    const rank = bytesToInt(bytes);
    if (rank >= FACT[39]) throw new Error("This nonce does not fit in 39 cards.");
    return unrank(39, rank);
}

export function decksToHex(decks) {
    return decks.map((deck) => "0x" + deckToCipherBytes(deck).map((byte) => byte.toString(16).padStart(2, "0")).join("")).join("\n");
}

export function hexToDecks(text) {
    const trimmed = text.trim();
    if (!trimmed) throw new Error("The ciphertext is empty.");
    if (!/^0x/i.test(trimmed)) throw new Error("Ciphertext is hex, so the box needs an 0x prefix. Without that prefix it is text.");
    const bytes = boxToBytes(trimmed);
    if (bytes.length === 0 || bytes.length % 29 !== 0) {
        throw new Error("Each ciphertext block is 29 bytes: 0x and then 58 hex digits.");
    }
    const decks = [];
    for (let i = 0; i < bytes.length; i += 29) decks.push(cipherBytesToDeck(bytes.slice(i, i + 29)));
    return decks;
}

export function randomHex(bytes) {
    const data = new Uint8Array(bytes);
    crypto.getRandomValues(data);
    return [...data].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}
