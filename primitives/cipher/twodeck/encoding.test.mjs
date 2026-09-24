import { ecb_decrypt, ecb_encrypt, ctr_decrypt, ctr_encrypt } from "../../../demos/twodeck/generated/twodeck.mjs";
import {
    bytesToDeck,
    cipherBytesToDeck,
    deckToCipherBytes,
    deckToMessageBytes,
    deckToWire,
    decksToHex,
    decksToText,
    hexToDecks,
    padMessage,
    textToDecks,
    textToKey,
    textToNonce,
    unpadMessage,
    wireToDeck,
} from "../../../demos/twodeck/cards.js";

function assert(cond, message) {
    if (!cond) throw new Error(message);
}

const fact = [1n];
for (let n = 1; n <= 52; n++) fact[n] = fact[n - 1] * BigInt(n);

function rankOf(perm) {
    const items = Array.from({ length: perm.length }, (_, i) => i);
    let value = 0n;
    for (const card of perm) {
        const index = items.indexOf(card);
        value += BigInt(index) * fact[items.length - 1];
        items.splice(index, 1);
    }
    return value;
}

const identity = bytesToDeck(new Array(28).fill(0));
assert(identity.every((card, i) => card === i), "rank 0 is the CHaSeD order");
assert(rankOf(identity) === 0n, "rank of the identity deck is 0");

const swapped = [...identity];
[swapped[50], swapped[51]] = [swapped[51], swapped[50]];
assert(rankOf(swapped) === 1n, "swapping the last two cards is rank 1, the §5.2 digit");

const fringe = fact[52] - 1n;
const fringeBytes = [];
let rest = fringe;
for (let i = 0; i < 29; i++) {
    fringeBytes.unshift(Number(rest & 0xffn));
    rest >>= 8n;
}
const fringeDeck = cipherBytesToDeck(fringeBytes);
assert(rankOf(fringeDeck) === fringe, "29-byte form reaches 52! − 1");
assert(deckToCipherBytes(fringeDeck).every((byte, i) => byte === fringeBytes[i]), "29-byte form round-trips the last deck");
let rejected = false;
try {
    deckToMessageBytes(fringeDeck);
} catch {
    rejected = true;
}
assert(rejected, "a deck at or above 2^224 has no 28-byte form");

const past = new Array(29).fill(0);
past[0] = 1;
const almost = cipherBytesToDeck(past);
assert(rankOf(almost) === 1n << 224n, "2^224 is the first integer with no 28-byte form");
rejected = false;
try {
    deckToMessageBytes(almost);
} catch {
    rejected = true;
}
assert(rejected, "2^224 itself is rejected as a 28-byte message");
const top = bytesToDeck(new Array(28).fill(255));
assert(deckToMessageBytes(top).every((byte) => byte === 255), "every 28-byte block unranks and ranks back");

assert(padMessage([]).length === 28 && padMessage([])[0] === 0x80, "empty message is one pad block");
assert(padMessage(new Array(28).fill(1)).length === 56, "an exact block gains a pad block");
assert(unpadMessage(padMessage([1, 2, 0x80])).join(",") === "1,2,128", "a payload that ends in 0x80 keeps that byte");

for (const text of ["", "hello", "héllo", "1234567890123456789012345678", "a longer message that crosses a block boundary"]) {
    assert(decksToText(textToDecks(text)) === text, `text round-trip: ${JSON.stringify(text)}`);
}
assert(decksToText(textToDecks("0x68656c6c6f")) === "hello", "0x hex is the bytes, not the characters");
assert(decksToText(textToDecks("0xff")) === "0xff", "bytes that are not text come back with 0x");

const key = textToKey("cryptoy");
assert(textToKey("0x63727970746f79").every((card, i) => card === key[i]), "0x key matches the same ASCII bytes");
assert(key.length === 52 && new Set(key).size === 52, "a short key is one deck");
rejected = false;
try {
    textToKey("");
} catch {
    rejected = true;
}
assert(rejected, "an empty key is rejected");
rejected = false;
try {
    textToKey("x".repeat(29));
} catch {
    rejected = true;
}
assert(rejected, "a key longer than 28 bytes is rejected");

const wire = deckToWire(identity);
assert(wireToDeck(wire).every((card, i) => card === identity[i]), "52-byte wire form round-trips");
rejected = false;
try {
    wireToDeck(identity.map((card, i) => (i === 1 ? 0 : card)));
} catch {
    rejected = true;
}
assert(rejected, "a wire deck with a duplicate card is rejected");

rejected = false;
try {
    hexToDecks("ab".repeat(29));
} catch {
    rejected = true;
}
assert(rejected, "hex without an 0x prefix is rejected");

const nonce = textToNonce("nonce");
assert(textToNonce("0x6e6f6e6365").every((card, i) => card === nonce[i]), "0x nonce matches the same ASCII bytes");
assert(nonce.length === 39 && new Set(nonce).size === 39 && nonce.every((card) => card < 39), "nonce is 39 non-diamond cards");

for (const text of ["hello", "", "héllo", "1234567890123456789012345678"]) {
    const blocks = textToDecks(text);
    const ecb = ecb_encrypt(blocks, key);
    assert(decksToHex(ecb).split("\n").every((line) => /^0x[0-9a-f]{58}$/.test(line)), "ECB ciphertext is 0x and 29 bytes per block");
    assert(decksToText(ecb_decrypt(hexToDecks(decksToHex(ecb)), key)) === text, `ECB byte round-trip: ${JSON.stringify(text)}`);
    const ctr = ctr_encrypt(blocks, key, nonce);
    assert(decksToText(ctr_decrypt(ctr, key, nonce)) === text, `CTR byte round-trip: ${JSON.stringify(text)}`);
}

console.log("encoding tests passed");
