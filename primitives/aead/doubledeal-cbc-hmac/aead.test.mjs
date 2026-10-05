import { bytesToHex, hexToBytes, katIvDeck, loadAead, loadModule, readKats } from "./aead_harness.mjs";
import { randomDeck } from "./aead.mjs";

function assert(cond, message) {
    if (!cond) throw new Error(message);
}

function bump(bytes, index) {
    const out = [...bytes];
    out[index] = (out[index] + 1) % 256;
    return out;
}

function isDeck(d) {
    return d.length === 52 && new Set(d).size === 52 && d.every((c) => Number.isInteger(c) && c >= 0 && c < 52);
}

// AEAD_OUT: see aead_harness.mjs.
const aead = await loadAead();
const m = await loadModule();
const kats = readKats();
assert(kats.product === "DoubleDeal-CBC-Sandwich" && kats.version === "v2", "KAT header");

// The optional key derivation reproduces the published key decks.
const [kEnc, kMac] = aead.deriveKeyDecks(hexToBytes(kats.master));
assert(JSON.stringify(kEnc) === JSON.stringify(kats.k_enc), "KAT k_enc");
assert(JSON.stringify(kMac) === JSON.stringify(kats.k_mac), "KAT k_mac");
assert(bytesToHex(m.mac_tag(kMac, [m.version_deck()])) === kats.mac_version_only, "KAT mac_version_only");
// The KAT IV deck is unrank(Hash("DoubleDeal-CBC-Sandwich/v2 KAT IV") mod 52!) (SPEC §9).
assert(JSON.stringify(await katIvDeck()) === JSON.stringify(kats.iv), "KAT iv");

for (const v of kats.vectors) {
    const pt = hexToBytes(v.plaintext);
    const aad = hexToBytes(v.aad);
    const blob = aead.encryptWithIv(pt, kEnc, kMac, aad, kats.iv);
    assert(bytesToHex(blob) === v.blob, `KAT encrypt ${v.name}`);
    assert(bytesToHex(aead.decrypt(blob, kEnc, kMac, aad)) === v.plaintext, `KAT decrypt ${v.name}`);
    assert(bytesToHex(blob.slice(0, 29)) === bytesToHex(hexToBytes(v.blob).slice(0, 29)), "IV leads the blob");
}
const byName = Object.fromEntries(kats.vectors.map((v) => [v.name, v]));
assert(byName.abc.blob.slice(0, -58) === byName.abc_aad.blob.slice(0, -58), "AAD changes the tag only");
assert(byName.abc.blob !== byName.abc_aad.blob, "AAD is in the MAC");

// User-supplied key decks: any two distinct full decks.
const ke = randomDeck();
const km = randomDeck();
for (const text of ["", "abc", "1234567890123456789012345678", "crosses a 28-byte boundary!!!"]) {
    const pt = [...new TextEncoder().encode(text)];
    const aad = [...new TextEncoder().encode("hdr")];
    const blob = aead.encrypt(pt, ke, km, aad);
    assert(blob.length % 29 === 0 && blob.length >= 87, "blob shape");
    assert(aead.decrypt(blob, ke, km, aad).join(",") === pt.join(","), `round-trip ${JSON.stringify(text)}`);
    const again = aead.encrypt(pt, ke, km, aad);
    assert(bytesToHex(again) !== bytesToHex(blob), "a fresh IV deck every message");
}

for (let i = 0; i < 20; i++) assert(isDeck(randomDeck()), "randomDeck is a deck");

function mustReject(label, fn) {
    let rejected = false;
    try {
        fn();
    } catch {
        rejected = true;
    }
    assert(rejected, label);
}

const sample = aead.encrypt([1, 2, 3], ke, km, [9]);
mustReject("tag byte", () => aead.decrypt(bump(sample, sample.length - 1), ke, km, [9]));
mustReject("ciphertext byte", () => aead.decrypt(bump(sample, 40), ke, km, [9]));
mustReject("IV byte", () => aead.decrypt(bump(sample, 5), ke, km, [9]));
mustReject("AAD", () => aead.decrypt(sample, ke, km, [8]));
mustReject("truncated", () => aead.decrypt(sample.slice(0, -1), ke, km, [9]));
mustReject("dropped block", () => aead.decrypt(sample.slice(29), ke, km, [9]));
mustReject("keys swapped", () => aead.decrypt(sample, km, ke, [9]));
mustReject("other MAC key", () => aead.decrypt(sample, ke, randomDeck(), [9]));
mustReject("not a deck (IV = 2^232 - 1)", () => aead.decrypt(Array(29).fill(255).concat(sample.slice(29)), ke, km, [9]));
mustReject("equal key decks", () => aead.encrypt([1], ke, ke, []));
mustReject("key not a deck", () => aead.encrypt([1], ke.slice(1), km, []));

console.log("doubledeal-cbc-sandwich v2 aead tests passed");
