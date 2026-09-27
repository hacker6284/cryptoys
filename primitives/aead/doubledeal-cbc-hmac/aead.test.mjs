import { bytesToHex, hexToBytes, loadAead, readKats } from "./kats/aead_harness.mjs";

function assert(cond, message) {
    if (!cond) throw new Error(message);
}

function flip(bytes, index) {
    const out = [...bytes];
    out[index] ^= 1;
    return out;
}

// AEAD_OUT / DD_MJS: see kats/aead_harness.mjs.
const aead = await loadAead();
const kats = readKats();

const master = hexToBytes(kats.master);
const iv = hexToBytes(kats.iv);

const byName = Object.fromEntries(kats.vectors.map((v) => [v.name, v]));
const abcC = hexToBytes(byName.abc.blob).slice(0, -29);
const abcAadC = hexToBytes(byName.abc_aad.blob).slice(0, -29);
assert(abcC.join(",") === abcAadC.join(","), "AAD changes the tag only (Encrypt-then-MAC)");
assert(byName.abc.blob !== byName.abc_aad.blob, "AAD is in the MAC");

for (const vector of kats.vectors) {
    const plaintext = hexToBytes(vector.plaintext);
    const aad = hexToBytes(vector.aad);
    const blob = aead.encrypt(plaintext, master, iv, aad);
    assert(bytesToHex(blob) === vector.blob, `KAT encrypt ${vector.name}`);
    assert(bytesToHex(aead.decrypt(blob, master, iv, aad)) === vector.plaintext, `KAT decrypt ${vector.name}`);
}

for (const text of ["", "abc", "hello", "1234567890123456789012345678", "crosses a 28-byte boundary!!"]) {
    const plaintext = [...new TextEncoder().encode(text)];
    const aad = [...new TextEncoder().encode("hdr")];
    const blob = aead.encrypt(plaintext, master, iv, aad);
    assert(aead.decrypt(blob, master, iv, aad).join(",") === plaintext.join(","), `round-trip ${JSON.stringify(text)}`);
    const emptyAad = aead.encrypt(plaintext, master, iv, []);
    assert(emptyAad.join(",") !== blob.join(","), "AAD is in the tag");
}

const sample = aead.encrypt([1, 2, 3], master, iv, [9]);
assert(sample.length >= 58 && (sample.length - 29) % 29 === 0, "blob shape");

function mustReject(label, fn) {
    let rejected = false;
    try {
        fn();
    } catch {
        rejected = true;
    }
    assert(rejected, label);
}

mustReject("tag flip", () => aead.decrypt(flip(sample, sample.length - 1), master, iv, [9]));
mustReject("ciphertext flip", () => aead.decrypt(flip(sample, 0), master, iv, [9]));
mustReject("aad flip", () => aead.decrypt(sample, master, iv, [8]));
mustReject("iv flip", () => aead.decrypt(sample, master, flip(iv, 0), [9]));
mustReject("truncated tag", () => aead.decrypt(sample.slice(0, -1), master, iv, [9]));
mustReject("empty master", () => aead.encrypt([1], [], iv, []));
mustReject("wrong master key", () => aead.decrypt(sample, flip(master, 0), iv, [9]));

const otherIv = flip(iv, 3);
const other = aead.encrypt([1, 2, 3], master, otherIv, [9]);
assert(other.join(",") !== sample.join(","), "IV changes the ciphertext");
mustReject("wrong iv on decrypt", () => aead.decrypt(other, master, iv, [9]));

console.log("doubledeal-cbc-hmac aead tests passed");
