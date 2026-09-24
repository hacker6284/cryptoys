import { pathToFileURL } from "node:url";
import { createAead } from "./aead.mjs";
import {
    bytesToDeck,
    cipherBytesToDeck,
    deckToCipherBytes,
    deckToMessageBytes,
} from "../../../demos/doubledeal/cards.js";
import { decrypt, encrypt } from "../../../demos/doubledeal/generated/doubledeal.mjs";
import kats from "./kats/doubledeal_cbc_hmac_kats.json" with { type: "json" };

function assert(cond, message) {
    if (!cond) throw new Error(message);
}

function hexToBytes(hex) {
    const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
    if (clean.length % 2 !== 0) throw new Error("hex length");
    const out = [];
    for (let i = 0; i < clean.length; i += 2) out.push(Number.parseInt(clean.slice(i, i + 2), 16));
    return out;
}

function bytesToHex(bytes) {
    return "0x" + bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
}

function flip(bytes, index) {
    const out = [...bytes];
    out[index] ^= 1;
    return out;
}

const outDir = process.env.AEAD_OUT || "/tmp/ddch";
const hmacMod = await import(pathToFileURL(`${outDir}/doubledeal_cbc_hmac.mjs`).href);

const aead = createAead({
    HMAC: hmacMod.HMAC,
    derive_keys: hmacMod.derive_keys,
    pad_iso7816: hmacMod.pad_iso7816,
    unpad_iso7816: hmacMod.unpad_iso7816,
    mac_input: hmacMod.mac_input,
    xor_bytes: hmacMod.xor_bytes,
    cbc_chain_from_cipher_block: hmacMod.cbc_chain_from_cipher_block,
    tags_equal: hmacMod.tags_equal,
    encrypt,
    decrypt,
    bytesToDeck,
    deckToMessageBytes,
    deckToCipherBytes,
    cipherBytesToDeck,
});

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
