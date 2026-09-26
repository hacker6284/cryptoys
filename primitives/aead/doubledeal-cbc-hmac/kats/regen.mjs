// Regenerate kats/doubledeal_cbc_hmac_kats.json blobs from the conformance
// sudo (HMAC / KDF / pad via AEAD_OUT) and DoubleDeal encrypt (DD_MJS), using
// the same aead.mjs path as aead.test.mjs. Keeps master / iv / plaintexts / aad.
// Usage (after tools/generate-demos.sh-style builds):
//   AEAD_OUT=/tmp/ddch-test [DD_MJS=demos/doubledeal/generated/doubledeal.mjs] \
//     node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs [--check]
import { readFileSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createAead } from "../aead.mjs";
import { bytesToDeck, cipherBytesToDeck, deckToCipherBytes, deckToMessageBytes } from "../../../../demos/doubledeal/cards.js";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "../../../..");
const outDir = process.env.AEAD_OUT || "/tmp/ddch";
const ddPath = resolve(process.env.DD_MJS || join(root, "demos/doubledeal/generated/doubledeal.mjs"));
const hmac = await import(pathToFileURL(`${outDir}/doubledeal_cbc_hmac.mjs`).href);
const dd = await import(pathToFileURL(ddPath).href);
const aead = createAead({
    HMAC: hmac.HMAC, derive_keys: hmac.derive_keys, pad_iso7816: hmac.pad_iso7816,
    unpad_iso7816: hmac.unpad_iso7816, mac_input: hmac.mac_input, xor_bytes: hmac.xor_bytes,
    cbc_chain_from_cipher_block: hmac.cbc_chain_from_cipher_block, tags_equal: hmac.tags_equal,
    encrypt: dd.encrypt, decrypt: dd.decrypt,
    bytesToDeck, deckToMessageBytes, deckToCipherBytes, cipherBytesToDeck,
});
const hexToBytes = (h) => { const c = h.startsWith("0x") ? h.slice(2) : h; const o = []; for (let i = 0; i < c.length; i += 2) o.push(parseInt(c.slice(i, i + 2), 16)); return o; };
const bytesToHex = (b) => "0x" + b.map((x) => x.toString(16).padStart(2, "0")).join("");
const file = join(here, "doubledeal_cbc_hmac_kats.json");
const kats = JSON.parse(readFileSync(file, "utf8"));
const master = hexToBytes(kats.master), iv = hexToBytes(kats.iv);
let changed = 0;
for (const v of kats.vectors) {
    const blob = bytesToHex(aead.encrypt(hexToBytes(v.plaintext), master, iv, hexToBytes(v.aad)));
    if (blob !== v.blob) changed++;
    v.blob = blob;
}
if (process.argv.includes("--check")) {
    console.log(changed === 0 ? "kats match" : `kats differ in ${changed} vectors`);
    process.exit(changed === 0 ? 0 : 1);
}
writeFileSync(file, JSON.stringify(kats, null, 2) + "\n");
console.log(`wrote ${file} (${changed} blobs changed)`);
