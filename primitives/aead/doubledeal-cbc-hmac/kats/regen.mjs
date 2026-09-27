// Regenerate the blobs in kats/doubledeal_cbc_hmac_kats.json with the same
// aead.mjs wiring as aead.test.mjs (aead_harness.mjs). Keeps master / iv /
// plaintexts / aad; rewrites only each vector's blob. aead.test.mjs is the check.
//
// Usage, from the repo root, after the builds in this directory's README
// (sudoc JS build of doubledeal_cbc_hmac.sudo into /tmp/ddch, then tools/build.sh):
//   AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs
// Optional: DD_MJS=path/to/doubledeal.mjs (default demos/doubledeal/generated/doubledeal.mjs).
import { writeFileSync } from "node:fs";
import { bytesToHex, hexToBytes, katsPath, loadAead, readKats } from "../aead_harness.mjs";

const aead = await loadAead();
const kats = readKats();
const master = hexToBytes(kats.master);
const iv = hexToBytes(kats.iv);
let changed = 0;
for (const v of kats.vectors) {
    const blob = bytesToHex(aead.encrypt(hexToBytes(v.plaintext), master, iv, hexToBytes(v.aad)));
    if (blob !== v.blob) changed++;
    v.blob = blob;
}
writeFileSync(katsPath, JSON.stringify(kats, null, 2) + "\n");
console.log(`wrote ${katsPath} (${changed} blobs changed)`);
