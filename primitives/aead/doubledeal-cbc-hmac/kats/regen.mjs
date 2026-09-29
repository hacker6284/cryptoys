// Regenerate the blobs in kats/doubledeal_cbc_hmac_kats.json with the same
// aead.mjs wiring as aead.test.mjs (aead_harness.mjs). Keeps master / iv /
// plaintexts / aad; rewrites only each vector's blob. aead.test.mjs is the check.
//
// Usage, from the repo root, after the builds in this directory's README
// (sudoc JS build of doubledeal_cbc_hmac.sudo into /tmp/ddch, then tools/build.sh):
//   AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs [--check]
// Optional: DD_MJS=path/to/doubledeal.mjs (default demos/doubledeal/generated/doubledeal.mjs).
// --check (same convention as tools/gencheck.py): never write; print "OK <file>" if a
// fresh run would reproduce the committed JSON byte for byte, else "STALE <file>" and exit 1.
// tools/generate-demos.sh runs it with --check.
import { readFileSync, writeFileSync } from "node:fs";
import { relative } from "node:path";
import { bytesToHex, hexToBytes, katsPath, loadAead, readKats, repoRoot } from "../aead_harness.mjs";

const args = process.argv.slice(2);
const check = args.includes("--check");
const unknown = args.filter((a) => a !== "--check");
if (unknown.length) {
    console.error(`regen.mjs: unknown argument(s) ${unknown.join(" ")} (usage: regen.mjs [--check])`);
    process.exit(2);
}

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
const text = JSON.stringify(kats, null, 2) + "\n";
const rel = relative(repoRoot, katsPath);
if (check) {
    if (readFileSync(katsPath, "utf8") === text) {
        console.log(`OK ${rel}`);
    } else {
        console.error(`STALE ${rel} differs from a fresh run (${changed} blobs changed; fix: AEAD_OUT=... node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs)`);
        process.exit(1);
    }
} else {
    writeFileSync(katsPath, text);
    console.log(`wrote ${rel} (${changed} blobs changed)`);
}
