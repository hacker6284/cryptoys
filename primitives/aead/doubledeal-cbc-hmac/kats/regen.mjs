// Regenerate kats/doubledeal_cbc_hmac_kats.json from the real code: the sudoc JS build of
// doubledeal_cbc_hmac.sudo, wired by aead_harness.mjs. Keeps the inputs (master, iv,
// plaintexts, aad); rewrites every output (k_enc, k_mac, the KAT IV deck, each blob,
// mac_version_only). The IV deck is unrank(Hash("DoubleDeal-CBC-Sandwich/v2 KAT IV") mod 52!)
// from the build (aead_harness.mjs katIvDeck).
// aead.test.mjs is the check.
//
// Usage, from the repo root, after the sudoc JS build in this directory's README:
//   AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs [--check]
// --check (same convention as tools/gencheck.py): never write; print "OK <file>" if a
// fresh run would reproduce the committed JSON byte for byte, else "STALE <file>" and exit 1.
// tools/generate-demos.sh runs it with --check.
import { readFileSync, writeFileSync } from "node:fs";
import { relative } from "node:path";
import { bytesToHex, hexToBytes, katIvDeck, katsPath, loadAead, loadModule, readKats, repoRoot } from "../aead_harness.mjs";

const args = process.argv.slice(2);
const check = args.includes("--check");
const unknown = args.filter((a) => a !== "--check");
if (unknown.length) {
    console.error(`regen.mjs: unknown argument(s) ${unknown.join(" ")} (usage: regen.mjs [--check])`);
    process.exit(2);
}

const aead = await loadAead();
const m = await loadModule();
const kats = readKats();
const [kEnc, kMac] = aead.deriveKeyDecks(hexToBytes(kats.master));
kats.k_enc = kEnc;
kats.k_mac = kMac;
kats.iv = await katIvDeck();
let changed = 0;
for (const v of kats.vectors) {
    const blob = bytesToHex(aead.encryptWithIv(hexToBytes(v.plaintext), kEnc, kMac, hexToBytes(v.aad), kats.iv));
    if (blob !== v.blob) changed++;
    v.blob = blob;
}
kats.mac_version_only = bytesToHex(m.mac_tag(kMac, [m.version_deck()]));
// Decks as one-line arrays, the rest indented.
const text = JSON.stringify(kats, null, 2).replace(/\[\s+([\d,\s]+?)\s+\]/g, (_, xs) => "[" + xs.split(/\s*,\s*/).join(", ") + "]") + "\n";
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
