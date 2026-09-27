// Check witness_v8.json against the JS target of the frozen doubledeal_v8.sudo.
// Usage: sudoc build --target js -o /tmp/dd-v8-js primitives/cipher/doubledeal/v8/doubledeal_v8.sudo
//        node proofs/deprecated/doubledeal-v8/attack/check_witness.mjs /tmp/dd-v8-js
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
const here = dirname(fileURLToPath(import.meta.url));
const out = process.argv[2] || "/tmp/dd-v8-js";
const dd = await import(pathToFileURL(join(out, "doubledeal_v8.mjs")).href);
const w = JSON.parse(readFileSync(join(here, "..", "witness_v8.json"), "utf8"));
const [x, y] = w.tau;
const tau = (c) => (c === x ? y : c === y ? x : c);
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const c1 = dd.encrypt(w.message, w.key);
const c2 = dd.encrypt(w.message.map(tau), w.key);
const ok = eq(c1, w.cipher) && eq(c2, c1.map(tau)) && !eq(c1, c2);
console.log(`v8 witness (JS target): E(M)=C ${eq(c1, w.cipher)}, E(tau M)=tau E(M) ${eq(c2, c1.map(tau))}, tau acts ${!eq(c1, c2)}`);
process.exit(ok ? 0 : 1);
