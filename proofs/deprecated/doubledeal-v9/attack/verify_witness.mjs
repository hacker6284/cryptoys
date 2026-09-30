// Independent check of exact-commutation witnesses against the spec-emitted JS encrypt
// (demos/doubledeal/generated/doubledeal.mjs, built by sudoc from doubledeal.sudo).
// usage: node verify_witness.mjs PATH/TO/doubledeal.mjs VECTORS.json WITNESSES.json
import { readFileSync } from "fs";
import { pathToFileURL } from "url";
const [mod, vecs, wits] = process.argv.slice(2);
const { encrypt } = await import(pathToFileURL(mod).href);
const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
let nv = 0;
for (const v of JSON.parse(readFileSync(vecs)).vectors)
  if (v.kind === "encrypt") { if (!eq(encrypt(v.message, v.key), v.cipher)) throw new Error("vector mismatch"); nv++; }
const W = JSON.parse(readFileSync(wits));
const [x, y] = W.swap, sig = c => (c === x ? y : c === y ? x : c);
let ok = 0;
for (const w of W.witnesses) {
  const C = encrypt(w.message, w.key), C2 = encrypt(w.message.map(sig), w.key);
  if (!eq(C, w.cipher) || !eq(C2, C.map(sig))) throw new Error("witness FAILED: " + JSON.stringify(w));
  ok++;
}
console.log(`JS encrypt matches ${nv} committed vectors; ${ok}/${W.witnesses.length} witnesses verified: ` +
  `encrypt(swap(m),k) == swap(encrypt(m,k)) for swap ${x}<->${y}`);
