// Demo, exhaustive: the generated curve_test() and make_certificate() of ecbs.sudo on
// every (x, y) in GF(3^7)^2 (4,782,969 pairs). Writes, for pair i = 2187 x + y (a number
// is the integer sum t_j 3^j of its trits), one byte (curve test passed) and two int16s
// (the certificate's x and y, or -1 when there is none). This file only loops and packs;
// every value comes from the generated code. Driven by soundness_demo.py.
//
// Usage: node demo_exhaustive.mjs <sudoc-js-outdir> <out-prefix> <shard> <shards>

import { writeFileSync } from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const [outDir, prefix, shardS, shardsS] = process.argv.slice(2);
const E = await import(pathToFileURL(path.resolve(outDir, "ecbs.mjs")).href);
const t = E.tier("Demo");
const Q = 2187, n = 7;
const shard = Number(shardS), shards = Number(shardsS);
const dig = (v) => { const a = []; for (let i = 0; i < n; i++) { a.push(v % 3); v = Math.floor(v / 3); } return a; };
const num = (a) => a.reduce((s, d, i) => s + d * 3 ** i, 0);
const xs = [];
for (let x = shard; x < Q; x += shards) xs.push(x);
const curve = new Uint8Array(xs.length * Q), cx = new Int16Array(xs.length * Q), cy = new Int16Array(xs.length * Q);
let j = 0;
for (const x of xs) {
  const X = dig(x);
  for (let y = 0; y < Q; y++, j++) {
    const c = { x: X, y: dig(y) };
    curve[j] = E.curve_test(t, c) ? 1 : 0;
    const a = E.make_certificate(t, c);
    cx[j] = a === null ? -1 : num(a.x);
    cy[j] = a === null ? -1 : num(a.y);
  }
}
writeFileSync(`${prefix}.${shard}.xs.json`, JSON.stringify(xs));
writeFileSync(`${prefix}.${shard}.curve`, curve);
writeFileSync(`${prefix}.${shard}.cx`, Buffer.from(cx.buffer));
writeFileSync(`${prefix}.${shard}.cy`, Buffer.from(cy.buffer));
