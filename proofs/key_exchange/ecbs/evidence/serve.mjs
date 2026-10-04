// Serve calls into a sudoc JS build of primitives/key_exchange/ecbs/ecbs.sudo, one
// JSON line per call on stdin ({"fn": name, "args": [...]}), one JSON line per
// result on stdout ({"r": value} or {"err": message}). Tiers are passed by name
// ({"tier": "Toy"}) and turned into E.tier(name) here. This file only converts
// JSON; every value comes from the generated code. Driven by sudo_js.py.
//
// Usage: node serve.mjs <sudoc-js-outdir>

import path from "node:path";
import readline from "node:readline";
import { pathToFileURL } from "node:url";

const E = await import(pathToFileURL(path.resolve(process.argv[2], "ecbs.mjs")).href);
const tiers = {};
const conv = (a) => (a && typeof a === "object" && !Array.isArray(a) && "tier" in a && Object.keys(a).length === 1)
  ? (tiers[a.tier] ??= E.tier(a.tier)) : a;
const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
for await (const line of rl) {
  if (!line) continue;
  const { fn, args } = JSON.parse(line);
  let out;
  try {
    if (!(fn in E)) throw new Error(`no export ${fn}`);
    out = { r: E[fn](...args.map(conv)) ?? null };
  } catch (e) {
    out = { err: `${e?.constructor?.name ?? "Error"}: ${e?.message ?? e}` };
  }
  process.stdout.write(JSON.stringify(out) + "\n");
}
