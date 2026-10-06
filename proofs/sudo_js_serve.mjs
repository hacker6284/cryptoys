// Serve calls into a sudoc JS build (host API module <stem>.mjs), one JSON line per call on
// stdin ({"fn": name, "args": [...]}), one JSON line per result on stdout ({"r": value} or
// {"err": message}). An argument {"$call": name, "args": [...]} is replaced by the result of
// that exported call (memoised), e.g. a tier by name. This file only converts JSON; every
// value comes from the generated code. Driven by proofs/sudo_js.py.
//
// Usage: node sudo_js_serve.mjs <sudoc-js-outdir> <stem>

import path from "node:path";
import readline from "node:readline";
import { pathToFileURL } from "node:url";

const E = await import(pathToFileURL(path.resolve(process.argv[2], `${process.argv[3]}.mjs`)).href);
const memo = new Map();
const conv = (a) => {
  if (!(a && typeof a === "object" && !Array.isArray(a) && "$call" in a)) return a;
  const key = JSON.stringify(a);
  if (!memo.has(key)) memo.set(key, E[a.$call](...a.args.map(conv)));
  return memo.get(key);
};
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
