// Shared JSON / trit helpers of the key-exchange vector collectors
// (bs/vectors/collect_vectors.mjs, ecbs/vectors/collect_vectors.mjs). Conversion only:
// nothing here computes a vector.
import { readFileSync } from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

export function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

// Registers and cell strings: '.WR' = 0/1/2, hole 0 (or the first cell) first.
export const toTrits = (s) => [...s].map((c) => ".WR".indexOf(c));
export const toPegs = (xs) => xs.map((t) => ".WR"[t]).join("");
export const ROWS = "ABCDEFGHIJ";

// argv[2] is the sudoc JS outdir; returns the generated module <name>.mjs and the
// collector's inputs.json (beside the collector, in `here`).
export async function load(name, here) {
  const outDir = process.argv[2];
  if (!outDir) {
    console.error("usage: node collect_vectors.mjs <sudoc-js-outdir>");
    process.exit(2);
  }
  const mod = await import(pathToFileURL(path.resolve(outDir, `${name}.mjs`)).href);
  const inputs = JSON.parse(readFileSync(path.join(here, "inputs.json"), "utf8"));
  return { mod, inputs };
}

// The first keys of every vectors file; the hash comes from <NAME>_SUDO_SHA256
// (set by vectors_regen.sh).
export function header(name) {
  return {
    schema: 1,
    generated_by: `proofs/key_exchange/${name}/vectors/regen.sh`,
    source: `primitives/key_exchange/${name}/${name}.sudo`,
    sudo_sha256: process.env[`${name.toUpperCase()}_SUDO_SHA256`] ?? "",
    sudocode_commit: process.env.SUDOCODE_COMMIT ?? "",
  };
}
