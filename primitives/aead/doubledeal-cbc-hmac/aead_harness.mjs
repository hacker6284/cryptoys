// Shared setup for aead.test.mjs and kats/regen.mjs: load the sudoc JS build of
// doubledeal_cbc_hmac.sudo (which imports MegaDreifach and DoubleDeal) and wire it
// into aead.mjs. One copy, so the test and the regenerator cannot drift apart.
//
//   AEAD_OUT  sudoc JS build dir of doubledeal_cbc_hmac.sudo (default /tmp/ddch)
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createAead } from "./aead.mjs";

const here = dirname(fileURLToPath(import.meta.url));
export const repoRoot = resolve(here, "../../..");
export const katsPath = join(here, "kats", "doubledeal_cbc_hmac_kats.json");

export function hexToBytes(hex) {
    const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
    if (clean.length % 2 !== 0) throw new Error("hex length");
    const out = [];
    for (let i = 0; i < clean.length; i += 2) out.push(Number.parseInt(clean.slice(i, i + 2), 16));
    return out;
}

export function bytesToHex(bytes) {
    return "0x" + [...bytes].map((b) => b.toString(16).padStart(2, "0")).join("");
}

export function readKats() {
    return JSON.parse(readFileSync(katsPath, "utf8"));
}

export async function loadModule({ aeadOut = process.env.AEAD_OUT || "/tmp/ddch" } = {}) {
    return import(pathToFileURL(resolve(aeadOut, "doubledeal_cbc_hmac.mjs")).href);
}

export async function loadAead(opts = {}) {
    const m = await loadModule(opts);
    return createAead({ seal: m.aead_seal, open: m.aead_open, derive_key_decks: m.derive_key_decks });
}
