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

// The fixed IV deck of the KAT vectors (SPEC §9): unrank(Hash(KAT_IV_LABEL) mod 52!), computed by
// the build alone: the imported MegaDreifach module's Hash, then the sudo's unrank_reduce (an
// internal function, called through the build's impl module). No arithmetic here.
export const KAT_IV_LABEL = "DoubleDeal-CBC-Sandwich/v2 KAT IV";
export async function katIvDeck({ aeadOut = process.env.AEAD_OUT || "/tmp/ddch" } = {}) {
    const at = (f) => import(pathToFileURL(resolve(aeadOut, f)).href);
    const [impl, rt, md] = await Promise.all([at("_doubledeal_cbc_hmac_impl.mjs"), at("_sudo_rt.mjs"), at("megadreifach.mjs")]);
    const digest = [...md.Hash([...new TextEncoder().encode(KAT_IV_LABEL)])].map(Number);
    return [...impl.unrank_reduce(rt.lst(digest.map(BigInt)))].map(Number);
}

export async function loadAead(opts = {}) {
    const m = await loadModule(opts);
    return createAead({ seal: m.aead_seal, open: m.aead_open, derive_key_decks: m.derive_key_decks });
}
