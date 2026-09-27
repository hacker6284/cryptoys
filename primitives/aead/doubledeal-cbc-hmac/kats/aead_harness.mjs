// Shared setup for aead.test.mjs and kats/regen.mjs: load the sudoc JS build
// of doubledeal_cbc_hmac.sudo (HMAC / KDF / pad / CBC helpers) and the
// DoubleDeal module, and wire them into aead.mjs. One copy, so the test and
// the regenerator cannot drift apart.
//
//   AEAD_OUT  sudoc JS build dir of doubledeal_cbc_hmac.sudo (default /tmp/ddch)
//   DD_MJS    DoubleDeal JS module (default demos/doubledeal/generated/doubledeal.mjs,
//             written by tools/build.sh)
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createAead } from "../aead.mjs";
import {
    bytesToDeck,
    cipherBytesToDeck,
    deckToCipherBytes,
    deckToMessageBytes,
} from "../../../../demos/doubledeal/cards.js";

const here = dirname(fileURLToPath(import.meta.url));
export const repoRoot = resolve(here, "../../../..");
export const katsPath = join(here, "doubledeal_cbc_hmac_kats.json");

export function hexToBytes(hex) {
    const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
    if (clean.length % 2 !== 0) throw new Error("hex length");
    const out = [];
    for (let i = 0; i < clean.length; i += 2) out.push(Number.parseInt(clean.slice(i, i + 2), 16));
    return out;
}

export function bytesToHex(bytes) {
    return "0x" + bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
}

export function readKats() {
    return JSON.parse(readFileSync(katsPath, "utf8"));
}

export async function loadAead({
    aeadOut = process.env.AEAD_OUT || "/tmp/ddch",
    ddMjs = process.env.DD_MJS || join(repoRoot, "demos/doubledeal/generated/doubledeal.mjs"),
} = {}) {
    const hmac = await import(pathToFileURL(resolve(aeadOut, "doubledeal_cbc_hmac.mjs")).href);
    const dd = await import(pathToFileURL(resolve(ddMjs)).href);
    return createAead({
        HMAC: hmac.HMAC,
        derive_keys: hmac.derive_keys,
        pad_iso7816: hmac.pad_iso7816,
        unpad_iso7816: hmac.unpad_iso7816,
        mac_input: hmac.mac_input,
        xor_bytes: hmac.xor_bytes,
        cbc_chain_from_cipher_block: hmac.cbc_chain_from_cipher_block,
        tags_equal: hmac.tags_equal,
        encrypt: dd.encrypt,
        decrypt: dd.decrypt,
        bytesToDeck,
        deckToMessageBytes,
        deckToCipherBytes,
        cipherBytesToDeck,
    });
}
