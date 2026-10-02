// Reads [{deal, h: {cp, co, ep, eo}}, ...] as JSON on stdin and prints one line per item: the hex
// digest of HashDeckBodyFrom(deal, h) from the sudoc JS build of v3/megadreifach.sudo
// ($MD3_OUT, default /tmp/megadreifach-v3). Used by em4_vs_sudo.py. Computes nothing itself.
import { readFileSync } from "node:fs";
import { join } from "node:path";

const out = process.env.MD3_OUT || "/tmp/megadreifach-v3";
const md = await import(join(out, "megadreifach.mjs"));
const items = JSON.parse(readFileSync(0, "utf8"));
const hex = (b) => b.map((x) => x.toString(16).padStart(2, "0")).join("");
for (const { deal, h } of items) console.log(hex(md.HashDeckBodyFrom(deal, h)));
