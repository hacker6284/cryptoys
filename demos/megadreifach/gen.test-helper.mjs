// Shared by the MegaDreifach node tests: the generated module (tools/build.sh)
// and plain-number views of its internal records.
import { existsSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));

/**
 * Throws in CI when the generated module is missing (CI builds it first,
 * so a missing module there is a failure, not a skip). Locally returns
 * null and the caller skips its generated checks.
 */
export function requireGenerated(file = "generated/_megadreifach_impl.mjs") {
    if (existsSync(join(here, file))) return true;
    if (process.env.CI) throw new Error(`${file} is missing: run tools/build.sh (CI never skips these tests)`);
    return false;
}

export async function loadGenerated() {
    const impl = join(here, "generated/_megadreifach_impl.mjs");
    if (!requireGenerated()) return null;
    const [host, raw, rt] = await Promise.all([
        import(join(here, "generated/megadreifach.mjs")),
        import(impl),
        import(join(here, "generated/_sudo_rt.mjs")),
    ]);
    const num = (v) => (typeof v === "bigint" ? Number(v) : v);
    const list = (v) => [...v].map(num);
    const toPos = (p) => rt.rec(new raw.Position(...["cp", "co", "ep", "eo"].map((k) => rt.lst(p[k].map(BigInt)))));
    const fromPos = (p) => ({ cp: list(p.cp), co: list(p.co), ep: list(p.ep), eo: list(p.eo) });
    return {
        host,
        raw,
        list,
        identity: () => fromPos(raw.identity()),
        faceTurn: (p, face, clicks) => fromPos(raw.face_turn(toPos(p), BigInt(face), BigInt(((clicks % 5) + 5) % 5))),
        nbrs: (f) => list(raw.face_nbrs(BigInt(f))),
        opposite: (f) => num([...raw.opposites][f]),
        spin: (o, k) => list(raw.spin_about_up(rt.lst(o.map(BigInt)), BigInt(k))),
        kats: () => JSON.parse(readFileSync(join(here, "generated/kats.json"), "utf8")),
    };
}

export function samePos(a, b) {
    return ["cp", "co", "ep", "eo"].every((k) => a[k].length === b[k].length && a[k].every((v, i) => v === b[k][i]));
}

export function bytesOfHex(hex) {
    const out = [];
    for (let i = 0; i < hex.length; i += 2) out.push(parseInt(hex.slice(i, i + 2), 16));
    return out;
}
