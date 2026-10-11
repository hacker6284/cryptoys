// Shared by the BS node tests: the generated module (tools/build.sh) and the
// known-answer file it copies beside the page.
import { existsSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));

/** Throws in CI when the generated module is missing; locally returns false (the caller skips). */
export function requireGenerated(file = "generated/_bs_impl.mjs") {
    if (existsSync(join(here, file))) return true;
    if (process.env.CI) throw new Error(`${file} is missing: run tools/build.sh (CI never skips these tests)`);
    return false;
}

export async function loadGenerated() {
    if (!requireGenerated() || !requireGenerated("generated/kats.json")) return null;
    const [host, raw, rt] = await Promise.all([
        import(join(here, "generated/bs.mjs")),
        import(join(here, "generated/_bs_impl.mjs")),
        import(join(here, "generated/_sudo_rt.mjs")),
    ]);
    const kats = JSON.parse(readFileSync(join(here, "generated/kats.json"), "utf8"));
    return { host, raw, rt, kats, exchanges: kats.vectors.filter((v) => v.kind === "exchange") };
}
