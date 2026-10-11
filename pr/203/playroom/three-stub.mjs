import { register } from "node:module";

// Node has no import map: resolve "three" to `source` and "three/…" addons
// to an empty module. Call before dynamically importing playroom modules.
export function stubThree(source = "") {
    const three = `data:text/javascript,${encodeURIComponent(source)}`;
    register(`data:text/javascript,${encodeURIComponent(`export async function resolve(spec, ctx, next) {
    if (spec === "three") return { url: ${JSON.stringify(three)}, shortCircuit: true };
    if (spec.startsWith("three/")) return { url: "data:text/javascript,", shortCircuit: true };
    return next(spec, ctx);
}`)}`);
}
