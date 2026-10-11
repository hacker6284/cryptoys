/**
 * A sudoc-generated value as plain numbers, arrays and objects, for
 * postMessage and for view code: ints as numbers, lists as arrays, records
 * as objects by their sudo field list, an enum case without payload as its
 * name ("Destroyer"), one with payload as { case, ...fields }.
 */
export function plain(v) {
    if (typeof v === "bigint") return Number(v);
    const ctor = v?.constructor;
    if (ctor && Array.isArray(ctor._sudoFields)) {
        const kind = ctor._sudoKind;
        const enumCase = kind && kind[0] === "e" ? kind[1].split(".").pop() : null;
        if (enumCase && !ctor._sudoFields.length) return enumCase;
        const out = enumCase ? { case: enumCase } : {};
        for (const f of ctor._sudoFields) out[f] = plain(v[f]);
        return out;
    }
    if (v && typeof v !== "string" && typeof v[Symbol.iterator] === "function") return Array.from(v, plain);
    return v;
}
