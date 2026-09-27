// three bakes light counts (per type, plus shadow casters) into every lit
// shader, so adding, removing, hiding or shadow-toggling a light mid-scene
// relinks every lit material. Every light is registered at boot, then only
// its intensity / color / position / parent change.
export function createLights(scene) {
    const byKey = new Map();
    let sealed = null;

    function signature() {
        const counts = {};
        scene.traverseVisible((o) => {
            if (!o.isLight) return;
            counts[o.type] = (counts[o.type] || 0) + 1;
            if (o.castShadow) counts.castShadow = (counts.castShadow || 0) + 1;
        });
        return JSON.stringify(counts, Object.keys(counts).sort());
    }

    return {
        add(key, light, parent = scene) {
            if (sealed) throw new Error(`lights sealed: cannot add "${key}" after boot`);
            if (byKey.has(key)) throw new Error(`light "${key}" already registered`);
            byKey.set(key, light);
            parent.add(light);
            if (light.target) scene.add(light.target);
            return light;
        },
        get(key) {
            const light = byKey.get(key);
            if (!light) throw new Error(`unknown light "${key}"`);
            return light;
        },
        seal() {
            sealed = signature();
        },
        check() {
            const now = signature();
            if (now !== sealed) throw new Error(`scene lights changed after boot: ${sealed} -> ${now}`);
        },
    };
}
