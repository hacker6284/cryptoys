import { FLY_MS } from "./constants.js";

/**
 * Toy director — Unify-1.
 *
 * Shelf holds one of each kind. Scramble borrows the cube, flies it to the
 * round table, and hands off to the adapter. Back reverses. Hover rims the
 * algorithm's shelf toys (and the chest if extras will be needed). Click
 * skips; prefers-reduced-motion snaps in place.
 *
 * DoubleDeal borrow / chest extras are Unify-2.
 */

const RECIPES = {
    scramble: { toys: ["cube"], extras: [], pose: "scramble" },
    doubledeal: { toys: ["deck"], extras: ["chest"], pose: "seated" },
    twodeck: { toys: ["deck"], extras: ["chest"], pose: "seated" },
};

function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
}

function easeInOutCubic(t) {
    return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
}

function clonePose(pose) {
    return {
        position: { ...pose.position },
        rotation: { ...pose.rotation },
    };
}

function poseOf(object) {
    return {
        position: { x: object.position.x, y: object.position.y, z: object.position.z },
        rotation: { x: object.rotation.x, y: object.rotation.y, z: object.rotation.z },
    };
}

function midPoint(a, b) {
    return {
        x: (a.x + b.x) * 0.5,
        y: Math.max(a.y, b.y) + 0.32,
        z: (a.z + b.z) * 0.5,
    };
}

function bezier(a, m, b, t) {
    const u = 1 - t;
    return {
        x: u * u * a.x + 2 * u * t * m.x + t * t * b.x,
        y: u * u * a.y + 2 * u * t * m.y + t * t * b.y,
        z: u * u * a.z + 2 * u * t * m.z + t * t * b.z,
    };
}

export function createToyDirector(world) {
    let highlightId = null;
    let flight = null;
    let occupied = null;

    function recipeOf(id) {
        return RECIPES[id] || null;
    }

    function highlight(algorithmId) {
        if (occupied) return;
        const recipe = recipeOf(algorithmId);
        if (!recipe) return;
        if (highlightId && highlightId !== algorithmId) clearHighlight();
        highlightId = algorithmId;
        world.setHighlight(recipe.toys, true);
        if (recipe.extras.length) world.setHighlight(recipe.extras, true);
    }

    function clearHighlight() {
        if (!highlightId) return;
        const recipe = recipeOf(highlightId);
        if (recipe) {
            world.setHighlight(recipe.toys, false);
            if (recipe.extras.length) world.setHighlight(recipe.extras, false);
        }
        highlightId = null;
    }

    function applyFlight(t) {
        if (!flight) return;
        const k = easeInOutCubic(t);
        const { toy, from, to, mid } = flight;
        const p = bezier(from.position, mid, to.position, k);
        toy.position.set(p.x, p.y, p.z);
        toy.rotation.set(
            from.rotation.x + (to.rotation.x - from.rotation.x) * k,
            from.rotation.y + (to.rotation.y - from.rotation.y) * k,
            from.rotation.z + (to.rotation.z - from.rotation.z) * k,
        );
        toy.quaternion.setFromEuler(toy.rotation);
    }

    function finishFlight() {
        if (!flight) return;
        applyFlight(1);
        const done = flight.onDone;
        flight = null;
        done?.();
    }

    function flyToy(name, to, { snap, duration = FLY_MS } = {}) {
        const toy = world.toys[name];
        const from = poseOf(toy);
        if (snap || prefersReducedMotion()) {
            world.applyPose(toy, to);
            return Promise.resolve();
        }
        return new Promise((resolve) => {
            flight = {
                toy,
                from,
                to: clonePose(to),
                mid: midPoint(from.position, to.position),
                start: performance.now(),
                duration,
                onDone: resolve,
            };
        });
    }

    async function borrow(algorithmId, { snap = false } = {}) {
        const recipe = recipeOf(algorithmId);
        if (!recipe) throw new Error(`unknown algorithm: ${algorithmId}`);
        if (algorithmId !== "scramble") {
            throw new Error("toy director: DoubleDeal borrow is Unify-2");
        }
        if (occupied === algorithmId) return recipe;
        if (flight) skip();
        clearHighlight();
        occupied = algorithmId;
        const name = recipe.toys[0];
        world.setSlotEmpty(name, true);
        await flyToy(name, world.getTablePose(name), { snap });
        return recipe;
    }

    async function home({ snap = false } = {}) {
        if (!occupied) return;
        if (flight) skip();
        const recipe = recipeOf(occupied);
        const name = recipe.toys[0];
        await flyToy(name, world.getShelfPose(name), { snap });
        world.setSlotEmpty(name, false);
        occupied = null;
    }

    function skip() {
        if (!flight) return;
        finishFlight();
    }

    function update(now = performance.now()) {
        if (!flight) return;
        const u = Math.min(1, (now - flight.start) / flight.duration);
        applyFlight(u);
        if (u >= 1) finishFlight();
    }

    return {
        highlight,
        clearHighlight,
        borrow,
        home,
        skip,
        update,
        recipeOf,
        prefersReducedMotion,
        get busy() {
            return Boolean(flight);
        },
        get occupied() {
            return occupied;
        },
    };
}
