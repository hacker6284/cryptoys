import { FLY_MS, LIFT_MS } from "./constants.js";

/**
 * Toy director — Unify-1.
 *
 * Shelf holds one of each kind. Scramble borrows the cube: lift from the
 * slot, then arc to the felt. Camera follow is the pose controller's job;
 * this module only moves toys. Click skips; prefers-reduced-motion snaps.
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

function easeOutCubic(t) {
    return 1 - (1 - t) ** 3;
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

function lerp(a, b, t) {
    return a + (b - a) * t;
}

function samplePath(from, lift, mid, to, t) {
    const liftEnd = LIFT_MS / FLY_MS;
    if (t <= liftEnd) {
        const u = easeOutCubic(t / liftEnd);
        return {
            x: lerp(from.x, lift.x, u),
            y: lerp(from.y, lift.y, u),
            z: lerp(from.z, lift.z, u),
        };
    }
    const u = easeInOutCubic((t - liftEnd) / (1 - liftEnd));
    const s = 1 - u;
    return {
        x: s * s * lift.x + 2 * s * u * mid.x + u * u * to.x,
        y: s * s * lift.y + 2 * s * u * mid.y + u * u * to.y,
        z: s * s * lift.z + 2 * s * u * mid.z + u * u * to.z,
    };
}

export function createToyDirector(world) {
    let highlightId = null;
    let flight = null;
    let occupied = null;

    function recipeOf(id) {
        return RECIPES[id] || null;
    }

    function writeFlightDebug(u, toy) {
        const root = document.documentElement;
        root.dataset.flight = Number.isFinite(u) ? String(Math.round(Math.min(1, Math.max(0, u)) * 100)) : "";
        if (toy) {
            root.dataset.cubeX = toy.position.x.toFixed(2);
            root.dataset.cubeY = toy.position.y.toFixed(2);
            root.dataset.cubeZ = toy.position.z.toFixed(2);
        }
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

    function setTravelLight(toy, on) {
        let light = toy.userData.travelLight;
        if (!light) {
            light = world.createTravelLight?.(toy);
            if (!light) return;
        }
        light.intensity = on ? 2.4 : 0;
    }

    function applyFlight(t) {
        if (!flight) return;
        const { toy, from, lift, mid, to } = flight;
        const p = samplePath(from.position, lift, mid, to.position, t);
        toy.position.set(p.x, p.y, p.z);
        toy.rotation.set(
            lerp(from.rotation.x, to.rotation.x, t),
            lerp(from.rotation.y, to.rotation.y, t),
            lerp(from.rotation.z, to.rotation.z, t),
        );
        toy.quaternion.setFromEuler(toy.rotation);
        toy.updateMatrixWorld(true);
        writeFlightDebug(t, toy);
    }

    function finishFlight() {
        if (!flight) return;
        applyFlight(1);
        setTravelLight(flight.toy, false);
        if (flight.raf) cancelAnimationFrame(flight.raf);
        const done = flight.onDone;
        flight = null;
        writeFlightDebug(1);
        done?.();
    }

    function flyToy(name, to, { snap, duration = FLY_MS } = {}) {
        const toy = world.toys[name];
        if (!toy) return Promise.resolve();
        const from = poseOf(toy);
        const dest = clonePose(to);
        if (snap || prefersReducedMotion()) {
            world.applyPose(toy, dest);
            toy.updateMatrixWorld(true);
            writeFlightDebug(1, toy);
            return Promise.resolve();
        }
        const lift = {
            x: from.position.x,
            y: from.position.y + 0.34,
            z: from.position.z,
        };
        const mid = {
            x: from.position.x * 0.35 + dest.position.x * 0.65,
            y: Math.max(from.position.y, dest.position.y) + 0.52,
            z: from.position.z * 0.35 + dest.position.z * 0.65,
        };
        return new Promise((resolve) => {
            if (flight?.raf) cancelAnimationFrame(flight.raf);
            flight = {
                toy,
                from,
                lift,
                mid,
                to: dest,
                start: performance.now(),
                duration,
                onDone: resolve,
                raf: 0,
            };
            setTravelLight(toy, true);
            applyFlight(0);
            const step = () => {
                if (!flight || flight.onDone !== resolve) return;
                const now = performance.now();
                const u = Math.min(1, (now - flight.start) / flight.duration);
                applyFlight(u);
                if (u >= 1) finishFlight();
                else flight.raf = requestAnimationFrame(step);
            };
            flight.raf = requestAnimationFrame(step);
        });
    }

    async function borrow(algorithmId, { snap = false } = {}) {
        const recipe = recipeOf(algorithmId);
        if (!recipe) throw new Error(`unknown algorithm: ${algorithmId}`);
        if (algorithmId !== "scramble") {
            throw new Error("toy director: DoubleDeal borrow is Unify-2");
        }
        if (occupied === algorithmId && !flight) return recipe;
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
        writeFlightDebug("", world.toys[name]);
    }

    function skip() {
        if (!flight) return;
        finishFlight();
    }

    function update() {
        // Flights drive their own rAF so they cannot stall if the render
        // loop passes a mismatched timestamp. Kept as a no-op hook.
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
        get flying() {
            return flight?.toy ?? null;
        },
    };
}
