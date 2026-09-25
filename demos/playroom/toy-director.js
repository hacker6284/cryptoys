import { FLY_MS, LIFT_MS } from "./constants.js";

/**
 * Toy director.
 *
 * Shelf holds one of each kind. Scramble borrows the cube and DoubleDeal
 * borrows the deck: lift from the slot, then arc to the felt. Camera
 * follow is the pose controller's job. Click skips; reduced-motion snaps.
 * Chest extras highlight only; unbox / deal choreography is later.
 */

const RECIPES = {
    scramble: { toys: ["cube"], extras: [], pose: "scramble" },
    doubledeal: { toys: ["deck"], extras: ["chest"], pose: "doubledeal" },
    twodeck: { toys: ["deck"], extras: ["chest"], pose: "doubledeal" },
};

function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
}

function easeOutCubic(t) {
    return 1 - (1 - t) ** 3;
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
    // Leave the slot promptly (ease-out). ease-in-out kept the cube on the
    // shelf for most of the first second, so the landing shot never read
    // a departure — only a later pop on the felt.
    const u = easeOutCubic((t - liftEnd) / (1 - liftEnd));
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
        const root = typeof document !== "undefined" ? document.documentElement : null;
        if (!root || root.dataset.playroomDebug !== "1") return;
        root.dataset.flight = Number.isFinite(u) ? String(Math.round(Math.min(1, Math.max(0, u)) * 100)) : "";
        if (toy) {
            root.dataset.toyX = toy.position.x.toFixed(2);
            root.dataset.toyY = toy.position.y.toFixed(2);
            root.dataset.toyZ = toy.position.z.toFixed(2);
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
        light.intensity = on ? 4.2 : 0;
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
        flight.toy.userData.flightBusy = false;
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
            toy.userData.flightBusy = false;
            world.applyPose(toy, dest);
            toy.updateMatrixWorld(true);
            writeFlightDebug(1, toy);
            return Promise.resolve();
        }
        const lift = {
            x: from.position.x,
            y: from.position.y + 0.38,
            z: from.position.z,
        };
        const mid = {
            x: from.position.x * 0.28 + dest.position.x * 0.72,
            y: Math.max(from.position.y, dest.position.y) + 0.58,
            z: from.position.z * 0.28 + dest.position.z * 0.72,
        };
        return new Promise((resolve) => {
            toy.userData.flightBusy = true;
            flight = {
                toy,
                from,
                lift,
                mid,
                to: dest,
                last: performance.now(),
                elapsed: 0,
                duration,
                onDone: resolve,
            };
            setTravelLight(toy, true);
            applyFlight(0);
        });
    }

    async function borrow(algorithmId, { snap = false } = {}) {
        const recipe = recipeOf(algorithmId);
        if (!recipe) throw new Error(`unknown algorithm: ${algorithmId}`);
        if (occupied === algorithmId && !flight) return recipe;
        if (flight) skip();
        occupied = algorithmId;
        const name = recipe.toys[0];
        world.setSlotEmpty(name, true);
        await flyToy(name, world.getTablePose(name), { snap });
        const toy = world.toys[name];
        if (toy) toy.userData.seatedY = toy.position.y;
        clearHighlight();
        return recipe;
    }

    async function home({ snap = false } = {}) {
        if (!occupied) return;
        if (flight) {
            flight.toy.userData.flightBusy = false;
            const resolve = flight.onDone;
            flight = null;
            resolve?.();
        }
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
        if (!flight) return;
        const now = performance.now();
        // 50ms cap: 60fps stays real-time (~1.8s). A hitch cannot skip
        // the arc, and software-GL still draws the in-between poses.
        flight.elapsed += Math.min(50, Math.max(0, now - flight.last));
        flight.last = now;
        const u = Math.min(1, flight.elapsed / flight.duration);
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
        get flying() {
            return flight?.toy ?? null;
        },
    };
}
