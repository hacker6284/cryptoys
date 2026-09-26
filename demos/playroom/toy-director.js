import { FLY_MS, LID_CLOSE_MS, LID_OPEN_MS, LIFT_MS } from "./constants.js";
import { easeInOutCubic, easeOutCubic } from "./beat-clock.js";
import { markBeat } from "./motion.js";

/**
 * Toy director.
 *
 * Shelf holds one of each kind. Scramble borrows the cube. DoubleDeal
 * borrows two decks: KEY lifts from the shelf slot, MSG lifts from the
 * toy chest (lid hinges open, deck leaves, lid closes). Camera follow
 * is the pose controller's job. Click skips; reduced-motion snaps.
 * DoubleDeal unbox lives in the adapter.
 */

const RECIPES = {
    scramble: { toys: ["cube"], extras: [], pose: "scramble" },
    doubledeal: { toys: ["deck", "deck2"], extras: ["chest"], pose: "doubledeal" },
    twodeck: { toys: ["deck", "deck2"], extras: ["chest"], pose: "doubledeal" },
};

function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
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

function samplePath(from, lift, mid, to, t, { ease = easeOutCubic, duration = FLY_MS } = {}) {
    const liftEnd = Math.min(0.28, LIFT_MS / Math.max(1, duration));
    if (t <= liftEnd) {
        const u = ease(t / liftEnd);
        return {
            x: lerp(from.x, lift.x, u),
            y: lerp(from.y, lift.y, u),
            z: lerp(from.z, lift.z, u),
        };
    }
    // Shelf departure stays ease-out so the lift reads in the hub
    // frame. Home flights pass ease-in-out so the return does not
    // rocket off the felt.
    const u = ease((t - liftEnd) / (1 - liftEnd));
    const s = 1 - u;
    return {
        x: s * s * lift.x + 2 * s * u * mid.x + u * u * to.x,
        y: s * s * lift.y + 2 * s * u * mid.y + u * u * to.y,
        z: s * s * lift.z + 2 * s * u * mid.z + u * u * to.z,
    };
}

export function recipeMotionMs(recipe) {
    if (!recipe?.extras?.includes("chest")) return FLY_MS;
    return LID_OPEN_MS + FLY_MS + LID_CLOSE_MS;
}

export function createToyDirector(world) {
    let highlightId = null;
    let flights = [];
    let lidAnim = null;
    let occupied = null;
    let borrowGen = 0;
    let skipGen = 0;
    let homing = false;

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

    function applyFlight(item, t) {
        if (!item) return;
        const { toy, from, lift, mid, to } = item;
        const p = samplePath(from.position, lift, mid, to.position, t, {
            ease: item.ease || easeOutCubic,
            duration: item.duration || FLY_MS,
        });
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

    function finishFlight(item) {
        if (!item) return;
        if (item.toy.userData.pendingDest) {
            item.to = clonePose(item.toy.userData.pendingDest);
            delete item.toy.userData.pendingDest;
        }
        applyFlight(item, 1);
        setTravelLight(item.toy, false);
        item.toy.userData.flightBusy = false;
        item.toy.userData.seatedY = item.toy.position.y;
        flights = flights.filter((entry) => entry !== item);
        writeFlightDebug(1, item.toy);
        item.onDone?.();
    }

    function flyToy(name, to, { snap, duration = FLY_MS, ease = easeOutCubic } = {}) {
        const toy = world.toys[name];
        if (!toy || !to) return Promise.resolve();
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
            const item = {
                toy,
                from,
                lift,
                mid,
                to: dest,
                last: performance.now(),
                elapsed: 0,
                duration,
                ease,
                onDone: resolve,
            };
            flights.push(item);
            setTravelLight(toy, true);
            applyFlight(item, 0);
        });
    }

    function animateLid(to, { snap, duration = 480 } = {}) {
        if (!world.setChestLid) return Promise.resolve();
        if (snap || prefersReducedMotion()) {
            world.setChestLid(to);
            return Promise.resolve();
        }
        const from = world.getChestLid?.() ?? 0;
        return new Promise((resolve) => {
            lidAnim = {
                from,
                to,
                elapsed: 0,
                last: performance.now(),
                duration,
                onDone: resolve,
            };
        });
    }

    async function borrow(algorithmId, { snap = false } = {}) {
        const recipe = recipeOf(algorithmId);
        if (!recipe) throw new Error(`unknown algorithm: ${algorithmId}`);
        if (occupied === algorithmId && !flights.length && !lidAnim) return recipe;
        if (flights.length || lidAnim) skip();
        occupied = algorithmId;
        const token = ++borrowGen;
        const primary = recipe.toys[0];
        world.setSlotEmpty(primary, true);
        const extras = recipe.toys.slice(1);
        const startedSkip = skipGen;
        let extraJob = null;
        if (recipe.extras.includes("chest") && extras.length) {
            extraJob = (async () => {
                markBeat("lid-open");
                await animateLid(1, { snap, duration: LID_OPEN_MS });
                if (token !== borrowGen || startedSkip !== skipGen) return;
                for (const name of extras) {
                    if (token !== borrowGen || startedSkip !== skipGen) return;
                    world.setSlotEmpty(name, true);
                    if (world.toys[name]) world.toys[name].userData.seatSurface = "table";
                    markBeat("msg-out");
                    await flyToy(name, world.getTablePose(name), { snap, duration: FLY_MS - 200 });
                }
                if (token !== borrowGen || startedSkip !== skipGen) return;
                markBeat("lid-close");
                await animateLid(0, { snap, duration: LID_CLOSE_MS });
            })();
        }
        markBeat(primary === "cube" ? "cube-fly" : "key-fly");
        if (world.toys[primary]) world.toys[primary].userData.seatSurface = "table";
        await flyToy(primary, world.getTablePose(primary), { snap });
        if (snap && extraJob) await extraJob;
        const toy = world.toys[primary];
        if (toy) toy.userData.seatedY = toy.position.y;
        clearHighlight();
        return recipe;
    }

    function prepareHome() {
        if (!occupied) return;
        homing = true;
        abandonFlights();
    }

    function abandonFlights() {
        if (lidAnim) {
            const done = lidAnim.onDone;
            lidAnim = null;
            done?.();
        }
        for (const item of [...flights]) {
            setTravelLight(item.toy, false);
            item.toy.userData.flightBusy = false;
            item.onDone?.();
        }
        flights = [];
    }

    async function home({ snap = false } = {}) {
        if (!occupied) return;
        borrowGen += 1;
        homing = true;
        try {
            // Keep live poses — do not finish-to-table or teleport extras.
            abandonFlights();
            const recipe = recipeOf(occupied);
            const names = recipe.toys.filter((name) => world.toys[name]);
            if (recipe.extras.includes("chest")) {
                markBeat("lid-receive");
                await animateLid(1, { snap, duration: LID_OPEN_MS });
            }
            markBeat("fly-home");
            await Promise.all(names.map((name) => {
                const toy = world.toys[name];
                if (toy) toy.userData.seatSurface = "shelf";
                return flyToy(name, world.getShelfPose(name), {
                    snap,
                    ease: easeInOutCubic,
                });
            }));
            for (const name of names) world.setSlotEmpty(name, false);
            if (recipe.extras.includes("chest")) {
                markBeat("lid-shut");
                await animateLid(0, { snap, duration: LID_CLOSE_MS });
            }
            occupied = null;
            writeFlightDebug("", world.toys[names[0]]);
        } finally {
            homing = false;
        }
    }

    function skip() {
        skipGen += 1;
        if (lidAnim) {
            world.setChestLid?.(homing ? 0 : lidAnim.to);
            const done = lidAnim.onDone;
            lidAnim = null;
            done?.();
        }
        for (const item of [...flights]) finishFlight(item);
        if (!occupied) return;
        const recipe = recipeOf(occupied);
        if (!recipe) return;
        if (homing) {
            for (const name of recipe.toys) {
                const toy = world.toys[name];
                const pose = world.getShelfPose?.(name);
                if (!toy || !pose) continue;
                toy.userData.flightBusy = false;
                world.applyPose(toy, pose);
                toy.updateMatrixWorld?.(true);
                world.setSlotEmpty(name, false);
            }
            if (recipe.extras.includes("chest")) world.setChestLid?.(0);
            return;
        }
        for (const name of recipe.toys.slice(1)) {
            const toy = world.toys[name];
            const pose = world.getTablePose?.(name);
            if (!toy || !pose) continue;
            toy.userData.flightBusy = false;
            toy.userData.seatSurface = "table";
            world.applyPose(toy, pose);
            toy.updateMatrixWorld?.(true);
        }
        if (recipe.extras.includes("chest")) world.setChestLid?.(0);
    }

    function update() {
        const now = performance.now();
        if (lidAnim) {
            lidAnim.elapsed += Math.min(50, Math.max(0, now - lidAnim.last));
            lidAnim.last = now;
            const u = Math.min(1, lidAnim.elapsed / lidAnim.duration);
            world.setChestLid?.(lerp(lidAnim.from, lidAnim.to, easeInOutCubic(u)));
            if (u >= 1) {
                const done = lidAnim.onDone;
                lidAnim = null;
                done?.();
            }
        }
        if (!flights.length) return;
        // 50ms cap: 60fps stays real-time (~1.8s). A hitch cannot skip
        // the arc, and software-GL still draws the in-between poses.
        for (const item of [...flights]) {
            item.elapsed += Math.min(50, Math.max(0, now - item.last));
            item.last = now;
            const u = Math.min(1, item.elapsed / item.duration);
            applyFlight(item, u);
            if (u >= 1) finishFlight(item);
        }
    }

    return {
        highlight,
        clearHighlight,
        borrow,
        home,
        prepareHome,
        skip,
        update,
        recipeOf,
        borrowMs(id) {
            return recipeMotionMs(recipeOf(id));
        },
        homeMs(id) {
            return recipeMotionMs(recipeOf(id) || recipeOf(occupied));
        },
        prefersReducedMotion,
        get busy() {
            return Boolean(flights.length || lidAnim);
        },
        get occupied() {
            return occupied;
        },
        get flying() {
            return flights[0]?.toy ?? null;
        },
    };
}
