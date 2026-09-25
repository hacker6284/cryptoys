import * as THREE from "three";
import { FLY_MS, HOLD_MS, LIFT_MS, SHELF_Y1, SHELF_Z, SLOTS } from "../playroom/constants.js";
import { createToyDirector } from "../playroom/toy-director.js";
import { mountWorld } from "../playroom/world.js";
import { createUnboxRig } from "./deck-rig.js";
import { createBeatClock, prefersReducedMotion } from "./timeline.js";
import {
    SPIKE_SHOTS,
    applyShot,
    finishTableau,
    playBloom,
    playPhysical,
    playShot,
} from "./takes.js";

const canvas = document.querySelector("#playroom");
const titleEl = document.querySelector("#title");
const takeNav = document.querySelector("#takes");
const replayBtn = document.querySelector("#replay");
const beatEl = document.querySelector("#beat");
const errorEl = document.querySelector("#load-error");

const TAKES = {
    physical: { title: "physical", play: playPhysical },
    bloom: { title: "bloom", play: playBloom },
};

function takeFromQuery() {
    const raw = new URLSearchParams(location.search).get("take");
    return TAKES[raw] ? raw : "physical";
}

function writeTake(id) {
    const url = new URL(location.href);
    if (id === "physical") url.searchParams.delete("take");
    else url.searchParams.set("take", id);
    history.replaceState(null, "", `${url.pathname}${url.search}${url.hash}`);
}

function syncTake(id) {
    document.documentElement.dataset.take = id;
    titleEl.textContent = "unbox spike";
    document.title = `unbox spike · ${TAKES[id].title}`;
    takeNav.querySelectorAll("[data-take]").forEach((btn) => {
        btn.classList.toggle("on", btn.dataset.take === id);
        btn.setAttribute("aria-pressed", btn.dataset.take === id ? "true" : "false");
    });
}

function disposeObject(object) {
    if (!object) return;
    object.traverse?.((node) => {
        if (!node.isMesh) return;
        node.geometry?.dispose();
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) mat?.dispose();
    });
    object.parent?.remove(object);
}

try {
    const world = await mountWorld(canvas);
    const params = new URLSearchParams(location.search);
    if (params.get("debug") === "1") {
        document.documentElement.dataset.playroomDebug = "1";
        if (beatEl) beatEl.hidden = false;
    }
    const reduced = prefersReducedMotion();
    document.documentElement.dataset.motion = reduced ? "reduce" : "full";

    const anisotropy = Math.min(8, world.renderer.capabilities.getMaxAnisotropy());
    const rig = await createUnboxRig({ anisotropy });
    const prev = world.replaceToy("deck", rig.group);
    disposeObject(prev);
    world.shelfHome("deck");

    const director = createToyDirector(world);
    const clock = createBeatClock({ reduced });

    const shelfKey = new THREE.SpotLight(0xffd8b0, 2.1, 2.4, Math.PI / 5.5, 0.45, 1.3);
    shelfKey.position.set(SLOTS.deck.x + 0.10, SHELF_Y1 + 0.58, SHELF_Z + 0.58);
    shelfKey.target.position.set(SLOTS.deck.x, SHELF_Y1 + 0.05, SHELF_Z);
    world.scene.add(shelfKey);
    world.scene.add(shelfKey.target);

    const keyLight = new THREE.SpotLight(0xffc898, 0, 2.4, Math.PI / 5.4, 0.5, 1.15);
    keyLight.position.set(world.table.den.x + 0.16, 1.16, world.table.den.z + 0.30);
    keyLight.target.position.set(world.table.den.x, world.table.feltTopY + 0.04, world.table.den.z);
    world.scene.add(keyLight);
    world.scene.add(keyLight.target);

    let active = takeFromQuery();
    let running = null;
    let gen = 0;
    let ignoreSkipUntil = 0;

    function trackBox() {
        return world.toys.deck?.position;
    }

    async function restStage() {
        for (const mesh of rig.cards) {
            if (mesh.parent && mesh.parent !== rig.packet) {
                rig.packet.attach(mesh);
            }
        }
        if (rig.packet.parent !== rig.group) rig.group.add(rig.packet);
        rig.restow();
        rig.group.rotation.set(0, 0, 0);
        await director.home({ snap: true });
        keyLight.intensity = 0;
        applyShot(world.camera, SPIKE_SHOTS.landing);
        document.documentElement.dataset.beat = "landing";
        if (beatEl) beatEl.textContent = "";
    }

    async function runSequence(id) {
        const take = TAKES[id];
        if (!take) return;
        clock.skip();
        director.skip();
        if (running) await running;
        await restStage();
        gen = clock.begin();
        const mine = gen;
        syncTake(id);
        writeTake(id);
        document.documentElement.dataset.beat = "shelf";
        ignoreSkipUntil = performance.now() + LIFT_MS;

        running = (async () => {
            try {
                await playShot(world.camera, SPIKE_SHOTS.shelf, clock, mine, {
                    ms: reduced ? 0 : 720,
                });
                document.documentElement.dataset.beat = "shelf-hold";
                if (clock.dead(mine)) {
                    finishTableau(world, rig, world.camera, keyLight);
                    return;
                }
                const fly = director.borrow("doubledeal", { snap: reduced });
                await clock.wait(HOLD_MS * 0.45, mine);
                await playShot(world.camera, SPIKE_SHOTS.travel, clock, mine, {
                    ms: reduced ? 0 : FLY_MS - 200,
                    track: trackBox,
                });
                await fly;
                if (clock.dead(mine)) {
                    finishTableau(world, rig, world.camera, keyLight);
                    return;
                }
                await take.play({
                    world,
                    rig,
                    camera: world.camera,
                    clock,
                    gen: mine,
                    keyLight,
                    trackBox,
                });
                if (clock.dead(mine)) {
                    finishTableau(world, rig, world.camera, keyLight);
                }
            } catch (err) {
                console.error(err);
                throw err;
            }
        })();
        await running;
        running = null;
    }

    function skip() {
        if (performance.now() < ignoreSkipUntil) return;
        director.skip();
        clock.skip();
    }

    syncTake(active);
    applyShot(world.camera, SPIKE_SHOTS.landing);
    titleEl.classList.add("on");
    takeNav.classList.add("on");
    replayBtn.hidden = false;
    document.body.classList.add("is-ready");
    document.documentElement.dataset.playroomReady = "1";

    takeNav.addEventListener("click", (event) => {
        const btn = event.target.closest("[data-take]");
        if (!btn) return;
        event.preventDefault();
        active = btn.dataset.take;
        void runSequence(active);
    });
    replayBtn.addEventListener("click", () => void runSequence(active));

    window.addEventListener("pointerdown", (event) => {
        if (event.target.closest("a[href], button")) return;
        skip();
    });
    window.addEventListener("keydown", (event) => {
        if (event.key === "Escape") {
            skip();
            event.preventDefault();
        }
    });
    window.addEventListener("resize", () => world.resize());

    const observer = new MutationObserver(() => {
        if (beatEl) beatEl.textContent = document.documentElement.dataset.beat || "";
    });
    observer.observe(document.documentElement, { attributes: true, attributeFilter: ["data-beat"] });

    function tick() {
        director.update(performance.now());
        world.render();
        requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);

    if (params.get("auto") !== "0") {
        void runSequence(active);
    }
} catch (err) {
    console.error(err);
    document.body.classList.add("is-error");
    errorEl.hidden = false;
    errorEl.textContent = "The unbox spike failed to load."
        + (err && err.message ? ` (${err.message})` : "");
    titleEl.classList.add("on");
}
