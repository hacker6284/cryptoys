import { adapters } from "./adapters.js";
import { FOLLOW_HOLD_MS, LIFT_MS } from "./constants.js";
import { installCapture } from "./capture-strip.js";
import { continueTo, followEnter, followLeave, markBeat, trackActive, trackToys } from "./motion.js";
import { createPoseController } from "./pose-controller.js";
import { resolvePoseName } from "./poses.js";
import { playroomDebugEnabled } from "./puzzles.js";
import { createToyDirector } from "./toy-director.js";
import { mountWorld } from "./world.js";

const canvas = document.querySelector("#playroom");
const titleEl = document.querySelector("#title");
const menuEl = document.querySelector("#menu");
const sitBtn = document.querySelector("#sit");
const backBtn = document.querySelector("#back");
const errorEl = document.querySelector("#load-error");

const ALGOS = {
    scramble: { title: "Scramble", pose: "scramble", toy: "cube" },
    doubledeal: { title: "DoubleDeal", pose: "doubledeal", toy: "deck" },
};

let activeAlgo = null;
let leaving = false;
let starting = false;
let skippedStart = false;
let ignoreSkipUntil = 0;
let resizeWorld = () => {};

function seatedQueryPose(pose) {
    if (!pose) return pose;
    if (pose === "scramble" || pose === "doubledeal") return "seated";
    if (String(pose).startsWith("unbox")) return "seated";
    return pose;
}

function writeQuery({ pose, algo }) {
    const url = new URL(location.href);
    const poseName = seatedQueryPose(pose);
    if (!poseName || poseName === "landing") url.searchParams.delete("pose");
    else url.searchParams.set("pose", poseName);
    if (!algo) url.searchParams.delete("algo");
    else url.searchParams.set("algo", algo);
    if (algo !== "scramble" || !playroomDebugEnabled(url.search)) url.searchParams.delete("puzzle");
    history.replaceState(null, "", `${url.pathname}${url.search}${url.hash}`);
}

function syncOverlays({ name, overlays, tweening }) {
    const showMenu = Boolean(overlays?.menu) && !tweening && !activeAlgo;
    const algoName = ALGOS[activeAlgo]?.title || "cryptoys";
    titleEl.textContent = algoName;
    if (activeAlgo) document.title = algoName;
    else document.title = "cryptoys";
    titleEl.classList.toggle("on", Boolean(overlays?.title));
    menuEl.classList.toggle("on", showMenu);
    sitBtn.hidden = name !== "landing" || tweening || Boolean(activeAlgo);
    backBtn.hidden = tweening || (name === "landing" && !activeAlgo);
    document.documentElement.dataset.pose = name;
    document.documentElement.dataset.algo = activeAlgo || "";
    document.documentElement.dataset.playroomTween = tweening ? "1" : "0";
    document.querySelectorAll(".playroom-dock").forEach((dock) => {
        const on = Boolean(activeAlgo) && !tweening && !leaving && !starting && dock.id === `${activeAlgo}-dock`;
        dock.classList.toggle("on", on);
    });
    requestAnimationFrame(() => resizeWorld());
}

try {
    const world = await mountWorld(canvas);
    resizeWorld = () => world.resize();
    const params = new URLSearchParams(location.search);
    if (params.get("debug") === "1") document.documentElement.dataset.playroomDebug = "1";
    const capture = installCapture(canvas);
    const initialPose = resolvePoseName(params.get("pose"));
    const initialAlgo = String(params.get("algo") || "").trim().toLowerCase();
    const poses = createPoseController(world.camera, {
        domElement: canvas,
        onChange(state) {
            syncOverlays(state);
            if (!state.tweening) {
                writeQuery({
                    pose: state.name,
                    algo: activeAlgo,
                });
            }
        },
    });
    const installOpts = {
        poses,
        prefersReducedMotion: () => poses.prefersReducedMotion(),
    };
    const capture = installCapture(canvas);
    if (typeof window !== "undefined" && (params.get("debug") === "1" || params.get("debugCapture") === "1")) {
        window.__playroomWorld = world;
    }
    adapters.scramble.install(world, installOpts);
    adapters.doubledeal.install(world, installOpts);
    void adapters.scramble.preload();
    void adapters.doubledeal.preload();
    await adapters.scramble.ready?.();
    const director = createToyDirector(world);

    async function startAlgo(id, { snap = false } = {}) {
        const meta = ALGOS[id];
        const adapter = adapters[id];
        if (!meta || !adapter) return;
        if (activeAlgo === id || starting || leaving) return;
        starting = true;
        skippedStart = false;
        activeAlgo = id;
        capture.begin(`${id}-enter`);
        markBeat("enter-start");
        syncOverlays({
            name: poses.name,
            overlays: { title: true, menu: false },
            tweening: !snap && !poses.prefersReducedMotion(),
        });
        try {
            const reduced = snap || poses.prefersReducedMotion();
            ignoreSkipUntil = performance.now() + LIFT_MS;
            const warm = adapter.preload();
            await adapter.prepareEnter?.();
            const recipe = director.recipeOf(id);
            const flyToys = recipe?.toys || [meta.toy];
            const fly = director.borrow(id, { snap: reduced });
            if (reduced) {
                poses.snap(meta.pose);
            } else {
                // Shared hub→play: follow whatever is in flight for
                // the full borrow (lid + extras), then keep tracking
                // so unbox does not cut to a named seat.
                const enterTrack = trackActive(world, flyToys);
                followEnter(poses, {
                    to: meta.pose,
                    track: enterTrack,
                    holdMs: FOLLOW_HOLD_MS,
                    duration: director.borrowMs(id),
                });
                poses.followLive?.(enterTrack);
            }
            await Promise.all([fly, warm]);
            markBeat("enter-landed");
            if (leaving) {
                capture.end();
                return;
            }
            adapter.view()?.rememberSeated?.();
            await adapter.enter({ snap: reduced || skippedStart });
            starting = false;
            markBeat("enter-done");
            capture.end();
            if (leaving) return;
            writeQuery({ pose: "seated", algo: id });
            syncOverlays({
                name: poses.name,
                overlays: { title: true, menu: false, teach: true },
                tweening: poses.busy,
            });
        } catch (err) {
            console.error(err);
            await adapter.leave({ snap: true });
            await director.home({ snap: true });
            adapter.revealShelf?.();
            activeAlgo = null;
            errorEl.hidden = false;
            errorEl.textContent = err && err.message
                ? err.message
                : `${meta.title} could not start in the playroom.`;
            poses.snap("landing");
            capture.end();
        } finally {
            starting = false;
        }
    }

    async function leaveAlgo() {
        if (leaving) return;
        if (!activeAlgo) {
            poses.goTo("landing");
            return;
        }
        leaving = true;
        const id = activeAlgo;
        capture.begin(`${id}-leave`);
        markBeat("leave-start");
        const meta = ALGOS[id];
        const reduced = poses.prefersReducedMotion();
        const recipe = director.recipeOf(id);
        const flyToys = recipe?.toys || [meta.toy];
        const prepMs = adapters[id]?.leaveMs?.({ snap: reduced }) ?? 0;
        const homeMs = director.homeMs(id);
        ignoreSkipUntil = performance.now() + LIFT_MS;
        director.prepareHome?.();
        if (reduced) poses.snap("landing");
        else {
            // Shared play→hub: one follow shot covering gather + home.
            // Toys and camera stay on the same clock — no via:shelf,
            // no look.copy, no cut to landing while flights are live.
            followLeave(poses, {
                to: "landing",
                track: trackToys(world, flyToys),
                holdMs: FOLLOW_HOLD_MS,
                duration: prepMs + homeMs,
            });
        }
        await adapters[id]?.leave?.({ snap: reduced });
        markBeat("leave-home");
        await director.home({ snap: reduced });
        poses.followLive?.(null);
        adapters[id]?.revealShelf?.();
        markBeat("hub-settle");
        activeAlgo = null;
        leaving = false;
        capture.end();
        writeQuery({ pose: "landing", algo: null });
        syncOverlays({
            name: poses.name,
            overlays: { title: true, menu: true },
            tweening: poses.busy,
        });
    }

    if (ALGOS[initialAlgo]) {
        if (initialAlgo === "doubledeal" && !poses.prefersReducedMotion()) {
            poses.snap("landing");
        } else {
            poses.snap(ALGOS[initialAlgo].pose);
        }
    } else {
        poses.snap(initialPose);
    }

    document.body.classList.add("is-ready");
    document.documentElement.dataset.playroomReady = "1";
    document.documentElement.dataset.motion = poses.prefersReducedMotion() ? "reduce" : "full";
    if (!ALGOS[initialAlgo]) markBeat("hub-rest");

    function tick(now) {
        director.update(now);
        poses.update(performance.now());
        world.render();
        capture.tick(now, world.camera, poses.lookTarget);
        requestAnimationFrame(tick);
    }
    // The rAF clock must run before any non-snap enter. Deep-link
    // DoubleDeal awaits the physical unbox; fly / flap need director
    // + pose updates on this loop (hub clicks already have it).
    requestAnimationFrame(tick);

    menuEl.addEventListener("pointerenter", (event) => {
        const item = event.target.closest("[data-algo]");
        if (item) director.highlight(item.dataset.algo);
    }, true);
    menuEl.addEventListener("pointerleave", () => director.clearHighlight());
    menuEl.addEventListener("focusin", (event) => {
        const item = event.target.closest("[data-algo]");
        if (item) director.highlight(item.dataset.algo);
    });
    menuEl.addEventListener("focusout", (event) => {
        if (!menuEl.contains(event.relatedTarget)) director.clearHighlight();
    });

    menuEl.addEventListener("click", (event) => {
        const item = event.target.closest("[data-algo]");
        if (!item) return;
        if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
        event.preventDefault();
        event.stopPropagation();
        void startAlgo(item.dataset.algo);
    });

    sitBtn.addEventListener("click", () => poses.goTo("seated"));
    backBtn.addEventListener("click", () => void leaveAlgo());

    function enterBusy() {
        return Boolean(adapters[activeAlgo]?.busy);
    }

    function skipMotion() {
        if (performance.now() < ignoreSkipUntil) return;
        skippedStart = true;
        director.skip();
        adapters[activeAlgo]?.skipEnter?.();
        if (activeAlgo && (starting || enterBusy())) {
            // Continue from the live shot — do not snap to a named seat.
            continueTo(poses, ALGOS[activeAlgo].pose, { duration: 720 });
        } else {
            poses.skip();
        }
    }

    function shouldSkip(event) {
        if (performance.now() < ignoreSkipUntil) return false;
        if (!director.busy && !poses.busy && !enterBusy()) return false;
        if (event.target.closest("a[href], button, input, textarea, select, dialog, .playroom-dock, .playroom-menu")) {
            return false;
        }
        return true;
    }

    window.addEventListener("pointerdown", (event) => {
        if (!shouldSkip(event)) return;
        skipMotion();
    });

    window.addEventListener("keydown", (event) => {
        if (event.key === "Escape" && (poses.busy || director.busy || enterBusy())) {
            skipMotion();
            event.preventDefault();
        }
    });

    window.addEventListener("resize", () => world.resize());

    if (ALGOS[initialAlgo]) {
        if (initialAlgo === "doubledeal" && !poses.prefersReducedMotion()) {
            void startAlgo(initialAlgo);
        } else {
            void startAlgo(initialAlgo, { snap: true });
        }
    }
} catch (err) {
    console.error(err);
    document.body.classList.add("is-error");
    errorEl.hidden = false;
    errorEl.textContent = "The playroom failed to load. DoubleDeal and Scramble still work from the menu."
        + (err && err.message ? ` (${err.message})` : "");
    titleEl.classList.add("on");
    menuEl.classList.add("on");
    sitBtn.hidden = true;
    backBtn.hidden = true;
}
