import { adapters } from "./adapters.js";
import { FLY_MS, HOLD_MS, LIFT_MS } from "./constants.js";
import { createPoseController } from "./pose-controller.js";
import { resolvePoseName } from "./poses.js";
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
let ignoreSkipUntil = 0;
let resizeWorld = () => {};

function writeQuery({ pose, algo }) {
    const url = new URL(location.href);
    const poseName = pose === "scramble" || pose === "doubledeal" ? "seated" : pose;
    if (!poseName || poseName === "landing") url.searchParams.delete("pose");
    else url.searchParams.set("pose", poseName);
    if (!algo) url.searchParams.delete("algo");
    else url.searchParams.set("algo", algo);
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
        const on = Boolean(activeAlgo) && !tweening && !leaving && dock.id === `${activeAlgo}-dock`;
        dock.classList.toggle("on", on);
    });
    requestAnimationFrame(() => resizeWorld());
}

function trackToy(world, name) {
    return () => world.toys[name]?.position;
}

try {
    const world = await mountWorld(canvas);
    resizeWorld = () => world.resize();
    const params = new URLSearchParams(location.search);
    if (params.get("debug") === "1") document.documentElement.dataset.playroomDebug = "1";
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
    adapters.scramble.install(world, installOpts);
    adapters.doubledeal.install(world, installOpts);
    void adapters.scramble.preload();
    void adapters.doubledeal.preload();
    const director = createToyDirector(world);

    async function startAlgo(id, { snap = false } = {}) {
        const meta = ALGOS[id];
        const adapter = adapters[id];
        if (!meta || !adapter) return;
        if (activeAlgo === id || starting || leaving) return;
        starting = true;
        activeAlgo = id;
        syncOverlays({
            name: poses.name,
            overlays: { title: true, menu: false },
            tweening: !snap && !poses.prefersReducedMotion(),
        });
        try {
            const reduced = snap || poses.prefersReducedMotion();
            ignoreSkipUntil = performance.now() + LIFT_MS;
            const fly = director.borrow(id, { snap: reduced });
            const warm = adapter.preload();
            if (reduced) {
                poses.snap(meta.pose);
            } else {
                poses.goTo(meta.pose, {
                    duration: FLY_MS,
                    via: "shelf",
                    viaT: HOLD_MS / FLY_MS,
                    track: trackToy(world, meta.toy),
                });
            }
            await Promise.all([fly, warm]);
            if (leaving) return;
            adapter.view()?.rememberSeated?.();
            await adapter.enter();
            writeQuery({ pose: "seated", algo: id });
            syncOverlays({
                name: poses.name,
                overlays: { title: true, menu: false, teach: true },
                tweening: poses.busy,
            });
        } catch (err) {
            console.error(err);
            adapter.leave();
            await director.home({ snap: true });
            activeAlgo = null;
            errorEl.hidden = false;
            errorEl.textContent = err && err.message
                ? err.message
                : `${meta.title} could not start in the playroom.`;
            poses.snap("landing");
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
        const meta = ALGOS[activeAlgo];
        adapters[activeAlgo]?.leave();
        const reduced = poses.prefersReducedMotion();
        ignoreSkipUntil = performance.now() + LIFT_MS;
        const home = director.home({ snap: reduced });
        if (reduced) poses.snap("landing");
        else {
            poses.goTo("landing", {
                duration: FLY_MS - LIFT_MS,
                via: "shelf",
                viaT: 0.42,
                delay: LIFT_MS,
                track: trackToy(world, meta?.toy || "cube"),
            });
        }
        await home;
        activeAlgo = null;
        leaving = false;
        writeQuery({ pose: "landing", algo: null });
        syncOverlays({
            name: poses.name,
            overlays: { title: true, menu: true },
            tweening: poses.busy,
        });
    }

    if (ALGOS[initialAlgo]) {
        poses.snap(ALGOS[initialAlgo].pose);
        await startAlgo(initialAlgo, { snap: true });
    } else {
        poses.snap(initialPose);
    }

    document.body.classList.add("is-ready");
    document.documentElement.dataset.playroomReady = "1";
    document.documentElement.dataset.motion = poses.prefersReducedMotion() ? "reduce" : "full";

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

    function shouldSkip(event) {
        if (performance.now() < ignoreSkipUntil) return false;
        if (!director.busy && !poses.busy) return false;
        if (event.target.closest("a[href], button, input, textarea, select, dialog, .playroom-dock, .playroom-menu")) {
            return false;
        }
        return true;
    }

    window.addEventListener("pointerdown", (event) => {
        if (!shouldSkip(event)) return;
        director.skip();
        poses.skip();
    });

    window.addEventListener("keydown", (event) => {
        if (event.key === "Escape" && (poses.busy || director.busy)) {
            director.skip();
            poses.skip();
            event.preventDefault();
        }
    });

    window.addEventListener("resize", () => world.resize());

    function tick(now) {
        director.update(now);
        poses.update(performance.now());
        world.render();
        requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);
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
