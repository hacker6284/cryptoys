import { adapters } from "./adapters.js";
import { createPoseController } from "./pose-controller.js";
import { resolvePoseName } from "./poses.js";
import { createToyDirector } from "./toy-director.js";
import { mountWorld } from "./world.js";

// Adapters stay stubbed this PR; imported so the hub session owns the slot.
void adapters;

const canvas = document.querySelector("#playroom");
const titleEl = document.querySelector("#title");
const menuEl = document.querySelector("#menu");
const sitBtn = document.querySelector("#sit");
const backBtn = document.querySelector("#back");
const errorEl = document.querySelector("#load-error");

function writePoseQuery(name) {
    const url = new URL(location.href);
    if (name === "landing") url.searchParams.delete("pose");
    else url.searchParams.set("pose", name);
    history.replaceState(null, "", `${url.pathname}${url.search}${url.hash}`);
}

function syncOverlays({ name, overlays, tweening }) {
    const showMenu = Boolean(overlays?.menu) && !tweening;
    titleEl.classList.toggle("on", Boolean(overlays?.title));
    menuEl.classList.toggle("on", showMenu);
    sitBtn.hidden = name !== "landing" || tweening;
    backBtn.hidden = (name !== "seated" && name !== "lean") || tweening;
    document.documentElement.dataset.pose = name;
    document.documentElement.dataset.playroomTween = tweening ? "1" : "0";
}

try {
    const world = await mountWorld(canvas);
    const director = createToyDirector(world);
    const initial = resolvePoseName(new URLSearchParams(location.search).get("pose"));
    const poses = createPoseController(world.camera, {
        onChange(state) {
            syncOverlays(state);
            if (!state.tweening) writePoseQuery(state.name);
        },
    });

    poses.snap(initial);
    document.body.classList.add("is-ready");
    document.documentElement.dataset.playroomReady = "1";

    menuEl.addEventListener("pointerenter", (event) => {
        const item = event.target.closest("[data-algo]");
        if (item) director.highlight(item.dataset.algo);
    }, true);
    menuEl.addEventListener("pointerleave", () => director.clearHighlight());

    sitBtn.addEventListener("click", () => poses.goTo("seated"));
    backBtn.addEventListener("click", () => poses.goTo("landing"));

    window.addEventListener("pointerdown", (event) => {
        if (!poses.busy) return;
        if (event.target.closest("a[href]")) return;
        poses.skip();
    });

    window.addEventListener("keydown", (event) => {
        if (event.key === "Escape" && poses.busy) {
            poses.skip();
            event.preventDefault();
        }
    });

    window.addEventListener("resize", () => world.resize());

    function tick(now) {
        poses.update(now);
        world.render();
        requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);
} catch (err) {
    console.error(err);
    document.body.classList.add("is-error");
    errorEl.hidden = false;
    errorEl.textContent = "The playroom failed to load. TwoDeck and Scramble still work from the menu."
        + (err && err.message ? ` (${err.message})` : "");
    titleEl.classList.add("on");
    menuEl.classList.add("on");
    sitBtn.hidden = true;
    backBtn.hidden = true;
}
