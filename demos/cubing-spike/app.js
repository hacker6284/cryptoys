import { CUBE } from "../playroom/constants.js";
import { createPoseController } from "../playroom/pose-controller.js";
import { mountWorld } from "../playroom/world.js";
import { PUZZLES, PUZZLE_IDS, createTwistyRig } from "./twisty-rig.js";

const canvas = document.querySelector("#playroom");
const titleEl = document.querySelector("#title");
const statusEl = document.querySelector("#spike-status");
const notesEl = document.querySelector("#spike-notes");
const errorEl = document.querySelector("#load-error");
const puzzleButtons = [...document.querySelectorAll("[data-puzzle]")];
const playBtn = document.querySelector("#play");
const pauseBtn = document.querySelector("#pause");
const stepBtn = document.querySelector("#step");
const resetBtn = document.querySelector("#reset");
const liftBtn = document.querySelector("#lift");
const seatBtn = document.querySelector("#seat");
const algInput = document.querySelector("#alg");

const params = new URLSearchParams(location.search);
const initialPuzzle = PUZZLE_IDS.includes(params.get("puzzle")) ? params.get("puzzle") : "3x3x3";

let world = null;
let poses = null;
let rig = null;
let seated = true;
let lifted = false;
let playing = false;

function writeQuery(puzzle) {
    const url = new URL(location.href);
    if (!puzzle || puzzle === "3x3x3") url.searchParams.delete("puzzle");
    else url.searchParams.set("puzzle", puzzle);
    history.replaceState(null, "", `${url.pathname}${url.search}`);
}

function setStatus(text) {
    if (statusEl) statusEl.textContent = text;
}

function markPuzzle(id) {
    for (const button of puzzleButtons) {
        button.classList.toggle("on", button.dataset.puzzle === id);
    }
}

function markTransport() {
    playBtn?.classList.toggle("on", playing);
    liftBtn?.classList.toggle("on", lifted);
    seatBtn?.classList.toggle("on", !seated);
    if (seatBtn) seatBtn.textContent = seated ? "Shelf" : "Table";
    if (liftBtn) liftBtn.textContent = lifted ? "Drop" : "Lift";
}

function applySeat() {
    if (!world || !rig) return;
    const pose = seated ? world.getTablePose("cube") : world.getShelfPose("cube");
    world.applyPose(rig.group, pose);
    world.setSlotEmpty("cube", seated);
    markTransport();
}

function renderLookNotes(current) {
    if (!notesEl || !current) return;
    const types = current.look.types.map(([type, n]) => `${type}×${n}`).join(", ") || "none";
    const same = current.skew.instanceofOurObject3D ? "yes" : "NO — two three.js copies";
    notesEl.innerHTML = `
      <p><strong>Embed:</strong> ${current.fallback
        ? `adopt failed (${current.fallbackError}). TwistyPlayer canvas is the fallback — room lights still run.`
        : `<code>experimentalCurrentThreeJSPuzzleObject</code> → playroom <code>scene</code>. Twisty host is a 80×56 off-to-the-corner canvas.`}</p>
      <p><strong>three.js:</strong> playroom r${current.skew.ourRevision}; <code>instanceof Object3D</code> ${same} (<code>${current.skew.constructorName}</code>). Native bbox max ${current.framed.nativeMax.toFixed(3)}, fitted ${Number(current.framed.fittedMax || 0).toFixed(3)}.</p>
      <p><strong>Default look:</strong> ${current.look.meshCount} meshes; ${types}. Standard/physical materials: ${current.look.standardLike}. Twisty stickers are brighter and less “plastic” than our MeshStandard cubies — see NOTES.md.</p>
      <p><strong>Hand-rolled remaining:</strong> seat/fly, local lift, room camera framing, chrome. Not cubies, not facelet animation, not megaminx/pyraminx meshes.</p>
    `;
}

async function refreshStatus(extra = "") {
    if (!rig) return;
    const info = await rig.status();
    const bits = [
        rig.puzzleId,
        seated ? "table" : "shelf",
        lifted ? "lifted" : "seated",
        playing ? "playing" : "paused",
        info.total ? `leaf ${info.index + 1}/${info.total}` : "no leaves",
    ];
    if (extra) bits.push(extra);
    setStatus(bits.join(" · "));
}

async function mountPuzzle(puzzleId) {
    const prev = rig;
    playing = false;
    setStatus(`Loading ${PUZZLES[puzzleId]?.label || puzzleId}…`);
    const next = await createTwistyRig({
        puzzle: puzzleId,
        edge: CUBE,
        alg: algInput?.value.trim() || PUZZLES[puzzleId].alg,
        onStage: (stage) => setStatus(`Loading ${PUZZLES[puzzleId]?.label || puzzleId} · ${stage}`),
        onRenderScheduled: () => {
            // Playroom already has a rAF loop; callback is the official hook
            // if we ever render on-demand.
        },
    });
    world.replaceToy("cube", next.group);
    if (prev) prev.dispose();
    rig = next;
    if (algInput) algInput.value = next.alg;
    rig.setLifted(lifted);
    applySeat();
    markPuzzle(puzzleId);
    markTransport();
    writeQuery(puzzleId);
    renderLookNotes(next);
    await refreshStatus(next.fallback ? "Twisty canvas fallback" : "adopted");
}

try {
    world = await mountWorld(canvas);
    poses = createPoseController(world.camera);
    poses.snap("scramble");
    titleEl.textContent = "cubing.js spike";
    titleEl.classList.add("on");
    document.title = "cubing.js spike";

    if (algInput) algInput.value = PUZZLES[initialPuzzle].alg;

    document.body.classList.add("is-ready");
    document.documentElement.dataset.playroomReady = "1";
    document.documentElement.dataset.algo = "cubing-spike";
    window.addEventListener("resize", () => world.resize());
    function tick(now) {
        poses.update(now);
        world.render();
        requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);

    for (const button of puzzleButtons) {
        button.addEventListener("click", () => {
            const id = button.dataset.puzzle;
            if (!id || id === rig?.puzzleId) return;
            if (algInput) algInput.value = PUZZLES[id].alg;
            void mountPuzzle(id).catch((err) => {
                console.error(err);
                setStatus(err?.message || "Puzzle swap failed");
            });
        });
    }

    playBtn?.addEventListener("click", () => {
        if (!rig) return;
        playing = true;
        rig.play();
        markTransport();
        void refreshStatus();
    });
    pauseBtn?.addEventListener("click", () => {
        if (!rig) return;
        playing = false;
        rig.pause();
        markTransport();
        void refreshStatus();
    });
    stepBtn?.addEventListener("click", async () => {
        if (!rig) return;
        playing = false;
        const stepped = await rig.step();
        markTransport();
        await refreshStatus(stepped.total ? `stepped to leaf ${stepped.index + 1}` : "empty alg");
    });
    resetBtn?.addEventListener("click", () => {
        if (!rig) return;
        playing = false;
        rig.reset();
        markTransport();
        void refreshStatus("reset");
    });
    liftBtn?.addEventListener("click", () => {
        lifted = !lifted;
        rig?.setLifted(lifted);
        markTransport();
        void refreshStatus();
    });
    seatBtn?.addEventListener("click", () => {
        seated = !seated;
        applySeat();
        void refreshStatus();
    });
    algInput?.addEventListener("change", () => {
        if (!rig) return;
        const next = algInput.value.trim() || PUZZLES[rig.puzzleId].alg;
        algInput.value = next;
        rig.setAlg(next);
        playing = false;
        rig.reset();
        markTransport();
        void refreshStatus("alg set");
    });

    await mountPuzzle(initialPuzzle);

} catch (err) {
    console.error(err);
    document.body.classList.add("is-error");
    errorEl.hidden = false;
    errorEl.textContent = "cubing.js spike failed to load."
        + (err && err.message ? ` (${err.message})` : "");
    titleEl.classList.add("on");
}
