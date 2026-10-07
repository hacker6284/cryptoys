import assert from "node:assert/strict";

// Runs on the real generated/scramble.mjs: build it first (tools/build.sh; CI does).
function el(tag = "div", extras = {}) {
    const node = {
        nodeName: tag.toUpperCase(),
        tagName: tag.toUpperCase(),
        id: extras.id || "",
        className: extras.className || "",
        value: extras.value ?? "",
        textContent: "",
        hidden: false,
        disabled: false,
        placeholder: "",
        title: "",
        dataset: { ...(extras.dataset || {}) },
        children: [],
        style: {},
        classList: {
            _on: new Set(),
            add(name) { this._on.add(name); },
            remove(name) { this._on.delete(name); },
            contains(name) { return this._on.has(name); },
            toggle(name, force) {
                if (force === false || this._on.has(name)) this._on.delete(name);
                else this._on.add(name);
                return this._on.has(name);
            },
        },
        listeners: {},
        matches(sel) {
            if (sel === "input, textarea") return tag === "input" || tag === "textarea";
            return false;
        },
        addEventListener(type, fn) {
            (this.listeners[type] ||= []).push(fn);
        },
        setAttribute(name, value) {
            if (name === "aria-label") this.title = value;
        },
        replaceChildren(...next) {
            this.children = next;
        },
        append(...next) {
            this.children.push(...next);
        },
        querySelector() { return null; },
        scrollIntoView() {},
    };
    return node;
}

const nodes = {
    message: el("textarea", { id: "message", value: "hello" }),
    status: el("p", { id: "status" }),
    digest: el("textarea", { id: "digest" }),
    error: el("p", { id: "error" }),
    speed: el("input", { id: "speed", value: "0" }),
    teach: el("div", { id: "teach" }),
    tape: el("div", { id: "tape" }),
    "teach-card": el("article", { id: "teach-card" }),
    "teach-pos": el("span", { id: "teach-pos" }),
    outline: el("div", { id: "outline" }),
    "io-note": el("p", { id: "io-note" }),
    "message-file-btn": el("button", { id: "message-file-btn" }),
    "message-file-input": el("input", { id: "message-file-input" }),
    "message-file": Object.assign(el("div", { id: "message-file" }), { hidden: true }),
    "message-file-name": el("span", { id: "message-file-name" }),
    "message-file-clear": el("button", { id: "message-file-clear" }),
    play: el("button", { id: "play" }),
    "skip-end": el("button", { id: "skip-end" }),
    step: el("button", { id: "step" }),
    reset: el("button", { id: "reset" }),
    "digest-btn": el("button", { id: "digest-btn" }),
    solve: el("button", { id: "solve" }),
    spec: { showModal() {}, addEventListener() {}, close() {} },
    "spec-body": el("article", { id: "spec-body" }),
    "spec-btn": el("button", { id: "spec-btn" }),
    "spec-close": el("button", { id: "spec-close" }),
};

const created = [];
const document = {
    createElement(tag) {
        const node = el(tag);
        created.push(node);
        return node;
    },
    querySelector() { return null; },
    querySelectorAll() { return []; },
};
const window = {
    addEventListener() {},
};
globalThis.document = document;
globalThis.window = window;
globalThis.HTMLTextAreaElement = function HTMLTextAreaElement() {};
HTMLTextAreaElement.prototype = { value: "" };

const segments = {
    "[data-version]": [el("button", { dataset: { version: "1" } }), el("button", { dataset: { version: "2" } })],
    "[data-encoding]": [el("button", { dataset: { encoding: "text" } }), el("button", { dataset: { encoding: "hex" } })],
};

const root = {
    dataset: {},
    querySelector(sel) {
        if (sel.startsWith("#")) return nodes[sel.slice(1)] || null;
        return null;
    },
    querySelectorAll(sel) {
        if (segments[sel]) return segments[sel];
        if (sel === "[data-puzzle]" || sel === "[data-jump]") {
            return [];
        }
        if (sel === "textarea.grow-field") return [];
        return [];
    },
};

const algs = [];
const jumps = [];
const speeds = [];
const view = {
    setAlg(alg) { algs.push(String(alg || "")); },
    async playLeaves() { return { index: 0, total: 1 }; },
    async jumpToLeaf(index) { jumps.push(index); },
    setSpeed(m) { speeds.push(m); },
    pauseTimeline() {},
    resetTimeline() {},
    settle() {},
    clearHighlights() {},
    paint() {},
    highlightLayer() {},
    highlightRuleB() {},
};

const { createScrambleSession, FILE_MAX_BYTES } = await import("./session.js");
const session = createScrambleSession({
    view,
    specUrl: "about:blank",
    root,
});

assert.ok(nodes.digest.value.startsWith("0x"), "initial Digest is live hex");
assert.deepEqual(speeds, [1], "the dock's speed reaches the view as a multiplier: 1× at start");
assert.equal(algs.length, 0, "session start does not setAlg");

nodes.message.value = "hello world";
session.recompute();
assert.ok(nodes.digest.value.startsWith("0x"), "typing keeps Digest live");
assert.equal(algs.length, 0, "Message input / recompute must not setAlg");

session.enterTeach();
assert.equal(algs.length, 1, "Step / teach binds the current Message");
assert.ok(algs[0].length > 0, "bound alg comes from the current trace");

session.enterTeach();
assert.equal(algs.length, 1, "second teach does not rebuild the same timeline");

nodes.message.value = "changed";
session.recompute();
assert.equal(algs.length, 1, "typing after teach updates Digest only");
session.enterTeach();
assert.equal(algs.length, 2, "Play / Step after a new Message calls setAlg");

function click(id) {
    for (const fn of nodes[id].listeners.click || []) fn();
}

click("skip-end");
assert.equal(algs.length, 2, "skip to end does not rebuild a current timeline");
assert.equal(nodes.teach.hidden, true, "skip finishes in the played state, not the teach walk");
assert.match(nodes.status.textContent, /Seat white up/, "skip shows the seated digest pose");
const finalLeaf = algs.at(-1).split(/\s+/).filter(Boolean).length - 1;
assert.equal(jumps.at(-1), finalLeaf, "skip seeks the final leaf");
click("skip-end");
assert.equal(jumps.at(-1), finalLeaf, "a second skip stays on the final leaf");
assert.equal(nodes.play.classList.contains("is-playing"), false, "skip leaves play idle");

let releasePlay;
view.playLeaves = () => new Promise((resolve) => {
    releasePlay = resolve;
});
session.reset();
click("play");
click("skip-end");
releasePlay({ index: 0, total: 1 });
await Promise.resolve();
assert.equal(jumps.at(-1), finalLeaf, "skip during play keeps the final leaf");
assert.match(nodes.status.textContent, /Seat white up/, "skip during play keeps the final cursor");

// Files: the worker (real hash-worker.js behind a fake Worker), the
// page fallback, Gen / Clear / cap, and controls while a file hashes.
const pick = (sel, i) => { for (const fn of segments[sel][i].listeners.click) fn(); };
const gen = (v) => pick("[data-version]", v - 1);
async function until(ok) {
    for (let i = 0; i < 400 && !ok(); i++) await new Promise((resolve) => setTimeout(resolve, 5));
}
function chooseFile(file) {
    nodes["message-file-input"].files = [file];
    nodes["message-file-input"].value = `C:\\fakepath\\${file.name}`;
    for (const fn of nodes["message-file-input"].listeners.change) fn();
}
function typed(hex) {
    nodes.message.value = hex;
    session.recompute();
    return nodes.digest.value;
}

const bin = new File([new Uint8Array([0x00, 0xff, 0x10, 0x80, 0x7f, 0x01])], "blob.bin");
const direct = await import("./generated/scramble.mjs");
function directHex(version) {
    const state = version === 2 ? direct.scramble_v2() : direct.scramble_v1();
    direct.update(state, [0x00, 0xff, 0x10, 0x80, 0x7f, 0x01]);
    const hex = direct.evaluate(state).digest.map((b) => Number(b).toString(16).padStart(2, "0"));
    return `0x${hex.join("").toUpperCase().slice(1)}`;
}
const pads = () => { session.enterTeach(); return nodes.tape.children.filter((c) => c.classList.contains("pad")).length; };
pick("[data-encoding]", 1);
gen(1);
const hexV1 = typed("00ff10807f01");
assert.equal(hexV1, directHex(1), "typed hex hashes with the generated module (Gen 1)");
gen(2);
const hexV2 = typed("00ff10807f01");
assert.equal(hexV2, directHex(2), "typed hex hashes with the generated module (Gen 2)");
const typedPads = pads();
assert.ok(typedPads < nodes.tape.children.length, "the tape does not pad the message's own nybbles");
click("skip-end");
const hexAlg = algs.at(-1);
const abV2 = typed("ab");
assert.notEqual(hexV1, hexV2);
assert.notEqual(abV2, hexV2);

globalThis.self = {};
await import("./hash-worker.js");
const runWorker = self.onmessage;
const workers = [];
let workerMode = "run";
globalThis.Worker = class {
    constructor(url, opts) {
        Object.assign(this, { url: String(url), opts, terminated: false, replied: false });
        workers.push(this);
    }
    postMessage(data) {
        setTimeout(() => {
            if ((this.terminated && workerMode !== "late") || workerMode === "hang") return;
            if (workerMode === "fail") return this.onerror(new Event("error"));
            if (workerMode === "garbage") return this.onmessage({ data: {} });
            self.postMessage = (reply) => {
                this.replied = true;
                this.onmessage({ data: structuredClone(reply) });
            };
            runWorker({ data: structuredClone(data) });
        }, workerMode === "late" ? 50 : 0);
    }
    terminate() { this.terminated = true; }
};

let browsed = 0;
nodes["message-file-input"].click = () => { browsed += 1; };
click("message-file-btn");
assert.equal(browsed, 1, "the paperclip opens the file picker");
chooseFile(bin);
assert.equal(nodes["message-file-input"].value, "", "the input resets so the same file can be picked again");
await until(() => nodes.digest.value === hexV2);
assert.equal(nodes.digest.value, hexV2, "file Digest = same bytes typed as hex (Gen 2)");
assert.equal(nodes["message-file"].hidden, false, "picking a file shows its chip");
assert.equal(nodes["message-file-name"].textContent, "blob.bin · 6 B");
assert.equal(pads(), typedPads, "the teach tape pads after the file's own nybbles");
assert.match(workers[0].url, /\/hash-worker\.js$/);
assert.equal(workers[0].opts.type, "module");
assert.ok(workers[0].replied && workers[0].terminated, "the worker hashed the file and was released");
assert.equal(nodes["message-file"].classList.contains("is-hashing"), false, "Hashing… clears");

gen(1);
await until(() => nodes.digest.value === hexV1);
assert.equal(nodes.digest.value, hexV1, "Gen switch rehashes the file (Gen 1)");
const before = workers.length;
gen(2);
gen(1);
gen(2);
await until(() => nodes.digest.value === hexV2 && workers.at(-1).replied);
assert.equal(nodes.digest.value, hexV2, "Gen switch back rehashes the file (Gen 2)");
assert.ok(workers.slice(before, -1).every((w) => w.terminated && !w.replied), "a newer hash stops the stale worker");

nodes.message.value = "ab";
session.recompute();
pick("[data-encoding]", 0);
pick("[data-encoding]", 1);
assert.equal(nodes.digest.value, hexV2, "typing / Encoding do not touch a file's Digest");
click("skip-end");
assert.equal(algs.at(-1), hexAlg, "Skip to end walks the file like the typed hex");

const edge = { name: "edge.bin", size: FILE_MAX_BYTES, arrayBuffer: async () => new Uint8Array([0xab]).buffer };
chooseFile(edge);
await until(() => nodes.digest.value === abV2);
assert.equal(nodes.digest.value, abV2, "a file at the cap is hashed");
assert.equal(nodes["message-file-name"].textContent, "edge.bin · 4 KiB");
chooseFile({ name: "big.bin", size: FILE_MAX_BYTES + 1 });
assert.equal(nodes.error.textContent, "Files can be up to 4 KiB.", "over-cap files are rejected");
assert.equal(nodes["message-file-name"].textContent, "edge.bin · 4 KiB", "reject keeps the current file");
assert.equal(nodes.digest.value, abV2);

nodes.message.value = "00ff10807f01";
click("message-file-clear");
assert.equal(nodes.digest.value, hexV2, "Clear rehashes the typed Message");
assert.equal(nodes["message-file"].hidden, true);
assert.equal(nodes.error.textContent, "");

assert.equal(typed("ab"), abV2);
nodes.message.value = "zz";
workerMode = "fail";
chooseFile(bin);
await until(() => nodes.digest.value === hexV2);
assert.equal(nodes.digest.value, hexV2, "a failed worker falls back to the page; a file ignores bad typed hex");

workerMode = "hang";
nodes.message.value = "ab";
click("message-file-clear");
chooseFile(bin);
await until(() => workers.at(-1).opts && nodes.digest.value === "");
assert.ok(nodes["message-file"].classList.contains("is-hashing"), "the chip says Hashing…");
assert.equal(nodes.digest.value, "", "Digest waits for the file");
const algsWhileHashing = algs.length;
click("play");
click("skip-end");
click("step");
assert.equal(algs.length, algsWhileHashing, "Play / Skip / Step wait while the file hashes");
const hung = workers.at(-1);
click("message-file-clear");
assert.ok(hung.terminated, "Clear stops the running worker");
assert.equal(nodes.digest.value, abV2, "Clear during a hash shows the typed Message");
workerMode = "late";
let made = workers.length;
chooseFile(bin);
await until(() => workers.length > made);
click("message-file-clear");
await until(() => workers.at(-1).replied);
assert.ok(workers.at(-1).replied, "the late worker still replied");
assert.equal(nodes.digest.value, abV2, "a result that lands after Clear is dropped");
// Reads that resolve after Clear, or out of order, must not win.
function slowFile(name, bytes) {
    let release;
    const read = new Promise((ok) => { release = () => ok(new Uint8Array(bytes).buffer); });
    return { file: { name, size: bytes.length, arrayBuffer: () => read }, release };
}
const tick = () => new Promise((resolve) => setTimeout(resolve, 20));
const lateRead = slowFile("late.bin", [0x00, 0xff, 0x10, 0x80, 0x7f, 0x01]);
chooseFile(lateRead.file);
click("message-file-clear");
lateRead.release();
await tick();
assert.equal(nodes["message-file"].hidden, true, "a read that lands after Clear shows no chip");
assert.equal(typed("00ff10807f01"), hexV2, "typing updates Digest again after Clear");
nodes.message.value = "ab";
session.recompute();
workerMode = "run";
const first = slowFile("first.bin", [0x00, 0xff, 0x10, 0x80, 0x7f, 0x01]);
const second = slowFile("second.bin", [0xab]);
chooseFile(first.file);
chooseFile(second.file);
second.release();
await until(() => nodes.digest.value === abV2 && workers.at(-1).replied);
first.release();
await tick();
assert.equal(nodes["message-file-name"].textContent, "second.bin · 1 B", "the newer pick wins");
assert.equal(nodes.digest.value, abV2, "an older read that lands last is dropped");

workerMode = "garbage";
chooseFile(bin);
await until(() => nodes.error.textContent);
assert.ok(nodes.error.textContent, "a bad worker reply shows an error");
assert.equal(nodes["message-file"].classList.contains("is-hashing"), false, "a failed hash settles");

const RealWorker = globalThis.Worker;
globalThis.Worker = class { constructor() { throw new Error("blocked"); } };
nodes.digest.value = "";
chooseFile(bin);
await until(() => nodes.digest.value === hexV2);
assert.equal(nodes.digest.value, hexV2, "a Worker constructor that throws falls back to the page");
globalThis.Worker = RealWorker;

workerMode = "hang";
made = workers.length;
chooseFile(bin);
await until(() => workers.length > made);

session.dispose();
assert.ok(workers.at(-1).terminated, "dispose stops the running worker");

delete globalThis.Worker;
for (const node of [...Object.values(nodes), ...Object.values(segments).flat()]) node.listeners = {};
const plain = createScrambleSession({ view, specUrl: "about:blank", root });
chooseFile(bin);
await until(() => nodes.digest.value === hexV2);
assert.equal(nodes.digest.value, hexV2, "without Worker the page hashes the file with the generated module");
plain.dispose();
console.log("scramble session digest/timeline tests ok");
