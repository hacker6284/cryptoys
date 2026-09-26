import assert from "node:assert/strict";
import { mkdirSync, writeFileSync, existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const SOLVED = "WWWWWWWWWRRRRRRRRRGGGGGGGGGYYYYYYYYYOOOOOOOOOBBBBBBBBB";
const here = dirname(fileURLToPath(import.meta.url));
const generated = join(here, "generated/scramble.mjs");
const impl = join(here, "generated/_scramble_impl.mjs");

if (!existsSync(impl)) {
    mkdirSync(dirname(generated), { recursive: true });
    writeFileSync(generated, `
export function solved_facelets() {
    return ${JSON.stringify(SOLVED)};
}
export function scramble_v1() { return { v: 1, bytes: [] }; }
export function scramble_v2() { return { v: 2, bytes: [] }; }
export function update(state, bytes) { state.bytes = bytes; }
export function evaluate(state) {
    const digest = [0x00, 0xab, 0xcd, state.bytes?.length || 0];
    const facelets = ${JSON.stringify(SOLVED)};
    const move = (state.bytes?.length || 0) % 2 === 0 ? "U" : "R";
    return {
        digest,
        trace: [
            { kind: "move", move, nybble: "0", block: 0, index: 0, facelets },
            { kind: "closer", move: "F2", facelets },
            { kind: "canonicalize", facelets },
        ],
    };
}
`, "utf8");
}

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
    speed: el("input", { id: "speed", value: "1.4" }),
    teach: el("div", { id: "teach" }),
    tape: el("div", { id: "tape" }),
    "teach-card": el("article", { id: "teach-card" }),
    "teach-pos": el("span", { id: "teach-pos" }),
    outline: el("div", { id: "outline" }),
    "io-note": el("p", { id: "io-note" }),
    "message-file-btn": el("button", { id: "message-file-btn" }),
    "message-file-input": el("input", { id: "message-file-input" }),
    "message-file": el("div", { id: "message-file" }),
    "message-file-name": el("span", { id: "message-file-name" }),
    "message-file-clear": el("button", { id: "message-file-clear" }),
    "message-file-progress": el("div", { id: "message-file-progress" }),
    "message-file-progress-bar": el("div", { id: "message-file-progress-bar" }),
    play: el("button", { id: "play" }),
    "step-through": el("button", { id: "step-through" }),
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

const root = {
    dataset: {},
    querySelector(sel) {
        if (sel.startsWith("#")) return nodes[sel.slice(1)] || null;
        return null;
    },
    querySelectorAll(sel) {
        if (sel === "[data-version]" || sel === "[data-encoding]" || sel === "[data-puzzle]" || sel === "[data-jump]") {
            return [];
        }
        if (sel === "textarea.grow-field") return [];
        return [];
    },
};

const algs = [];
const view = {
    setAlg(alg) { algs.push(String(alg || "")); },
    async playLeaves() { return { index: 0, total: 1 }; },
    async jumpToLeaf() {},
    setTempo() {},
    pauseTimeline() {},
    resetTimeline() {},
    settle() {},
    clearHighlights() {},
    paint() {},
    highlightLayer() {},
    highlightRuleB() {},
};

const { createIncrementalHasher, createSilentHasher } = await import("../shared/file-hash.js");
const { DEMO_FILE_MAX_BYTES, DEMO_FILE_TEACH_MAX_BYTES } = await import("../shared/file-hash.js");

async function hashInline({ file, version, onProgress }) {
    const bytes = new Uint8Array(await file.arrayBuffer());
    onProgress?.({ processed: Math.min(1, bytes.length), total: bytes.length || 1 });
    if (existsSync(impl)) {
        const scrambleImpl = await import("./generated/_scramble_impl.mjs");
        const rt = await import("./generated/_sudo_rt.mjs");
        const hasher = createSilentHasher({ impl: scrambleImpl, rt });
        hasher.start(version);
        hasher.push(bytes);
        onProgress?.({ processed: bytes.length, total: bytes.length });
        assert.equal(nodes["message-file-progress"].hidden, false, "progress is visible while hashing");
        return hasher.finish();
    }
    const { scramble_v1, scramble_v2, update, evaluate } = await import("./generated/scramble.mjs");
    const hasher = createIncrementalHasher({ scramble_v1, scramble_v2, update, evaluate });
    hasher.start(version);
    hasher.push(bytes);
    onProgress?.({ processed: bytes.length, total: bytes.length });
    assert.equal(nodes["message-file-progress"].hidden, false, "progress is visible while hashing");
    return hasher.finish();
}

const { createScrambleSession } = await import("./session.js");
const session = createScrambleSession({
    view,
    specUrl: "about:blank",
    root,
    hashFile: hashInline,
});

assert.ok(nodes.digest.value.startsWith("0x"), "initial Digest is live hex");
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

const algsAfterType = algs.length;
const modest = new File([new Uint8Array([104, 101, 108, 108, 111])], "hello.bin");
await session.applyFile(modest);
assert.ok(nodes.digest.value.startsWith("0x"), "file Digest fills when the hasher finishes");
assert.match(nodes["message-file-name"].textContent, /hello\.bin/);
assert.match(nodes["message-file-name"].textContent, /5 B/);
assert.equal(nodes.message.hidden, false, "Message textarea stays on the paperclip row");
assert.equal(nodes["message-file-progress"].hidden, true, "progress clears when Digest lands");
assert.equal(algs.length, algsAfterType, "setAlg is not called during file hash progress");

session.enterTeach();
assert.equal(algs.length, algsAfterType + 1, "Play / Step after a modest file binds the timeline");

const tooBig = { name: "huge.bin", size: DEMO_FILE_MAX_BYTES + 1 };
assert.equal(await session.applyFile(tooBig), false, "oversized files are rejected");
assert.match(nodes["io-note"].textContent, /10 MB/);
assert.match(nodes["message-file-name"].textContent, /hello\.bin/, "reject keeps the current file");
assert.equal(algs.length, algsAfterType + 1, "oversized reject does not setAlg");

session.clearFile();
assert.equal(nodes.message.hidden, false, "clear restores the typed Message field");
assert.ok(nodes.digest.value.startsWith("0x"), "clear rehashes typed Message");
assert.equal(algs.length, algsAfterType + 1, "clearing a file updates Digest only");

const jpeg = new Uint8Array(DEMO_FILE_TEACH_MAX_BYTES + 64);
jpeg[0] = 0xff;
jpeg[1] = 0xd8;
jpeg[2] = 0xff;
const image = new File([jpeg], "shot.jpg", { type: "image/jpeg" });
await session.applyFile(image);
assert.ok(nodes.digest.value.startsWith("0x"), "JPEG pick writes Digest without a second click");
assert.match(nodes["message-file-name"].textContent, /shot\.jpg/);
assert.equal(nodes.message.hidden, false, "filename is not wedged into the Message line");
assert.equal(nodes["message-file-progress"].hidden, true, "progress clears after the JPEG digest");
assert.match(nodes["io-note"].textContent, /Play \/ Step stay off/);
const algsAfterLarge = algs.length;
session.enterTeach();
assert.equal(algs.length, algsAfterLarge, "large file must not build a leave timeline");

session.dispose();
console.log("scramble session digest/timeline tests ok");
