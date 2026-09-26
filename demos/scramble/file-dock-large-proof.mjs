/**
 * In-session proof that the playroom dock path writes Digest for a
 * ~1.54 MiB JPEG-shaped file. Same factory as adapters.js: no hashFile
 * seam, then session.applyFile + #digest.value.
 */
import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
if (!existsSync(join(here, "generated/_scramble_impl.mjs"))) {
    throw new Error("Need generated Scramble to prove the dock file hash.");
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
            return sel === "input, textarea" && (tag === "input" || tag === "textarea");
        },
        addEventListener(type, fn) {
            (this.listeners[type] ||= []).push(fn);
        },
        setAttribute(name, value) {
            this.attrs = this.attrs || {};
            this.attrs[name] = value;
        },
        removeAttribute(name) {
            if (this.attrs) delete this.attrs[name];
        },
        replaceChildren(...next) { this.children = next; },
        append(...next) { this.children.push(...next); },
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

globalThis.document = {
    createElement(tag) { return el(tag); },
    querySelector() { return null; },
    querySelectorAll() { return []; },
};
globalThis.window = { addEventListener() {} };
globalThis.HTMLTextAreaElement = function HTMLTextAreaElement() {};
HTMLTextAreaElement.prototype = { value: "" };

const root = {
    dataset: {},
    querySelector(sel) {
        if (sel.startsWith("#")) return nodes[sel.slice(1)] || null;
        return null;
    },
    querySelectorAll() { return []; },
};

const view = {
    setAlg() {},
    async playLeaves() { return { index: 0, total: 1 }; },
    async jumpToLeaf() {},
    setTempo() {},
    pauseTimeline() {},
    resetTimeline() {},
    settle() {},
    clearHighlights() {},
    paint() {},
};

const { createScrambleSession } = await import("./session.js");
const session = createScrambleSession({
    view,
    specUrl: "about:blank",
    root,
});

const bytes = new Uint8Array(1610613);
bytes[0] = 0xff;
bytes[1] = 0xd8;
bytes[2] = 0xff;
bytes[3] = 0xe0;
const file = new File([bytes], "scramble-large-fronalpstock-3840.jpg", { type: "image/jpeg" });

const started = Date.now();
const ok = await session.applyFile(file);
const ms = Date.now() - started;
const digest = nodes.digest.value;
session.recompute();

assert.equal(ok, true, "applyFile accepts the JPEG");
assert.ok(digest.startsWith("0x"), `dock Digest must be hex, got ${JSON.stringify(digest)}`);
assert.ok(digest.length > 4, "dock Digest must be nonempty");
assert.equal(nodes.digest.value, digest, "recompute must not clear the file Digest");
assert.equal(nodes["message-file-progress"].hidden, true, "progress clears after Digest");
assert.match(nodes["message-file-name"].textContent, /scramble-large-fronalpstock-3840\.jpg/);
assert.match(nodes["message-file-name"].textContent, /1\.5 MB/);
assert.ok(ms < 60000, `dock hash took ${ms}ms`);

session.dispose();
console.log(JSON.stringify({
    pass: true,
    path: "createScrambleSession.applyFile (no hashFileFn)",
    digest,
    bytes: bytes.length,
    ms,
}, null, 2));
