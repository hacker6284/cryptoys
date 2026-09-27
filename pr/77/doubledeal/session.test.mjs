import assert from "node:assert/strict";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const generated = join(here, "generated/doubledeal.mjs");

for (const rel of ["../playroom/adapters.js", "./index.html", "../scramble/index.html"]) {
    const text = readFileSync(new URL(rel, import.meta.url), "utf8");
    assert.equal(text.includes("Step through"), false, `${rel} still says Step through`);
    assert.equal(text.includes("step-through"), false, `${rel} still has a step-through control`);
    assert.match(text, /Skip to end/, `${rel} should label skip to end`);
}
for (const rel of ["../scramble/session.js", "./session.js"]) {
    const text = readFileSync(new URL(rel, import.meta.url), "utf8");
    assert.equal(text.includes("Step through"), false, `${rel} still says Step through`);
    assert.equal(text.includes("step-through"), false, `${rel} still wires step through`);
}

if (!existsSync(generated)) {
    mkdirSync(dirname(generated), { recursive: true });
    writeFileSync(generated, `
function flip(blocks) { return blocks.map((deck) => deck.slice().reverse()); }
export function ecb_encrypt(blocks) { return flip(blocks); }
export function ecb_decrypt(blocks) { return flip(blocks); }
export function ctr_encrypt(blocks) { return flip(blocks); }
export function ctr_decrypt(blocks) { return flip(blocks); }
function trace(message, key) {
    return [{ kind: "compose", label: "Final Compose", message, key, row: -1, col: -1, amount: 0, total: 0, flag: 0, card: 0 }];
}
export function trace_ecb(blocks, key) { return trace(blocks[0], key); }
export function trace_ctr(blocks, key) { return trace(blocks[0], key); }
export function trace_decrypt(block, key) { return trace(block, key); }
export function trace_ctr_decrypt(blocks, key) { return trace(blocks[0], key); }
`, "utf8");
}

function el(tag, extras = {}) {
    return {
        nodeName: tag.toUpperCase(),
        tagName: tag.toUpperCase(),
        id: extras.id || "",
        value: extras.value ?? "",
        textContent: "",
        hidden: false,
        disabled: false,
        dataset: {},
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
        removeEventListener() {},
        setAttribute() {},
    };
}

const nodes = {
    message: el("textarea", { id: "message", value: "hello" }),
    key: el("textarea", { id: "key", value: "cryptoy" }),
    nonce: el("textarea", { id: "nonce", value: "nonce" }),
    digest: el("textarea", { id: "digest" }),
    error: el("p", { id: "error" }),
    status: el("p", { id: "status" }),
    speed: el("input", { id: "speed", value: "1.8" }),
    teach: el("div", { id: "teach" }),
    play: el("button", { id: "play" }),
    "skip-end": el("button", { id: "skip-end" }),
    step: el("button", { id: "step" }),
    reset: el("button", { id: "reset" }),
};

const root = {
    querySelector(sel) {
        return sel.startsWith("#") ? nodes[sel.slice(1)] || null : null;
    },
    querySelectorAll() {
        return [];
    },
};

globalThis.document = {
    createElement: (tag) => el(tag),
    querySelector: () => null,
    querySelectorAll: () => [],
};
globalThis.window = { addEventListener() {} };
globalThis.HTMLTextAreaElement = function HTMLTextAreaElement() {};

const shown = [];
let plays = 0;
let instants = 0;
const view = {
    showDecks(message, key) {
        shown.push({ message: message.slice(), key: key.slice() });
    },
    snapshot() { return { ok: true }; },
    restore() {},
    applyInstant() { instants += 1; },
    play() { plays += 1; return Promise.resolve(); },
    clearHighlights() {},
    highlightRow() {},
    highlightCol() {},
    highlightSeat() {},
    highlightCard() {},
    rowRanks() { return []; },
    colRanks() { return []; },
    frameTable() {},
    frameTeach() {},
};

const { createDoubleDealSession } = await import("./session.js");
const { ecb_encrypt } = await import("./generated/doubledeal.mjs");
const { decksToHex, textToDecks, textToKey } = await import("./cards.js");

const session = createDoubleDealSession({
    view,
    specUrl: "about:blank",
    root,
    liveDigest: true,
});

function click(id) {
    for (const fn of nodes[id].listeners.click || []) fn();
}

const message = textToDecks("hello");
const key = textToKey("cryptoy");
const result = ecb_encrypt(message, key);
const caption = "Ciphertext on the left. Key on the right.";

function expectEnd(why) {
    const last = shown.at(-1);
    assert.deepEqual(last.message, result[0], why);
    assert.deepEqual(last.key, key, why);
    assert.equal(nodes.digest.value, decksToHex(result), why);
    assert.equal(nodes.status.textContent, caption, why);
    assert.equal(nodes.error.textContent, "", why);
    assert.equal(nodes.teach.hidden, true, why);
    assert.equal(plays, 0, why);
    assert.equal(instants, 0, why);
    assert.equal(nodes.play.classList.contains("is-playing"), false, why);
}

click("skip-end");
expectEnd("skip from the start matches a finished encrypt");

click("step");
assert.equal(nodes.teach.hidden, false, "step still opens the walk");
click("skip-end");
expectEnd("skip from the walk matches a finished encrypt");

session.dispose();
console.log("doubledeal skip-to-end tests ok");
