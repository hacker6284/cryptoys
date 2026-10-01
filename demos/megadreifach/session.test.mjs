// MegaDreifach session on a fake DOM, with the real generated module
// behind a stub hasher (worker.js answer(), run inline).
import assert from "node:assert/strict";
import { readFileSync, existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { test } from "node:test";

const here = dirname(fileURLToPath(import.meta.url));
const ready = existsSync(join(here, "generated/_megadreifach_impl.mjs"));

function el(tag, id = "", dataset = {}) {
    const node = {
        tagName: tag.toUpperCase(),
        id,
        value: "",
        textContent: "",
        hidden: false,
        disabled: false,
        placeholder: "",
        title: "",
        type: "",
        className: "",
        dataset: { ...dataset },
        children: [],
        attrs: {},
        listeners: {},
        classList: {
            _on: new Set(),
            add(n) { this._on.add(n); },
            remove(n) { this._on.delete(n); },
            contains(n) { return this._on.has(n); },
            toggle(n, force) {
                const on = force === undefined ? !this._on.has(n) : force;
                if (on) this._on.add(n); else this._on.delete(n);
                return on;
            },
        },
        addEventListener(type, fn, opts) {
            (this.listeners[type] ||= []).push(fn);
            opts?.signal?.addEventListener?.("abort", () => {
                this.listeners[type] = (this.listeners[type] || []).filter((f) => f !== fn);
            });
        },
        removeEventListener(type, fn) {
            this.listeners[type] = (this.listeners[type] || []).filter((f) => f !== fn);
        },
        fire(type) { for (const fn of this.listeners[type] || []) fn({ target: this }); },
        setAttribute(k, v) { this.attrs[k] = v; },
        replaceChildren(...next) { this.children = next; },
        append(...next) { this.children.push(...next); },
        querySelector: () => null,
        querySelectorAll: () => [],
        close() {},
        showModal() {},
    };
    return node;
}

function makeRoot() {
    const ids = ["message", "digest", "status", "error", "anim-note", "io-note", "teach", "teach-card",
        "teach-pos", "play", "step", "skip-end", "reset", "speed", "kat", "kat-menu", "spec", "spec-body",
        "spec-btn", "spec-close", "digest-btn", "sound", "ff-counter"];
    const byId = Object.fromEntries(ids.map((id) => [id, el(id === "message" || id === "digest" ? "textarea" : "div", id)]));
    byId.speed.value = "12";
    byId["anim-note"].hidden = true;
    byId["ff-counter"].hidden = true;
    const enc = ["text", "hex"].map((e) => el("button", "", { encoding: e }));
    const jumps = ["back", "fwd", "stage-back", "stage-fwd", "round-back", "round-fwd"].map((j) => el("button", "", { jump: j }));
    const root = {
        dataset: {},
        byId,
        querySelector: (sel) => (sel.startsWith("#") ? byId[sel.slice(1)] ?? null : null),
        querySelectorAll: (sel) => (sel === "[data-encoding]" ? enc : sel === "[data-jump]" ? jumps : []),
    };
    return root;
}

function stubView(root) {
    const calls = [];
    return {
        calls,
        loadShow: async (show) => { calls.push(["load", show.beats.length]); },
        seek: async (i) => { calls.push(["seek", i]); },
        playBeat: async (beat, i, hooks) => {
            calls.push(["beat", i]);
            if (beat.kind === "ff") {
                // A real view ticks the counter through every block it shows.
                for (let b = beat.from; b <= beat.to; b++) {
                    hooks.progress(b);
                    calls.push(["ff", b, root.byId["ff-counter"].textContent]);
                }
            }
        },
        clearShow: async () => { calls.push(["clear"]); },
        setTempo: (t) => { calls.push(["tempo", t]); },
    };
}

async function setup() {
    globalThis.window ??= { addEventListener() {}, removeEventListener() {} };
    globalThis.document ??= { createElement: (tag) => el(tag) };
    const katsFile = readFileSync(join(here, "generated/kats.json"), "utf8");
    globalThis.fetch = async (url) => ({
        ok: String(url).endsWith("kats.json"),
        json: async () => JSON.parse(katsFile),
        text: async () => "",
    });
    const { answer } = await import("./worker.js");
    const { createMegaDreifachSession } = await import("./session.js");
    const hasher = {
        digest: async (bytes) => answer({ op: "digest", bytes }),
        show: async (bytes) => answer({ op: "show", bytes }),
    };
    const chimes = [];
    const sound = { play: (n) => chimes.push(n), bindToggle: (b) => { b.bound = true; return () => { b.bound = false; }; } };
    const root = makeRoot();
    const view = stubView(root);
    const session = createMegaDreifachSession({ view, root, specUrl: "SPEC.md", hasher, sound, katsUrl: "kats.json" });
    return { root, view, session, chimes, answer };
}

const settle = () => new Promise((r) => setTimeout(r, 20));
const hex = (bytes) => Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");

test("empty state: placeholder copy, no digest, transport off", { skip: !ready }, async () => {
    const { root, session } = await setup();
    await settle();
    const $ = root.byId;
    assert.equal($.status.textContent, "Type a message, or pick a known answer.");
    assert.equal($.digest.value, "");
    assert.equal($.message.value, "", "no prefilled message");
    assert.equal($.play.disabled, true);
    assert.equal($["anim-note"].hidden, true);
    assert.equal($.sound.bound, true, "mute toggle bound");
    session.dispose();
    assert.equal($.sound.bound, false);
});

test("typing hashes live with the generated Hash", { skip: !ready }, async () => {
    const { root, session, answer } = await setup();
    const $ = root.byId;
    $.message.value = "hi";
    $.message.fire("input");
    await new Promise((r) => setTimeout(r, 220));
    assert.equal($.digest.value, hex(answer({ op: "digest", bytes: [0x68, 0x69] }).digest));
    assert.match($.status.textContent, /^2 bytes · 1 block · /);
    assert.equal($.play.disabled, false);
    session.dispose();
});

test("KAT picker: every vector's digest matches, and a pass chimes", { skip: !ready }, async () => {
    const { root, session, chimes } = await setup();
    const $ = root.byId;
    const names = JSON.parse(readFileSync(join(here, "generated/kats.json"), "utf8")).vectors.map((v) => v.name);
    for (const name of names) {
        await session.pickKat(name);
        await settle();
        assert.match($.status.textContent, new RegExp(`“${name}”.*digest matches the KAT file ✓`), name);
    }
    assert.equal(chimes.filter((c) => c === "chime").length, names.length);
    session.dispose();
});

test("longer than one block: block 1 turn for turn, then a marked fast-forward", { skip: !ready }, async () => {
    const { root, view, session, chimes } = await setup();
    const $ = root.byId;
    await session.pickKat("multi_56");
    await settle();
    assert.equal($["anim-note"].hidden, false);
    assert.match($["anim-note"].textContent, /^3 blocks\. The show plays block 1 turn for turn.*fast-forwards blocks 2–3/);
    assert.doesNotMatch($["anim-note"].textContent, /47|digest only/);
    assert.equal($.play.disabled, false);
    assert.equal($.step.disabled, false);
    assert.match($.status.textContent, /“multi_56”, 3 blocks: digest matches the KAT file ✓/);
    chimes.length = 0;
    await session.play();
    const { beats } = session.state();
    const ff = view.calls.filter((c) => c[0] === "ff");
    assert.deepEqual(ff.map((c) => c[1]), [2, 3], "the counter ticks through blocks 2 and 3");
    assert.match(ff[0][2], /^Fast-forward: blocks 2–3 · block 2 of 3$/);
    assert.equal($["ff-counter"].hidden, false);
    assert.match($["ff-counter"].textContent, /^Fast-forward: blocks 2–3 · done, 3 of 3$/);
    assert.equal(session.state().cursor, beats - 1);
    assert.match($.status.textContent, new RegExp(`^Done\\. A holds the digest ${$.digest.value}\\.$`));
    assert.deepEqual(chimes, ["chime"]);
    // Seeking back into block 1 hides the counter; the end shows it done.
    await session.seek(10);
    assert.equal($["ff-counter"].hidden, true);
    await session.skipToEnd();
    assert.match($["ff-counter"].textContent, /done, 3 of 3$/);
    session.dispose();
});

test("KAT menu: one-block vectors play fully, longer ones are marked fast-forward", { skip: !ready }, async () => {
    const { root, session } = await setup();
    await session.pickKat("empty");
    const labels = root.byId["kat-menu"].children.map((b) => b.textContent);
    assert.equal(labels.length, 8);
    const ff = labels.filter((t) => t.endsWith("(fast-forward after block 1)"));
    assert.equal(ff.length, 5, labels.join(" | "));
    assert.ok(labels.every((t) => !/digest only/.test(t)));
    session.dispose();
});

test("controls: skip, reset, play to the end (chime), step opens teach", { skip: !ready }, async () => {
    const { root, view, session, chimes } = await setup();
    const $ = root.byId;
    await session.pickKat("short_abc");
    await settle();
    chimes.length = 0;
    await session.skipToEnd();
    const beats = session.state().beats;
    assert.ok(beats > 100, "one block is a long show");
    assert.deepEqual(view.calls.filter((c) => c[0] === "seek").at(-1), ["seek", beats - 1]);
    assert.match($.status.textContent, /^Done\. A holds the digest [0-9a-f]+\.$/);
    await session.reset();
    assert.equal(session.state().cursor, -1);
    assert.equal($.reset.disabled, false);
    await session.play();
    assert.equal(session.state().cursor, beats - 1);
    assert.equal(view.calls.filter((c) => c[0] === "beat").length, beats);
    assert.deepEqual(chimes, ["chime"], "chime on reaching the digest");
    await session.reset();
    await session.step(1);
    assert.equal(session.state().teaching, true);
    assert.equal($.teach.hidden, false);
    assert.equal(session.state().cursor, 0);
    assert.match($["teach-pos"].textContent, new RegExp(`^1 / ${beats}$`));
    session.dispose();
});
