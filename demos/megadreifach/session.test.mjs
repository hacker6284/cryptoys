// MegaDreifach session on a fake DOM, with the real generated module
// behind a stub hasher (worker.js answer(), run inline).
import assert from "node:assert/strict";
import { readFileSync, existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { test } from "node:test";

const here = dirname(fileURLToPath(import.meta.url));
const ready = existsSync(join(here, "generated/_megadreifach_impl.mjs"));
if (!ready && process.env.CI) throw new Error("generated module missing: run tools/build.sh (CI never skips these tests)");

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
        "spec-btn", "spec-close", "digest-btn"];
    const byId = Object.fromEntries(ids.map((id) => [id, el(id === "message" || id === "digest" ? "textarea" : "div", id)]));
    byId.speed.value = "12";
    byId["anim-note"].hidden = true;
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

function stubView() {
    const calls = [];
    return {
        calls,
        loadShow: async (show) => { calls.push(["load", show.beats.length]); },
        seek: async (i) => { calls.push(["seek", i]); },
        playBeat: async (beat, i) => { calls.push(["beat", i, beat.kind]); },
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
    const worker = await import("./worker.js");
    const { createMegaDreifachSession } = await import("./session.js");
    const hasher = {
        digest: async (bytes) => worker.answer({ op: "digest", bytes }),
        show: async (bytes) => worker.answer({ op: "show", bytes }),
    };
    const root = makeRoot();
    const view = stubView();
    const session = createMegaDreifachSession({ view, root, specUrl: "SPEC.md", hasher, katsUrl: "kats.json" });
    return { root, view, session, answer: worker.answer, traced: worker.hasTrace() };
}

const settle = () => new Promise((r) => setTimeout(r, 20));
const hex = (bytes) => Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");

test("empty state: no prefilled message, no digest, transport off", { skip: !ready }, async () => {
    const { root, session } = await setup();
    await settle();
    const $ = root.byId;
    assert.equal($.status.textContent, "Type a message, or pick a known answer.");
    assert.equal($.digest.value, "");
    assert.equal($.message.value, "", "no prefilled message");
    assert.equal($.play.disabled, true);
    assert.equal($["anim-note"].hidden, true);
    session.dispose();
});

test("typing hashes live with the generated Hash", { skip: !ready }, async () => {
    const { root, session, answer, traced } = await setup();
    const $ = root.byId;
    $.message.value = "hi";
    $.message.fire("input");
    await new Promise((r) => setTimeout(r, 220));
    assert.equal($.digest.value, hex(answer({ op: "digest", bytes: [0x68, 0x69] }).digest));
    assert.match($.status.textContent, /^2 bytes · 1 block · /);
    assert.equal($.play.disabled, !traced, "Play needs the generated trace");
    session.dispose();
});

test("KAT picker: every v3 vector's digest matches", { skip: !ready }, async () => {
    const { root, session } = await setup();
    const $ = root.byId;
    const names = JSON.parse(readFileSync(join(here, "generated/kats.json"), "utf8")).vectors.map((v) => v.name);
    assert.equal(names.length, 8);
    for (const name of names) {
        await session.pickKat(name);
        await settle();
        assert.match($.status.textContent, new RegExp(`“${name}”.*digest matches the KAT file ✓`), name);
    }
    session.dispose();
});

test("longer than one block: digest only, too long to trace, no fast-forward", { skip: !ready }, async () => {
    const { root, view, session } = await setup();
    const $ = root.byId;
    await session.pickKat("multi_56");
    await settle();
    assert.equal($["anim-note"].hidden, false);
    assert.match($["anim-note"].textContent, /^3 blocks: too long to trace\./);
    assert.equal($.play.disabled, true);
    assert.equal($.step.disabled, true);
    assert.match($.status.textContent, /“multi_56”, 3 blocks: digest matches the KAT file ✓/);
    await session.play();
    assert.equal(view.calls.filter((c) => c[0] === "beat").length, 0, "nothing animates");
    session.dispose();
});

test("KAT menu: longer vectors are marked digest only", { skip: !ready }, async () => {
    const { root, session } = await setup();
    await session.pickKat("empty");
    const labels = root.byId["kat-menu"].children.map((b) => b.textContent);
    assert.equal(labels.length, 8);
    assert.equal(labels.filter((t) => t.endsWith("(digest only)")).length, 5, labels.join(" | "));
    assert.ok(labels.every((t) => !/fast-forward/.test(t)));
    session.dispose();
});

test("no trace in the generated code: digest only, says why", { skip: !ready }, async () => {
    // A hasher whose generated module had no trace_hash (the fallback).
    globalThis.window ??= { addEventListener() {}, removeEventListener() {} };
    const { answer } = await import("./worker.js");
    const { createMegaDreifachSession } = await import("./session.js");
    const hasher = {
        digest: async (bytes) => ({ ...answer({ op: "digest", bytes }), traced: false }),
        show: async () => ({ show: null, reason: "no-trace" }),
    };
    const root = makeRoot();
    const view = stubView();
    const session = createMegaDreifachSession({ view, root, specUrl: "SPEC.md", hasher, katsUrl: "kats.json" });
    const $ = root.byId;
    await session.pickKat("short_abc");
    await settle();
    assert.equal($.play.disabled, true);
    assert.equal($["anim-note"].hidden, false);
    assert.match($["anim-note"].textContent, /no trace \(trace_hash is not in the v3 \.sudo yet\)/);
    session.dispose();
});

test("with the trace: skip, reset, play every beat to the end, step opens teach", { skip: !ready }, async () => {
    const { root, view, session, traced } = await setup();
    assert.ok(traced, "the generated v3 module has trace_hash");
    const $ = root.byId;
    await session.pickKat("short_abc");
    await settle();
    await session.skipToEnd();
    const beats = session.state().beats;
    assert.ok(beats > 700, "one block is a long show");
    assert.deepEqual(view.calls.filter((c) => c[0] === "seek").at(-1), ["seek", beats - 1]);
    assert.match($.status.textContent, /^Done\. A holds the digest [0-9a-f]+\.$/);
    await session.reset();
    assert.equal(session.state().cursor, -1);
    await session.play();
    assert.equal(session.state().cursor, beats - 1);
    const played = view.calls.filter((c) => c[0] === "beat");
    assert.equal(played.length, beats, "every beat plays: nothing truncated");
    assert.equal(played.filter((c) => c[2] === "card").length, 52);
    assert.equal(played.filter((c) => c[2] === "echo").length, 26);
    assert.equal(played.filter((c) => c[2] === "count").length, 26);
    await session.reset();
    await session.step(1);
    assert.equal(session.state().teaching, true);
    assert.equal($.teach.hidden, false);
    assert.equal(session.state().cursor, 0);
    assert.match($["teach-pos"].textContent, new RegExp(`^1 / ${beats}$`));
    session.dispose();
});
