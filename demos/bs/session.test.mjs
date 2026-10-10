// BS session on a fake DOM, with the real generated module behind stub keys
// (worker.js answer(), run inline) and a stub view that records its calls.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { test } from "node:test";
import { requireGenerated } from "./gen.test-helper.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const ready = requireGenerated() && requireGenerated("generated/kats.json");

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
    const ids = ["seed", "roll", "out-a", "out-b", "out-k", "status", "error", "anim-note", "teach", "teach-card",
        "teach-pos", "play", "step", "skip-end", "reset", "speed", "kat", "kat-menu", "spec", "spec-body",
        "spec-btn", "spec-close", "speed-out"];
    const byId = Object.fromEntries(ids.map((id) => [id, el(id.startsWith("out-") ? "textarea" : "div", id)]));
    byId.speed.value = "0"; // the shared log slider (shared/speed.js): 1×
    byId["anim-note"].hidden = true;
    const jumps = ["back", "fwd", "stage-back", "stage-fwd", "round-back", "round-fwd"].map((j) => el("button", "", { jump: j }));
    return {
        dataset: {},
        byId,
        jumps,
        querySelector: (sel) => (sel.startsWith("#") ? byId[sel.slice(1)] ?? null : null),
        querySelectorAll: (sel) => (sel === "[data-jump]" ? jumps : []),
    };
}

function stubView() {
    const calls = [];
    return {
        calls,
        loadShow: async (show) => { calls.push(["load", show.beats.length]); },
        seek: async (i) => { calls.push(["seek", i]); },
        playBeat: async (beat, i) => { calls.push(["beat", i, beat.kind]); },
        playExpanded: async (beat, i) => { calls.push(["expand", i, beat.kind]); },
        clearShow: async () => { calls.push(["clear"]); },
        setSpeed: (m) => { calls.push(["speed", m]); },
    };
}

async function setup(seed) {
    globalThis.window ??= { addEventListener() {}, removeEventListener() {} };
    globalThis.document ??= { createElement: (tag) => el(tag) };
    const katsFile = readFileSync(join(here, "generated/kats.json"), "utf8");
    globalThis.fetch = async (url) => ({ ok: String(url).endsWith("kats.json"), json: async () => JSON.parse(katsFile) });
    const worker = await import("./worker.js");
    const host = await import("./generated/bs.mjs");
    const { diceFromSeed, regString } = await import("./trace.js");
    const { createBsSession } = await import("./session.js");
    const keys = {
        show: async (s) => worker.answer({ op: "show", seed: s }),
        showVector: async (vector) => worker.answer({ op: "show", vector }),
        check: async (vector) => worker.answer({ op: "check", vector }),
    };
    const root = makeRoot();
    const view = stubView();
    const session = createBsSession({ view, root, specUrl: "SPEC.md", keys, katsUrl: "kats.json", ...(seed ? { seed } : {}) });
    await session.ready();
    const exchange = (s) => {
        const d = diceFromSeed(s);
        const built = (x) => host.build_key_grid({ ...x, next12: 0, next6: 0, next10: 0 }).grid;
        const ex = host.exchange(host.tier("T1"), [built(d.a)], [built(d.b)]);
        return { A: regString(ex.public_a), B: regString(ex.public_b), K: regString(ex.secret_a) };
    };
    return { root, view, session, exchange, kats: JSON.parse(katsFile).vectors.filter((v) => v.kind === "exchange") };
}

test("the seed builds both keys; A, B and K are the generated exchange's", { skip: !ready }, async () => {
    const { root, view, session, exchange } = await setup();
    const $ = root.byId;
    assert.equal($.seed.value, "cryptoys");
    const want = exchange("cryptoys");
    assert.equal($["out-a"].value, want.A);
    assert.equal($["out-b"].value, want.B);
    assert.equal($["out-k"].value, want.K);
    const s = session.state();
    assert.ok(s.beats > 2000, "a beat per summary");
    assert.deepEqual(view.calls.find(([k]) => k === "load"), ["load", s.beats]);
    assert.equal($.play.disabled, false);
    assert.match($.status.textContent, /Seed “cryptoys” · [\d,]+ steps/);
    session.dispose();
});

test("Play plays every summary once, in order, then reports A, B and K", { skip: !ready }, async () => {
    const { root, view, session } = await setup("p1");
    await session.play();
    const beats = view.calls.filter(([k]) => k === "beat");
    assert.equal(beats.length, session.state().beats);
    beats.forEach(([, i], k) => assert.equal(i, k));
    assert.ok(!view.calls.some(([k]) => k === "expand"), "Play never expands");
    assert.match(root.byId.status.textContent, /^Done\. A [.WR]{18} · B [.WR]{18} · K [.WR]{18}$/);
    assert.equal(session.state().lastPlay.beats, beats.length);
    session.dispose();
});

test("Step expands one summary into its peg moves and opens the teach card", { skip: !ready }, async () => {
    const { root, view, session } = await setup("s1");
    await session.step(1);
    await session.step(1);
    assert.deepEqual(view.calls.filter(([k]) => k === "expand"), [["expand", 0, "build"], ["expand", 1, "build"]]);
    assert.equal(session.state().teaching, true);
    assert.equal(root.byId["teach-pos"].textContent, `2 / ${session.state().beats}`);
    await session.step(-1);
    assert.deepEqual(view.calls.at(-1), ["seek", 0], "back seeks to the summary before");
    session.dispose();
});

test("the next-phase jump lands on the last beat of BUILD", { skip: !ready }, async () => {
    const { root, view, session } = await setup("j1");
    root.jumps.find((b) => b.dataset.jump === "round-fwd").fire("click");
    await new Promise((r) => setTimeout(r, 30));
    assert.deepEqual(view.calls.at(-1), ["seek", 199], "both players' 100 holes");
    session.dispose();
});

test("Roll keys picks a fresh seed and new keys", { skip: !ready }, async () => {
    const { root, session, exchange } = await setup();
    root.byId.roll.fire("click");
    await new Promise((r) => setTimeout(r, 600));
    await session.ready();
    const seed = root.byId.seed.value;
    assert.match(seed, /^[0-9a-f]{8}$/);
    assert.equal(root.byId["out-k"].value, exchange(seed).K);
    session.dispose();
});

test("known answers: T1 plays and matches the file; T2 and T6 are checked only", { skip: !ready }, async () => {
    const { root, session, kats } = await setup();
    const $ = root.byId;
    for (const v of kats) {
        await session.pickKat(v.name);
        const s = session.state();
        assert.equal(s.kat, v.name);
        assert.equal(s.verdict, "A, B and K match the file ✓", v.name);
        assert.equal($["out-a"].value, v.public_a);
        assert.equal($["out-b"].value, v.public_b);
        assert.equal($["out-k"].value, v.secret_a);
        assert.equal(s.playable, v.tier === "T1");
        assert.equal($.play.disabled, v.tier !== "T1", `${v.name}: Play ${v.tier === "T1" ? "on" : "off"}`);
        assert.equal($["anim-note"].hidden, v.tier === "T1");
        assert.equal(s.hasShow, v.tier === "T1");
    }
    session.dispose();
});

test("the dock's speed reaches the stage as a multiplier", { skip: !ready }, async () => {
    const { root, view, session } = await setup();
    assert.deepEqual(view.calls.find(([k]) => k === "speed"), ["speed", 1]);
    root.byId.speed.value = "2";
    root.byId.speed.fire("input");
    assert.deepEqual(view.calls.filter(([k]) => k === "speed").at(-1), ["speed", 100]);
    session.dispose();
});
