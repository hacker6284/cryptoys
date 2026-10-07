// One implementation per demo (Zachary, 2026-10-07: "There shouldn't be
// copies like this. The individual pages should be identical to the
// playroom demos."): each demo's own URL forwards to the playroom's demo,
// and every demo docks the one shared speed slider (shared/speed.js,
// 0.1× to 100× on a log scale, 1× by default).
import assert from "node:assert/strict";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import vm from "node:vm";
import { stubThree } from "./three-stub.mjs";

stubThree();
const { DEMOS } = await import("./demos.js");
const here = (path) => new URL(path, import.meta.url);
const ids = Object.keys(DEMOS).sort();
assert.deepEqual(ids, ["doubledeal", "megadreifach", "scramble"]);

// ---- each standalone URL forwards to the playroom --------------------------

const forwardJs = readFileSync(here("../shared/forward.js"), "utf8");

function forwardFrom(href, algo) {
    const replaced = [];
    const url = new URL(href);
    const context = {
        URL,
        URLSearchParams,
        document: { currentScript: { getAttribute: (name) => (name === "data-algo" ? algo : null) } },
        location: {
            href: url.href,
            search: url.search,
            hash: url.hash,
            replace: (to) => replaced.push(to),
        },
    };
    vm.runInNewContext(forwardJs, context);
    return replaced;
}

for (const id of ids) {
    const html = readFileSync(here(`../${id}/index.html`), "utf8");
    const scripts = [...html.matchAll(/<script\b([^>]*)>/g)].map((m) => m[1]);
    assert.deepEqual(scripts.map((attrs) => attrs.trim()), [`src="../shared/forward.js" data-algo="${id}"`],
        `${id}/index.html only forwards (no page of its own)`);
    assert.doesNotMatch(html, /<link[^>]+stylesheet/, `${id}/index.html has no styles of its own`);
    assert.doesNotMatch(html, /type="module"|importmap|<canvas|id="speed"/, `${id}/index.html has no demo of its own`);
    assert.match(html, new RegExp(`href="\\.\\./\\?algo=${id}"`), `${id}/index.html links the room without JS`);
    for (const file of ["app.js", "view.js", "style.css"]) {
        assert.equal(existsSync(here(`../${id}/${file}`)), false, `${id}/${file} (a standalone copy) is gone`);
    }

    assert.deepEqual(forwardFrom(`https://hacker6284.github.io/cryptoys/${id}/`, id),
        [`/cryptoys/?algo=${id}`], `${id}/ forwards to the playroom's ${id}`);
    assert.deepEqual(forwardFrom(`https://hacker6284.github.io/cryptoys/pr/9/${id}/index.html`, id),
        [`/cryptoys/pr/9/?algo=${id}`], `${id}/index.html forwards inside a PR preview`);
    assert.deepEqual(forwardFrom(`https://cryptoygraphy.com/${id}/?standalone=1&debug=1&puzzle=megaminx#teach`, id),
        [`/?algo=${id}&debug=1&puzzle=megaminx#teach`], `old ${id}/?standalone=1 links keep their other params and hash`);
    assert.deepEqual(forwardFrom(`https://cryptoygraphy.com/${id}/?algo=other`, id),
        [`/?algo=${id}`], `${id}/ always opens ${id}`);
}
assert.equal(existsSync(here("../shared/step.css")), false, "the standalone pages' step.css is gone");

// ---- every demo uses the shared slider -------------------------------------

const speed = await import("../shared/speed.js");
assert.equal(speed.SPEED_MIN, 0.1);
assert.equal(speed.SPEED_MAX, 100);
assert.equal(speed.SPEED_DEFAULT, 1);
const markup = speed.speedSliderMarkup();
const attr = (name) => Number(markup.match(new RegExp(` ${name}="([^"]+)"`))[1]);
assert.equal(speed.speedFromSlider(attr("min")), 0.1, "range starts at 0.1×");
assert.equal(speed.speedFromSlider(attr("max")), 100, "range ends at 100×");
assert.equal(speed.speedFromSlider(attr("value")), 1, "default 1×");
assert.ok(Math.abs((attr("value") - attr("min")) / (attr("max") - attr("min")) - 1 / 3) < 1e-12,
    "the thumb starts a third of the way along");
assert.match(markup, /<output id="speed-out" for="speed">1×<\/output>/, "the multiplier shows next to it");
assert.ok(Math.abs(speed.speedFromSlider(0.5) - Math.sqrt(10)) < 1e-9, "log scale: half way between 1× and 10× is √10×");
assert.equal(speed.sliderFromSpeed(10), 1);
assert.equal(speed.speedFromSlider(5), 100, "clamped");
assert.equal(speed.speedFromSlider("nope"), 1);
for (const [m, text] of [[0.1, "0.1×"], [0.25, "0.25×"], [1, "1×"], [1.5, "1.5×"], [25, "25×"], [99.6, "100×"], [100, "100×"]]) {
    assert.equal(speed.formatSpeed(m), text);
}

const adapters = readFileSync(here("./adapters.js"), "utf8");
assert.equal((adapters.match(/speedSliderMarkup\(\)/g) || []).length, 1, "the dock builds the one shared slider");
assert.doesNotMatch(adapters, /type="range"/, "no slider of a demo's own");
assert.doesNotMatch(adapters, /speed: \{/, "no per-demo slider range");
assert.equal((adapters.match(/createDock\("(\w+)"/g) || []).length, ids.length, "every demo docks through createDock");
for (const id of ids) assert.match(adapters, new RegExp(`createDock\\("${id}"`), `${id} docks the shared dock`);
for (const file of ["../scramble/session.js", "../doubledeal/session.js", "../megadreifach/session.js"]) {
    const src = readFileSync(here(file), "utf8");
    assert.match(src, /bindSpeedSlider\(root, /, `${file} reads the shared slider`);
    assert.match(src, /view\.setSpeed\?\.\(/, `${file} hands the view the multiplier`);
    assert.doesNotMatch(src, /Number\(speed(El)?\??\.value/, `${file} never reads raw slider units`);
}
// No other page in the demos ships a speed slider of its own.
function walk(dir) {
    return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
        const path = new URL(entry.name + (entry.isDirectory() ? "/" : ""), dir);
        if (entry.isDirectory()) return ["vendor", "generated", "micro", "anim"].includes(entry.name) ? [] : walk(path);
        return /\.(html|js)$/.test(entry.name) ? [path] : [];
    });
}
for (const file of walk(here("../"))) {
    if (file.pathname.endsWith("/shared/speed.js")) continue;
    assert.doesNotMatch(readFileSync(file, "utf8"), /id="speed"/, `${file.pathname} has no slider of its own`);
}

// Each view maps the multiplier onto its locked tempo (1× changes nothing).
const cubeStage = readFileSync(here("./cube-stage.js"), "utf8");
assert.match(cubeStage, /rig\.setTempo\?\.\(\(timing\.speed \|\| 1\) \* speed\)/, "Scramble / megaminx: timing.speed × multiplier");
const dreiStage = readFileSync(here("./drei-stage.js"), "utf8");
assert.match(dreiStage, /setTempo\(MINX_TURN\.speed \* /, "MegaDreifach: the megaminx tempo × multiplier");
const cardStage = readFileSync(here("./card-stage.js"), "utf8");
assert.match(cardStage, /table\.play\(step, TABLE_PACE \* speed, TABLE_PACE\)/, "DoubleDeal: TABLE_PACE × multiplier");
const { timing: cubeTiming } = await import("../anim/cube/index.js");
const { timing: minxTiming } = await import("../anim/megaminx/index.js");
const { timing: dealTiming } = await import("../anim/deck/deal/index.js");
assert.equal(cubeTiming.speed, 1.4, "Scramble 1× = 1.4");
assert.equal(minxTiming.speed, 1.4, "MegaDreifach 1× = 1.4");
assert.equal(dealTiming.pace, 1.8, "DoubleDeal 1× = 1.8");

console.log("one-copy tests ok");
