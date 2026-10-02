import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";

// The library is the one place an animation's values live: each entry
// has settings.js and index.js, its microdemo keeps no copy, and the
// README says whether Zachary has approved it.
const here = new URL("./", import.meta.url);
const micro = new URL("../micro/", import.meta.url);
const readme = readFileSync(new URL("README.md", here), "utf8");
const entries = readdirSync(here, { withFileTypes: true })
    .filter((d) => d.isDirectory() && d.name !== "sounds")
    .map((d) => d.name);
assert.ok(entries.includes("scramble-turn"), "scramble-turn is in the library");
for (const name of entries) {
    assert.ok(existsSync(new URL(`${name}/settings.js`, here)), `${name}: settings.js`);
    assert.ok(existsSync(new URL(`${name}/index.js`, here)), `${name}: index.js`);
    assert.ok(!existsSync(new URL(`${name}/settings.js`, micro)), `${name}: the microdemo keeps no copy of the settings`);
    const viewer = new URL(`${name}/page.js`, micro);
    if (existsSync(viewer)) {
        assert.match(readFileSync(viewer, "utf8"), new RegExp(`anim/${name}/index\\.js`), `${name}: the microdemo views the entry`);
    }
    assert.match(readme, new RegExp("\\| `" + name + "` \\|"), `${name}: listed in README.md`);
}

// scramble-turn is approved as Zachary heard it at af9a8fb.
assert.match(readme, /\| `scramble-turn` \|[^\n]*approved[^\n]*af9a8fb/);

const { settings, timing, slots } = await import(new URL("scramble-turn/index.js", here));
assert.equal(timing, settings.timing, "timing is the settings object itself");
assert.deepEqual(slots.map((s) => s.name), ["single", "double", "triple", "rotation", "lift", "settle"]);

const { slotOf, clickTimes } = await import(new URL("twisty.js", here));
assert.equal(slotOf("R"), "single");
assert.equal(slotOf("R'"), "single");
assert.equal(slotOf("R2"), "double");
assert.equal(slotOf("R3"), "triple");
assert.equal(slotOf("x"), "rotation");
const [half, seat] = clickTimes(2, 1);
assert.ok(Math.abs(seat) < 1, "the last click is the seat");
assert.equal(Math.round(half), -750, "a double turn's first click is at half way");

// Face-turn clicks are placed from the moment the face starts moving:
// peakAtMs is where the loudest click lands, scaled with the turn, so
// at peakAtMs 0 it sits on the turn's start at any tempo (the file
// starts its head's length before the turn).
const { stretchContact, fileStart } = await import(new URL("voice.js", here));
const peaks = { single: 143.3, double: 119.8, triple: 194.3 }; // loudest samples, decoded
for (const [slot, peakMs] of Object.entries(peaks)) {
    const s = settings.sounds[slot];
    assert.equal(s.offsetMs, undefined, `${slot} is placed by peakAtMs`);
    for (const tempo of [0.5, 1.4, 4]) {
        const turnStart = 5000;
        const peakAt = fileStart(s, turnStart, peakMs, timing.speed / tempo) + peakMs;
        assert.ok(Math.abs(peakAt - (turnStart + s.peakAtMs * timing.speed / tempo)) < 1e-9, `${slot} peak at ${tempo}×`);
    }
}
assert.equal(fileStart({ peakAtMs: 100 }, 0, 143, 1.4 / 0.7), 200 - 143, "peakAtMs scales with the turn: half the tempo, twice as late");

// offsetMs sounds (the rotation): the time from the loudest sample to
// the contact scales the same way.
const { offsetMs } = settings.sounds.rotation;
const peakMs = 127.6;
for (const tempo of [0.5, 1.4, 4]) {
    const end = 1000 / tempo;
    const peakAt = fileStart({ offsetMs }, end, peakMs, timing.speed / tempo) + peakMs;
    assert.ok(Math.abs((end - peakAt) - (-offsetMs - peakMs) * timing.speed / tempo) < 1e-9, `rotation peak at ${tempo}×`);
}
assert.equal(stretchContact(1000, offsetMs, peakMs, 1), 1000, "unchanged at the tuned tempo");

console.log("animation library tests ok");
