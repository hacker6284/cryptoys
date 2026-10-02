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

// LOCKED rule (Zachary, 2026-10-02, superseding the single's af9a8fb /
// 2b5f6d4 lock): "the audible part of the sound should be centered over
// the part of the animation where the face is at maximum velocity."
// cubing.js's smootherStep is fastest at exactly half of each move; every
// face-turn sound's audible centroid lands there, at any tempo. Do not
// loosen this test to fit a new value; change the rule with Zachary.
const { stretchContact, fileStart } = await import(new URL("voice.js", here));
const { PEAK_VELOCITY, smootherStep } = await import(new URL("twisty.js", here));
assert.ok(Math.abs(PEAK_VELOCITY - 0.5) < 1e-3, "smootherStep turns fastest half way");
assert.ok(Math.abs((smootherStep(0.5 + 1e-6) - smootherStep(0.5 - 1e-6)) / 2e-6 - 1.875) < 1e-6, "1.875× the mean speed there");
const { turnContacts } = await import(new URL("scramble-turn/index.js", here));
const files = { // decoded: audible centroid (sound.js audibleCentroidMs), loudest sample
    single: { move: "R", centroidMs: 141.2, peakMs: 143.3 },
    double: { move: "R2", centroidMs: 106.9, peakMs: 119.8 },
    triple: { move: "R3", centroidMs: 203.0, peakMs: 194.3 },
};
for (const [slot, { move, centroidMs, peakMs }] of Object.entries(files)) {
    const s = settings.sounds[slot];
    assert.equal(s.align, "peak-velocity", `${slot} is centred on peak velocity`);
    assert.equal(s.nudgeMs ?? 0, 0, `${slot} has no nudge`);
    assert.equal(s.offsetMs, undefined, `${slot} has no magic offset`);
    assert.equal(s.peakAtMs, undefined, `${slot} has no magic offset`);
    for (const tempo of [0.5, 1.4, 4]) {
        const at = 10000;
        const len = { R: 1000, R2: 1500, R3: 2000 }[move] / tempo;
        const [[got, contactMs, stretch]] = turnContacts({ at, tempo, leaves: [move] });
        assert.equal(got, slot);
        const start = fileStart(s, contactMs, { centroidMs, peakMs }, stretch);
        assert.ok(Math.abs(start + centroidMs - (at + len / 2)) < 1e-9, `${slot}'s audible centre on peak velocity at ${tempo}×`);
    }
}
assert.equal(fileStart({ align: "peak-velocity", nudgeMs: 20 }, 1000, { centroidMs: 100 }, 1.4 / 0.7), 1000 + 40 - 100, "nudgeMs scales with the turn");
assert.equal(settings.sounds.single.file, "scramble-turn/single/single_spacejoe-486564", "single file is the approved one");
assert.equal(settings.sounds.single.gainDb, 11, "single gain is the approved one");
assert.equal(fileStart({ peakAtMs: 100 }, 0, 143, 1.4 / 0.7), 200 - 143, "peakAtMs scales with the turn");

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
