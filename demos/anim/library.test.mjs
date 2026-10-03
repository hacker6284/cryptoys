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
assert.match(readme, /\| `scramble-turn` \|[^\n]*face-turn sounds approved and LOCKED at `6014bfc`/, "README records the face-turn lock");

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
// APPROVED and LOCKED at 6014bfc (Zachary: "All look pretty good."):
// exactly these entries; nothing else may move them.
assert.deepEqual(
    { single: settings.sounds.single, double: settings.sounds.double, triple: settings.sounds.triple },
    {
        single: { file: "scramble-turn/single/single_spacejoe-486564", gainDb: 11, align: "peak-velocity", nudgeMs: 0 },
        double: { file: "scramble-turn/double/double_spacejoe-486567", gainDb: 8.5, align: "peak-velocity", nudgeMs: 0 },
        triple: { file: "scramble-turn/triple/triple_spacejoe-486581", gainDb: 6.5, align: "peak-velocity", nudgeMs: 0 },
    },
    "the approved face-turn sounds (6014bfc) are unchanged",
);
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

// The rotation swish (approved 2026-10-02, its swell at mid-rotation for
// a quarter turn) follows the same rule: its swell (loudest 10 ms, 124.3
// ms into the decoded file) at mid-rotation for any rotation and tempo.
{
    const rot = settings.sounds.rotation;
    assert.deepEqual(rot, { file: "scramble-rotate/7_sadiquecat-816261-broomstick-soft", gainDb: -14.9, align: "peak-velocity", centre: "swell", nudgeMs: 0 }, "the approved rotation swish");
    const file = { swellMs: 124.3, centroidMs: 146.1, peakMs: 127.6 };
    for (const [move, ms] of [["y", 1000], ["y2", 1500], ["x'", 1000]]) {
        for (const tempo of [0.5, 1.4, 4]) {
            const at = 10000;
            const len = ms / tempo;
            const [[slot, contactMs, stretch]] = turnContacts({ at, tempo, leaves: [move] });
            assert.equal(slot, "rotation");
            const swellAt = fileStart(rot, contactMs, file, stretch) + file.swellMs;
            assert.ok(Math.abs(swellAt - (at + len / 2)) < 1e-9, `${move} swell at mid-rotation at ${tempo}×`);
            if (move === "y" && tempo === 1.4) {
                // Where Zachary approved it: the file 482 ms before the end of
                // the 714 ms quarter rotation (offsetMs −482, 2026-10-02).
                assert.ok(Math.abs(fileStart(rot, contactMs, file, stretch) - (at + len - 482)) < 1, "quarter rotation within 1 ms of the approved timing");
            }
        }
    }
}
assert.equal(stretchContact(1000, -482, 127.6, 1), 1000, "offsetMs sounds: unchanged at the tuned tempo");

// megaminx-turn: the default rules from the start. Its single, double and
// triple sounds are APPROVED and LOCKED at d952e6a (Zachary: "Sounds are ok
// for that one."): exactly these entries; nothing else may move them.
assert.match(readme, /\| `megaminx-turn` \|[^\n]*sounds approved and LOCKED at `d952e6a`/, "README records the megaminx lock");
// The whole entry (animation and sounds) is APPROVED and LOCKED at a927bb2
// (Zachary approved the animation at the real 70 mm size, seated on the felt).
assert.match(readme, /\| `megaminx-turn` \|[^\n]*Animation and sounds APPROVED and LOCKED at `a927bb2`/, "README records the megaminx animation lock");
{
    const mm = await import(new URL("megaminx-turn/index.js", here));
    assert.deepEqual(
        { single: mm.settings.sounds.single, double: mm.settings.sounds.double, triple: mm.settings.sounds.triple },
        {
            single: { file: "megaminx-turn/single/single_spacejoe-486573", gainDb: 10, align: "peak-velocity", nudgeMs: 0 },
            double: { file: "megaminx-turn/double/double_spacejoe-486565", gainDb: 6.5, align: "peak-velocity", nudgeMs: 0 },
            triple: { file: "megaminx-turn/triple/triple_spacejoe-486566", gainDb: 5, align: "peak-velocity", nudgeMs: 0 },
        },
        "the approved megaminx face-turn sounds (d952e6a) are unchanged",
    );
    assert.equal(mm.timing, mm.settings.timing);
    assert.deepEqual(
        { ...mm.settings.timing },
        { speed: 1.4, TURN_LIFT_MS: 320, TURN_LIFT: 0.14, SETTLE_HOLD_MS: 90 },
        "the approved megaminx animation timing (a927bb2) is unchanged",
    );
    assert.deepEqual(Object.keys(mm.settings.sounds), ["single", "double", "triple", "rotation", "lift", "settle"]);
    for (const [slot, move, ms] of [["single", "U", 1000], ["double", "U2", 1500], ["triple", "U3", 2000]]) {
        const s = mm.settings.sounds[slot];
        assert.match(s.file, new RegExp(`^megaminx-turn/${slot}/`), `megaminx ${slot}: its own click`);
        assert.equal(s.align, "peak-velocity", `megaminx ${slot}: centred on peak velocity`);
        assert.equal(s.offsetMs, undefined);
        for (const tempo of [0.5, 1.4, 4]) {
            const [[got, contactMs, stretch]] = mm.turnContacts({ at: 0, tempo, leaves: [move] });
            assert.equal(got, slot);
            const start = fileStart(s, contactMs, { centroidMs: 120 }, stretch);
            assert.ok(Math.abs(start + 120 - ms / tempo / 2) < 1e-9, `megaminx ${slot} centre half way at ${tempo}×`);
        }
    }
    assert.deepEqual(mm.settings.sounds.settle, settings.sounds.settle, "megaminx lands with scramble-turn's muffled pat");
    assert.equal(mm.settings.sounds.rotation, null);
    assert.ok(!JSON.stringify(mm.settings.sounds).includes("emapuree"), "no wooden-block thud");
}

console.log("animation library tests ok");
