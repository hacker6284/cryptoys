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

// doubledeal-grid-deal: ANIMATION APPROVED and LOCKED at 7b5028f
// (Zachary: "at speed it looks fine"): the motion, timing, real-size
// layout and camera of 0aef6e8. Sound is on hold (card: null pending).
assert.match(readme, /\| `doubledeal-grid-deal` \|[^\n]*Animation APPROVED and LOCKED at `7b5028f`/, "README records the grid-deal animation lock");
{
    const gd = await import(new URL("doubledeal-grid-deal/index.js", here));
    const { REAL_LAYOUT, REAL_MM, UNIT_M } = await import(new URL("../doubledeal/real-layout.js", here));
    assert.deepEqual({ ...gd.settings.timing }, { pace: 1.8, dealMs: 260, dealStaggerMs: 36 }, "the approved grid-deal timing (7b5028f) is unchanged");
    assert.equal(gd.settings.loopGapMs, 700);
    assert.deepEqual({ ...gd.settings.choices }, { major: "deal" });
    const table = readFileSync(new URL("../doubledeal/table.js", here), "utf8");
    assert.match(table, /liftHop: 0\.9,/, "the approved card hop (liftHop 0.9 units = 101 mm)");
    assert.deepEqual(REAL_MM, { card: [63, 88, 0.3], gap: 4, gutter: 40, pileGap: 80, grid: [8, 13] }, "the approved real-size layout");
    assert.ok(Math.abs(UNIT_M - 0.1125) < 1e-12);
    assert.equal(REAL_LAYOUT.artAspect, 63 / 88);
    assert.equal(REAL_LAYOUT.liftM, 0.0005);
    assert.equal(REAL_LAYOUT.seatY, REAL_LAYOUT.cardT / 2);
    const corners = [[0, 0, "message"], [3, 12, "message"], [0, 0, "key"], [3, 12, "key"]].map(([r, c, side]) => REAL_LAYOUT.cell(r, c, side));
    const mm = (v) => Math.round(v * UNIT_M * 1e4) / 10;
    assert.deepEqual(corners.map((p) => [mm(p.x), mm(p.z)]), [[-252.5, -552], [-51.5, 552], [51.5, -552], [252.5, 552]], "the approved seats (mm)");
    const p0 = REAL_LAYOUT.pile("hand", 0, 52);
    assert.deepEqual([mm(p0.x), mm(p0.z)], [-152, 720], "the approved hand packet (mm)");
    const page = readFileSync(new URL("../micro/doubledeal-grid-deal/page.js", here), "utf8");
    assert.match(page, /camera: \{ position: \[DEN\.x, 1\.672, DEN\.z \+ 1\.0\], target: \[DEN\.x, 0\.772, DEN\.z\], fov: 40, fill: 0\.88 \}/, "the approved camera");
    assert.match(page, /frameAll: true,/);
    assert.match(page, /frameLift: TABLE_TIMING\.liftHop \* REAL_LAYOUT\.scale,/);
    assert.match(page, /kind === "deal" \? "scoopcm" : "scooprm"/, "each loop starts from the neat hand packet");
}

// doubledeal-grid-deal: the same rule for a moving
// card. Each card slides with easeInOutQuad (fastest half way) while it
// hops sin(πt) × liftHop; on the real-size layout every card's path is
// long enough that its speed peaks half way, and the stream's audible
// centre lands on the mean of the 52 cards' peaks at any pace.
{
    const gd = await import(new URL("doubledeal-grid-deal/index.js", here));
    const { REAL_LAYOUT } = await import(new URL("../doubledeal/real-layout.js", here));
    assert.equal(gd.timing, gd.settings.timing);
    assert.equal(gd.PEAK_VELOCITY, 0.5);
    const s = gd.settings.sounds.stream;
    assert.equal(s.align, "peak-velocity", "grid deal stream: centred on peak velocity");
    assert.equal(s.offsetMs, undefined);
    assert.equal(gd.settings.sounds.card, null, "no per-card file chosen yet");
    assert.equal(gd.CARD_ALIGN, "motion-start");
    // every card's sound plays, overlapping freely: no gap, a voice per
    // card of the deal (sound.js drops rather than steals; no maxMs cut)
    const cardSlot = gd.slots.find((x) => x.name === "card");
    assert.equal(cardSlot.gapMs, 0);
    assert.ok(cardSlot.voices >= 52, "a voice for every card of a deal");
    assert.equal(gd.settings.sounds.card?.maxMs, undefined);
    for (const pace of [1, 1.8, 3]) {
        const [[slot, at], ...cards] = gd.dealContacts(pace);
        assert.equal(slot, "stream");
        assert.equal(cards.length, 52);
        // card (motion-start, the entry's rule): each card's contact is
        // the moment it leaves the packet, and the file's audible onset
        // lands on it, scaling with the pace.
        cards.forEach(([cs, t], i) => {
            assert.equal(cs, "card");
            assert.ok(Math.abs(t - (i * gd.timing.dealStaggerMs) / pace) < 1e-9, `card ${i} contact as it leaves the packet at ${pace}×`);
        });
        const card = { file: "x", align: "motion-start", nudgeMs: 0 };
        assert.ok(Math.abs(fileStart(card, cards[7][1], { onsetMs: 12.5, centroidMs: 40 }) + 12.5 - cards[7][1]) < 1e-9, "card onset on its departure");
        assert.equal(fileStart({ ...card, nudgeMs: 10 }, 0, { onsetMs: 0 }, 2), 20, "nudgeMs scales");
        // the old rule still available: per card at its peak velocity
        const peaks = gd.dealContacts(pace, 52, gd.timing, { card: { align: "peak-velocity" } }).slice(1);
        peaks.forEach(([, t], i) => assert.ok(Math.abs(t - gd.cardPeakMs(i, pace)) < 1e-9));
        const mean = peaks.reduce((a, [, t]) => a + t, 0) / 52;
        assert.ok(Math.abs(at - mean) < 1e-9);
        assert.ok(Math.abs(at - (25.5 * gd.timing.dealStaggerMs + 0.5 * gd.timing.dealMs) / pace) < 1e-9);
        assert.ok(Math.abs(fileStart(s, at, { centroidMs: 300 }) + 300 - at) < 1e-9, `stream centre on the mean peak at ${pace}×`);
    }
    const table = readFileSync(new URL("../doubledeal/table.js", here), "utf8");
    const hop = Number(table.match(/liftHop: ([\d.]+)/)[1]);
    const ease = (t) => (t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2);
    for (const major of ["col", "row"]) {
        for (let i = 0; i < 52; i++) {
            const row = major === "row" ? Math.floor(i / 13) : i % 4;
            const col = major === "row" ? i % 13 : Math.floor(i / 4);
            const a = REAL_LAYOUT.pile("hand", i, 52);
            const b = REAL_LAYOUT.cell(row, col, "message");
            const dist = Math.hypot(b.x - a.x, b.z - a.z);
            const pos = (t) => [dist * ease(t), Math.sin(Math.PI * t) * hop];
            let best = 0;
            let bestT = 0;
            for (let k = 0; k < 2000; k++) {
                const t = (k + 0.5) / 2000;
                const [x0, y0] = pos(t - 2.5e-4);
                const [x1, y1] = pos(t + 2.5e-4);
                const v = Math.hypot(x1 - x0, y1 - y0);
                if (v > best) [best, bestT] = [v, t];
            }
            assert.ok(Math.abs(bestT - 0.5) < 2e-3, `card ${i} (${major}) moves fastest half way (got ${bestT.toFixed(3)})`);
        }
    }
    const gaps = REAL_LAYOUT.restingClearance();
    for (const [k, v] of Object.entries(gaps)) assert.ok(v > 0, `real layout: no overlap (${k})`);
}

// P1 carry and P2 hinge: the general primitives. NOT YET APPROVED: these
// pin the laws as they stand and run every check over the seeded loops
// the microdemos play (micro/carry, micro/hinge), so a change to a law,
// the room or the placements shows up here. Update the pinned values
// only with Zachary's sign-off once he has approved them.
{
    const geom = await import(new URL("geom.js", here));
    const room = await import(new URL("room.js", here));
    const carry = await import(new URL("carry/index.js", here));
    const cp = await import(new URL("carry/placements.js", here));
    const hinge = await import(new URL("hinge/index.js", here));
    const hp = await import(new URL("hinge/placements.js", here));
    assert.match(readme, /\| `carry` \|[^\n]*not yet approved/i, "README: carry awaits approval");
    assert.match(readme, /\| `hinge` \|[^\n]*not yet approved/i, "README: hinge awaits approval");

    // Real sizes: the shapes the primitives plan with are the toys' drawn bounds.
    const dims = (b) => [0, 1, 2].map((k) => Math.round((b.max[k] - b.min[k]) * 10000) / 10);
    assert.deepEqual(dims(cp.DECK_BOX), [67, 92, 20.4], "deck box 67 × 92 × 20 mm (+ its label)");
    assert.deepEqual(dims(hp.TUCK_BOX), [67, 94.8, 21.2], "tuck box 67 × 92 × 20 mm (+ the shut flap and label)");

    // The carry laws.
    assert.deepEqual(carry.timing, { tempo: 1, baseMs: 450, perSqrtM: 650, minMs: 500, maxMs: 2000, riseM: 0.03, risePerM: 0.18, riseMaxM: 0.5, clearM: 0.03, turnFrom: 0.12, turnTo: 0.88 });
    assert.equal(carry.carryMs(0), 500);
    assert.equal(carry.carryMs(1), 1100);
    assert.equal(carry.carryMs(4), 1750);
    assert.equal(carry.carryMs(9), 2000);
    assert.equal(carry.carryMs(1, { ...carry.timing, tempo: 2 }), 550, "÷ tempo");
    assert.ok(Math.abs(carry.riseFor(1) - 0.21) < 1e-12 && carry.riseFor(10) === 0.5);
    assert.ok(Math.abs(geom.smootherStepD(0.5) - carry.PEAK_RATIO) < 1e-12, "smootherstep is 1.875× the mean speed half way");
    // Quaternion slerp along the shorter arc, three.js conventions.
    const qa = geom.quatFromEuler(0, 0.2, 0), qb = geom.quatFromEuler(Math.PI / 2, 2.9, 0);
    for (let i = 0; i <= 10; i++) assert.ok(Math.abs(Math.hypot(...geom.slerp(qa, qb, i / 10)) - 1) < 1e-9);
    assert.ok(Math.abs(geom.quatAngle(qa, geom.slerp(qa, qb, 0.5)) - geom.quatAngle(qa, qb) / 2) < 1e-9, "slerp turns at a steady rate");

    // Every carry of every seeded loop: no overlap, seated by drawn geometry
    // at both ends, ends exact, duration and peak speed on the law, slerp.
    for (const seed of [1, 2, 3, 4, 5, 6]) {
        const sch = cp.carrySchedule(seed);
        assert.equal(sch.cycles.length, cp.CYCLES);
        const at = { deck: sch.poseOf(sch.start.deck), deck2: sch.poseOf(sch.start.deck2) };
        const lengths = [], targets = new Set(), kinds = { real: 0, edge: 0, random: 0 };
        let flips = 0;
        for (const c of sch.cycles) {
            assert.ok(c.check.ok, `carry seed ${seed} cycle ${c.n} (${c.label}): ${c.check.fail.join("; ")}`);
            assert.deepEqual(c.from, at[c.mover], `carry seed ${seed} cycle ${c.n} starts where its box was left`);
            at[c.mover] = c.to;
            lengths.push(c.plan.L);
            targets.add(c.target.surface);
            kinds[c.kind] += 1;
            if (geom.quatAngle(c.from.q, c.to.q) > Math.PI / 3) flips += 1;
            assert.ok(c.plan.top < 2.68 - 0.06, "below the ceiling");
        }
        assert.deepEqual(sch.end.deck, sch.start.deck, `carry seed ${seed}: the loop ends where it starts`);
        assert.deepEqual(sch.end.deck2, sch.start.deck2);
        assert.ok(Math.min(...lengths) < 0.15 && Math.max(...lengths) > 4, `carry seed ${seed}: near and far (${Math.min(...lengths).toFixed(2)}–${Math.max(...lengths).toFixed(2)} m)`);
        assert.deepEqual([...targets].sort(), ["chest", "felt", "shelf"]);
        assert.ok(kinds.real >= 5 && kinds.edge >= 10 && kinds.random >= 6 && flips >= 4, `carry seed ${seed}: real, edge and random poses, flips`);
    }

    // The hinge curves.
    const { parts } = hinge;
    assert.deepEqual(parts, {
        "chest-lid": { openRad: 1.45, stopGapM: 0.01, open: { ms: 640, curve: "swing", overshoot: 0.03, settle: 0.25 }, close: { ms: 520, curve: "fall", bounce: 0.035, settle: 0.24 } },
        "tuck-flap": { openRad: 2.15, stopGapM: 0.001, open: { ms: 380, curve: "swing", overshoot: 0.06, settle: 0.3 }, close: { ms: 300, curve: "swing", overshoot: 0, settle: 0 } },
    });
    for (const p of Object.values(parts)) for (const spec of [p.open, p.close]) {
        assert.equal(hinge.curveAt(spec, 0), 0);
        assert.ok(Math.abs(hinge.curveAt(spec, 1) - 1) < 1e-12);
    }
    assert.ok(Math.abs(hinge.curvePeakAt(parts["tuck-flap"].open) - 0.35) < 1e-12 && Math.abs(hinge.curvePeakAt(parts["chest-lid"].close) - 0.76) < 1e-12);
    assert.ok(Math.abs(Math.max(...Array.from({ length: 201 }, (_, i) => hinge.curveAt(parts["tuck-flap"].open, i / 200))) - 1.06) < 1e-3, "the flap overshoots 6 %");
    assert.equal(hinge.hingeMs(parts["chest-lid"].open, 0.25), 320, "a quarter sweep takes half the time");

    // The chest as the microdemos place it: its lid clears the walls at full
    // open (with the overshoot). In the live room (yaw π/2) it would not.
    const walls = room.ROOM.filter((x) => x.name.startsWith("wall") || x.name.startsWith("sconce"));
    assert.ok(geom.worstDepth(room.chestLidObb(1.45 * 1.03), walls, 0).depth < 0, "the turned chest's lid clears the walls");
    const live = room.chestLidObb(1.45, { ...room.CHEST, yaw: Math.PI / 2 });
    assert.ok(geom.worstDepth(live, walls, 0).depth > 0.3, "the live chest's lid swings 30+ cm into the wall");

    // Every swing of every seeded hinge loop (and the carries between them).
    for (const seed of [1, 2, 3]) {
        const sch = hp.hingeSchedule(seed);
        assert.equal(sch.cycles.length, hp.CYCLES);
        let lids = 0, stops = new Set();
        for (const c of sch.cycles) {
            if (c.carry) assert.ok(c.carry.check.ok, `hinge seed ${seed} cycle ${c.n} carry: ${c.carry.check.fail.join("; ")}`);
            if (c.what === "lid") lids += 1;
            for (const w of c.swings) {
                assert.ok(w.check.ok, `hinge seed ${seed} cycle ${c.n} (${c.label}): ${w.check.fail.join("; ")}`);
                if (w.plan.stopped) stops.add(w.plan.stopped);
            }
        }
        assert.equal(lids, 5);
        assert.ok(stops.has("shelf-back") && stops.has("table"), `hinge seed ${seed}: the flap meets the backboard and the felt (${[...stops]})`);
        assert.equal(sch.cycles[0].swings[0].plan.to, parts["tuck-flap"].openRad, "a free flap opens all the way");
        assert.equal(sch.cycles[3].swings[0].plan.to, parts["chest-lid"].openRad, "the chest lid opens all the way");
    }
}

console.log("animation library tests ok");
