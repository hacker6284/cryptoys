import assert from "node:assert/strict";
import {
    FACE_HEX,
    FACE_MOVE,
    FACE_NAME,
    FACE_NORMAL,
    cardFaceIndex,
    cardLabel,
    gripMatrix,
    gripQuaternion,
    mulMatrix,
    spinMatrix,
    turnMove,
} from "./minx.js";
import { loadGenerated } from "./gen.test-helper.mjs";

const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const close = (a, b, eps = 1e-9) => Math.abs(a - b) < eps;

// Colour names and cubing.js colours are pinned (community scheme; source in minx.js).
assert.deepEqual(FACE_NAME, [
    "white", "green", "purple", "yellow", "blue", "red",
    "pale yellow", "light blue", "orange", "light green", "pink", "grey",
]);
assert.deepEqual(FACE_MOVE, ["U", "F", "L", "BL", "BR", "R", "FR", "FL", "DL", "B", "DR", "D"]);
assert.deepEqual(FACE_HEX, [
    "#ffffff", "#008800", "#8800dd", "#f4f400", "#0000ff", "#ff0000",
    "#e8d0a0", "#3399ff", "#ff8000", "#99ff00", "#ff66cc", "#888888",
]);

// Literal clicks: +k and a King's −k, never the shortest turn.
assert.equal(turnMove(0, 1), "U");
assert.equal(turnMove(3, 4), "BL4");
assert.equal(turnMove(0, -3), "U3'");
assert.equal(turnMove(11, -1), "D'");
assert.throws(() => turnMove(0, 0));
assert.equal(cardLabel(0), "A♣");
assert.equal(cardLabel(46), "Q♠");
assert.equal(cardLabel(51), "K♦");
assert.equal(cardFaceIndex(46), 2 * 13 + 11); // spade_queen in loadCardTextures order
assert.equal(cardFaceIndex(0), 0);

// Unit normals, grip matrices are rotations.
for (const n of FACE_NORMAL) assert.ok(close(dot(n, n), 1));
const aNeighbour = (up) => FACE_NORMAL.findIndex((n) => close(dot(n, FACE_NORMAL[up]), 1 / Math.sqrt(5)));
for (let up = 0; up < 12; up++) {
    const m = gripMatrix(up, aNeighbour(up));
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) assert.ok(close(dot(m[i], m[j]), i === j ? 1 : 0));
    const q = gripQuaternion(up, aNeighbour(up));
    assert.ok(close(Math.hypot(...q), 1));
}
assert.deepEqual(gripQuaternion(0, 1).map((v) => Math.round(v * 1e9) / 1e9), [0, 0, 0, 1]);

const gen = await loadGenerated();
if (!gen) {
    console.log("minx.test: SKIP generated checks (run tools/build.sh)");
} else {
    const names = new Set(FACE_NAME);
    assert.equal(names.size, 12);
    for (let f = 0; f < 12; f++) {
        // Opposites: normal −n, and the scheme's light/dark partners.
        const o = gen.opposite(f);
        const n = FACE_NORMAL[f];
        assert.ok(close(dot(n, FACE_NORMAL[o]), -1), `face ${f} opposite ${o}`);
        const nb = gen.nbrs(f);
        assert.equal(nb.length, 5);
        for (let i = 0; i < 5; i++) {
            const a = FACE_NORMAL[nb[i]];
            const b = FACE_NORMAL[nb[(i + 1) % 5]];
            assert.ok(close(dot(n, a), 1 / Math.sqrt(5), 1e-9), `neighbour ${nb[i]} of ${f}`);
            // Clockwise seen from outside: a × b points into the face.
            assert.ok(dot(cross(a, b), n) < 0, `clockwise ${f}: ${nb[i]} → ${nb[(i + 1) % 5]}`);
        }
    }
    const pairs = [["white", "grey"], ["red", "orange"], ["green", "light green"],
        ["purple", "pink"], ["yellow", "pale yellow"], ["blue", "light blue"]];
    for (const [dark, light] of pairs) {
        assert.equal(gen.opposite(FACE_NAME.indexOf(dark)), FACE_NAME.indexOf(light), `${dark} / ${light}`);
    }
    // Around white, clockwise: red, green, purple, yellow, blue.
    const ring = gen.nbrs(0).map((f) => FACE_NAME[f]);
    const start = ring.indexOf("red");
    assert.deepEqual([...ring.slice(start), ...ring.slice(0, start)], ["red", "green", "purple", "yellow", "blue"]);

    // Generated: spin_about_up(o, 1) brings hold position 2 (left of Front) to Front.
    const home = [...Array(12).keys()];
    for (let k = 1; k <= 4; k++) {
        const o = gen.spin(home, k);
        assert.equal(o[0], 0);
        const drawn = mulMatrix(spinMatrix(k), gripMatrix(0, 1));
        // The face now facing front in the drawing is the generated o[1].
        const facing = FACE_NORMAL.map((n, f) => [f, dot(drawn[2], n)]).sort((a, b) => b[1] - a[1])[0][0];
        assert.equal(facing, o[1], `spin ${k}`);
    }
}
console.log("minx.test: ok");
