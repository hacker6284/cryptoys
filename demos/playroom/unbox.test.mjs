import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { HAND, HAND_FACE_INDEXES, pickHandTextures } from "./unbox-hand.js";

const SUIT_FILE = ["club", "heart", "spade", "diamond"];
const RANK_FILE = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "jack", "queen", "king"];

function faceIndex(file) {
    const match = /^([a-z]+)_([0-9a-z]+)\.png$/.exec(file);
    assert.ok(match, `hand file ${file}`);
    const suit = SUIT_FILE.indexOf(match[1]);
    const rank = RANK_FILE.indexOf(match[2]);
    assert.ok(suit >= 0 && rank >= 0, `known face ${file}`);
    return suit * 13 + rank;
}

assert.equal(HAND.length, 8, "unbox deals a short packet, not the cipher grid");
assert.equal(HAND_FACE_INDEXES.length, 8);
assert.deepEqual(HAND_FACE_INDEXES, HAND.map(faceIndex));
assert.ok(HAND_FACE_INDEXES.every((index) => index >= 0 && index < 52));

const faces = Array.from({ length: 52 }, (_, i) => `face-${i}`);
const picked = pickHandTextures({ faces, red: "back-red" });
assert.equal(picked.faces.length, 8);
assert.equal(picked.back, "back-red");
assert.equal(picked.faces[0], "face-26");
assert.equal(picked.faces[7], "face-6");

const adapters = readFileSync(new URL("./adapters.js", import.meta.url), "utf8");
assert.match(adapters, /playPhysical/);
assert.match(adapters, /createUnboxRig/);
assert.match(adapters, /cutToTable/);
assert.equal(adapters.includes("handoffToTable"), false);
assert.equal(adapters.includes("fadeTree"), false, "enter does not fade");
assert.equal(adapters.includes("fadeIn"), false, "enter does not fade the table in");
assert.equal(adapters.includes("fadeOut"), false, "leave does not fade the table out");
assert.equal(adapters.includes("setTreeOpacity"), false, "adapter does not lerp material opacity");
assert.equal(adapters.includes("playBloom"), false, "bloom is not the production enter");
assert.equal(adapters.includes("gsap"), false, "GSAP stays out of the room");
assert.equal(adapters.includes("DEAL_SCALE"), false, "adapter does not scale the unbox to 104 seats");

const cardStage = readFileSync(new URL("./card-stage.js", import.meta.url), "utf8");
assert.equal(cardStage.includes("fadeTree"), false);
assert.equal(cardStage.includes("fadeIn"), false);
assert.equal(cardStage.includes("setTreeOpacity"), false);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /unbox_travel/);
assert.match(app, /skipEnter/);
assert.match(app, /prepareEnter/);
const tickAt = app.indexOf("requestAnimationFrame(tick)");
const deepLinkAt = app.indexOf("void startAlgo(initialAlgo)");
assert.ok(tickAt >= 0 && deepLinkAt > tickAt, "rAF tick starts before deep-link DoubleDeal enter");
assert.ok(app.indexOf("addEventListener(\"pointerdown\"") < deepLinkAt, "skip is bound before deep-link enter");

const physical = readFileSync(new URL("./unbox-physical.js", import.meta.url), "utf8");
assert.match(physical, /setFlap/);
assert.match(physical, /unbox_deal/);
assert.equal(physical.includes("playBloom"), false);
assert.equal(physical.includes("gsap"), false);
assert.ok(!physical.includes("104"), "physical take does not deal 104 cipher seats");

console.log("unbox tests ok");
