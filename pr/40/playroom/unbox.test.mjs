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
assert.match(adapters, /formSessionTable/);
assert.match(adapters, /waitToyIdle/);
assert.match(adapters, /continueTo/);
assert.match(adapters, /deck2/);
assert.equal(adapters.includes("cutToTable"), false, "enter does not hide-prop / show-table");
assert.equal(adapters.includes("hideProp"), false, "happy path does not hide the unbox prop");
assert.equal(adapters.includes("handoffToTable"), false);
assert.equal(adapters.includes("fadeTree"), false, "enter does not fade");
assert.equal(adapters.includes("fadeIn"), false, "enter does not fade the table in");
assert.equal(adapters.includes("fadeOut"), false, "leave does not fade the table out");
assert.equal(adapters.includes("setTreeOpacity"), false, "adapter does not lerp material opacity");
assert.equal(adapters.includes("playBloom"), false, "bloom is not the production enter");
assert.equal(adapters.includes("gsap"), false, "GSAP stays out of the room");
assert.equal(adapters.includes("DEAL_SCALE"), false, "adapter does not scale the unbox to 104 seats");

const worldSrc = readFileSync(new URL("./world.js", import.meta.url), "utf8");
assert.match(worldSrc, /if \(slots\[name\]\) slots\[name\]\.slot/, "chest deck has no shelf slot");
assert.match(worldSrc, /deck2/);

const cardStage = readFileSync(new URL("./card-stage.js", import.meta.url), "utf8");
assert.equal(cardStage.includes("fadeTree"), false);
assert.equal(cardStage.includes("fadeIn"), false);
assert.equal(cardStage.includes("setTreeOpacity"), false);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /unbox_travel/);
assert.match(app, /skipEnter/);
assert.match(app, /prepareEnter/);
assert.match(app, /trackEnter/);
assert.match(app, /holdMs: HOLD_MS/);
assert.match(app, /continueTo/);
assert.ok(app.indexOf("via: \"shelf\"") > app.indexOf("id === \"doubledeal\""), "via:shelf stays on Scramble only");
const tickAt = app.indexOf("requestAnimationFrame(tick)");
const deepLinkAt = app.indexOf("void startAlgo(initialAlgo)");
assert.ok(tickAt >= 0 && deepLinkAt > tickAt, "rAF tick starts before deep-link DoubleDeal enter");
assert.ok(app.indexOf("addEventListener(\"pointerdown\"") < deepLinkAt, "skip is bound before deep-link enter");
assert.equal(app.includes("poses.snap(\"doubledeal\")"), false, "skip does not snap the seated shot");

const physical = readFileSync(new URL("./unbox-physical.js", import.meta.url), "utf8");
assert.match(physical, /setFlap/);
assert.match(physical, /hopTo/);
assert.match(physical, /seatToys/);
assert.match(physical, /restPose|getBoxRestPose/);
assert.equal(physical.includes("playShot"), false, "physical take does not snap named camera shots");
assert.equal(physical.includes("playBloom"), false);
assert.equal(physical.includes("gsap"), false);
assert.ok(!physical.includes("104"), "physical take does not deal 104 cipher seats");

const form = readFileSync(new URL("./table-form.js", import.meta.url), "utf8");
assert.match(form, /formSessionTable/);
assert.match(form, /shrinkHero/);
assert.match(form, /hopTo/);
assert.equal(form.includes("opacity"), false, "table form does not fade");
assert.equal(form.includes("gsap"), false);

const motion = readFileSync(new URL("./motion.js", import.meta.url), "utf8");
assert.match(motion, /export function hopTo/);
assert.match(motion, /export function trackEnter/);
assert.match(motion, /export function continueTo/);
assert.match(motion, /export async function waitToyIdle/);
assert.match(motion, /export async function seatToys/);
assert.equal(motion.includes("fadeTree"), false, "shared motion does not fade");
assert.equal(motion.includes("gsap"), false);
assert.equal(motion.includes("cutToTable"), false);

console.log("unbox tests ok");
