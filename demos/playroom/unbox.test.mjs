import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    HAND,
    HAND_FACE_INDEXES,
    MSG_HAND,
    MSG_FACE_INDEXES,
    pickHandTextures,
    pickMsgTextures,
} from "./unbox-hand.js";

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
assert.equal(MSG_HAND.length, 8, "MSG unbox is the same short packet");
assert.equal(MSG_FACE_INDEXES.length, 8);
assert.deepEqual(MSG_FACE_INDEXES, MSG_HAND.map(faceIndex));
assert.ok(MSG_FACE_INDEXES.every((index) => index >= 0 && index < 52));
assert.equal(
    new Set([...HAND_FACE_INDEXES, ...MSG_FACE_INDEXES]).size,
    16,
    "KEY and MSG packets do not share faces",
);

const faces = Array.from({ length: 52 }, (_, i) => `face-${i}`);
const picked = pickHandTextures({ faces, red: "back-red" });
assert.equal(picked.faces.length, 8);
assert.equal(picked.back, "back-red");
assert.equal(picked.faces[0], "face-26");
assert.equal(picked.faces[7], "face-6");
const pickedMsg = pickMsgTextures({ faces, navy: "back-navy" });
assert.equal(pickedMsg.faces.length, 8);
assert.equal(pickedMsg.back, "back-navy");
assert.equal(pickedMsg.faces[0], "face-13");

const adapters = readFileSync(new URL("./adapters.js", import.meta.url), "utf8");
assert.match(adapters, /playDualUnbox/);
assert.match(adapters, /createUnboxRig/);
assert.match(adapters, /pickMsgTextures/);
assert.match(adapters, /formSessionTable/);
assert.match(adapters, /waitToyIdle/);
assert.match(adapters, /continueTo/);
assert.match(adapters, /deck2/);
assert.match(adapters, /msgPacket/);
assert.match(adapters, /label: "MSG"/);
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
assert.match(app, /skipEnter/);
assert.match(app, /prepareEnter/);
assert.match(app, /followEnter/);
assert.match(app, /trackActive/);
assert.match(app, /FOLLOW_HOLD_MS/);
assert.match(app, /continueTo/);
const startAt = app.indexOf("async function startAlgo");
const leaveAt = app.indexOf("async function leaveAlgo");
assert.ok(startAt >= 0 && leaveAt > startAt);
assert.equal(
    app.slice(startAt, leaveAt).includes("via: \"shelf\""),
    false,
    "shared enter does not use via:shelf",
);
assert.equal(
    app.slice(startAt, leaveAt).includes("unbox_travel"),
    false,
    "shared enter does not chain unbox_travel",
);
assert.equal(
    app.slice(startAt, leaveAt).includes("id === \"doubledeal\""),
    false,
    "hub→play is one director for both algos",
);
assert.ok(app.includes("via: \"shelf\""), "leave may still ease home via shelf");
const tickAt = app.indexOf("requestAnimationFrame(tick)");
const deepLinkAt = app.indexOf("void startAlgo(initialAlgo)");
assert.ok(tickAt >= 0 && deepLinkAt > tickAt, "rAF tick starts before deep-link DoubleDeal enter");
assert.ok(app.indexOf("addEventListener(\"pointerdown\"") < deepLinkAt, "skip is bound before deep-link enter");
assert.equal(app.includes("poses.snap(\"doubledeal\")"), false, "skip does not snap the seated shot");

const physical = readFileSync(new URL("./unbox-physical.js", import.meta.url), "utf8");
assert.match(physical, /export async function playUnbox/);
assert.match(physical, /export async function playDualUnbox/);
assert.match(physical, /setFlap/);
assert.match(physical, /hopTo/);
assert.match(physical, /seatToys/);
assert.match(physical, /restPose|getBoxRestPose/);
assert.match(physical, /name === "deck2"/);
assert.equal(physical.includes("playShot"), false, "physical take does not snap named camera shots");
assert.equal(physical.includes("playBloom"), false);
assert.equal(physical.includes("gsap"), false);
assert.ok(!physical.includes("104"), "physical take does not deal 104 cipher seats");

const rigSrc = readFileSync(new URL("./unbox-rig.js", import.meta.url), "utf8");
assert.match(rigSrc, /label = "KEY"/);
assert.match(rigSrc, /bodyHex/);

const form = readFileSync(new URL("./table-form.js", import.meta.url), "utf8");
assert.match(form, /formSessionTable/);
assert.match(form, /shrinkHero/);
assert.match(form, /msgPacket/);
assert.match(form, /MSG_FACE_INDEXES/);
assert.match(form, /hopTo/);
assert.equal(form.includes("opacity"), false, "table form does not fade");
assert.equal(form.includes("gsap"), false);

const motion = readFileSync(new URL("./motion.js", import.meta.url), "utf8");
assert.match(motion, /export function hopTo/);
assert.match(motion, /export function followEnter/);
assert.match(motion, /export function trackActive/);
assert.match(motion, /export function trackToys/);
assert.match(motion, /export function continueTo/);
assert.match(motion, /export async function waitToyIdle/);
assert.match(motion, /export async function seatToys/);
assert.equal(motion.includes("fadeTree"), false, "shared motion does not fade");
assert.equal(motion.includes("gsap"), false);
assert.equal(motion.includes("cutToTable"), false);

const posesCtl = readFileSync(new URL("./pose-controller.js", import.meta.url), "utf8");
assert.match(posesCtl, /function followTo/);
assert.match(posesCtl, /function applyFollow/);
assert.match(posesCtl, /mode: "follow"/);
assert.equal(posesCtl.includes("gsap"), false);

console.log("unbox tests ok");
