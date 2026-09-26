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
assert.equal(adapters.includes("createCubeRig"), false, "playroom has no hand-rolled cube path");
assert.equal(adapters.includes("legacyCube"), false, "no ?legacyCube=1 fallback");
assert.match(adapters, /prepareEnter/);
assert.match(adapters, /reseatCube/);
assert.match(adapters, /seatSurface/, "reseat uses the intended surface, not flightBusy");
assert.equal(adapters.includes("flightBusy ? \"table\" : \"shelf\""), false, "do not infer table vs shelf from flightBusy");
assert.match(adapters, /playDualUnbox/);
assert.match(adapters, /playRestow/);
{
    const enterFn = adapters.slice(adapters.indexOf("async enter"), adapters.indexOf("async leave"));
    assert.ok(
        enterFn.indexOf("playDualUnbox") < enterFn.indexOf("stageCardTable")
            || enterFn.indexOf("unboxJob = playDualUnbox") < enterFn.indexOf("setupJob"),
        "physical unbox starts before the 104-card table alloc",
    );
    assert.match(adapters, /if \(unbox && unbox2\) return unbox/, "click must not re-adopt / shelfHome");
}
assert.match(adapters, /gatherSessionTable/);
assert.match(adapters, /followLive/);
assert.match(adapters, /createUnboxRig/);
assert.match(adapters, /pickMsgTextures/);
assert.match(adapters, /formSessionTable/);
assert.match(adapters, /waitToyIdle/);
assert.match(adapters, /continueTo/);
assert.match(adapters, /deck2/);
assert.match(adapters, /msgPacket/);
assert.match(adapters, /label: "MSG"/);
assert.match(adapters, /leaveMs/);
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
assert.equal(worldSrc.includes("function makeCubeToy"), false, "hub cube is not a hand-rolled mesh");
assert.match(worldSrc, /seatOnSurface/, "world seats through the shared helper");
assert.match(worldSrc, /width === viewW/, "resize is a no-op when the canvas did not change");
assert.match(worldSrc, /keepFitted/, "host render re-applies Twisty fit before draw");
assert.match(worldSrc, /if \(slots\[name\]\) slots\[name\]\.slot/, "chest deck has no shelf slot");
assert.match(worldSrc, /deck2/);
assert.match(worldSrc, /pivot\.attach\(lid\)/, "lid keeps its authored closed pose");
assert.match(worldSrc, /lidWorld\.min\.z/, "hinge is the wall seam after +π/2 yaw");
assert.match(worldSrc, /openAngle = -1\.45/, "lid swings −X so the cavity faces the room");
assert.equal(worldSrc.includes("lidWorld.max.z"), false, "do not hinge on the room-facing +Z seam");
assert.equal(worldSrc.includes("-gb.min.z"), false, "lid is not rebuilt from geometry bbox");
assert.equal(worldSrc.includes("rotation.x = -0.95"), false, "old front-hinge swing is gone");

const directorSrc = readFileSync(new URL("./toy-director.js", import.meta.url), "utf8");
assert.match(directorSrc, /seatSurface = "table"/, "enter fly records table as the intended seat");
assert.match(directorSrc, /seatSurface = "shelf"/, "leave fly records shelf as the intended seat");
assert.match(directorSrc, /animateLid\(0/, "chest closes after MSG leaves");
assert.equal(directorSrc.includes("setChestLid?.(1)"), false, "skip does not leave the chest stuck open");
assert.match(directorSrc, /setChestLid\?\.\(0\)/);
assert.match(directorSrc, /abandonFlights/);
assert.match(directorSrc, /prepareHome/);
assert.match(directorSrc, /homing/);
assert.match(directorSrc, /recipeMotionMs/);
assert.match(directorSrc, /easeInOutCubic/);

const cardStage = readFileSync(new URL("./card-stage.js", import.meta.url), "utf8");
assert.equal(cardStage.includes("fadeTree"), false);
assert.equal(cardStage.includes("fadeIn"), false);
assert.equal(cardStage.includes("setTreeOpacity"), false);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /skipEnter/);
assert.match(app, /prepareEnter/);
assert.match(app, /followEnter/);
assert.match(app, /followLeave/);
assert.match(app, /trackToys/);
assert.match(app, /FOLLOW_HOLD_MS/);
{
    const startAlgo = app.slice(app.indexOf("async function startAlgo"), app.indexOf("async function leaveAlgo"));
    assert.ok(
        startAlgo.indexOf("followEnter") < startAlgo.indexOf("await prep;"),
        "hub camera starts before prepareEnter finishes",
    );
    assert.match(startAlgo, /trackToys\(/, "enter frames the full toy set, not busy-only");
    assert.match(startAlgo, /extras\?\.includes\("chest"\)/, "Scramble enter does not track the chest");
}
assert.equal(app.includes("doubledeal.prepareEnter"), false, "do not hide-build DD on the hub");
assert.match(app, /playroomTray/);

const css = readFileSync(new URL("./style.css", import.meta.url), "utf8");
assert.equal(
    css.includes("height: calc(100dvh - var(--io-band))"),
    false,
    "portrait tray must not shrink the WebGL canvas",
);
assert.match(css, /translateY\(100%\)/, "portrait io band slides over the canvas");
assert.match(app, /continueTo/);
assert.match(app, /borrowMs/);
assert.match(app, /homeMs/);
assert.match(app, /leaveMs/);
assert.match(app, /prepareHome/);
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
assert.equal(app.includes("via: \"shelf\""), false, "leave does not ease home via shelf");
assert.equal(app.includes("trackToy("), false, "leave tracks the full toy set, not one named toy");
const tickAt = app.indexOf("requestAnimationFrame(tick)");
const deepLinkAt = app.indexOf("void startAlgo(initialAlgo)");
assert.ok(tickAt >= 0 && deepLinkAt > tickAt, "rAF tick starts before deep-link DoubleDeal enter");
assert.ok(app.indexOf("addEventListener(\"pointerdown\"") < deepLinkAt, "skip is bound before deep-link enter");
assert.equal(app.includes("poses.snap(\"doubledeal\")"), false, "skip does not snap the seated shot");

const physical = readFileSync(new URL("./unbox-physical.js", import.meta.url), "utf8");
assert.match(physical, /export async function playUnbox/);
assert.match(physical, /export async function playDualUnbox/);
assert.match(physical, /export async function playRestow/);
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
assert.match(rigSrc, /label: labelText = "KEY"/);
assert.match(rigSrc, /bodyHex/);

const form = readFileSync(new URL("./table-form.js", import.meta.url), "utf8");
assert.match(form, /formSessionTable/);
assert.match(form, /gatherSessionTable/);
assert.match(adapters, /setCardsVisible/);
{
    const gatherStart = form.indexOf("export async function gatherSessionTable");
    const gatherEnd = form.indexOf("function hopSeat");
    assert.equal(
        form.slice(gatherStart, gatherEnd).includes("setCardsVisible"),
        false,
        "gather leaves piles visible; adapter hides on restow",
    );
}
assert.match(form, /shrinkHero/);
assert.match(form, /msgPacket/);
assert.match(form, /MSG_FACE_INDEXES/);
assert.match(form, /hopTo/);
assert.equal(form.includes("opacity"), false, "table form does not fade");
assert.equal(form.includes("gsap"), false);

const motion = readFileSync(new URL("./motion.js", import.meta.url), "utf8");
assert.match(motion, /export function hopTo/);
assert.match(motion, /export function onMarkBeat/);
assert.match(motion, /export function seatOnSurface/);
assert.match(motion, /export function measureLocalBox/);
assert.match(motion, /export function fitToLocalEdge/);
assert.match(motion, /export function keepFitted/);
assert.match(motion, /export function measureWorldBox/);
assert.match(motion, /export function followEnter/);
assert.match(motion, /export function followLeave/);
assert.match(motion, /export function trackActive/);
assert.match(motion, /export function trackToys/);
assert.match(motion, /export function continueTo/);
assert.match(motion, /export async function waitToyIdle/);
assert.match(motion, /export async function seatToys/);
assert.equal(motion.includes("fadeTree"), false, "shared motion does not fade");
assert.equal(motion.includes("gsap"), false);
assert.equal(motion.includes("cutToTable"), false);

const captureSrc = readFileSync(new URL("./capture-strip.js", import.meta.url), "utf8");
assert.match(captureSrc, /debugCapture/);
assert.match(captureSrc, /installCapture/);
assert.match(captureSrc, /pendingBeat/);
assert.match(captureSrc, /CLOCK_STEP_MS/);
assert.match(app, /installCapture/);
assert.equal(captureSrc.includes("gsap"), false);

const posesCtl = readFileSync(new URL("./pose-controller.js", import.meta.url), "utf8");
assert.match(posesCtl, /function followTo/);
assert.match(posesCtl, /function applyFollow/);
assert.match(posesCtl, /function applyReturn/);
assert.match(posesCtl, /function followLive/);
assert.match(posesCtl, /mode: opts.mode === "return" \? "return" : "follow"/);
assert.match(posesCtl, /settleAt/);
assert.match(posesCtl, /easeOutCubic/);
assert.match(posesCtl, /CLOCK_STEP_MS/);
assert.match(posesCtl, /tween.from = capture\(\)/, "enter hold recaptures so look-lead does not snap back");
assert.equal(posesCtl.includes("look.copy(trackPos)"), false, "goTo track eases look, never copies");
assert.equal(posesCtl.includes("gsap"), false);

console.log("unbox tests ok");
