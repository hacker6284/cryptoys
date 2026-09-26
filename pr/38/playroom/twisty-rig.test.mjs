import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const src = readFileSync(new URL("./twisty-rig.js", import.meta.url), "utf8");

assert.equal(src.includes("export function inspectMaterials"), false, "spike inspectMaterials stays out");
assert.equal(src.includes("export function describeThreeSkew"), false, "spike describeThreeSkew stays out");
assert.equal(src.includes("userData.twistySkew"), false, "no twistySkew probe");
assert.equal(src.includes("look,"), false, "rig.look probe stays out");
assert.match(src, /if \(disposed\) return/, "playLeaves bails after dispose");

const hostRemove = src.indexOf("hidePlayerHost(player)");
const tryAt = src.indexOf("try {", hostRemove);
const catchRemove = src.indexOf("player.remove();", tryAt);
assert.ok(hostRemove >= 0 && tryAt > hostRemove && catchRemove > tryAt, "host is removed if adopt throws after append");

console.log("twisty-rig source tests ok");
