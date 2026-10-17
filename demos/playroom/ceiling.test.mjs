import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

// The shared playroom ceiling (world.js, used by every demo) is one plane.
// Its +Z normal is turned to −Y, and only that inward face is drawn, so a
// camera above the room sees through it and a camera inside still sees it.
const src = readFileSync(new URL("./world.js", import.meta.url), "utf8");
const start = src.indexOf("const ceiling = new THREE.Mesh");
assert.ok(start >= 0, "the playroom builds one ceiling");
const block = src.slice(start, src.indexOf("scene.add(ceiling)", start));
const side = block.match(/side:\s*THREE\.(\w+)/);
assert.equal(side?.[1], "FrontSide", "ceiling draws only its inward face");
const rot = block.match(/ceiling\.rotation\.x\s*=\s*([^;]+);/);
assert.ok(rot, "ceiling plane is turned flat");
const rotationX = { "Math.PI/2": Math.PI / 2, "-Math.PI/2": -Math.PI / 2 }[rot[1].replace(/\s+/g, "")];
assert.equal(typeof rotationX, "number", `ceiling rotation.x is ${rot[1].trim()}`);
// Rx(θ) sends PlaneGeometry's +Z normal to (0, −sin θ, cos θ).
const ny = -Math.sin(rotationX);
assert.ok(ny < -0.99, `ceiling normal faces down (ny=${ny.toFixed(3)}) so FrontSide is the room side`);

console.log("ceiling side tests ok");
