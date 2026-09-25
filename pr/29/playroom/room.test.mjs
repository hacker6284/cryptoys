import assert from "node:assert/strict";
import { tableSpan } from "../doubledeal/layout.js";
import { DEAL_SCALE, DEN, TABLE_R } from "./constants.js";
import { POSES, resolvePoseName } from "./poses.js";
import { createToyDirector } from "./toy-director.js";

const span = tableSpan();
const feltDiameter = 2 * (TABLE_R - 0.08);
const scaledWidth = span.width * DEAL_SCALE;
const scaledDepth = span.depth * DEAL_SCALE;

assert.ok(span.width > 0, "standalone table has a width");
assert.ok(scaledWidth < feltDiameter, `scaled decks ${scaledWidth.toFixed(3)}m must sit on the ${feltDiameter.toFixed(3)}m felt`);
assert.ok(scaledDepth < feltDiameter, `scaled depth ${scaledDepth.toFixed(3)}m must sit on the felt`);

assert.ok(POSES.doubledeal, "doubledeal pose exists");
assert.equal(resolvePoseName("doubledeal"), "doubledeal");
assert.equal(resolvePoseName("lean_deck"), "doubledeal");
assert.equal(resolvePoseName("scramble"), "scramble");
assert.ok(POSES.doubledeal.fov <= 32, "doubledeal FOV stays in the scramble-lean family");
assert.ok(POSES.doubledeal.position[1] <= 1.28, "doubledeal camera height matches seated lean");
assert.ok(POSES.doubledeal.position[2] - DEN.z <= 1.05, "doubledeal stay close to the felt");

const director = createToyDirector({});
const recipe = director.recipeOf("doubledeal");
assert.deepEqual(recipe.toys, ["deck"]);
assert.deepEqual(recipe.extras, ["chest"]);
assert.equal(recipe.pose, "doubledeal");
assert.equal(director.recipeOf("scramble").toys[0], "cube");

console.log("playroom room tests ok");
