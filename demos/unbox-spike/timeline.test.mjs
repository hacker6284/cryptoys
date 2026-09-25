import assert from "node:assert/strict";
import { easeInOutCubic, easeOutCubic, easeOutQuart, lerp } from "./timeline.js";

assert.equal(lerp(0, 10, 0), 0);
assert.equal(lerp(0, 10, 1), 10);
assert.equal(lerp(2, 8, 0.5), 5);

assert.equal(easeOutCubic(0), 0);
assert.equal(easeOutCubic(1), 1);
assert.ok(easeOutCubic(0.5) > 0.8, "ease-out spends time off the shelf");

assert.equal(easeInOutCubic(0), 0);
assert.equal(easeInOutCubic(1), 1);
assert.ok(Math.abs(easeInOutCubic(0.5) - 0.5) < 1e-9);

assert.equal(easeOutQuart(0), 0);
assert.equal(easeOutQuart(1), 1);
assert.ok(easeOutQuart(0.5) > easeOutCubic(0.5), "quart leaves faster than cubic");
