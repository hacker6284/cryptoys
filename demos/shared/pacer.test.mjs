// Frame skipping (shared/pacer.js): motions and waits shorter than a frame
// at a fast speed jump to their end and pass their time on a virtual
// clock that keeps to the wall clock, so 100× really is 100× faster.
import assert from "node:assert/strict";

globalThis.requestAnimationFrame ??= (fn) => setTimeout(() => fn(performance.now()), 1000 / 60);
const { FRAME_MS, pacedTimer, pacedWait, skipMs } = await import("./pacer.js");

assert.equal(skipMs(700, 1), null, "1×: every motion tweens as before");
assert.equal(skipMs(5, 1), null, "1×: even a sub-frame motion keeps its old path");
assert.equal(skipMs(5, 0.5), null, "slower than 1×: unchanged");
assert.equal(skipMs(700, 10), null, "70 ms at 10× still tweens");
assert.equal(skipMs(700, 100), 7, "7 ms at 100× skips frames");
assert.equal(skipMs(5, 100), FRAME_MS / 100, "a motion's 1× frame floor scales");
assert.equal(skipMs(0, 100, { floor: false }), 0, "a zero wait stays zero");
assert.equal(skipMs(300, 100, { floor: false }), 3);

// A chain of 400 waits of 1 ms takes about 400 ms of wall clock, not 400 frames.
{
    const t0 = performance.now();
    for (let i = 0; i < 400; i++) await pacedWait(1);
    const ms = performance.now() - t0;
    // A frame each would be 400 × 16.7 ≈ 6,700 ms.
    assert.ok(ms >= 380 && ms < 2000, `400 × 1 ms chained: ${ms.toFixed(0)} ms`);
}
// Side by side they share their time; order holds by due time.
{
    const order = [];
    const t0 = performance.now();
    await Promise.all(Array.from({ length: 52 }, (_, i) => pacedWait(5 + (i % 4)).then(() => order.push(i % 4))));
    const ms = performance.now() - t0;
    // One after another they would take 52 × 6.5 ≈ 340 ms.
    assert.ok(ms < 200, `52 parallel waits of 5–8 ms: ${ms.toFixed(0)} ms`);
    assert.deepEqual(order, [...order].sort((a, b) => a - b), "released in due order");
}
// Steps chained across parallel motions are applied in order, every one.
{
    let applied = 0;
    const seen = [];
    for (let step = 0; step < 100; step++) {
        await Promise.all([0, 1, 2].map(async (k) => {
            await pacedWait(2 + k);
            seen.push(step);
        }));
        applied += 1;
    }
    assert.equal(applied, 100);
    assert.deepEqual(seen, Array.from({ length: 300 }, (_, i) => Math.floor(i / 3)), "no step skipped or reordered");
}
// A virtual timer can be cancelled.
{
    let fired = 0;
    const cancel = pacedTimer(() => { fired += 1; }, 3, 3);
    cancel();
    pacedTimer(() => { fired += 10; }, 3, 3);
    await pacedWait(10);
    assert.equal(fired, 10);
}
console.log("pacer tests ok");
