/**
 * Split live Message hashing from expensive teach / play prep.
 *
 * Typing or pasting must update Digest only. cubing.js `setAlg`,
 * leave-trace, and teach snaps wait for Play / Step / teach
 * (`ensureTimeline`). Hash math is cheap; rebuilding a move timeline
 * on every keystroke is not.
 *
 * DoubleDeal already follows this split (`preview` vs `computeTrace`).
 * Use the same gate there if a demo starts binding heavy 3D on input.
 */

export function createLiveDigest() {
    let digestGen = 0;
    let timelineGen = -1;

    return {
        /** Digest (and any cheap session fields) just became current. */
        afterDigest() {
            digestGen += 1;
        },
        /**
         * Bind the teach / play view if it is behind Digest.
         * @param {() => void} [bind]
         * @returns {boolean} true when `bind` ran
         */
        ensureTimeline(bind) {
            if (timelineGen === digestGen) return false;
            bind?.();
            timelineGen = digestGen;
            return true;
        },
        /** Puzzle swap / new view: the bound alg is gone. */
        dropTimeline() {
            timelineGen = -1;
        },
        stale() {
            return timelineGen !== digestGen;
        },
    };
}
