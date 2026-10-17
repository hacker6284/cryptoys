/**
 * Private helper for the retail boxes with a lift-off lid (battleship/box,
 * yahtzee/box): an open-topped card base and a lid over it, each as the
 * oriented boxes of its card (floor or top, four walls), and the moves
 * every such box has (the lid off and on, what it holds out and in), all
 * from the object's own measured constants and settings. It holds no
 * constants and is not an entry.
 *
 *   lidParts({ hx, hz, y0, y1, wall, top })   → the lid's card, lid frame
 *   baseParts({ hx, hz, h, wall, floor })     → the base's card, base frame
 *   solidsAt(pose, parts)                     → named oriented boxes, world
 *   pocketAt(boxPose, { p, yaw })             → world pose of a pocket
 *   lidBoxMoves({ ... })                      → the box's plans and moves
 */
import { add, obbOf, quatAxisAngle, quatMul, quatRotate } from "./geom.js";
import { planHop } from "./hop.js";
import { playPose, rafRun, worldPose } from "./run.js";

const part = (min, max, name) => ({ min, max, name });

/** A lid's top and four walls (y0 … y1 in the lid's frame; on the box it shares the box's frame). */
export function lidParts({ hx, hz, y0 = 0, y1, wall, top }) {
    return [
        part([-hx, y1 - top, -hz], [hx, y1, hz], "lid top"),
        part([-hx, y0, -hz], [-hx + wall, y1, hz], "lid end"),
        part([hx - wall, y0, -hz], [hx, y1, hz], "lid end"),
        part([-hx, y0, -hz], [hx, y1, -hz + wall], "lid side"),
        part([-hx, y0, hz - wall], [hx, y1, hz], "lid side"),
    ];
}

/** A base's floor and four walls (its origin under the middle of its floor). */
export function baseParts({ hx, hz, h, wall, floor }) {
    return [
        part([-hx, 0, -hz], [hx, floor, hz], "box floor"),
        part([-hx, 0, -hz], [-hx + wall, h, hz], "box end wall"),
        part([hx - wall, 0, -hz], [hx, h, hz], "box end wall"),
        part([-hx, 0, -hz], [hx, h, -hz + wall], "box back wall"),
        part([-hx, 0, hz - wall], [hx, h, hz], "box front wall"),
    ];
}

/** The parts as named world solids at `pose`. */
export function solidsAt(pose, parts, prefix = "") {
    return parts.map((s) => ({ ...obbOf(pose, s), name: prefix + s.name }));
}

const pocketQ = ({ q, yaw = 0 }) => q ?? quatAxisAngle([0, 1, 0], yaw);

/** World pose of a pocket { p, yaw } or { p, q } (box frame: where something lies in the base) in the box at `boxPose`. */
export function pocketAt(boxPose, pocket) {
    return { p: add(boxPose.p, quatRotate(boxPose.q, pocket.p)), q: quatMul(boxPose.q, pocketQ(pocket)) };
}

function reparent(object, parent) {
    if (parent && object.parent !== parent) parent.attach(object);
}

/** Put `object` in `parent` at the local pose { p, yaw } or { p, q } exactly. */
function seatIn(object, parent, pocket) {
    reparent(object, parent);
    const { p } = pocket;
    object.position.set(p[0], p[1], p[2]);
    object.quaternion.set(...pocketQ(pocket));
}

/**
 * The plans and moves of one lid box, from its entry's own measures:
 *   lid: the lid's parts (lid frame); baseSolids(pose): the base's own solids;
 *   lidClearY(boxPose) / packClearY(boxPose): the height the lid's / a held
 *     thing's bottom clears on the way across (the entry's law adds clearM);
 *   pockets: [{ p, yaw } or { p, q }] box frame; held: [parts] of what lies in each;
 *   laws: { lid, held } hop laws (settings); timing: the entry's timing.
 * Returned (k: the pocket):
 *   pocketPose(boxPose, k); planLidOff({ box, to }), planLidOn({ box, from }),
 *   planOut({ box, k, to }), planIn({ box, k, from }) (each also takes
 *   solids, tempo); liftLid(rig, to), putLid(rig), liftOut(rig, k, thing, to),
 *   putIn(rig, k, thing) (each also takes { solids, tempo, run }); pack(rig, k, thing).
 * rig: { group (the base), lid (a child at the group's origin while on) }.
 */
export function lidBoxMoves({ lid, baseSolids, lidClearY, packClearY, pockets, held, laws, timing }) {
    const pocketPose = (boxPose, k = 0) => pocketAt(boxPose, pockets[k]);
    const lidHop = (from, to, boxPose, solids, tempo) =>
        planHop({ from, to, parts: lid, clearY: lidClearY(boxPose) + laws.lid.clearM, solids, law: laws.lid, tempo });
    const heldHop = (from, to, boxPose, k, solids, tempo) =>
        planHop({ from, to, parts: held[k], clearY: packClearY(boxPose) + laws.held.clearM, solids: [...baseSolids(boxPose), ...solids], law: laws.held, tempo });

    const planLidOff = ({ box, to, solids = [], tempo = timing.tempo }) => lidHop(box, to, box, solids, tempo);
    const planLidOn = ({ box, from, solids = [], tempo = timing.tempo }) => lidHop(from, box, box, solids, tempo);
    const planOut = ({ box, k = 0, to, solids = [], tempo = timing.tempo }) => heldHop(pocketPose(box, k), to, box, k, solids, tempo);
    const planIn = ({ box, k = 0, from, solids = [], tempo = timing.tempo }) => heldHop(from, pocketPose(box, k), box, k, solids, tempo);

    return {
        pocketPose,
        planLidOff,
        planLidOn,
        planOut,
        planIn,
        /** Take the lid off and set it down at `to` (a child of the box's parent). Resolves with the plan (null if stopped). */
        liftLid(rig, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
            const plan = planLidOff({ box: worldPose(rig.group), to, solids, tempo });
            reparent(rig.lid, rig.group.parent);
            return playPose(rig.lid, plan, run);
        },
        /** Put the lid back on (a child of the box again, at its origin). */
        async putLid(rig, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
            const plan = planLidOn({ box: worldPose(rig.group), from: worldPose(rig.lid), solids, tempo });
            const done = await playPose(rig.lid, plan, run);
            seatIn(rig.lid, rig.group, { p: [0, 0, 0] });
            return done;
        },
        /** Lift what lies in pocket k out and set it down at `to` (a child of the box's parent). */
        liftOut(rig, k, thing, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
            const plan = planOut({ box: worldPose(rig.group), k, to, solids, tempo });
            reparent(thing, rig.group.parent);
            return playPose(thing, plan, run);
        },
        /** Put it back in pocket k (a child of the box again, exactly in its pocket). */
        async putIn(rig, k, thing, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
            const plan = planIn({ box: worldPose(rig.group), k, from: worldPose(thing), solids, tempo });
            const done = await playPose(thing, plan, run);
            seatIn(thing, rig.group, pockets[k]);
            return done;
        },
        /** Pack it in pocket k at once (a box that starts packed). */
        pack(rig, k, thing) {
            seatIn(thing, rig.group, pockets[k]);
        },
    };
}
