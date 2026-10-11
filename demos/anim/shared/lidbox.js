/**
 * Private helper for the retail boxes with a lift-off lid (battleship/box,
 * yahtzee/box): an open-topped card base and a lid over it, each as the
 * oriented boxes of its card (floor or top, four walls), from the object's
 * own measured constants. It holds no constants and is not an entry.
 *
 *   lidParts({ hx, hz, y0, y1, wall, top })   → the lid's card, lid frame
 *   baseParts({ hx, hz, h, wall, floor })     → the base's card, base frame
 *   solidsAt(pose, parts)                     → named oriented boxes, world
 */
import { obbOf } from "./geom.js";

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
