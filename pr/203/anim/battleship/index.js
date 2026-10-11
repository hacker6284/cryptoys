/**
 * battleship: the Battleship set (Hasbro 2015), one logical object: its
 * retail box and the two units it holds.
 *
 *   battleship.box.liftLid / putLid / liftOut / putIn   (./box, not yet approved)
 *   battleship.unit.openLid / closeLid                  (./unit, not yet approved)
 *
 * The pegs, the ships and the key dice are their own objects (../peg,
 * ../ship, ../dice).
 */
export * as box from "./box/index.js";
export * as unit from "./unit/index.js";
