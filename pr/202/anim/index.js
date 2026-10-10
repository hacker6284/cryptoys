/**
 * The animation library, by object (see README.md):
 *
 *   import { deck, chest, cube, megaminx, peg, ship, dice } from "./demos/anim/index.js";
 *   await deck.box.openFlap(box);  await chest.openLid(rig);  deck.carry(toy, to);
 *   await peg.insert(mesh, seat, axis);  await ship.place(piece, at);  await dice.roll(die, "d10", 7);
 *
 * Each object's folder holds its own moves and constants; anim/shared/
 * holds the helpers they share (geometry, the playroom's solids, poses,
 * voices, the swing curves). No object imports another.
 */
export * as deck from "./deck/index.js";
export * as chest from "./chest/index.js";
export * as cube from "./cube/index.js";
export * as megaminx from "./megaminx/index.js";
export * as peg from "./peg/index.js";
export * as ship from "./ship/index.js";
export * as dice from "./dice/index.js";
