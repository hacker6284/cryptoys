/**
 * The animation library, by object (see README.md):
 *
 *   import { deck, chest, cube, megaminx } from "./demos/anim/index.js";
 *   await deck.box.openFlap(box);  await chest.openLid(rig);  deck.carry(toy, to);
 *
 * Each object's folder holds its own moves and constants; anim/shared/
 * holds the helpers they share (geometry, the playroom's solids, poses,
 * voices, the swing curves). No object imports another.
 */
export * as deck from "./deck/index.js";
export * as chest from "./chest/index.js";
export * as cube from "./cube/index.js";
export * as megaminx from "./megaminx/index.js";
