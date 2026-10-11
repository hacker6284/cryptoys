/**
 * deck: one logical object, the deck of cards in its tuck box. Its own
 * moves, and its sub-objects with theirs:
 *
 *   deck.carry(toy, to, opts)     the deck (in its box) from where it is to `to`   (./carry, not yet approved)
 *   deck.deal                     deal into a layout: the grid deal              (./deal, animation LOCKED)
 *   deck.box.openFlap(box, opts)  / deck.box.closeFlap(box, opts)                (./box, not yet approved)
 *   deck.card.turnOver(mesh) / deck.card.move(mesh, to)                          (./card, not yet approved)
 *
 * Gather (the deck's own move back into a packet) is not built yet.
 */
export * as box from "./box/index.js";
export * as card from "./card/index.js";
export * as deal from "./deal/index.js";
export { carry, planCarry, checkPlan as checkCarry, carryMs } from "./carry/index.js";
