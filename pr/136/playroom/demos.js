import { createDoubleDealAdapter, createScrambleAdapter } from "./adapters.js";

// One entry per playroom demo, keyed by its ?algo= id (null prototype:
// ?algo=constructor is no demo). Boot installs the adapters in this
// order (then seals the lights).
//   pose: camera seat in poses.js.
//   toys: borrowed world.toys; toys[0] flies from its shelf slot.
//     toys[1..] fly out of the chest only when chest is set, and
//     otherwise stay on the shelf.
//   chest: the chest opens for the borrow and the return.
//   deepLinkPlays: ?algo= plays the full enter from the hub instead of
//     seating at once (reduced motion still seats).
export const DEMOS = Object.assign(Object.create(null), {
    scramble: {
        title: "Scramble",
        pose: "scramble",
        toys: ["cube"],
        chest: false,
        deepLinkPlays: false,
        adapter: createScrambleAdapter(),
    },
    doubledeal: {
        title: "DoubleDeal",
        pose: "doubledeal",
        toys: ["deck", "deck2"],
        chest: true,
        deepLinkPlays: true,
        adapter: createDoubleDealAdapter(),
    },
});
