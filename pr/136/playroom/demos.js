import { createDoubleDealAdapter, createScrambleAdapter } from "./adapters.js";

// One entry per playroom demo, keyed by its ?algo= id. Boot installs
// the adapters in this order (then seals the lights).
//   pose: camera seat in poses.js.
//   toys: borrowed world.toys; the first flies from its shelf slot, the
//     rest from the chest when extras has "chest".
//   deepLinkPlays: ?algo= plays the full enter from the hub instead of
//     seating at once (reduced motion still seats).
export const DEMOS = {
    scramble: {
        title: "Scramble",
        pose: "scramble",
        toys: ["cube"],
        extras: [],
        adapter: createScrambleAdapter(),
    },
    doubledeal: {
        title: "DoubleDeal",
        pose: "doubledeal",
        toys: ["deck", "deck2"],
        extras: ["chest"],
        deepLinkPlays: true,
        adapter: createDoubleDealAdapter(),
    },
};
