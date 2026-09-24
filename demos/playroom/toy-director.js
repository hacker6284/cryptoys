/**
 * Toy director — stub.
 *
 * Later: the shelf holds one of each kind. On algorithm pick, resolve the
 * borrow list (shelf item + chest extras if needed), fly toys to the round
 * table in under ~2 s, then hand off to a demo adapter for layout on the felt.
 * Back reverses. Hover rims the algorithm's shelf toys (and the chest if
 * extras will be needed). Click skips; prefers-reduced-motion snaps in place.
 *
 * Not implemented in this PR. TwoDeck and Scramble stay on their own pages.
 */

export function createToyDirector(/* world */) {
    return {
        highlight(_algorithmId) {
            // TODO: warm rim on the borrowed shelf toys (and chest if extras).
        },
        clearHighlight() {
            // TODO
        },
        async borrow(_algorithmId) {
            throw new Error("toy director: borrow / fly-in is not implemented yet");
        },
        async home() {
            // TODO: reverse arcs; shelf item home; extras into the chest.
        },
    };
}
