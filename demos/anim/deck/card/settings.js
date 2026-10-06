// deck/card: a single card of the deck and its own moves. Played by the
// MegaDreifach v3 stage (playroom/drei-stage.js). Edit a value and reload.
//
// NOT YET APPROVED (placeholders for the MegaDreifach v3 demo; no
// microdemo yet). Curves, u = time / ms (ms ÷ tempo):
//   turnOver: the card rises straight up off its seat, rolls 180° about
//     its long (z) axis at the top of the lift (easeInOutCubic, fastest
//     half way) and comes straight down onto the same seat. The lift
//     clears the card's half width (31.5 mm) so no edge ever dips into
//     the felt: lift = halfWidth + clearM at the middle of the roll.
//   move: a card slides from one pose to another (easeInOutQuad, fastest
//     half way) while it hops sin(πu) × hopM, its height eased from start
//     to end so it never jumps. Used to hold a card and to gather cards
//     back into their box; the deal itself plays deck/deal's locked law.
//   straight: a card slides straight along its own plane (easeInOutQuad):
//     out of the tuck box's mouth before it is dealt, and back down into
//     the box when it is gathered. clearM: how far its edge clears the
//     mouth before it may hop.
export default {
    loopGapMs: 600,
    choices: {},
    timing: {
        tempo: 1,
    },
    turnOver: { ms: 520, clearM: 0.012 },
    move: { ms: 420, hopM: 0.06 },
    straight: { ms: 200, clearM: 0.006 },
    sounds: {},
};
