/**
 * DoubleDeal deal into the grid: the hand packet, a neat stack with its
 * top card first, is dealt card by card onto the message grid (column by
 * column), each card hopping from the packet to its seat; one card-fan
 * sound per deal, its audible centre on the cards' peak velocity, and
 * (when settings name a file) one sound per card, its audible onset as
 * the card leaves the packet (align "motion-start"). The values live in
 * ./settings.js.
 *
 * Played by doubledeal/table.js (TABLE_TIMING reads timing) on the
 * real-size layout (doubledeal/real-layout.js) and audited by
 * demos/micro/deck/deal.
 */
import settings from "./settings.js";
import { createVoice } from "../../shared/voice.js";

export { settings };
export const timing = settings.timing;
const CARDS = 52;
// card: every card's sound plays, overlapping freely. No minimum gap, and
// a voice per card of the deal, so sound.js never drops one (it drops
// rather than steals, and nothing cuts a file short: no maxMs). At 1.8×
// the cards leave 20 ms apart and a 200 ms take overlaps ~10 others.
export const slots = [
    { name: "stream", gapMs: 300, voices: 2 },
    { name: "card", gapMs: 0, voices: CARDS },
];

/** easeInOutQuad (table.js tween) is fastest half way through a card's slide. */
export const PEAK_VELOCITY = 0.5;

/** When card `index` moves fastest, ms after the deal starts at `pace`. */
export function cardPeakMs(index, pace = timing.pace, t = timing) {
    return (index * t.dealStaggerMs + PEAK_VELOCITY * t.dealMs) / pace;
}

/** When card `index` leaves the packet (its move starts), ms after the deal starts at `pace`. */
export function cardDepartMs(index, pace = timing.pace, t = timing) {
    return (index * t.dealStaggerMs) / pace;
}

/** The card slot's rule: motion-start unless its settings say otherwise. */
export const CARD_ALIGN = "motion-start";

/**
 * [slot, msFromStart] for a deal of `count` cards at `pace`. stream: on
 * the mean of the cards' peak-velocity times (motion-start: as the first
 * card leaves). card: one per card, as it leaves the packet
 * (motion-start, the default) or at its peak velocity ("peak-velocity").
 */
export function dealContacts(pace = timing.pace, count = CARDS, t = timing, sounds = settings.sounds) {
    const at = (align, i) => (align === "peak-velocity" ? cardPeakMs(i, pace, t) : cardDepartMs(i, pace, t));
    const cards = Array.from({ length: count }, (_, i) => at(sounds?.card?.align ?? CARD_ALIGN, i));
    const peaks = Array.from({ length: count }, (_, i) => cardPeakMs(i, pace, t));
    const stream = sounds?.stream?.align === "motion-start" ? cardDepartMs(0, pace, t) : peaks.reduce((a, b) => a + b, 0) / count;
    return [["stream", stream], ...cards.map((ms) => ["card", ms])];
}

const SOUNDS = new URL("../../sounds/", import.meta.url);
let voice = null;

/** The entry's sounds on the page's shared AudioContext (made once). */
export function gridDealVoice() {
    voice ??= createVoice({ settings, slots, base: SOUNDS });
    return voice;
}
