/**
 * DoubleDeal deal into the grid: the hand packet, a neat stack with its
 * top card first, is dealt card by card onto the message grid (column by
 * column), each card hopping from the packet to its seat; one card-fan
 * sound per deal, its audible centre on the cards' peak velocity. The
 * values live in ./settings.js.
 *
 * Played by doubledeal/table.js (TABLE_TIMING reads timing) on the
 * real-size layout (doubledeal/real-layout.js) and audited by
 * demos/micro/doubledeal-grid-deal.
 */
import settings from "./settings.js";
import { createVoice } from "../voice.js";

export { settings };
export const timing = settings.timing;
export const slots = [
    { name: "stream", gapMs: 300, voices: 2 },
    { name: "card", gapMs: 66, voices: 4 },
];

/** easeInOutQuad (table.js tween) is fastest half way through a card's slide. */
export const PEAK_VELOCITY = 0.5;
const CARDS = 52;

/** When card `index` moves fastest, ms after the deal starts at `pace`. */
export function cardPeakMs(index, pace = timing.pace, t = timing) {
    return (index * t.dealStaggerMs + PEAK_VELOCITY * t.dealMs) / pace;
}

/**
 * [slot, msFromStart] for a deal of `count` cards at `pace`: the stream on
 * the mean of the cards' peak-velocity times, a card contact on each one's.
 */
export function dealContacts(pace = timing.pace, count = CARDS, t = timing) {
    const peaks = Array.from({ length: count }, (_, i) => cardPeakMs(i, pace, t));
    const mean = peaks.reduce((a, b) => a + b, 0) / count;
    return [["stream", mean], ...peaks.map((at) => ["card", at])];
}

const SOUNDS = new URL("../sounds/", import.meta.url);
let voice = null;

/** The entry's sounds on the page's shared AudioContext (made once). */
export function gridDealVoice() {
    voice ??= createVoice({ settings, slots, base: SOUNDS });
    return voice;
}
