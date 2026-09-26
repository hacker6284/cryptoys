/**
 * Tiny Lucide (ISC) icon helper for playroom chrome.
 * Paths match Lucide 0.468 stroke icons.
 */

const PATHS = {
    play: `<polygon points="6 3 20 12 6 21 6 3"/>`,
    pause: `<rect width="4" height="16" x="6" y="4"/><rect width="4" height="16" x="14" y="4"/>`,
    "skip-forward": `<polygon points="5 4 15 12 5 20 5 4"/><line x1="19" x2="19" y1="5" y2="19"/>`,
    "chevron-left": `<path d="m15 18-6-6 6-6"/>`,
    "chevron-right": `<path d="m9 18 6-6-6-6"/>`,
    "chevrons-left": `<path d="m11 17-5-5 5-5"/><path d="m18 17-5-5 5-5"/>`,
    "chevrons-right": `<path d="m6 17 5-5-5-5"/><path d="m13 17 5-5-5-5"/>`,
    "rotate-ccw": `<path d="M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"/><path d="M3 3v5h5"/>`,
    info: `<circle cx="12" cy="12" r="10"/><path d="M12 16v-4"/><path d="M12 8h.01"/>`,
    paperclip: `<path d="m21.44 11.05-9.19 9.19a6 6 0 0 1-8.49-8.49l8.57-8.57A4 4 0 1 1 18 8.84l-8.59 8.57a2 2 0 0 1-2.83-2.83l8.49-8.48"/>`,
};

const FILL = new Set(["play", "pause"]);

export function lucideSvg(name, size = 22) {
    const inner = PATHS[name];
    if (!inner) return "";
    const fill = FILL.has(name) ? "currentColor" : "none";
    return `<svg class="lucide lucide-${name}" xmlns="http://www.w3.org/2000/svg" width="${size}" height="${size}" viewBox="0 0 24 24" fill="${fill}" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${inner}</svg>`;
}
