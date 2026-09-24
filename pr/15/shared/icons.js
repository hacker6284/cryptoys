/**
 * Tiny Lucide (ISC) icon helper for playroom chrome.
 * Paths match Lucide 0.468 stroke icons.
 */

const PATHS = {
    play: `<polygon points="6 3 20 12 6 21 6 3"/>`,
    pause: `<rect width="4" height="16" x="6" y="4"/><rect width="4" height="16" x="14" y="4"/>`,
    "skip-forward": `<polygon points="5 4 15 12 5 20 5 4"/><line x1="19" x2="19" y1="5" y2="19"/>`,
    "chevron-right": `<path d="m9 18 6-6-6-6"/>`,
    "rotate-ccw": `<path d="M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"/><path d="M3 3v5h5"/>`,
    info: `<circle cx="12" cy="12" r="10"/><path d="M12 16v-4"/><path d="M12 8h.01"/>`,
};

export function lucideSvg(name, size = 22) {
    const inner = PATHS[name];
    if (!inner) return "";
    return `<svg class="lucide lucide-${name}" xmlns="http://www.w3.org/2000/svg" width="${size}" height="${size}" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${inner}</svg>`;
}
