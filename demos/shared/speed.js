/**
 * The one speed control every demo docks (Scramble, DoubleDeal,
 * MegaDreifach): a log-scale slider from 0.1× to 100×.
 *
 * The slider's value is log10 of the multiplier (min -1, max 2), so 1×
 * sits a third of the way along and each third is a factor of ten. 1× is
 * each demo's locked default tempo; the demo's view maps the multiplier
 * onto its own units (view.setSpeed). The current multiplier shows next
 * to the slider ("1×", "25×").
 */
export const SPEED_MIN = 0.1;
export const SPEED_MAX = 100;
export const SPEED_DEFAULT = 1;

const LOG_MIN = Math.log10(SPEED_MIN);
const LOG_MAX = Math.log10(SPEED_MAX);
// Slider steps in log10 units: 300 steps from 0.1× to 100× (≈2.3 % each).
export const SPEED_STEP = 0.01;

function clamp(value, lo, hi) {
    return Math.min(hi, Math.max(lo, value));
}

/** The multiplier a slider value (log10 units) stands for, clamped to 0.1 … 100. */
export function speedFromSlider(value) {
    const v = Number(value);
    if (!Number.isFinite(v)) return SPEED_DEFAULT;
    return clamp(10 ** clamp(v, LOG_MIN, LOG_MAX), SPEED_MIN, SPEED_MAX);
}

/** The slider value (log10 units) for a multiplier. */
export function sliderFromSpeed(multiplier) {
    const m = Number(multiplier);
    if (!(m > 0)) return 0;
    return clamp(Math.log10(m), LOG_MIN, LOG_MAX);
}

/** "0.1×", "0.45×", "1×", "2.5×", "25×", "100×". */
export function formatSpeed(multiplier) {
    const m = clamp(Number(multiplier) || SPEED_DEFAULT, SPEED_MIN, SPEED_MAX);
    let text;
    if (m >= 9.95) text = String(Math.round(m));
    else if (m >= 0.995) text = String(Math.round(m * 10) / 10);
    else text = String(Math.round(m * 100) / 100);
    return `${text}×`;
}

/** The dock's speed control: the slider (#speed) and its readout (#speed-out). */
export function speedSliderMarkup() {
    const value = sliderFromSpeed(SPEED_DEFAULT);
    const shown = formatSpeed(SPEED_DEFAULT);
    return `<label class="slider speed-slider">Speed <input id="speed" type="range" data-speed="log"`
        + ` min="${LOG_MIN}" max="${LOG_MAX}" step="${SPEED_STEP}" value="${value}"`
        + ` aria-valuetext="${shown}"><output id="speed-out" for="speed">${shown}</output></label>`;
}

/** The multiplier the slider shows now (1 when there is no slider). */
export function readSpeed(input) {
    if (!input) return SPEED_DEFAULT;
    return speedFromSlider(input.value);
}

/**
 * Keeps the readout in step with the slider and calls onChange(multiplier)
 * now and on every move. Returns a reader for the current multiplier.
 */
export function bindSpeedSlider(root, onChange, listen) {
    const input = root.querySelector("#speed");
    const out = root.querySelector("#speed-out");
    const sync = () => {
        const m = readSpeed(input);
        const shown = formatSpeed(m);
        if (out) out.textContent = shown;
        input?.setAttribute?.("aria-valuetext", shown);
        onChange?.(m);
        return m;
    };
    input?.addEventListener("input", sync, listen);
    sync();
    return () => readSpeed(input);
}
