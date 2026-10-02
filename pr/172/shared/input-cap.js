/**
 * Demo-scale input cap for live-hashed fields (Message, and DoubleDeal
 * Key / Nonce).
 *
 * Pasting a screenplay (Bee Movie, …) used to freeze Scramble: every
 * `input` ran a full hash walk and `view.setAlg(alg)` for a move
 * timeline proportional to the paste. Cap still drops surplus so we
 * never hash megabytes. Within the cap, typing updates Digest only
 * (`createLiveDigest`); Play / Step / teach bind cubing.js `setAlg`.
 * Field scroll is only UI comfort. Discarded surplus is never hashed
 * or animated.
 *
 * Cap: 4096 characters (~4 KiB of ASCII). Quiet note when we drop the
 * rest. Digest for a capped message still shows in full (grow / wrap /
 * scroll inside `--grow-field-max`).
 */

export const DEMO_INPUT_MAX_CHARS = 4096;
export const DEMO_INPUT_DEBOUNCE_MS = 150;

export function clipInputValue(text, maxChars = DEMO_INPUT_MAX_CHARS) {
    const raw = String(text ?? "");
    if (raw.length <= maxChars) return { value: raw, truncated: false };
    return { value: raw.slice(0, maxChars), truncated: true };
}

function setNote(noteEl, truncated, maxChars) {
    if (!noteEl) return;
    noteEl.hidden = !truncated;
    noteEl.textContent = truncated
        ? `Kept the first ${maxChars.toLocaleString()} characters.`
        : "";
}

export function bindCappedInput(el, {
    maxChars = DEMO_INPUT_MAX_CHARS,
    debounceMs = DEMO_INPUT_DEBOUNCE_MS,
    noteEl,
    onChange,
    signal,
} = {}) {
    if (!el) return () => {};
    let timer = 0;
    const opts = signal ? { signal } : undefined;

    const apply = (next, truncated) => {
        if (el.value !== next) el.value = next;
        setNote(noteEl, truncated, maxChars);
    };

    const schedule = () => {
        if (!onChange) return;
        clearTimeout(timer);
        timer = setTimeout(() => onChange(el.value), debounceMs);
    };

    const onInput = () => {
        const { value, truncated } = clipInputValue(el.value, maxChars);
        apply(value, truncated);
        schedule();
    };

    const onPaste = (event) => {
        const pasted = event.clipboardData?.getData("text/plain");
        if (pasted == null) return;
        event.preventDefault();
        const start = el.selectionStart ?? el.value.length;
        const end = el.selectionEnd ?? el.value.length;
        const merged = el.value.slice(0, start) + pasted + el.value.slice(end);
        const { value, truncated } = clipInputValue(merged, maxChars);
        apply(value, truncated);
        const caret = Math.min(start + pasted.length, value.length);
        try {
            el.setSelectionRange(caret, caret);
        } catch {
            // Readonly or unfocused fields can ignore the caret.
        }
        schedule();
    };

    el.addEventListener("input", onInput, opts);
    el.addEventListener("paste", onPaste, opts);

    return () => {
        clearTimeout(timer);
        el.removeEventListener("input", onInput);
        el.removeEventListener("paste", onPaste);
    };
}
