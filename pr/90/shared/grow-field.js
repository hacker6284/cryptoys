/**
 * Autosize `textarea.grow-field` to its content.
 *
 * CSS `field-sizing: content` does this natively where supported.
 * This helper covers other engines and programmatic `.value` writes
 * (live Digest / Ciphertext). Cap is `--grow-field-max` in
 * `grow-field.css` (8.5rem ≈ five to six lines); the field scrolls
 * after that.
 */

const BOUND = "growBound";
const roots = new Set();
let resizeBound = false;

export function growField(el) {
    if (!el || el.nodeName !== "TEXTAREA") return;
    const style = getComputedStyle(el);
    if (style.fieldSizing === "content") {
        el.style.height = "";
        return;
    }
    const min = parseFloat(style.minHeight) || 0;
    const maxParsed = parseFloat(style.maxHeight);
    const max = Number.isFinite(maxParsed) ? maxParsed : Number.POSITIVE_INFINITY;
    const borders =
        (parseFloat(style.borderTopWidth) || 0) + (parseFloat(style.borderBottomWidth) || 0);
    el.style.height = "auto";
    const next = Math.min(Math.max(el.scrollHeight + borders, min), max);
    el.style.height = `${next}px`;
}

function watchValue(el) {
    const desc = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, "value");
    if (!desc?.get || !desc?.set) return;
    Object.defineProperty(el, "value", {
        configurable: true,
        enumerable: desc.enumerable,
        get() {
            return desc.get.call(this);
        },
        set(next) {
            desc.set.call(this, next);
            queueMicrotask(() => growField(this));
        },
    });
}

function refit(root) {
    if (root !== document && root.isConnected === false) {
        roots.delete(root);
        return;
    }
    root.querySelectorAll("textarea.grow-field").forEach(growField);
}

function onResize() {
    for (const root of [...roots]) refit(root);
}

export function bindGrowFields(root = document) {
    if (!root?.querySelectorAll) return;
    roots.add(root);
    for (const el of root.querySelectorAll("textarea.grow-field")) {
        if (el.dataset[BOUND] === "1") continue;
        el.dataset[BOUND] = "1";
        watchValue(el);
        el.addEventListener("input", () => growField(el));
        growField(el);
    }
    if (!resizeBound && typeof window !== "undefined") {
        resizeBound = true;
        window.addEventListener("resize", onResize);
    }
}
