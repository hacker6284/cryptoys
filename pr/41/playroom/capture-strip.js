/**
 * Motion proof-strip harness. Off unless `?debugCapture=1`.
 * Samples the playroom canvas on named beats and on a steady clock
 * so enter/leave can be audited as a contact sheet — not one still.
 *
 * Production path: `installCapture` returns no-ops. No rAF work,
 * no overlay, no toDataURL.
 */

import { onMarkBeat } from "./motion.js";

export const CAPTURE_INTERVAL_MS = 240;

export function captureEnabled(search = typeof location !== "undefined" ? location.search : "") {
    try {
        return new URLSearchParams(search).get("debugCapture") === "1";
    } catch {
        return false;
    }
}

export function sheetLayout(count, { cols = 6, cellW = 320, cellH = 200 } = {}) {
    const n = Math.max(0, count | 0);
    const rows = Math.max(1, Math.ceil((n || 1) / cols));
    return {
        cols,
        rows,
        cellW,
        cellH,
        width: cols * cellW,
        height: rows * cellH,
    };
}

export function slugBeat(beat) {
    return String(beat || "frame")
        .toLowerCase()
        .replace(/[^a-z0-9]+/g, "-")
        .replace(/^-|-$/g, "") || "frame";
}

function noopCapture() {
    return {
        enabled: false,
        begin() {},
        end() {
            return null;
        },
        tick() {},
        get sequences() {
            return {};
        },
        peek() {
            return null;
        },
        async exportSheet() {
            return null;
        },
    };
}

function drawLabel(ctx, text, w) {
    ctx.save();
    ctx.font = "600 18px IBM Plex Sans, Helvetica Neue, sans-serif";
    const pad = 10;
    const tw = Math.min(w - 16, ctx.measureText(text).width + pad * 2);
    ctx.fillStyle = "rgba(10, 8, 6, 0.72)";
    ctx.fillRect(8, 8, tw, 28);
    ctx.fillStyle = "#f4efe6";
    ctx.fillText(text, 8 + pad, 28);
    ctx.restore();
}

function frameLabel(beat, ms) {
    return `${beat}  ${Math.round(ms)}ms`;
}

/**
 * Build a contact sheet from already-labeled data-URL frames.
 * Browser-only (needs Canvas). Returns a PNG data URL.
 */
export function composeContactSheet(frames, opts = {}) {
    if (typeof document === "undefined") return "";
    const layout = sheetLayout(frames.length, opts);
    const sheet = document.createElement("canvas");
    sheet.width = layout.width;
    sheet.height = layout.height;
    const ctx = sheet.getContext("2d");
    ctx.fillStyle = "#0e0b09";
    ctx.fillRect(0, 0, layout.width, layout.height);
    const jobs = frames.map((frame, i) => new Promise((resolve) => {
        const img = new Image();
        img.onload = () => {
            const col = i % layout.cols;
            const row = Math.floor(i / layout.cols);
            const x = col * layout.cellW;
            const y = row * layout.cellH;
            ctx.drawImage(img, x, y, layout.cellW, layout.cellH);
            ctx.strokeStyle = "rgba(244,239,230,0.18)";
            ctx.strokeRect(x + 0.5, y + 0.5, layout.cellW - 1, layout.cellH - 1);
            resolve();
        };
        img.onerror = () => resolve();
        img.src = frame.dataUrl;
    }));
    return Promise.all(jobs).then(() => sheet.toDataURL("image/png"));
}

export function installCapture(canvas, { intervalMs = CAPTURE_INTERVAL_MS } = {}) {
    if (!canvas || !captureEnabled()) return noopCapture();

    const root = document.documentElement;
    root.dataset.playroomCapture = "1";

    const scratch = document.createElement("canvas");
    const sequences = {};
    let active = null;
    let lastSample = -Infinity;
    let unlisten = () => {};

    function snapshot(beat) {
        if (!active) return;
        const w = canvas.width || canvas.clientWidth || 1280;
        const h = canvas.height || canvas.clientHeight || 800;
        if (!(w > 0 && h > 0)) return;
        scratch.width = w;
        scratch.height = h;
        const ctx = scratch.getContext("2d");
        ctx.drawImage(canvas, 0, 0, w, h);
        const ms = performance.now() - active.started;
        const label = frameLabel(beat || active.beat, ms);
        drawLabel(ctx, label, w);
        active.frames.push({
            ms: Math.round(ms),
            beat: beat || active.beat,
            dataUrl: scratch.toDataURL("image/jpeg", 0.74),
        });
        lastSample = performance.now();
    }

    function begin(name) {
        const id = String(name || "seq");
        active = {
            name: id,
            beat: "start",
            started: performance.now(),
            frames: [],
        };
        lastSample = -Infinity;
        return id;
    }

    function end() {
        if (!active) return null;
        snapshot(active.beat || "end");
        const done = {
            name: active.name,
            frames: active.frames,
            sheet: "",
        };
        sequences[done.name] = done;
        root.dataset.captureSeq = done.name;
        root.dataset.captureFrames = String(done.frames.length);
        active = null;
        return done;
    }

    async function exportSheet(name) {
        const seq = name ? sequences[name] : null;
        if (!seq) return null;
        if (!seq.sheet) seq.sheet = await composeContactSheet(seq.frames);
        return seq;
    }

    function tick() {
        if (!active) return;
        const now = performance.now();
        if (now - lastSample >= intervalMs) snapshot(active.beat);
    }

    unlisten = onMarkBeat((beat) => {
        if (!active) return;
        active.beat = beat;
        snapshot(beat);
        root.dataset.beat = beat;
    });

    const api = {
        enabled: true,
        begin,
        end,
        exportSheet,
        tick,
        snapshot,
        get sequences() {
            return sequences;
        },
        peek() {
            return active
                ? { name: active.name, beat: active.beat, frames: active.frames.length }
                : null;
        },
        dispose() {
            unlisten();
            active = null;
        },
    };

    if (typeof window !== "undefined") window.__playroomCapture = api;
    return api;
}
