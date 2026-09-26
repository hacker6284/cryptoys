/**
 * Motion proof-strip harness. Off unless `?debugCapture=1`.
 *
 * Composition (one sequence):
 *   fixed-Δt grid  ∪  named beats  ∪  camera-accel spikes
 *
 * The grid is a constant clock for the whole enter/leave (200 ms of
 * play time — same CLOCK_STEP_MS-capped clock as director / beat-clock
 * / camera, so 60fps wall time ≈ play time). Beats and camAccel are
 * *additional* labeled frames when they fire. They do not reset or
 * redistribute the grid. Near-duplicates within ~1 frame are dropped.
 *
 * Production path: `installCapture` returns no-ops. No rAF work,
 * no overlay, no toDataURL.
 */

import { CLOCK_STEP_MS } from "./constants.js";
import { onMarkBeat } from "./motion.js";

export const CAPTURE_INTERVAL_MS = 200;
export const CAPTURE_DEDUPE_MS = CLOCK_STEP_MS;
export const CAPTURE_MAX_WIDTH = 480;
export const CAM_ACCEL_POS = 42;
export const CAM_ACCEL_LOOK = 30;
export const CAM_ACCEL_COOLDOWN_MS = 420;

/**
 * True when an RGBA buffer is nearly black. Used to drop the first
 * pre-render canvas sample so strips do not open on a blank frame.
 */
export function frameIsBlank(pixels, { minLit = 0.02 } = {}) {
    if (!pixels?.length) return true;
    const n = Math.floor(pixels.length / 4);
    if (n <= 0) return true;
    let lit = 0;
    for (let i = 0; i < n; i += 1) {
        const o = i * 4;
        if (pixels[o] + pixels[o + 1] + pixels[o + 2] > 24) lit += 1;
    }
    return lit < n * minLit;
}

function len3(v) {
    return Math.hypot(v.x, v.y, v.z);
}

function sub3(a, b) {
    return { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z };
}

function dot3(a, b) {
    return a.x * b.x + a.y * b.y + a.z * b.z;
}

function readVec(value) {
    if (!value) return null;
    const x = value.x;
    const y = value.y;
    const z = value.z;
    if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) return null;
    return { x, y, z };
}

/**
 * Finite-difference acceleration of camera position and look, plus
 * a velocity-reversal flag for turnarounds.
 */
export function cameraAccel(prevVel, vel, dtSec) {
    if (!(dtSec > 0) || !prevVel || !vel) {
        return { pos: 0, look: 0, reverse: false };
    }
    const aPos = len3(sub3(vel.pos, prevVel.pos)) / dtSec;
    const aLook = len3(sub3(vel.look, prevVel.look)) / dtSec;
    const reverse = (dot3(vel.pos, prevVel.pos) < 0 && len3(vel.pos) > 0.35 && len3(prevVel.pos) > 0.35)
        || (dot3(vel.look, prevVel.look) < 0 && len3(vel.look) > 0.25 && len3(prevVel.look) > 0.25);
    return { pos: aPos, look: aLook, reverse };
}

export function isCamAccelSpike(accel, {
    posMin = CAM_ACCEL_POS,
    lookMin = CAM_ACCEL_LOOK,
} = {}, vel = null, prevVel = null) {
    if (!accel) return false;
    if (accel.reverse) return true;
    const onset = prevVel && vel
        && len3(prevVel.pos) < 0.45
        && len3(vel.pos) > 1.15;
    if (onset && (accel.pos >= posMin * 0.55 || accel.look >= lookMin * 0.55)) return true;
    return accel.pos >= posMin || accel.look >= lookMin;
}

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
    let lastNow = 0;
    let playElapsed = 0;
    let nextGridAt = 0;
    let lastAnyAt = -Infinity;
    let lastAccelAt = -Infinity;
    let pendingBeat = false;
    let pendingAccel = false;
    let lastPos = null;
    let lastLook = null;
    let lastVel = null;
    let unlisten = () => {};

    function snapshot(beat) {
        if (!active) return false;
        const w = canvas.width || canvas.clientWidth || 1280;
        const h = canvas.height || canvas.clientHeight || 800;
        if (!(w > 0 && h > 0)) return false;
        const scale = Math.min(1, CAPTURE_MAX_WIDTH / w);
        const dw = Math.max(1, Math.round(w * scale));
        const dh = Math.max(1, Math.round(h * scale));
        scratch.width = dw;
        scratch.height = dh;
        const ctx = scratch.getContext("2d");
        ctx.drawImage(canvas, 0, 0, dw, dh);
        const probe = Math.min(48, dw);
        const probeH = Math.min(32, dh);
        if (frameIsBlank(ctx.getImageData(0, 0, probe, probeH).data)) return false;
        const ms = playElapsed;
        const label = frameLabel(beat || active.beat, ms);
        drawLabel(ctx, label, dw);
        active.frames.push({
            ms: Math.round(ms),
            beat: beat || active.beat,
            dataUrl: scratch.toDataURL("image/jpeg", 0.55),
        });
        lastAnyAt = playElapsed;
        return true;
    }

    function take(beat) {
        if (lastAnyAt >= 0 && playElapsed - lastAnyAt < CAPTURE_DEDUPE_MS) return false;
        return snapshot(beat);
    }

    function watchCamera(camera, lookTarget, dtMs) {
        const pos = readVec(camera?.position);
        const look = readVec(lookTarget) || readVec(camera?.userData?.look);
        if (!pos || !look || !(dtMs > 0)) return;
        const dtSec = dtMs / 1000;
        if (lastPos && lastLook) {
            const vel = {
                pos: {
                    x: (pos.x - lastPos.x) / dtSec,
                    y: (pos.y - lastPos.y) / dtSec,
                    z: (pos.z - lastPos.z) / dtSec,
                },
                look: {
                    x: (look.x - lastLook.x) / dtSec,
                    y: (look.y - lastLook.y) / dtSec,
                    z: (look.z - lastLook.z) / dtSec,
                },
            };
            if (lastVel && playElapsed - lastAccelAt >= CAM_ACCEL_COOLDOWN_MS) {
                const accel = cameraAccel(lastVel, vel, dtSec);
                if (isCamAccelSpike(accel, {}, vel, lastVel)) {
                    pendingAccel = true;
                    lastAccelAt = playElapsed;
                }
            }
            lastVel = vel;
        }
        lastPos = pos;
        lastLook = look;
    }

    function begin(name) {
        const id = String(name || "seq");
        active = {
            name: id,
            beat: "start",
            started: performance.now(),
            frames: [],
        };
        lastNow = 0;
        playElapsed = 0;
        nextGridAt = 0;
        lastAnyAt = -Infinity;
        lastAccelAt = -Infinity;
        pendingBeat = true;
        pendingAccel = false;
        lastPos = null;
        lastLook = null;
        lastVel = null;
        return id;
    }

    function end() {
        if (!active) return null;
        take(active.beat || "end");
        const done = {
            name: active.name,
            frames: active.frames,
            sheet: "",
        };
        sequences[done.name] = done;
        root.dataset.captureSeq = done.name;
        root.dataset.captureFrames = String(done.frames.length);
        active = null;
        pendingBeat = false;
        pendingAccel = false;
        return done;
    }

    async function exportSheet(name) {
        const seq = name ? sequences[name] : null;
        if (!seq) return null;
        if (!seq.sheet) seq.sheet = await composeContactSheet(seq.frames);
        return seq;
    }

    function tick(now = performance.now(), camera = null, lookTarget = null) {
        if (!active) return;
        if (!lastNow) lastNow = now;
        const dtMs = Math.min(CLOCK_STEP_MS, Math.max(0, now - lastNow));
        lastNow = now;
        playElapsed += dtMs;
        watchCamera(camera, lookTarget, dtMs);

        if (pendingBeat && take(active.beat)) pendingBeat = false;
        else if (pendingAccel && take("camAccel")) pendingAccel = false;

        if (playElapsed >= nextGridAt) {
            if (playElapsed - lastAnyAt >= CAPTURE_DEDUPE_MS || lastAnyAt < 0) {
                take(active.beat || "tick");
            }
            nextGridAt += intervalMs;
            if (nextGridAt <= playElapsed) {
                nextGridAt = Math.floor(playElapsed / intervalMs) * intervalMs + intervalMs;
            }
        }
    }

    unlisten = onMarkBeat((beat) => {
        if (!active) return;
        active.beat = beat;
        pendingBeat = true;
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
