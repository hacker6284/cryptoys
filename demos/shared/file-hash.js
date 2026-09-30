/**
 * File input for a hash demo's Message field.
 *
 * Paste Message stays at the few-KB cap (`input-cap.js`). A file is a
 * separate path: ~10 MB first ceiling, never dumped into the textarea.
 * The Message card shows filename + human size. The demo's worker
 * hashes the bytes so the main thread stays usable.
 *
 * Teach / Play still go through `createLiveDigest` / `ensureTimeline`.
 * Large files keep Digest correct and skip the nybble→turns leave list.
 */

import { DEMO_INPUT_MAX_CHARS } from "./input-cap.js";

export const DEMO_FILE_MAX_BYTES = 10 * 1024 * 1024;
export const DEMO_FILE_TEACH_MAX_BYTES = DEMO_INPUT_MAX_CHARS;
export const DEMO_FILE_CHUNK_BYTES = 32 * 1024;
export const DEMO_FILE_WORKER_READY_MS = 4000;
export const DEMO_FILE_BUSY_MS = 200;
export const DEMO_FILE_DETERMINATE_BYTES = 1024 * 1024;

export function formatFileSize(bytes) {
    const n = Number(bytes) || 0;
    if (n < 1024) return `${n} B`;
    if (n < 1024 * 1024) {
        const kb = n / 1024;
        return kb >= 10 ? `${Math.round(kb)} KB` : `${kb.toFixed(1)} KB`;
    }
    const mb = n / (1024 * 1024);
    return mb >= 10 ? `${Math.round(mb)} MB` : `${mb.toFixed(1)} MB`;
}

export function formatFileLabel(file) {
    const name = String(file?.name || "file").trim() || "file";
    return `${name} · ${formatFileSize(file?.size)}`;
}

export function checkFileSize(file, maxBytes = DEMO_FILE_MAX_BYTES) {
    const size = Number(file?.size) || 0;
    if (size <= maxBytes) return { ok: true, size };
    return {
        ok: false,
        size,
        message: `Files can be up to ${formatFileSize(maxBytes)}.`,
    };
}

export function canWalkFile(file, maxBytes = DEMO_FILE_TEACH_MAX_BYTES) {
    return (Number(file?.size) || 0) <= maxBytes;
}

export async function readFileChunks(file, {
    chunkBytes = DEMO_FILE_CHUNK_BYTES,
    onChunk,
    signal,
} = {}) {
    const total = Number(file?.size) || 0;
    let offset = 0;
    while (offset < total) {
        if (signal?.aborted) {
            const err = new Error("Aborted");
            err.name = "AbortError";
            throw err;
        }
        const end = Math.min(offset + chunkBytes, total);
        const buf = await file.slice(offset, end).arrayBuffer();
        const bytes = new Uint8Array(buf);
        await onChunk?.(bytes, { processed: end, total });
        offset = end;
    }
    return { processed: offset, total };
}

function abortError() {
    const err = new Error("Aborted");
    err.name = "AbortError";
    return err;
}

/**
 * Hash `file` with the demo worker. `hashInline` is a test seam. Posts
 * one `hash` to a module Worker so the walk is off the main thread;
 * `done` carries the digest.
 *
 * GitHub Pages serves the worker as `application/javascript` at the
 * real `import.meta.url` (not a blob — blob workers break relative
 * imports). If `ready` is not posted within a few seconds, fall back
 * to host silent hash. A working worker is never killed for being slow:
 * a 1.5 MB V2 walk can take tens of seconds and must still post `done`.
 */
export async function hashFile(file, {
    version = 2,
    workerUrl,
    onProgress,
    signal,
    hashInline,
    fallback,
    readyMs = DEMO_FILE_WORKER_READY_MS,
} = {}) {
    const check = checkFileSize(file);
    if (!check.ok) throw new Error(check.message);

    if (typeof hashInline === "function") {
        return hashInline({ file, version, onProgress, signal });
    }

    const runFallback = (err) => {
        if (typeof fallback !== "function") throw err;
        return fallback({ file, version, onProgress, signal, error: err });
    };

    const href = typeof workerUrl === "string" ? workerUrl : workerUrl ? String(workerUrl) : "";
    const canWorker = Boolean(href) && typeof Worker === "function";
    if (!canWorker) {
        return runFallback(new Error("File hashing needs a Web Worker."));
    }

    let worker;
    try {
        worker = new Worker(href, { type: "module" });
    } catch (err) {
        return runFallback(err instanceof Error ? err : new Error("Could not hash this file."));
    }

    let settled = false;
    const pending = [];

    const waitReply = (expect) => new Promise((resolve, reject) => {
        pending.push({ expect, resolve, reject });
    });

    const failAll = (err) => {
        while (pending.length) pending.shift().reject(err);
    };

    const onMessage = (event) => {
        const msg = event?.data || {};
        if (msg.type === "error") {
            failAll(new Error(msg.message || "Could not hash this file."));
            return;
        }
        if (msg.type === "progress" && Number.isFinite(msg.processed) && Number.isFinite(msg.total)) {
            onProgress?.({ processed: msg.processed, total: msg.total });
        }
        const next = pending[0];
        if (next && next.expect === msg.type) {
            pending.shift();
            next.resolve(msg);
        }
    };
    const onError = () => {
        failAll(new Error("Could not hash this file."));
    };

    worker.addEventListener("message", onMessage);
    worker.addEventListener("error", onError);

    let readyTimer = 0;
    const clearReady = () => {
        if (readyTimer) clearTimeout(readyTimer);
        readyTimer = 0;
    };

    const stop = () => {
        clearReady();
        if (settled) return;
        settled = true;
        worker.removeEventListener("message", onMessage);
        worker.removeEventListener("error", onError);
        try {
            worker.terminate();
        } catch {
            // already gone
        }
    };

    if (signal) {
        if (signal.aborted) {
            stop();
            throw abortError();
        }
        signal.addEventListener("abort", () => {
            failAll(abortError());
            stop();
        }, { once: true });
    }

    try {
        worker.postMessage({ type: "start" });
        if (readyMs > 0) {
            readyTimer = setTimeout(() => {
                failAll(new Error("Could not hash this file."));
            }, readyMs);
        }
        await waitReply("ready");
        clearReady();

        const bytes = new Uint8Array(await file.arrayBuffer());
        if (signal?.aborted) throw abortError();
        worker.postMessage({ type: "hash", version, bytes });
        const done = await waitReply("done");
        const digest = Array.from(done.digest || []);
        if (!digest.length) throw new Error("Could not hash this file.");
        return { digest };
    } catch (err) {
        if (err?.name === "AbortError") throw err;
        return runFallback(err instanceof Error ? err : new Error("Could not hash this file."));
    } finally {
        stop();
    }
}

export function bindMessageFile({
    fileInput,
    fileBtn,
    fileClear,
    onPick,
    onClear,
    signal,
} = {}) {
    const opts = signal ? { signal } : undefined;
    fileBtn?.addEventListener("click", () => fileInput?.click(), opts);
    fileInput?.addEventListener("change", () => {
        const file = fileInput.files?.[0];
        if (fileInput) fileInput.value = "";
        if (file) onPick?.(file);
    }, opts);
    fileClear?.addEventListener("click", () => onClear?.(), opts);
}

export function showFileChip({ fileChip, fileNameEl, file }) {
    if (fileChip) fileChip.hidden = false;
    if (fileNameEl) fileNameEl.textContent = formatFileLabel(file);
}

export function hideFileChip({ fileChip, fileNameEl }) {
    if (fileChip) fileChip.hidden = true;
    if (fileNameEl) fileNameEl.textContent = "";
}
