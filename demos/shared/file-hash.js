/**
 * File hash input for Scramble (and any later hash demo).
 *
 * Paste Message stays at the few-KB cap (`input-cap.js`). A file is a
 * separate path: ~10 MB first ceiling, never dumped into the textarea.
 * The Message card shows filename + human size. Bytes are hashed in
 * chunks (Web Worker when available) so the main thread stays usable.
 *
 * Teach / Play still go through `createLiveDigest` / `ensureTimeline`.
 * Large files keep Digest correct and skip the nybble→turns leave list.
 */

import { DEMO_INPUT_MAX_CHARS } from "./input-cap.js";

export const DEMO_FILE_MAX_BYTES = 10 * 1024 * 1024;
export const DEMO_FILE_TEACH_MAX_BYTES = DEMO_INPUT_MAX_CHARS;
export const DEMO_FILE_CHUNK_BYTES = 32 * 1024;

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

export function dropTeachTrace(state) {
    if (!state || typeof state !== "object") return;
    if (Array.isArray(state.steps)) {
        state.steps.length = 0;
        return;
    }
    if (state.steps && typeof state.steps === "object") {
        try {
            state.steps.length = 0;
        } catch {
            state.steps = [];
        }
    }
}

/**
 * Incremental Scramble hasher on the host-facing generated API.
 * Fine for tests and tiny messages. Each `update` converts the whole
 * teach list back to host objects — do not use this for multi-KB files.
 * The worker uses `createSilentHasher` on the impl instead.
 */
export function createIncrementalHasher({ scramble_v1, scramble_v2, update, evaluate }) {
    let state = null;

    return {
        start(version) {
            state = Number(version) === 1 ? scramble_v1() : scramble_v2();
            dropTeachTrace(state);
        },
        push(bytes) {
            if (!state) throw new Error("Hasher was not started.");
            const list = bytes instanceof Uint8Array ? Array.from(bytes) : Array.from(bytes || []);
            if (!list.length) return;
            update(state, list);
            dropTeachTrace(state);
        },
        finish() {
            if (!state) throw new Error("Hasher was not started.");
            const result = evaluate(state);
            const digest = result?.digest ? Array.from(result.digest) : [];
            dropTeachTrace(state);
            state = null;
            return { digest };
        },
    };
}

export function asBytes(bytes) {
    if (bytes instanceof Uint8Array) return bytes;
    if (bytes instanceof ArrayBuffer) return new Uint8Array(bytes);
    return new Uint8Array(bytes || []);
}

function silentRuleB(impl, rt, cube) {
    const c = rt.dup(rt.at(cube, impl.cubie_at(cube, 1n, 1n, 1n)));
    return impl.reorient(cube, c.yp, c.zp);
}

function silentV2(impl, rt, cube, n) {
    cube = impl.apply_turns(cube, rt.at(impl.v2_a, n), 1n);
    cube = impl.apply_turns(cube, rt.at(impl.v2_b, n), 1n);
    return silentRuleB(impl, rt, cube);
}

function silentV1Block(impl, rt, cube, ny, block) {
    const base = block * 8n;
    for (let k = 0n; k <= 7n; k += 1n) {
        const n = rt.at(ny, base + k);
        cube = impl.apply_turns(cube, rt.at(impl.v1_face, n), rt.at(impl.v1_turns, n));
    }
    return silentRuleB(impl, rt, cube);
}

/**
 * Digest-only walk: same turns as generated update/evaluate, no teach
 * Step / facelets list. Required for images — a JPEG is far above 4 KiB
 * and `push_step` makes the host/impl update path stall.
 */
export function createSilentHasher({ impl, rt }) {
    let version = 2;
    let cube = null;
    let message = null;
    let processed = 0;

    const nyOf = (bytes) => impl.nybbles_of(rt.host_list(bytes, (v) => rt.host_int(v)));

    return {
        start(nextVersion) {
            version = Number(nextVersion) === 1 ? 1 : 2;
            cube = impl.solved_cube();
            message = [];
            processed = 0;
        },
        push(bytes) {
            if (!cube) throw new Error("Hasher was not started.");
            const chunk = asBytes(bytes);
            if (!chunk.length) return;
            for (let i = 0; i < chunk.length; i += 1) message.push(chunk[i]);
            const ny = nyOf(chunk);
            const added = Number(ny.length);
            if (version === 1) {
                const all = nyOf(message);
                const len = Number(all.length);
                while (processed + 8 <= len) {
                    cube = silentV1Block(impl, rt, cube, all, BigInt(processed / 8));
                    processed += 8;
                }
            } else {
                for (let i = 0; i < added; i += 1) {
                    cube = silentV2(impl, rt, cube, rt.at(ny, BigInt(i)));
                }
                processed += added;
            }
        },
        finish() {
            if (!cube) throw new Error("Hasher was not started.");
            const ny = nyOf(message);
            const padded = impl.pad_tape(ny, version === 1 ? 1n : 2n);
            const padLen = Number(padded.length);
            if (version === 1) {
                while (processed + 8 <= padLen) {
                    cube = silentV1Block(impl, rt, cube, padded, BigInt(processed / 8));
                    processed += 8;
                }
            } else {
                for (let i = processed; i < padLen; i += 1) {
                    cube = silentV2(impl, rt, cube, rt.at(padded, BigInt(i)));
                }
            }
            cube = impl.apply_turns(cube, 4n, 2n);
            cube = impl.apply_turns(cube, 5n, 2n);
            cube = impl.reorient(cube, 1n, 6n);
            const raw = impl.index_bytes(cube);
            const digest = Array.from(raw, (v) => rt.int_out(v));
            cube = null;
            message = null;
            return { digest };
        },
    };
}

/**
 * Same math, on sudoc's internal records. Drop `steps` after each
 * chunk so we never convert a leave list through the host wrapper.
 * Digest still comes from generated `evaluate` (pad + closer + seat).
 */
export function createGeneratedHasher({ impl, rt }) {
    let state = null;

    const emptySteps = () => (typeof rt.lst === "function" ? rt.lst([]) : []);

    return {
        start(version) {
            state = Number(version) === 1 ? impl.scramble_v1() : impl.scramble_v2();
            if (state) state.steps = emptySteps();
        },
        push(bytes) {
            if (!state) throw new Error("Hasher was not started.");
            const chunk = asBytes(bytes);
            if (!chunk.length) return;
            const list = rt.host_list(chunk, (v) => rt.host_int(v));
            state = impl.update(state, list);
            if (state) state.steps = emptySteps();
        },
        finish() {
            if (!state) throw new Error("Hasher was not started.");
            const out = impl.evaluate(state);
            const result = Array.isArray(out) ? out[0] : out;
            const raw = result?.digest || [];
            const digest = Array.from(raw, (v) => Number(rt.int_out(v)));
            state = null;
            return { digest };
        },
    };
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

function postWorker(worker, data, transfer) {
    if (transfer?.length) worker.postMessage(data, transfer);
    else worker.postMessage(data);
}

/**
 * Hash `file` with the demo worker. `createWorker` / `hashInline` are
 * test seams. Product path uses a module Worker so `evaluate` never
 * runs on the main thread for the file.
 */
export async function hashFile(file, {
    version = 2,
    workerUrl,
    chunkBytes = DEMO_FILE_CHUNK_BYTES,
    onProgress,
    signal,
    createWorker,
    hashInline,
    fallback,
    readyMs = 8000,
} = {}) {
    const check = checkFileSize(file);
    if (!check.ok) throw new Error(check.message);

    if (typeof hashInline === "function") {
        return hashInline({ file, version, onProgress, signal, chunkBytes });
    }

    const runFallback = (err) => {
        if (typeof fallback !== "function") throw err;
        return fallback({ file, version, onProgress, signal, chunkBytes, error: err });
    };

    const href = typeof workerUrl === "string" ? workerUrl : workerUrl ? String(workerUrl) : "";
    const canWorker = Boolean(href) && (createWorker || typeof Worker === "function");
    if (!canWorker) {
        return runFallback(new Error("File hashing needs a Web Worker."));
    }

    let worker;
    try {
        worker = createWorker
            ? createWorker(href)
            : new Worker(href, { type: "module" });
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
        postWorker(worker, { type: "start", version });
        if (readyMs > 0) {
            readyTimer = setTimeout(() => {
                failAll(new Error("Could not hash this file."));
            }, readyMs);
        }
        await waitReply("ready");
        clearReady();
        await readFileChunks(file, {
            chunkBytes,
            signal,
            async onChunk(bytes, progress) {
                const copy = bytes.slice();
                postWorker(worker, { type: "chunk", bytes: copy }, [copy.buffer]);
                await waitReply("progress");
                onProgress?.(progress);
            },
        });
        postWorker(worker, { type: "finish" });
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

export function showFileChip({ input, fileChip, fileNameEl, file }) {
    if (input) input.hidden = true;
    if (fileChip) fileChip.hidden = false;
    if (fileNameEl) fileNameEl.textContent = formatFileLabel(file);
}

export function hideFileChip({ input, fileChip, fileNameEl }) {
    if (input) input.hidden = false;
    if (fileChip) fileChip.hidden = true;
    if (fileNameEl) fileNameEl.textContent = "";
}
