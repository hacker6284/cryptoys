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
export const DEMO_FILE_CHUNK_BYTES = 8 * 1024;
export const DEMO_FILE_HOST_CHUNK_BYTES = 4 * 1024;
export const DEMO_FILE_WORKER_READY_MS = 1000;
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

const V2_A = [0, 0, 0, 0, 1, 1, 2, 2, 4, 4, 5, 4, 3, 4, 2, 2];
const V2_B = [2, 4, 3, 5, 2, 4, 0, 1, 0, 1, 0, 2, 0, 3, 4, 5];
const V1_FACE = [0, 0, 1, 1, 3, 3, 2, 2, 4, 4, 5, 5, 0, 1, 3, 2];
const V1_TURNS = [1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2];
const TAPE_F = [6, 0, 7, 1, 8, 2, 9, 3];
const TAPE_I = [6, 0, 7, 1];
const CX = [1, -1, -1, 1, 1, -1, -1, 1];
const CY = [1, 1, 1, 1, -1, -1, -1, -1];
const CZ = [1, 1, -1, -1, 1, 1, -1, -1];
const CAX = [2, 0, 4, 2, 4, 1, 2, 1, 5, 2, 5, 0, 3, 4, 0, 3, 1, 4, 3, 5, 1, 3, 0, 5];
const EX = [1, 0, -1, 0, 1, 0, -1, 0, 1, -1, -1, 1];
const EY = [1, 1, 1, 1, -1, -1, -1, -1, 0, 0, 0, 0];
const EZ = [0, 1, 0, -1, 0, 1, 0, -1, 1, 1, -1, -1];
const EAX = [2, 0, 2, 4, 2, 1, 2, 5, 3, 0, 3, 4, 3, 1, 3, 5, 4, 0, 4, 1, 5, 1, 5, 0];

function solvedFastCube() {
    const cube = [];
    for (let x = -1; x <= 1; x += 1) {
        for (let y = -1; y <= 1; y += 1) {
            for (let z = -1; z <= 1; z += 1) {
                if (!x && !y && !z) continue;
                cube.push({
                    x, y, z,
                    xp: x === 1 ? 3 : 0,
                    xn: x === -1 ? 4 : 0,
                    yp: y === 1 ? 1 : 0,
                    yn: y === -1 ? 2 : 0,
                    zp: z === 1 ? 6 : 0,
                    zn: z === -1 ? 5 : 0,
                });
            }
        }
    }
    return cube;
}

function rotXyz(face, x, y, z) {
    if (face === 0 || face === 1) return [z, y, -x];
    if (face === 2) return [x, z, -y];
    if (face === 3) return [x, -z, y];
    if (face === 4) return [y, -x, z];
    return [-y, x, z];
}

function writeAxis(xp, xn, yp, yn, zp, zn, x, y, z, color) {
    if (x === 1 && y === 0 && z === 0) return [color, xn, yp, yn, zp, zn];
    if (x === -1 && y === 0 && z === 0) return [xp, color, yp, yn, zp, zn];
    if (x === 0 && y === 1 && z === 0) return [xp, xn, color, yn, zp, zn];
    if (x === 0 && y === -1 && z === 0) return [xp, xn, yp, color, zp, zn];
    if (x === 0 && y === 0 && z === 1) return [xp, xn, yp, yn, color, zn];
    return [xp, xn, yp, yn, zp, color];
}

function turnCubie(c, face) {
    const [nx, ny, nz] = rotXyz(face, c.x, c.y, c.z);
    let xp = 0;
    let xn = 0;
    let yp = 0;
    let yn = 0;
    let zp = 0;
    let zn = 0;
    const paint = (ax, ay, az, color) => {
        if (!color) return;
        const [rx, ry, rz] = rotXyz(face, ax, ay, az);
        [xp, xn, yp, yn, zp, zn] = writeAxis(xp, xn, yp, yn, zp, zn, rx, ry, rz, color);
    };
    paint(1, 0, 0, c.xp);
    paint(-1, 0, 0, c.xn);
    paint(0, 1, 0, c.yp);
    paint(0, -1, 0, c.yn);
    paint(0, 0, 1, c.zp);
    paint(0, 0, -1, c.zn);
    c.x = nx;
    c.y = ny;
    c.z = nz;
    c.xp = xp;
    c.xn = xn;
    c.yp = yp;
    c.yn = yn;
    c.zp = zp;
    c.zn = zn;
}

function onFace(face, x, y, z) {
    if (face === 0) return y === 1;
    if (face === 1) return y === -1;
    if (face === 2) return x === 1;
    if (face === 3) return x === -1;
    if (face === 4) return z === 1;
    return z === -1;
}

function applyTurns(cube, face, turns) {
    const n = Number(turns) || 0;
    for (let t = 0; t < n; t += 1) {
        for (let i = 0; i < cube.length; i += 1) {
            const c = cube[i];
            if (onFace(face, c.x, c.y, c.z)) turnCubie(c, face);
        }
    }
}

function stickerOn(c, axis) {
    if (axis === 0) return c.xp;
    if (axis === 1) return c.xn;
    if (axis === 2) return c.yp;
    if (axis === 3) return c.yn;
    if (axis === 4) return c.zp;
    return c.zn;
}

function cubieAt(cube, x, y, z) {
    for (let i = 0; i < cube.length; i += 1) {
        const c = cube[i];
        if (c.x === x && c.y === y && c.z === z) return i;
    }
    return 0;
}

function hasColor(c, color) {
    return c.xp === color || c.xn === color || c.yp === color || c.yn === color || c.zp === color || c.zn === color;
}

function centerDir(cube, color) {
    for (let i = 0; i < cube.length; i += 1) {
        const c = cube[i];
        const zeros = (c.x === 0 ? 1 : 0) + (c.y === 0 ? 1 : 0) + (c.z === 0 ? 1 : 0);
        if (zeros === 2 && hasColor(c, color)) return [c.x, c.y, c.z];
    }
    return [0, 0, 0];
}

function mulVec(m, x, y, z) {
    return [
        m[0][0] * x + m[0][1] * y + m[0][2] * z,
        m[1][0] * x + m[1][1] * y + m[1][2] * z,
        m[2][0] * x + m[2][1] * y + m[2][2] * z,
    ];
}

function applyMatrix(cube, m) {
    for (let i = 0; i < cube.length; i += 1) {
        const c = cube[i];
        const [nx, ny, nz] = mulVec(m, c.x, c.y, c.z);
        let xp = 0;
        let xn = 0;
        let yp = 0;
        let yn = 0;
        let zp = 0;
        let zn = 0;
        const paint = (ax, ay, az, color) => {
            if (!color) return;
            const [rx, ry, rz] = mulVec(m, ax, ay, az);
            [xp, xn, yp, yn, zp, zn] = writeAxis(xp, xn, yp, yn, zp, zn, rx, ry, rz, color);
        };
        paint(1, 0, 0, c.xp);
        paint(-1, 0, 0, c.xn);
        paint(0, 1, 0, c.yp);
        paint(0, -1, 0, c.yn);
        paint(0, 0, 1, c.zp);
        paint(0, 0, -1, c.zn);
        c.x = nx;
        c.y = ny;
        c.z = nz;
        c.xp = xp;
        c.xn = xn;
        c.yp = yp;
        c.yn = yn;
        c.zp = zp;
        c.zn = zn;
    }
}

function reorient(cube, up, front) {
    const [ux, uy, uz] = centerDir(cube, up);
    const [px, py, pz] = centerDir(cube, front);
    if (ux === 0 && uy === 1 && uz === 0 && px === 0 && py === 0 && pz === 1) return;
    const vx = uy * pz - uz * py;
    const vy = uz * px - ux * pz;
    const vz = ux * py - uy * px;
    applyMatrix(cube, [[vx, vy, vz], [ux, uy, uz], [px, py, pz]]);
}

function ruleB(cube) {
    const c = cube[cubieAt(cube, 1, 1, 1)];
    reorient(cube, c.yp, c.zp);
}

function applyV2(cube, n) {
    applyTurns(cube, V2_A[n], 1);
    applyTurns(cube, V2_B[n], 1);
    ruleB(cube);
}

function applyV1Block(cube, ny, block) {
    const base = block * 8;
    for (let k = 0; k < 8; k += 1) {
        const n = ny[base + k];
        applyTurns(cube, V1_FACE[n], V1_TURNS[n]);
    }
    ruleB(cube);
}

function nybblesOf(bytes) {
    const out = [];
    for (let i = 0; i < bytes.length; i += 1) {
        const b = bytes[i] & 255;
        out.push(b >> 4, b & 15);
    }
    return out;
}

function padTape(ny, version) {
    const out = ny.slice();
    out.push(8);
    if (version === 1) {
        const n = (8 - (out.length % 8)) % 8;
        for (let i = 0; i < n; i += 1) out.push(TAPE_F[i]);
        const remaining = 24 - out.length;
        for (let i = 0; i < remaining; i += 1) out.push(TAPE_F[i % 8]);
        return out;
    }
    const remaining = 12 - out.length;
    for (let k = 0; k < remaining; k += 1) out.push(TAPE_I[k % 4]);
    return out;
}

function has3(a, b, c, color) {
    return a === color || b === color || c === color;
}

function cornerPiece(a, b, c) {
    const w = has3(a, b, c, 1);
    const y = has3(a, b, c, 2);
    const r = has3(a, b, c, 3);
    const o = has3(a, b, c, 4);
    const bl = has3(a, b, c, 5);
    const g = has3(a, b, c, 6);
    if (w && g && r) return 0;
    if (w && g && o) return 1;
    if (w && bl && o) return 2;
    if (w && bl && r) return 3;
    if (y && g && r) return 4;
    if (y && g && o) return 5;
    if (y && bl && o) return 6;
    if (y && bl && r) return 7;
    return 0;
}

function edgePiece(a, b) {
    if ((a === 3 && b === 1) || (a === 1 && b === 3)) return 0;
    if ((a === 6 && b === 1) || (a === 1 && b === 6)) return 1;
    if ((a === 4 && b === 1) || (a === 1 && b === 4)) return 2;
    if ((a === 5 && b === 1) || (a === 1 && b === 5)) return 3;
    if ((a === 3 && b === 2) || (a === 2 && b === 3)) return 4;
    if ((a === 6 && b === 2) || (a === 2 && b === 6)) return 5;
    if ((a === 4 && b === 2) || (a === 2 && b === 4)) return 6;
    if ((a === 5 && b === 2) || (a === 2 && b === 5)) return 7;
    if ((a === 6 && b === 3) || (a === 3 && b === 6)) return 8;
    if ((a === 6 && b === 4) || (a === 4 && b === 6)) return 9;
    if ((a === 5 && b === 4) || (a === 4 && b === 5)) return 10;
    if ((a === 5 && b === 3) || (a === 3 && b === 5)) return 11;
    return 0;
}

function fact(n) {
    let r = 1n;
    for (let i = 2n; i <= n; i += 1n) r *= i;
    return r;
}

function rankPerm(p) {
    let total = 0n;
    const last = BigInt(p.length - 1);
    for (let n = 0; n < p.length; n += 1) {
        let inv = 0n;
        for (let j = n + 1; j < p.length; j += 1) {
            if (p[j] < p[n]) inv += 1n;
        }
        total += inv * fact(last - BigInt(n));
    }
    return total;
}

function digestBytes(s3, ori) {
    const buf = new Array(12).fill(0n);
    let v = s3;
    for (let i = 0; i < 12; i += 1) {
        buf[i] = v % 256n;
        v /= 256n;
    }
    for (let bit = 1; bit <= 11; bit += 1) {
        let carry = 0n;
        for (let j = 0; j < 12; j += 1) {
            const cur = buf[j] * 2n + carry;
            buf[j] = cur % 256n;
            carry = cur / 256n;
        }
    }
    let rest = ori;
    for (let j = 0; j < 12; j += 1) {
        const cur = buf[j] + (rest % 256n);
        buf[j] = cur % 256n;
        rest = rest / 256n + cur / 256n;
    }
    const out = [];
    for (let j = 8; j >= 0; j -= 1) out.push(Number(buf[j]));
    return out;
}

function indexBytes(cube) {
    const perm = [];
    let oriAcc = 0n;
    let pow3 = 1n;
    for (let i = 0; i < 8; i += 1) {
        const c = cube[cubieAt(cube, CX[i], CY[i], CZ[i])];
        const a0 = stickerOn(c, CAX[i * 3]);
        const a1 = stickerOn(c, CAX[i * 3 + 1]);
        const a2 = stickerOn(c, CAX[i * 3 + 2]);
        perm.push(cornerPiece(a0, a1, a2));
        let slot = 0n;
        if (a1 === 1 || a1 === 2) slot = 1n;
        if (a2 === 1 || a2 === 2) slot = 2n;
        if (i < 7) {
            oriAcc += slot * pow3;
            pow3 *= 3n;
        }
    }
    let s3 = rankPerm(perm) * 2187n + oriAcc;
    const eperm = [];
    let eori = 0n;
    let bit = 1n;
    for (let i = 0; i < 12; i += 1) {
        const c = cube[cubieAt(cube, EX[i], EY[i], EZ[i])];
        const a0 = stickerOn(c, EAX[i * 2]);
        const a1 = stickerOn(c, EAX[i * 2 + 1]);
        eperm.push(edgePiece(a0, a1));
        if (i < 11) {
            const keep = a0 === 1 || a0 === 2 || a0 === 3 || a0 === 4;
            eori += (keep ? 0n : 1n) * bit;
            bit *= 2n;
        }
    }
    s3 = s3 * 239500800n + rankPerm(eperm) / 2n;
    return digestBytes(s3, eori);
}

/**
 * Same turns as generated update/evaluate, but a mutable JS cube — no
 * CowList / push_step. A real JPEG can finish and write Digest.
 */
export function createFastHasher() {
    let version = 2;
    let cube = null;
    let message = null;
    let processed = 0;

    return {
        start(nextVersion) {
            version = Number(nextVersion) === 1 ? 1 : 2;
            cube = solvedFastCube();
            message = [];
            processed = 0;
        },
        push(bytes) {
            if (!cube) throw new Error("Hasher was not started.");
            const chunk = asBytes(bytes);
            if (!chunk.length) return;
            for (let i = 0; i < chunk.length; i += 1) message.push(chunk[i]);
            const ny = nybblesOf(chunk);
            if (version === 1) {
                const all = nybblesOf(message);
                while (processed + 8 <= all.length) {
                    applyV1Block(cube, all, processed / 8);
                    processed += 8;
                }
            } else {
                for (let i = 0; i < ny.length; i += 1) applyV2(cube, ny[i]);
                processed += ny.length;
            }
        },
        finish() {
            if (!cube) throw new Error("Hasher was not started.");
            const padded = padTape(nybblesOf(message), version);
            if (version === 1) {
                while (processed + 8 <= padded.length) {
                    applyV1Block(cube, padded, processed / 8);
                    processed += 8;
                }
            } else {
                for (let i = processed; i < padded.length; i += 1) applyV2(cube, padded[i]);
            }
            applyTurns(cube, 4, 2);
            applyTurns(cube, 5, 2);
            reorient(cube, 1, 6);
            const digest = indexBytes(cube);
            cube = null;
            message = null;
            return { digest };
        },
    };
}

/** @deprecated use createFastHasher — kept so older worker/session imports resolve. */
export function createSilentHasher() {
    return createFastHasher();
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
 *
 * GitHub Pages serves the worker as `application/javascript` at the
 * real `import.meta.url` (not a blob — blob workers break relative
 * `./generated/*.mjs` imports). If `ready` is not posted within ~1s,
 * fall back to host silent hash so Digest cannot stall empty.
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
    readyMs = DEMO_FILE_WORKER_READY_MS,
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
    // Keep the Message textarea on its own row with the paperclip.
    // Filename lives on the next full-width row — never hide the field
    // or the chip slides up beside the clip.
    if (input) input.hidden = false;
    if (fileChip) fileChip.hidden = false;
    if (fileNameEl) fileNameEl.textContent = formatFileLabel(file);
}

export function hideFileChip({ input, fileChip, fileNameEl }) {
    if (input) input.hidden = false;
    if (fileChip) fileChip.hidden = true;
    if (fileNameEl) fileNameEl.textContent = "";
}
