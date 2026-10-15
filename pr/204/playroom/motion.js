/**
 * Small playroom motion helpers. Continuous hops, holds, and camera
 * tracks — no opacity fades, no hide/show cuts. Shared by Scramble
 * and DoubleDeal enter (follow-cam + hops), not one-off per-algo
 * spaghetti.
 *
 * Not a second animation engine. Tweens stay on `beat-clock`.
 * Shelf / toybox fly-in stays on `toy-director`. Camera follow lives
 * on the pose controller (`followTo`).
 */

import { easeInOutCubic, easeOutCubic, lerp } from "./beat-clock.js";

const beatListeners = [];

export function onMarkBeat(fn) {
    if (typeof fn !== "function") return () => {};
    beatListeners.push(fn);
    return () => {
        const i = beatListeners.indexOf(fn);
        if (i >= 0) beatListeners.splice(i, 1);
    };
}

export function markBeat(beat) {
    const root = typeof document !== "undefined" ? document.documentElement : null;
    if (root && (root.dataset.playroomDebug === "1" || root.dataset.playroomCapture === "1")) {
        root.dataset.beat = beat;
    }
    for (const listener of beatListeners) listener(beat);
}

function transformPoint(e, x, y, z) {
    return {
        x: e[0] * x + e[4] * y + e[8] * z + e[12],
        y: e[1] * x + e[5] * y + e[9] * z + e[13],
        z: e[2] * x + e[6] * y + e[10] * z + e[14],
    };
}

function multiply4(a, b) {
    const te = new Array(16);
    const a11 = a[0];
    const a12 = a[4];
    const a13 = a[8];
    const a14 = a[12];
    const a21 = a[1];
    const a22 = a[5];
    const a23 = a[9];
    const a24 = a[13];
    const a31 = a[2];
    const a32 = a[6];
    const a33 = a[10];
    const a34 = a[14];
    const a41 = a[3];
    const a42 = a[7];
    const a43 = a[11];
    const a44 = a[15];
    const b11 = b[0];
    const b12 = b[4];
    const b13 = b[8];
    const b14 = b[12];
    const b21 = b[1];
    const b22 = b[5];
    const b23 = b[9];
    const b24 = b[13];
    const b31 = b[2];
    const b32 = b[6];
    const b33 = b[10];
    const b34 = b[14];
    const b41 = b[3];
    const b42 = b[7];
    const b43 = b[11];
    const b44 = b[15];
    te[0] = a11 * b11 + a12 * b21 + a13 * b31 + a14 * b41;
    te[4] = a11 * b12 + a12 * b22 + a13 * b32 + a14 * b42;
    te[8] = a11 * b13 + a12 * b23 + a13 * b33 + a14 * b43;
    te[12] = a11 * b14 + a12 * b24 + a13 * b34 + a14 * b44;
    te[1] = a21 * b11 + a22 * b21 + a23 * b31 + a24 * b41;
    te[5] = a21 * b12 + a22 * b22 + a23 * b32 + a24 * b42;
    te[9] = a21 * b13 + a22 * b23 + a23 * b33 + a24 * b43;
    te[13] = a21 * b14 + a22 * b24 + a23 * b34 + a24 * b44;
    te[2] = a31 * b11 + a32 * b21 + a33 * b31 + a34 * b41;
    te[6] = a31 * b12 + a32 * b22 + a33 * b32 + a34 * b42;
    te[10] = a31 * b13 + a32 * b23 + a33 * b33 + a34 * b43;
    te[14] = a31 * b14 + a32 * b24 + a33 * b34 + a34 * b44;
    te[3] = a41 * b11 + a42 * b21 + a43 * b31 + a44 * b41;
    te[7] = a41 * b12 + a42 * b22 + a43 * b32 + a44 * b42;
    te[11] = a41 * b13 + a42 * b23 + a43 * b33 + a44 * b43;
    te[15] = a41 * b14 + a42 * b24 + a43 * b34 + a44 * b44;
    return te;
}

function eulerXYZToQuat(rot) {
    const x = rot?.x || 0;
    const y = rot?.y || 0;
    const z = rot?.z || 0;
    const c1 = Math.cos(x / 2);
    const c2 = Math.cos(y / 2);
    const c3 = Math.cos(z / 2);
    const s1 = Math.sin(x / 2);
    const s2 = Math.sin(y / 2);
    const s3 = Math.sin(z / 2);
    return {
        x: s1 * c2 * c3 + c1 * s2 * s3,
        y: c1 * s2 * c3 - s1 * c2 * s3,
        z: c1 * c2 * s3 + s1 * s2 * c3,
        w: c1 * c2 * c3 - s1 * s2 * s3,
    };
}

/** Column-major TRS, same layout as three.js `Matrix4.compose`. */
export function composeLocalMatrix(position, quaternion, scale) {
    const q = quaternion && Number.isFinite(quaternion.w)
        ? quaternion
        : { x: 0, y: 0, z: 0, w: 1 };
    const x = q.x || 0;
    const y = q.y || 0;
    const z = q.z || 0;
    const w = Number.isFinite(q.w) ? q.w : 1;
    const sx = scale?.x ?? 1;
    const sy = scale?.y ?? 1;
    const sz = scale?.z ?? 1;
    const x2 = x + x;
    const y2 = y + y;
    const z2 = z + z;
    const xx = x * x2;
    const xy = x * y2;
    const xz = x * z2;
    const yy = y * y2;
    const yz = y * z2;
    const zz = z * z2;
    const wx = w * x2;
    const wy = w * y2;
    const wz = w * z2;
    return [
        (1 - (yy + zz)) * sx,
        (xy + wz) * sx,
        (xz - wy) * sx,
        0,
        (xy - wz) * sy,
        (1 - (xx + zz)) * sy,
        (yz + wx) * sy,
        0,
        (xz + wy) * sz,
        (yz - wx) * sz,
        (1 - (xx + yy)) * sz,
        0,
        position?.x || 0,
        position?.y || 0,
        position?.z || 0,
        1,
    ];
}

function localMatrixOf(node) {
    if (node.matrixAutoUpdate === false && node.matrix?.elements?.length >= 16) {
        return node.matrix.elements;
    }
    const position = node.position || { x: 0, y: 0, z: 0 };
    const scale = node.scale || { x: 1, y: 1, z: 1 };
    const quaternion = node.quaternion && Number.isFinite(node.quaternion.w)
        ? node.quaternion
        : eulerXYZToQuat(node.rotation);
    return composeLocalMatrix(position, quaternion, scale);
}

function finishBox(minX, minY, minZ, maxX, maxY, maxZ, hits) {
    if (!hits) return null;
    return {
        min: { x: minX, y: minY, z: minZ },
        max: { x: maxX, y: maxY, z: maxZ },
        size: { x: maxX - minX, y: maxY - minY, z: maxZ - minZ },
        center: {
            x: (minX + maxX) / 2,
            y: (minY + maxY) / 2,
            z: (minZ + maxZ) / 2,
        },
    };
}

/**
 * The vertex ranges the renderer actually draws for a mesh: null = all of
 * them; [] = none; else [[start, count], …] in draw order (index space if
 * indexed). cubing.js puzzles carry hidden geometry in the same buffer
 * (hint stickers, outer copies) behind invisible materials; measuring it
 * made the megaminx fit and seat on faces nobody sees.
 */
export function drawnRanges(node) {
    const geo = node?.geometry;
    if (!geo) return [];
    const mat = node.material;
    const total = geo.index ? geo.index.count : (geo.attributes?.position?.count || 0);
    const dr = geo.drawRange || { start: 0, count: Infinity };
    const lo = Math.max(0, dr.start || 0);
    const hi = Math.min(total, lo + (Number.isFinite(dr.count) ? dr.count : Infinity));
    const clip = (a, n) => {
        const s0 = Math.max(a, lo);
        const e0 = Math.min(a + n, hi);
        return e0 > s0 ? [s0, e0 - s0] : null;
    };
    if (Array.isArray(mat)) {
        const groups = geo.groups?.length ? geo.groups : [{ start: 0, count: total, materialIndex: 0 }];
        const out = [];
        for (const g of groups) {
            const m = mat[g.materialIndex ?? 0];
            if (!m || m.visible === false) continue;
            const r = clip(g.start, Number.isFinite(g.count) ? g.count : total - g.start);
            if (r) out.push(r);
        }
        return out;
    }
    if (mat && mat.visible === false) return [];
    if (lo === 0 && hi === total) return null;
    const r = clip(0, total);
    return r ? [r] : [];
}

/** Calls fn(vertexIndex) for each drawn vertex of the mesh. */
function eachDrawnVertex(node, fn) {
    const geo = node.geometry;
    const count = geo?.attributes?.position?.count || 0;
    const ranges = drawnRanges(node);
    const index = geo?.index?.array;
    if (ranges === null) {
        if (index) for (let i = 0; i < index.length; i += 1) fn(index[i]);
        else for (let i = 0; i < count; i += 1) fn(i);
        return;
    }
    for (const [start, n] of ranges) {
        for (let k = start; k < start + n; k += 1) fn(index ? index[k] : k);
    }
}

function absorbGeometry(node, e, absorb, absorbBox) {
    const geo = (node.isMesh || node.isInstancedMesh) ? node.geometry : null;
    if (!geo || !e || e.length < 16) return;
    const pos = geo.attributes?.position;
    const count = pos?.count || 0;
    const ranges = drawnRanges(node);
    if (ranges && !ranges.length) return;
    // Exact drawn vertices (not the geometry's bounding box, which also
    // covers hidden parts and swells when rotated), unless huge.
    if (count > 0 && count <= 20000 && pos.array) {
        const stride = pos.itemSize || 3;
        const arr = pos.array;
        eachDrawnVertex(node, (i) => {
            const w = transformPoint(e, arr[i * stride], arr[i * stride + 1], arr[i * stride + 2]);
            absorb(w.x, w.y, w.z);
        });
        return;
    }
    if (geo.boundingBox) absorbBox(e, geo.boundingBox);
    else if (typeof geo.computeBoundingBox === "function") {
        geo.computeBoundingBox();
        if (geo.boundingBox) absorbBox(e, geo.boundingBox);
    }
}

/**
 * AABB in `object`'s parent space from local TRS — never `matrixWorld`.
 * Ancestor yaw and Twisty world-matrix writes cannot inflate the edge
 * we fit to. Includes `object.scale` so a late cubing.js 1/3 is seen.
 */
export function measureLocalBox(object) {
    if (!object) return null;
    let minX = Infinity;
    let minY = Infinity;
    let minZ = Infinity;
    let maxX = -Infinity;
    let maxY = -Infinity;
    let maxZ = -Infinity;
    let hits = 0;

    function absorb(x, y, z) {
        if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) return;
        hits += 1;
        if (x < minX) minX = x;
        if (y < minY) minY = y;
        if (z < minZ) minZ = z;
        if (x > maxX) maxX = x;
        if (y > maxY) maxY = y;
        if (z > maxZ) maxZ = z;
    }

    function absorbBox(e, box) {
        if (!box?.min || !box?.max) return;
        const xs = [box.min.x, box.max.x];
        const ys = [box.min.y, box.max.y];
        const zs = [box.min.z, box.max.z];
        for (const x of xs) {
            for (const y of ys) {
                for (const z of zs) {
                    const w = transformPoint(e, x, y, z);
                    absorb(w.x, w.y, w.z);
                }
            }
        }
    }

    function walk(node, parentE) {
        if (!node || node.visible === false) return;
        const local = localMatrixOf(node);
        const e = parentE ? multiply4(parentE, local) : local;
        absorbGeometry(node, e, absorb, absorbBox);
        const kids = node.children;
        if (kids) {
            for (const child of kids) walk(child, e);
        }
    }

    walk(object, null);
    return finishBox(minX, minY, minZ, maxX, maxY, maxZ, hits);
}

/**
 * World AABB from live mesh vertices / bounding-box corners.
 * Walks foreign three.js graphs (cubing.js ships its own copy) by
 * reading `matrixWorld.elements` and geometry arrays — never
 * `Box3.setFromObject`, which throws across two three copies.
 */
export function measureWorldBox(object) {
    if (!object) return null;
    object.updateMatrixWorld?.(true);
    let minX = Infinity;
    let minY = Infinity;
    let minZ = Infinity;
    let maxX = -Infinity;
    let maxY = -Infinity;
    let maxZ = -Infinity;
    let hits = 0;

    function absorb(x, y, z) {
        if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) return;
        hits += 1;
        if (x < minX) minX = x;
        if (y < minY) minY = y;
        if (z < minZ) minZ = z;
        if (x > maxX) maxX = x;
        if (y > maxY) maxY = y;
        if (z > maxZ) maxZ = z;
    }

    function absorbBox(e, box) {
        if (!box?.min || !box?.max) return;
        const xs = [box.min.x, box.max.x];
        const ys = [box.min.y, box.max.y];
        const zs = [box.min.z, box.max.z];
        for (const x of xs) {
            for (const y of ys) {
                for (const z of zs) {
                    const w = transformPoint(e, x, y, z);
                    absorb(w.x, w.y, w.z);
                }
            }
        }
    }

    function walk(node) {
        if (!node || node.visible === false) return;
        const e = node.matrixWorld?.elements;
        absorbGeometry(node, e, absorb, absorbBox);
        const kids = node.children;
        if (kids) {
            for (const child of kids) walk(child);
        }
    }

    walk(object);
    return finishBox(minX, minY, minZ, maxX, maxY, maxZ, hits);
}

/**
 * Every vertex of `object` (visible meshes) in its parent space from
 * local TRS, like `measureLocalBox` (never `matrixWorld`), plus the
 * distinct triangle normals there (a direction and its opposite are one).
 */
export function measureLocalShape(object) {
    const points = [];
    const normals = new Map();
    function normalOf(a, b, c) {
        const ux = b.x - a.x, uy = b.y - a.y, uz = b.z - a.z;
        const vx = c.x - a.x, vy = c.y - a.y, vz = c.z - a.z;
        let nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
        const len = Math.hypot(nx, ny, nz);
        if (!(len > 1e-12)) return;
        nx /= len; ny /= len; nz /= len;
        const flip = nx < -1e-9 || (Math.abs(nx) <= 1e-9 && (ny < -1e-9 || (Math.abs(ny) <= 1e-9 && nz < 0)));
        if (flip) { nx = -nx; ny = -ny; nz = -nz; }
        const key = `${nx.toFixed(3)},${ny.toFixed(3)},${nz.toFixed(3)}`;
        if (!normals.has(key) && normals.size < 2048) normals.set(key, { x: nx, y: ny, z: nz });
    }
    function walk(node, parentE) {
        if (!node || node.visible === false) return;
        const local = localMatrixOf(node);
        const e = parentE ? multiply4(parentE, local) : local;
        const geo = (node.isMesh || node.isInstancedMesh) ? node.geometry : null;
        const pos = geo?.attributes?.position;
        if (pos?.array && pos.count > 0) {
            // Only what the renderer draws (see drawnRanges).
            const stride = pos.itemSize || 3;
            const arr = pos.array;
            const at = new Map();
            const vert = (i) => {
                let w = at.get(i);
                if (!w) {
                    w = transformPoint(e, arr[i * stride], arr[i * stride + 1], arr[i * stride + 2]);
                    at.set(i, w);
                    points.push(w);
                }
                return w;
            };
            const tri = [];
            eachDrawnVertex(node, (i) => {
                tri.push(vert(i));
                if (tri.length === 3) {
                    normalOf(tri[0], tri[1], tri[2]);
                    tri.length = 0;
                }
            });
        }
        for (const child of node.children || []) walk(child, e);
    }
    walk(object, null);
    return { points, normals: [...normals.values()] };
}

/**
 * The toy's real measure, in `object`'s parent space (see REAL_SIZES in
 * constants.js):
 *   "face-to-face" — the distance between opposite parallel faces: the
 *     narrowest width across the mesh's face normals (and x, y, z). A
 *     cube's edge; a megaminx's face-to-face.
 *   "edge" — the longest straight distance across the toy: a
 *     tetrahedron's (pyraminx's) edge.
 */
export function measureReal(object, measure = "face-to-face") {
    const { points, normals } = measureLocalShape(object);
    if (!points.length) return null;
    let minX = Infinity, minY = Infinity, minZ = Infinity;
    let maxX = -Infinity, maxY = -Infinity, maxZ = -Infinity;
    for (const p of points) {
        if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y; if (p.z < minZ) minZ = p.z;
        if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y; if (p.z > maxZ) maxZ = p.z;
    }
    const box = finishBox(minX, minY, minZ, maxX, maxY, maxZ, points.length);
    let value;
    if (measure === "edge") {
        const step = Math.max(1, Math.ceil(points.length / 4000));
        let d2 = 0;
        for (let i = 0; i < points.length; i += step) {
            const a = points[i];
            for (let j = i + step; j < points.length; j += step) {
                const b = points[j];
                const dx = a.x - b.x, dy = a.y - b.y, dz = a.z - b.z;
                const q = dx * dx + dy * dy + dz * dz;
                if (q > d2) d2 = q;
            }
        }
        value = Math.sqrt(d2);
    } else if (measure === "face-to-face") {
        value = Math.min(box.size.x, box.size.y, box.size.z);
        for (const n of normals) {
            let lo = Infinity, hi = -Infinity;
            for (const p of points) {
                const s = p.x * n.x + p.y * n.y + p.z * n.z;
                if (s < lo) lo = s;
                if (s > hi) hi = s;
            }
            if (hi - lo > 1e-9 && hi - lo < value) value = hi - lo;
        }
    } else {
        throw new Error(`unknown real measure "${measure}"`);
    }
    return { value, box };
}

/**
 * Scale `wrapper` so the toy shows at its declared real size:
 * `size` = { m, measure } from REAL_SIZES (constants.js). The invariant
 * is that every toy in the room is at real-life scale; a toy is never
 * fitted to another toy's box. Parent-space TRS only — never
 * `matrixWorld` — so ancestor yaw and Twisty world writes cannot
 * inflate the measure. Does not reset wrapper.scale to 1 (that flash is
 * spawn-then-shrink).
 */
export function fitToRealSize(wrapper, object, size) {
    const measured = measureReal(object, size.measure);
    const center = measured?.box?.center || { x: 0, y: 0, z: 0 };
    const native = Number.isFinite(measured?.value) && measured.value > 1e-6 ? measured.value : 1;
    const scale = size.m / native;
    wrapper.scale.setScalar(scale);
    if (Number.isFinite(center.x)) {
        wrapper.position.set(-center.x * scale, -center.y * scale, -center.z * scale);
    } else {
        wrapper.position.set(0, 0, 0);
    }
    wrapper.updateMatrixWorld?.(true);
    return {
        size: { ...(measured?.box?.size || { x: 1, y: 1, z: 1 }) },
        center: { ...center },
        measure: size.measure,
        nativeMeasure: native,
        fitted: size.m,
        scale,
        changed: true,
        rootScale: Number(object?.scale?.x),
    };
}

function applyLockedFit(wrapper, size, previous) {
    const native = previous.nativeMeasure || 1;
    const scale = size.m / native;
    const center = previous.center || { x: 0, y: 0, z: 0 };
    wrapper.scale.setScalar(scale);
    if (Number.isFinite(center.x)) {
        wrapper.position.set(-center.x * scale, -center.y * scale, -center.z * scale);
    }
    wrapper.updateMatrixWorld?.(true);
    return {
        ...previous,
        nativeMeasure: native,
        fitted: size.m,
        scale,
        changed: true,
    };
}

/**
 * Re-apply the real size if cubing.js changed *root* puzzle scale after
 * the first paint. The rest-pose `nativeMeasure` is locked so a
 * mid-turn cubie swell cannot pulse wrapper.scale.
 */
export function keepFitted(wrapper, object, size, previous = null) {
    const rootScale = Number(object?.scale?.x);
    const rootChanged = Number.isFinite(rootScale)
        && Number.isFinite(previous?.rootScale)
        && Math.abs(rootScale - previous.rootScale) > 1e-4;
    if (previous?.nativeMeasure && !rootChanged) {
        const scale = size.m / previous.nativeMeasure;
        const have = wrapper?.scale?.x;
        const drifted = !Number.isFinite(have) || Math.abs(have - scale) > Math.abs(scale) * 0.02;
        if (!drifted) {
            wrapper.updateMatrixWorld?.(true);
            return {
                ...previous,
                changed: false,
                scale: have,
                rootScale: Number.isFinite(rootScale) ? rootScale : previous.rootScale,
            };
        }
        return {
            ...applyLockedFit(wrapper, size, previous),
            rootScale: Number.isFinite(rootScale) ? rootScale : previous.rootScale,
        };
    }
    const fitted = fitToRealSize(wrapper, object, size);
    return {
        ...fitted,
        rootScale: Number.isFinite(rootScale) ? rootScale : fitted.rootScale,
    };
}

/**
 * Seat any toy from its *post-scale* AABB: the lowest measured point
 * lands on `surfaceY`. Never a hardcoded Y that assumes a puzzle size.
 * Probe pose is applied and restored synchronously so a flight rAF
 * never sees it.
 */
export function seatOnSurface(object, {
    x,
    surfaceY,
    z,
    rotation = { x: 0, y: 0, z: 0 },
    fallbackHalfHeight = 0,
    measureBox = measureWorldBox,
} = {}) {
    const rot = {
        x: rotation.x ?? 0,
        y: rotation.y ?? 0,
        z: rotation.z ?? 0,
    };
    if (!object) {
        return {
            position: { x, y: surfaceY + fallbackHalfHeight, z },
            rotation: rot,
        };
    }
    if (object.userData?.easeBusy) object.userData.cancelEase?.();
    const prev = {
        x: object.position.x,
        y: object.position.y,
        z: object.position.z,
        rx: object.rotation?.x ?? 0,
        ry: object.rotation?.y ?? 0,
        rz: object.rotation?.z ?? 0,
        quat: object.quaternion?.clone?.(),
    };
    object.position.set(x, 0, z);
    object.rotation?.set?.(rot.x, rot.y, rot.z);
    object.quaternion?.setFromEuler?.(object.rotation);
    object.updateMatrixWorld?.(true);
    const box = typeof measureBox === "function" ? measureBox(object) : null;
    const minY = box?.min?.y;
    const y = Number.isFinite(minY) ? surfaceY - minY : surfaceY + fallbackHalfHeight;
    object.position.set(prev.x, prev.y, prev.z);
    object.rotation?.set?.(prev.rx, prev.ry, prev.rz);
    if (prev.quat && object.quaternion?.copy) object.quaternion.copy(prev.quat);
    object.updateMatrixWorld?.(true);
    return {
        position: { x, y, z },
        rotation: rot,
    };
}

export function pose3(raw) {
    if (!raw) return null;
    if (raw.position) {
        return {
            x: raw.position.x,
            y: raw.position.y,
            z: raw.position.z,
            rx: raw.rotation?.x ?? 0,
            ry: raw.rotation?.y ?? 0,
            rz: raw.rotation?.z ?? 0,
        };
    }
    const hasRot = raw.rx != null || raw.ry != null || raw.rz != null;
    return {
        x: raw.x,
        y: raw.y,
        z: raw.z,
        rx: hasRot ? (raw.rx ?? 0) : null,
        ry: hasRot ? (raw.ry ?? 0) : null,
        rz: hasRot ? (raw.rz ?? 0) : null,
    };
}

/**
 * Hop or slide an object to a pose. Lift is a sine arc so the move
 * reads as a pick-up, not a slide through the felt.
 */
export function hopTo(object, dest, clock, gen, {
    ms = 520,
    lift = 0.06,
    delay = 0,
    ease = easeOutCubic,
} = {}) {
    const to = pose3(dest);
    if (!object || !to) return Promise.resolve();
    return (async () => {
        if (delay) await clock.wait(delay, gen);
        const from = pose3(object);
        const rotate = to.rx != null && object.rotation;
        await clock.tween(ms, (t) => {
            object.position.x = lerp(from.x, to.x, t);
            object.position.y = lerp(from.y, to.y, t) + Math.sin(Math.PI * t) * lift;
            object.position.z = lerp(from.z, to.z, t);
            if (rotate) {
                object.rotation.set(
                    lerp(from.rx, to.rx, t),
                    lerp(from.ry, to.ry, t),
                    lerp(from.rz, to.rz, t),
                );
                object.quaternion?.setFromEuler?.(object.rotation);
            }
        }, { ease, generation: gen });
    })();
}

export async function waitToyIdle(toy, clock, gen, { tries = 40, ms = 40 } = {}) {
    if (!toy) return;
    for (let i = 0; i < tries && toy.userData?.flightBusy; i++) {
        await clock.wait(ms, gen);
    }
}

export function trackToy(world, name) {
    return () => world.toys[name]?.position;
}

function worldXYZ(node) {
    if (!node) return null;
    if (typeof node.updateMatrixWorld === "function") {
        node.updateMatrixWorld(true);
        const e = node.matrixWorld?.elements;
        if (e && e.length >= 15 && Number.isFinite(e[12])) {
            return { x: e[12], y: e[13], z: e[14] };
        }
    }
    const p = node.position || node;
    if (p && Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z)) {
        return { x: p.x, y: p.y, z: p.z };
    }
    return null;
}

function pushPoint(points, value) {
    if (!value) return;
    const node = typeof value === "function" ? value() : value;
    const p = worldXYZ(node) || (node && Number.isFinite(node.x) ? node : null);
    if (p && Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z)) {
        points.push(p);
    }
}

function focusOf(points) {
    const c = centroidOf(points);
    if (!c) return null;
    let r = 0.05;
    for (const p of points) {
        const dx = p.x - c.x;
        const dy = p.y - c.y;
        const dz = p.z - c.z;
        r = Math.max(r, Math.hypot(dx, dy, dz));
    }
    return { x: c.x, y: c.y, z: c.z, r };
}

/** Average of live world-space points. Empty set → null. */
export function centroidOf(points) {
    if (!points?.length) return null;
    let x = 0;
    let y = 0;
    let z = 0;
    for (const p of points) {
        x += p.x;
        y += p.y;
        z += p.z;
    }
    const n = points.length;
    return { x: x / n, y: y / n, z: z / n };
}

/**
 * Frame the named toys (and optional extra meshes / getters).
 * Always the full set — use `trackActive` when only in-flight
 * props should pull the lens.
 */
export function trackToys(world, names, extras = []) {
    const list = Array.isArray(names) ? names : [names];
    return () => {
        const points = [];
        for (const name of list) pushPoint(points, world.toys?.[name]);
        for (const extra of extras) pushPoint(points, extra);
        return focusOf(points);
    };
}

/**
 * Dynamic enter framing: centroid of toys that are flying or
 * unboxing, falling back to the whole set so the lens never
 * snaps to a named empty shot.
 */
export function trackActive(world, names, extras = []) {
    const list = Array.isArray(names) ? names : [names];
    return () => {
        const busy = [];
        const all = [];
        for (const name of list) {
            const toy = world.toys?.[name];
            if (!toy) continue;
            pushPoint(all, toy);
            if (toy.userData?.flightBusy || toy.userData?.unboxBusy) pushPoint(busy, toy);
        }
        const extracting = [];
        for (const extra of extras) {
            const node = typeof extra === "function" ? extra() : extra;
            if (!node) continue;
            pushPoint(all, node);
            if (node.userData?.flightBusy || node.userData?.unboxBusy) pushPoint(busy, node);
            if (node.userData?.unboxBusy && node.name === "packet") pushPoint(extracting, node);
        }
        if (extracting.length) return focusOf(extracting);
        return focusOf(busy.length ? busy : all);
    };
}

/**
 * Hold the current shot so a toy leaving home stays in frame, then
 * ease to `to` while tracking. Kept for callers that still want a
 * named-shot ease; happy-path hub→play uses `followEnter`.
 */
export function trackEnter(poses, {
    to,
    track,
    holdMs = 0,
    duration,
    reduced = false,
} = {}) {
    if (!poses) return;
    if (reduced) {
        poses.snap?.(to);
        return;
    }
    poses.goTo(to, {
        duration,
        delay: holdMs || 0,
        track,
    });
}

/**
 * Continuous follow-cam hop. Shared by hub→play and play→hub so
 * neither path falls back to via:shelf / look.copy snaps.
 */
function followShot(poses, {
    to,
    track,
    holdMs = 0,
    duration,
    reduced = false,
    settleAt,
    mode,
} = {}) {
    if (!poses) return;
    if (reduced) {
        poses.snap?.(to);
        return;
    }
    if (poses.followTo) {
        return poses.followTo(to, {
            duration,
            delay: holdMs || 0,
            track,
            settleAt,
                    mode,
        });
    }
    poses.goTo(to, {
        duration,
        delay: holdMs || 0,
        track,
    });
}

/**
 * Shared hub→play enter for Scramble and DoubleDeal. Starts from the
 * live hub framing, follows the actual flying toys (no via:shelf /
 * unbox_travel chain), and lands at `to` without a cut.
 */
export function followEnter(poses, opts = {}) {
    return followShot(poses, {
        ...opts,
        settleAt: opts.settleAt ?? 0.9,
    });
}

/**
 * Shared play→hub return. Same follow primitive as enter: live track,
 * eased look, late settle into the room pose. No via:shelf, no cut.
 */
export function followLeave(poses, opts = {}) {
    return followShot(poses, {
        ...opts,
        to: opts.to || "landing",
        settleAt: opts.settleAt ?? 0.78,
        mode: opts.mode || "return",
    });
}

/** Ease from the live camera to a named pose. Skip uses this too. */
export function continueTo(poses, name, { duration = 720, reduced = false, restart = false } = {}) {
    if (!poses) return Promise.resolve();
    if (reduced) {
        poses.snap?.(name);
        return Promise.resolve(name);
    }
    if (poses.playTo) return poses.playTo(name, { duration, restart });
    poses.goTo?.(name, { duration, restart });
    return Promise.resolve(name);
}

/**
 * Set toys on a sensible felt rest (or table seat). Standing, not a
 * tipped discard. World supplies `getBoxRestPose` / `getTablePose`.
 */
export async function seatToys(world, clock, gen, names, { ms = 520, lift = 0.03 } = {}) {
    const jobs = names.map((name) => {
        const toy = world.toys?.[name];
        const dest = world.getBoxRestPose?.(name) || world.getTablePose?.(name);
        if (!toy || !dest) return Promise.resolve();
        return hopTo(toy, dest, clock, gen, { ms, lift, ease: easeInOutCubic });
    });
    await Promise.all(jobs);
}
