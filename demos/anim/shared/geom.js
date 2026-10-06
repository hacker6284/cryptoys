/**
 * Pure geometry for the motion primitives (carry, hinge): vectors,
 * quaternions (three.js conventions: [x, y, z, w], Euler order XYZ),
 * oriented boxes and the overlap test the primitives plan and check
 * with. No three.js, so node tests run the same code the pages run.
 */

// ---- seeded random (mulberry32) ----
export function rng(seed) {
    let a = seed >>> 0;
    return () => {
        a = (a + 0x6d2b79f5) >>> 0;
        let t = a;
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}

// ---- vectors ----
export const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
export const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
export const scale = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
export const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
export const len = (a) => Math.hypot(a[0], a[1], a[2]);
export const lerp3 = (a, b, t) => [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];
export const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];

// ---- eases ----
export const clamp01 = (t) => Math.min(1, Math.max(0, t));
/** Quintic smootherstep: zero speed and acceleration at both ends, fastest (1.875× mean) half way. */
export const smootherStep = (t) => { t = clamp01(t); return t * t * t * (t * (t * 6 - 15) + 10); };
export const smootherStepD = (t) => { t = clamp01(t); return 30 * t * t * (t - 1) * (t - 1); };
export const easeInOutCubic = (t) => { t = clamp01(t); return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2; };
export const easeInOutSine = (t) => -(Math.cos(Math.PI * clamp01(t)) - 1) / 2;
export const easeInQuad = (t) => { t = clamp01(t); return t * t; };

// ---- quaternions ----
export function quatFromEuler(x = 0, y = 0, z = 0) {
    const c1 = Math.cos(x / 2), c2 = Math.cos(y / 2), c3 = Math.cos(z / 2);
    const s1 = Math.sin(x / 2), s2 = Math.sin(y / 2), s3 = Math.sin(z / 2);
    return [
        s1 * c2 * c3 + c1 * s2 * s3,
        c1 * s2 * c3 - s1 * c2 * s3,
        c1 * c2 * s3 + s1 * s2 * c3,
        c1 * c2 * c3 - s1 * s2 * s3,
    ];
}
export function quatAxisAngle(axis, angle) {
    const s = Math.sin(angle / 2), n = len(axis);
    return [(axis[0] / n) * s, (axis[1] / n) * s, (axis[2] / n) * s, Math.cos(angle / 2)];
}
export function quatMul(a, b) {
    const [ax, ay, az, aw] = a, [bx, by, bz, bw] = b;
    return [
        ax * bw + aw * bx + ay * bz - az * by,
        ay * bw + aw * by + az * bx - ax * bz,
        az * bw + aw * bz + ax * by - ay * bx,
        aw * bw - ax * bx - ay * by - az * bz,
    ];
}
export const quatDot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
export function quatNorm(q) {
    const n = Math.hypot(q[0], q[1], q[2], q[3]);
    return [q[0] / n, q[1] / n, q[2] / n, q[3] / n];
}
export function quatRotate(q, v) {
    const [x, y, z, w] = q;
    const ix = w * v[0] + y * v[2] - z * v[1];
    const iy = w * v[1] + z * v[0] - x * v[2];
    const iz = w * v[2] + x * v[1] - y * v[0];
    const iw = -x * v[0] - y * v[1] - z * v[2];
    return [
        ix * w + iw * -x + iy * -z - iz * -y,
        iy * w + iw * -y + iz * -x - ix * -z,
        iz * w + iw * -z + ix * -y - iy * -x,
    ];
}
/** Spherical interpolation along the shorter arc (three.js Quaternion.slerp). */
export function slerp(a, b, t) {
    let d = quatDot(a, b);
    let bb = b;
    if (d < 0) { d = -d; bb = [-b[0], -b[1], -b[2], -b[3]]; }
    if (d > 0.9995) return quatNorm([a[0] + (bb[0] - a[0]) * t, a[1] + (bb[1] - a[1]) * t, a[2] + (bb[2] - a[2]) * t, a[3] + (bb[3] - a[3]) * t]);
    const th = Math.acos(Math.min(1, d));
    const s = Math.sin(th);
    const wa = Math.sin((1 - t) * th) / s, wb = Math.sin(t * th) / s;
    return [a[0] * wa + bb[0] * wb, a[1] * wa + bb[1] * wb, a[2] * wa + bb[2] * wb, a[3] * wa + bb[3] * wb];
}
/** Angle (rad) between two orientations. */
export function quatAngle(a, b) {
    return 2 * Math.acos(Math.min(1, Math.abs(quatDot(a, b))));
}

// ---- oriented boxes ----
/**
 * shape: the object's drawn local bounds { min: [x,y,z], max: [x,y,z] }
 * (measured from its meshes). pose: { p: [x,y,z], q: [x,y,z,w] }.
 * → { c, axes: [ax, ay, az], he: [hx, hy, hz] } in world space.
 */
export function obbOf(pose, shape) {
    const lc = scale(add(shape.min, shape.max), 0.5);
    const he = scale(sub(shape.max, shape.min), 0.5);
    const axes = [quatRotate(pose.q, [1, 0, 0]), quatRotate(pose.q, [0, 1, 0]), quatRotate(pose.q, [0, 0, 1])];
    return { c: add(pose.p, quatRotate(pose.q, lc)), axes, he };
}
/** An axis-aligned or yawed solid box { min, max, yaw } as an OBB. */
export function boxSolid(min, max, yaw = 0) {
    const c = scale(add(min, max), 0.5), he = scale(sub(max, min), 0.5);
    const q = quatFromEuler(0, yaw, 0);
    return { c, he, axes: [quatRotate(q, [1, 0, 0]), [0, 1, 0], quatRotate(q, [0, 0, 1])] };
}
export function obbCorners(o) {
    const out = [];
    for (let i = 0; i < 8; i++) {
        const sx = i & 1 ? 1 : -1, sy = i & 2 ? 1 : -1, sz = i & 4 ? 1 : -1;
        out.push(add(o.c, add(scale(o.axes[0], sx * o.he[0]), add(scale(o.axes[1], sy * o.he[1]), scale(o.axes[2], sz * o.he[2])))));
    }
    return out;
}
/** Lowest point of the OBB (world y). */
export function obbMinY(o) {
    return o.c[1] - (Math.abs(o.axes[0][1]) * o.he[0] + Math.abs(o.axes[1][1]) * o.he[1] + Math.abs(o.axes[2][1]) * o.he[2]);
}
export function obbMaxY(o) {
    return 2 * o.c[1] - obbMinY(o);
}
/** Grid of points over the OBB's surface (n per edge). */
export function obbSurface(o, n = 4) {
    const pts = [];
    const f = (i) => -1 + (2 * i) / (n - 1);
    for (let a = 0; a < 3; a++) {
        const b = (a + 1) % 3, c = (a + 2) % 3;
        for (const s of [-1, 1]) for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
            pts.push(add(o.c, add(scale(o.axes[a], s * o.he[a]), add(scale(o.axes[b], f(i) * o.he[b]), scale(o.axes[c], f(j) * o.he[c])))));
        }
    }
    return pts;
}

/**
 * Penetration depth of two OBBs (separating-axis test, 15 axes), each
 * grown by `margin` in total: > 0 overlap (metres along the least axis),
 * ≤ 0 separated by that much.
 */
export function obbDepth(A, B, margin = 0) {
    const axes = [...A.axes, ...B.axes];
    for (const a of A.axes) for (const b of B.axes) {
        const c = cross(a, b);
        const n = len(c);
        if (n > 1e-6) axes.push(scale(c, 1 / n));
    }
    const d = sub(B.c, A.c);
    let least = Infinity;
    for (const ax of axes) {
        const ra = A.he[0] * Math.abs(dot(A.axes[0], ax)) + A.he[1] * Math.abs(dot(A.axes[1], ax)) + A.he[2] * Math.abs(dot(A.axes[2], ax));
        const rb = B.he[0] * Math.abs(dot(B.axes[0], ax)) + B.he[1] * Math.abs(dot(B.axes[1], ax)) + B.he[2] * Math.abs(dot(B.axes[2], ax));
        const o = ra + rb + margin - Math.abs(dot(d, ax));
        if (o < least) least = o;
    }
    return least;
}

/**
 * Depth of an OBB in a solid: { kind: "box", ...OBB } or a vertical
 * cylinder / ring { kind: "cyl", x, z, r, rIn, y0, y1 } (sampled over
 * the box's surface; the solids are much bigger than the toys).
 */
export function depthIn(o, solid, margin = 0) {
    if (solid.kind !== "cyl") return obbDepth(o, solid, margin);
    let worst = -Infinity;
    const top = obbMaxY(o), bot = obbMinY(o);
    if (bot > solid.y1 + margin + 0.05 || top < solid.y0 - margin - 0.05) return Math.max(bot - solid.y1, solid.y0 - top) * -1;
    for (const p of obbSurface(o, 5)) {
        const rho = Math.hypot(p[0] - solid.x, p[2] - solid.z);
        const dr = solid.r + margin - rho;
        const dIn = solid.rIn ? rho - (solid.rIn - margin) : Infinity;
        const dy = Math.min(solid.y1 + margin - p[1], p[1] - (solid.y0 - margin));
        worst = Math.max(worst, Math.min(dr, dIn, dy));
    }
    return worst;
}

/** Worst depth of an OBB over a list of solids: { depth, solid }. */
export function worstDepth(o, solids, margin = 0) {
    let depth = -Infinity, which = null;
    for (const s of solids) {
        const d = depthIn(o, s, margin);
        if (d > depth) { depth = d; which = s; }
    }
    return { depth, solid: which };
}

/** Centre height that sets the shape's drawn bottom on `surfaceY` at orientation q. */
export function seatY(surfaceY, q, shape) {
    return surfaceY - obbMinY(obbOf({ p: [0, 0, 0], q }, shape));
}
