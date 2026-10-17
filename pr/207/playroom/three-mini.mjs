// Node tests only: the few three.js classes the BS unboxing touches
// (Vector3, Quaternion, Object3D / Group / Scene with world poses, no
// scale), in plain JS on anim/shared/geom.js's math, since three.js is not
// installed for the tests. Plus glbMesh(): a die model's mesh as the stage
// clones it (POSITION, the node's scale and rotation) for dice.restHeight.
import { readFileSync } from "node:fs";
import { add, cross, dot, len, quatAxisAngle, quatMul, quatRotate, sub } from "../anim/shared/geom.js";

const arr = (v) => [v.x, v.y, v.z];
const qarr = (q) => [q.x, q.y, q.z, q.w];

export class Vector3 {
    constructor(x = 0, y = 0, z = 0) {
        this.x = x;
        this.y = y;
        this.z = z;
    }
    set(x, y, z) {
        this.x = x;
        this.y = y;
        this.z = z;
        return this;
    }
    copy(v) { return this.set(v.x, v.y, v.z); }
    clone() { return new Vector3(this.x, this.y, this.z); }
    fromArray(a, o = 0) { return this.set(a[o], a[o + 1], a[o + 2]); }
    toArray() { return arr(this); }
    multiply(v) { return this.set(this.x * v.x, this.y * v.y, this.z * v.z); }
    length() { return len(arr(this)); }
    normalize() {
        const l = this.length() || 1;
        return this.set(this.x / l, this.y / l, this.z / l);
    }
    applyQuaternion(q) { return this.set(...quatRotate(qarr(q), arr(this))); }
    fromBufferAttribute(a, i) { return this.set(a.getX(i), a.getY(i), a.getZ(i)); }
}

export class Quaternion {
    constructor(x = 0, y = 0, z = 0, w = 1) {
        this.set(x, y, z, w);
    }
    set(x, y, z, w) {
        this.x = x;
        this.y = y;
        this.z = z;
        this.w = w;
        return this;
    }
    copy(q) { return this.set(q.x, q.y, q.z, q.w); }
    clone() { return new Quaternion(this.x, this.y, this.z, this.w); }
    identity() { return this.set(0, 0, 0, 1); }
    invert() { return this.set(-this.x, -this.y, -this.z, this.w); }
    multiply(q) { return this.set(...quatMul(qarr(this), qarr(q))); }
    premultiply(q) { return this.set(...quatMul(qarr(q), qarr(this))); }
    setFromAxisAngle(axis, angle) { return this.set(...quatAxisAngle(arr(axis), angle)); }
    // The shortest turn from unit a to unit b; turned right round, about the axis three.js picks.
    setFromUnitVectors(a, b) {
        const u = arr(a), v = arr(b);
        const c = cross(u, v), s = len(c), d = dot(u, v);
        if (s > 1e-12) return this.set(...quatAxisAngle(c, Math.atan2(s, d)));
        if (d > 0) return this.identity();
        return this.set(...quatAxisAngle(Math.abs(u[0]) > Math.abs(u[2]) ? [-u[1], u[0], 0] : [0, -u[2], u[1]], Math.PI));
    }
}

export class Object3D {
    constructor() {
        this.position = new Vector3();
        this.quaternion = new Quaternion();
        this.scale = new Vector3(1, 1, 1);
        this.parent = null;
        this.children = [];
        this.name = "";
        this.userData = {};
    }
    add(o) {
        o.removeFromParent();
        o.parent = this;
        this.children.push(o);
        return this;
    }
    remove(o) {
        const i = this.children.indexOf(o);
        if (i >= 0) this.children.splice(i, 1);
        o.parent = null;
        return this;
    }
    removeFromParent() {
        this.parent?.remove(this);
        return this;
    }
    /** World pose { p, q } as arrays. */
    world() {
        if (!this.parent) return { p: arr(this.position), q: qarr(this.quaternion) };
        const w = this.parent.world();
        return { p: add(w.p, quatRotate(w.q, arr(this.position))), q: quatMul(w.q, qarr(this.quaternion)) };
    }
    updateMatrixWorld() {}
    updateWorldMatrix() {}
    getWorldPosition(t) { return t.set(...this.world().p); }
    getWorldQuaternion(t) { return t.set(...this.world().q); }
    worldToLocal(v) {
        const w = this.world();
        return v.set(...quatRotate([-w.q[0], -w.q[1], -w.q[2], w.q[3]], sub(arr(v), w.p)));
    }
    attach(o) {
        const w = o.world();
        this.add(o);
        const me = this.world();
        o.position.set(...quatRotate([-me.q[0], -me.q[1], -me.q[2], me.q[3]], sub(w.p, me.p)));
        o.quaternion.set(...quatMul([-me.q[0], -me.q[1], -me.q[2], me.q[3]], w.q));
        return this;
    }
}
export class Group extends Object3D {}
export class Scene extends Object3D {}

/** The first mesh node of a GLB as { geometry.attributes.position, scale, quaternion } (the stage clones that node). */
export function glbMesh(url) {
    const b = readFileSync(url);
    const jsonLen = b.readUInt32LE(12);
    const json = JSON.parse(b.subarray(20, 20 + jsonLen).toString("utf8"));
    const bin = b.subarray(20 + jsonLen + 8);
    const node = json.nodes.find((n) => n.mesh !== undefined);
    const a = json.accessors[json.meshes[node.mesh].primitives[0].attributes.POSITION];
    if (a.componentType !== 5126 || a.type !== "VEC3") throw new Error("POSITION: float VEC3 expected");
    const view = json.bufferViews[a.bufferView];
    const stride = view.byteStride ?? 12;
    const base = (view.byteOffset ?? 0) + (a.byteOffset ?? 0);
    const get = (i, k) => bin.readFloatLE(base + i * stride + 4 * k);
    const position = { count: a.count, getX: (i) => get(i, 0), getY: (i) => get(i, 1), getZ: (i) => get(i, 2) };
    return {
        geometry: { attributes: { position } },
        scale: new Vector3(...(node.scale ?? [1, 1, 1])),
        quaternion: new Quaternion(...(node.rotation ?? [0, 0, 0, 1])),
    };
}
