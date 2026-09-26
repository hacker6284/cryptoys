import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { TWEEN_MS } from "./constants.js";
import { POSES, resolvePoseName } from "./poses.js";

const FRAME_LAMBDA = 7.2;

function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
}

function easeInOutCubic(t) {
    return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
}

function toVec(value) {
    if (value.isVector3) return value.clone();
    return new THREE.Vector3(value[0], value[1], value[2]);
}

function readPose(name) {
    const spec = POSES[name];
    if (!spec) return null;
    return {
        name,
        position: toVec(spec.position),
        target: toVec(spec.target),
        fov: spec.fov,
        overlays: spec.overlays,
    };
}

export function createPoseController(camera, { duration = TWEEN_MS, onChange, domElement } = {}) {
    const look = new THREE.Vector3();
    const tracked = new THREE.Vector3();
    const frameScratch = new THREE.Vector3();
    const frameDelta = new THREE.Vector3();
    const followFocus = new THREE.Vector3();
    const followPos = new THREE.Vector3();
    const destOffset = new THREE.Vector3();
    const chasePos = new THREE.Vector3();
    const chaseLook = new THREE.Vector3();
    let current = "landing";
    let tween = null;
    let framing = null;
    let orbitLocked = false;
    let lastFrame = performance.now();

    const controls = domElement ? new OrbitControls(camera, domElement) : null;
    if (controls) {
        controls.enableDamping = true;
        controls.dampingFactor = 0.085;
        controls.enablePan = true;
        controls.screenSpacePanning = true;
        controls.enableZoom = true;
        controls.minDistance = 0.38;
        controls.maxDistance = 8;
        controls.minPolarAngle = 0.2;
        controls.maxPolarAngle = Math.PI / 2 - 0.05;
        controls.enabled = false;
    }

    function setControlsEnabled(on) {
        if (!controls) return;
        controls.enabled = Boolean(on);
        if (on) controls.target.copy(look);
    }

    function readTrack(track) {
        if (!track) return null;
        const value = typeof track === "function" ? track() : track;
        if (!value) return null;
        if (value.isVector3) return tracked.copy(value);
        tracked.set(value.x, value.y, value.z);
        return tracked;
    }

    function apply(pose, t = 1, from = null, trackPos = null) {
        if (from && t <= 0) {
            // Hold the captured shot. Do not look at the table or the toy
            // during the delay — that is what made the shelf departure miss
            // the frame while the camera rushed to seated.
            camera.position.copy(from.position);
            camera.fov = from.fov;
            look.copy(from.target);
        } else if (from && t < 1) {
            const k = easeInOutCubic(t);
            camera.position.lerpVectors(from.position, pose.position, k);
            camera.fov = from.fov + (pose.fov - from.fov) * k;
            if (trackPos) {
                if (t < 0.72) look.copy(trackPos);
                else look.lerpVectors(trackPos, pose.target, (t - 0.72) / 0.28);
            } else {
                look.lerpVectors(from.target, pose.target, k);
            }
        } else {
            camera.position.copy(pose.position);
            look.copy(pose.target);
            camera.fov = pose.fov;
        }
        camera.up.set(0, 1, 0);
        camera.updateProjectionMatrix();
        camera.lookAt(look);
        if (controls) controls.target.copy(look);
    }

    function smoothstep(edge0, edge1, x) {
        if (edge1 <= edge0) return x >= edge1 ? 1 : 0;
        const t = Math.min(1, Math.max(0, (x - edge0) / (edge1 - edge0)));
        return t * t * (3 - 2 * t);
    }

    /**
     * Follow-cam: look eases onto the live track (never copies/snaps),
     * camera chases a dest-relative offset of that focus, then both
     * settle into the named play pose. No via named shots.
     */
    function applyFollow(pose, t = 1, from = null, trackPos = null) {
        if (!from || t <= 0) {
            apply(pose, 0, from, null);
            return;
        }
        if (t >= 1) {
            apply(pose, 1);
            return;
        }
        const focus = trackPos ? followFocus.copy(trackPos) : followFocus.copy(pose.target);
        destOffset.copy(pose.position).sub(pose.target);
        followPos.copy(focus).add(destOffset);
        const lookU = easeInOutCubic(smoothstep(0, 0.46, t));
        const moveU = easeInOutCubic(smoothstep(0.05, 0.86, t));
        const settleU = easeInOutCubic(smoothstep(0.58, 1, t));
        chasePos.copy(from.position).lerp(followPos, moveU);
        camera.position.copy(chasePos).lerp(pose.position, settleU);
        chaseLook.copy(from.target).lerp(focus, lookU);
        look.copy(chaseLook).lerp(pose.target, settleU);
        camera.fov = from.fov + (pose.fov - from.fov) * moveU;
        camera.up.set(0, 1, 0);
        camera.updateProjectionMatrix();
        camera.lookAt(look);
        if (controls) controls.target.copy(look);
    }

    function capture() {
        return {
            position: camera.position.clone(),
            target: look.clone(),
            fov: camera.fov,
        };
    }

    function emit(name, { tweening, next }) {
        const pose = readPose(name);
        onChange?.({
            name,
            next: next ?? name,
            tweening,
            overlays: pose?.overlays ?? POSES.landing.overlays,
        });
    }

    function finishTween(name, { emitChange = true } = {}) {
        const waiters = tween?.waiters || [];
        tween = null;
        if (name) current = name;
        if (emitChange) emit(current, { tweening: false });
        for (const waiter of waiters) waiter(current);
    }

    function snap(name) {
        const resolved = resolvePoseName(name, current);
        const pose = readPose(resolved);
        if (!pose) return current;
        finishTween(resolved, { emitChange: false });
        current = resolved;
        setControlsEnabled(false);
        apply(pose, 1);
        emit(current, { tweening: false });
        return current;
    }

    function goTo(name, opts = {}) {
        const resolved = resolvePoseName(name, current);
        const pose = readPose(resolved);
        if (!pose) return current;
        if (resolved === current && !tween && !opts.track) return current;
        if (tween && tween.to.name === resolved && !opts.track) {
            skip();
            return current;
        }
        if (opts.snap || prefersReducedMotion()) return snap(resolved);
        if (tween) finishTween(current, { emitChange: false });
        setControlsEnabled(false);
        const now = performance.now();
        const viaName = opts.via ? resolvePoseName(opts.via) : null;
        tween = {
            from: capture(),
            via: viaName ? readPose(viaName) : null,
            viaT: opts.viaT ?? 0.36,
            to: pose,
            delay: opts.delay || 0,
            holdElapsed: 0,
            elapsed: 0,
            last: now,
            holding: true,
            duration: opts.duration ?? duration,
            track: opts.track || null,
            waiters: [],
        };
        emit(current, { tweening: true, next: resolved });
        return current;
    }

    function followTo(name, opts = {}) {
        const resolved = resolvePoseName(name, current);
        const pose = readPose(resolved);
        if (!pose) return current;
        if (opts.snap || prefersReducedMotion()) return snap(resolved);
        if (tween) finishTween(current, { emitChange: false });
        setControlsEnabled(false);
        const now = performance.now();
        tween = {
            from: capture(),
            via: null,
            viaT: 0,
            to: pose,
            delay: opts.delay || 0,
            holdElapsed: 0,
            elapsed: 0,
            last: now,
            holding: true,
            duration: opts.duration ?? duration,
            track: opts.track || null,
            mode: "follow",
            waiters: [],
        };
        emit(current, { tweening: true, next: resolved });
        return current;
    }

    function setTrack(track) {
        if (tween) tween.track = track || null;
    }

    function playTo(name, opts = {}) {
        goTo(name, opts);
        if (!tween) return Promise.resolve(current);
        return new Promise((resolve) => {
            tween.waiters.push(resolve);
        });
    }

    function lockOrbit() {
        orbitLocked = true;
        setControlsEnabled(false);
    }

    function unlockOrbit() {
        orbitLocked = false;
    }

    function skip() {
        if (!tween) return current;
        return snap(tween.to.name);
    }

    function readFrameTarget() {
        if (!framing) return null;
        const value = typeof framing === "function" ? framing() : framing;
        if (!value) return null;
        if (value.isVector3) return frameScratch.copy(value);
        frameScratch.set(value.x, value.y, value.z);
        return frameScratch;
    }

    function applyFraming(dtMs) {
        const want = readFrameTarget();
        if (!want) return;
        const dt = Math.min(0.05, Math.max(0, dtMs / 1000));
        const k = 1 - Math.exp(-FRAME_LAMBDA * dt);
        if (controls) {
            frameDelta.copy(want).sub(controls.target).multiplyScalar(k);
            controls.target.add(frameDelta);
            camera.position.add(frameDelta);
            look.copy(controls.target);
        } else {
            look.lerp(want, k);
            camera.lookAt(look);
        }
    }

    function frame(getTarget) {
        framing = getTarget || null;
    }

    function releaseFrame() {
        framing = null;
    }

    function update(now = performance.now()) {
        const dt = Math.min(50, Math.max(0, now - lastFrame));
        lastFrame = now;
        if (tween) {
            setControlsEnabled(false);
            const stepDt = Math.min(50, Math.max(0, now - tween.last));
            tween.last = now;
            if (tween.holding) {
                tween.holdElapsed += stepDt;
                if (tween.holdElapsed < tween.delay) {
                    apply(tween.to, 0, tween.from, null);
                    return current;
                }
                tween.holding = false;
            }
            tween.elapsed += stepDt;
            const trackPos = readTrack(tween.track);
            const u = Math.min(1, tween.elapsed / tween.duration);
            if (tween.mode === "follow") {
                applyFollow(tween.to, u, tween.from, trackPos);
            } else if (tween.via && u < tween.viaT) {
                apply(tween.via, u / tween.viaT, tween.from, null);
            } else if (tween.via) {
                apply(tween.to, (u - tween.viaT) / (1 - tween.viaT), tween.via, trackPos);
            } else {
                apply(tween.to, u, tween.from, trackPos);
            }
            if (u >= 1) finishTween(tween.to.name);
            return current;
        }
        if (orbitLocked || !controls) {
            applyFraming(dt);
            return current;
        }
        if (!controls.enabled) setControlsEnabled(true);
        applyFraming(dt);
        controls.update();
        look.copy(controls.target);
        return current;
    }

    return {
        get name() {
            return current;
        },
        get busy() {
            return Boolean(tween);
        },
        get locked() {
            return orbitLocked;
        },
        get lookTarget() {
            return look;
        },
        get framing() {
            return Boolean(framing);
        },
        snap,
        goTo,
        followTo,
        setTrack,
        playTo,
        skip,
        lockOrbit,
        unlockOrbit,
        frame,
        releaseFrame,
        update,
        prefersReducedMotion,
    };
}
