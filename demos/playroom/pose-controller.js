import * as THREE from "three";
import { TWEEN_MS } from "./constants.js";
import { POSES, resolvePoseName } from "./poses.js";

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

export function createPoseController(camera, { duration = TWEEN_MS, onChange } = {}) {
    const look = new THREE.Vector3();
    const tracked = new THREE.Vector3();
    let current = "landing";
    let tween = null;

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

    function snap(name) {
        const resolved = resolvePoseName(name, current);
        const pose = readPose(resolved);
        if (!pose) return current;
        tween = null;
        current = resolved;
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
        const now = performance.now();
        const viaName = opts.via ? resolvePoseName(opts.via) : null;
        tween = {
            from: capture(),
            via: viaName ? readPose(viaName) : null,
            viaT: opts.viaT ?? 0.36,
            to: pose,
            start: now + (opts.delay || 0),
            duration: opts.duration ?? duration,
            track: opts.track || null,
        };
        emit(current, { tweening: true, next: resolved });
        return current;
    }

    function skip() {
        if (!tween) return current;
        return snap(tween.to.name);
    }

    function update(now = performance.now()) {
        if (!tween) return current;
        if (now < tween.start) {
            apply(tween.to, 0, tween.from, null);
            return current;
        }
        const trackPos = readTrack(tween.track);
        const u = Math.min(1, (now - tween.start) / tween.duration);
        if (tween.via && u < tween.viaT) {
            apply(tween.via, u / tween.viaT, tween.from, null);
        } else if (tween.via) {
            apply(tween.to, (u - tween.viaT) / (1 - tween.viaT), tween.via, trackPos);
        } else {
            apply(tween.to, u, tween.from, trackPos);
        }
        if (u >= 1) {
            current = tween.to.name;
            tween = null;
            emit(current, { tweening: false });
        }
        return current;
    }

    return {
        get name() {
            return current;
        },
        get busy() {
            return Boolean(tween);
        },
        get lookTarget() {
            return look;
        },
        snap,
        goTo,
        skip,
        update,
        prefersReducedMotion,
    };
}
