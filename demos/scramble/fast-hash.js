/**
 * Scramble digest for file bytes, off the generated module.
 *
 * Same turns, padding, closer, seat and digest as the generated
 * `update` / `evaluate` (primitives/hash/scramble/SPEC.md), on a mutable
 * JS cube with no teach trace, so a multi-MB file can finish. Bytes map
 * to the message exactly as hex Message does: each byte is two nybbles,
 * high first. `fast-hash.test.mjs` pins it to the generated module.
 */

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

function pidx(x, y, z) {
    return (x + 1) * 9 + (y + 1) * 3 + (z + 1);
}

function solvedFastCube() {
    const cube = [];
    const at = new Array(27);
    for (let x = -1; x <= 1; x += 1) {
        for (let y = -1; y <= 1; y += 1) {
            for (let z = -1; z <= 1; z += 1) {
                if (!x && !y && !z) continue;
                const c = {
                    x, y, z,
                    xp: x === 1 ? 3 : 0,
                    xn: x === -1 ? 4 : 0,
                    yp: y === 1 ? 1 : 0,
                    yn: y === -1 ? 2 : 0,
                    zp: z === 1 ? 6 : 0,
                    zn: z === -1 ? 5 : 0,
                };
                cube.push(c);
                at[pidx(x, y, z)] = c;
            }
        }
    }
    cube.at = at;
    return cube;
}

function turnCubie(c, face) {
    let nx;
    let ny;
    let nz;
    if (face === 0 || face === 1) {
        nx = c.z;
        ny = c.y;
        nz = -c.x;
    } else if (face === 2) {
        nx = c.x;
        ny = c.z;
        nz = -c.y;
    } else if (face === 3) {
        nx = c.x;
        ny = -c.z;
        nz = c.y;
    } else if (face === 4) {
        nx = c.y;
        ny = -c.x;
        nz = c.z;
    } else {
        nx = -c.y;
        ny = c.x;
        nz = c.z;
    }
    let xp = 0;
    let xn = 0;
    let yp = 0;
    let yn = 0;
    let zp = 0;
    let zn = 0;
    const paint = (ax, ay, az, color) => {
        if (!color) return;
        let rx;
        let ry;
        let rz;
        if (face === 0 || face === 1) {
            rx = az;
            ry = ay;
            rz = -ax;
        } else if (face === 2) {
            rx = ax;
            ry = az;
            rz = -ay;
        } else if (face === 3) {
            rx = ax;
            ry = -az;
            rz = ay;
        } else if (face === 4) {
            rx = ay;
            ry = -ax;
            rz = az;
        } else {
            rx = -ay;
            ry = ax;
            rz = az;
        }
        if (rx === 1) xp = color;
        else if (rx === -1) xn = color;
        else if (ry === 1) yp = color;
        else if (ry === -1) yn = color;
        else if (rz === 1) zp = color;
        else zn = color;
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
    const at = cube.at;
    const n = Number(turns) || 0;
    for (let t = 0; t < n; t += 1) {
        for (let i = 0; i < cube.length; i += 1) {
            const c = cube[i];
            if (!onFace(face, c.x, c.y, c.z)) continue;
            turnCubie(c, face);
            at[pidx(c.x, c.y, c.z)] = c;
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
    return cube.at[pidx(x, y, z)];
}

function hasColor(c, color) {
    return c.xp === color || c.xn === color || c.yp === color || c.yn === color || c.zp === color || c.zn === color;
}

const DIR_UP = [0, 0, 0];
const DIR_FRONT = [0, 0, 0];

function centerDirTo(cube, color, out) {
    const at = cube.at;
    const centers = [
        at[pidx(1, 0, 0)], at[pidx(-1, 0, 0)],
        at[pidx(0, 1, 0)], at[pidx(0, -1, 0)],
        at[pidx(0, 0, 1)], at[pidx(0, 0, -1)],
    ];
    for (let i = 0; i < 6; i += 1) {
        const c = centers[i];
        if (c && hasColor(c, color)) {
            out[0] = c.x;
            out[1] = c.y;
            out[2] = c.z;
            return;
        }
    }
    out[0] = 0;
    out[1] = 0;
    out[2] = 0;
}

function applyMatrixNums(cube, m00, m01, m02, m10, m11, m12, m20, m21, m22) {
    const at = cube.at;
    for (let i = 0; i < cube.length; i += 1) {
        const c = cube[i];
        const nx = m00 * c.x + m01 * c.y + m02 * c.z;
        const ny = m10 * c.x + m11 * c.y + m12 * c.z;
        const nz = m20 * c.x + m21 * c.y + m22 * c.z;
        let xp = 0;
        let xn = 0;
        let yp = 0;
        let yn = 0;
        let zp = 0;
        let zn = 0;
        const paint = (ax, ay, az, color) => {
            if (!color) return;
            const rx = m00 * ax + m01 * ay + m02 * az;
            const ry = m10 * ax + m11 * ay + m12 * az;
            const rz = m20 * ax + m21 * ay + m22 * az;
            if (rx === 1) xp = color;
            else if (rx === -1) xn = color;
            else if (ry === 1) yp = color;
            else if (ry === -1) yn = color;
            else if (rz === 1) zp = color;
            else zn = color;
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
        at[pidx(nx, ny, nz)] = c;
    }
}

function reorient(cube, up, front) {
    centerDirTo(cube, up, DIR_UP);
    centerDirTo(cube, front, DIR_FRONT);
    const ux = DIR_UP[0];
    const uy = DIR_UP[1];
    const uz = DIR_UP[2];
    const px = DIR_FRONT[0];
    const py = DIR_FRONT[1];
    const pz = DIR_FRONT[2];
    if (ux === 0 && uy === 1 && uz === 0 && px === 0 && py === 0 && pz === 1) return;
    const vx = uy * pz - uz * py;
    const vy = uz * px - ux * pz;
    const vz = ux * py - uy * px;
    applyMatrixNums(cube, vx, vy, vz, ux, uy, uz, px, py, pz);
}

function ruleB(cube) {
    const c = cubieAt(cube, 1, 1, 1);
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
    const suffix = padSuffixNybbles(ny.length, version);
    for (let i = 0; i < suffix.length; i += 1) out.push(suffix[i]);
    return out;
}

function padSuffixNybbles(nyLen, version) {
    const suffix = [8];
    let len = nyLen + 1;
    if (version === 1) {
        const n = (8 - (len % 8)) % 8;
        for (let i = 0; i < n; i += 1) suffix.push(TAPE_F[i]);
        len += n;
        const remaining = 24 - len;
        for (let i = 0; i < remaining; i += 1) suffix.push(TAPE_F[i % 8]);
        return suffix;
    }
    const remaining = 12 - len;
    if (remaining > 0) {
        for (let k = 0; k < remaining; k += 1) suffix.push(TAPE_I[k % 4]);
    }
    return suffix;
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
        const c = cubieAt(cube, CX[i], CY[i], CZ[i]);
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
        const c = cubieAt(cube, EX[i], EY[i], EZ[i]);
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
            message = version === 1 ? [] : null;
            processed = 0;
        },
        push(bytes) {
            if (!cube) throw new Error("Hasher was not started.");
            const chunk = bytes;
            if (!chunk.length) return;
            if (version === 1) {
                for (let i = 0; i < chunk.length; i += 1) message.push(chunk[i]);
                const all = nybblesOf(message);
                while (processed + 8 <= all.length) {
                    applyV1Block(cube, all, processed / 8);
                    processed += 8;
                }
                return;
            }
            for (let i = 0; i < chunk.length; i += 1) {
                const b = chunk[i] & 255;
                applyV2(cube, b >> 4);
                applyV2(cube, b & 15);
            }
            processed += chunk.length * 2;
        },
        finish() {
            if (!cube) throw new Error("Hasher was not started.");
            if (version === 1) {
                const padded = padTape(nybblesOf(message), version);
                while (processed + 8 <= padded.length) {
                    applyV1Block(cube, padded, processed / 8);
                    processed += 8;
                }
            } else {
                const suffix = padSuffixNybbles(processed, 2);
                for (let i = 0; i < suffix.length; i += 1) applyV2(cube, suffix[i]);
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
