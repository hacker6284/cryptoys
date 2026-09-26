import * as THREE from "three";
import { CARD_D, CARD_W, DECK_H } from "./constants.js";
import { cardAssetUrl } from "../doubledeal/table.js";
import { HAND } from "./unbox-hand.js";

// Standing tuck box — same outer measure as world.makeDeckBox so
// toy-director seat / fly keep working after replaceToy.
const BW = 0.067;
const BH = DECK_H;
const BD = 0.020;
const WALL = 0.0016;
const CARD_T = 0.00135;

function loadImage(url) {
    return new Promise((resolve, reject) => {
        const image = new Image();
        image.onload = () => resolve(image);
        image.onerror = () => reject(new Error(`Could not load ${url}`));
        image.src = url;
    });
}

function paintTexture(image, anisotropy) {
    const canvas = document.createElement("canvas");
    canvas.width = image.width;
    canvas.height = image.height;
    const g = canvas.getContext("2d");
    g.fillStyle = "#fffdf8";
    g.fillRect(0, 0, canvas.width, canvas.height);
    g.drawImage(image, 0, 0);
    const texture = new THREE.CanvasTexture(canvas);
    texture.colorSpace = THREE.SRGBColorSpace;
    texture.anisotropy = anisotropy;
    return texture;
}

function makeLabel(bodyHex) {
    const canvas = document.createElement("canvas");
    canvas.width = 128;
    canvas.height = 180;
    const ctx = canvas.getContext("2d");
    ctx.fillStyle = bodyHex;
    ctx.fillRect(0, 0, 128, 180);
    ctx.fillStyle = "#e8dcc8";
    ctx.fillRect(10, 18, 108, 28);
    ctx.fillStyle = bodyHex;
    ctx.font = "bold 16px Georgia,serif";
    ctx.textAlign = "center";
    ctx.fillText("KEY", 64, 38);
    ctx.strokeStyle = "#e8dcc8";
    ctx.lineWidth = 3;
    ctx.strokeRect(8, 8, 112, 164);
    ctx.fillStyle = "#e8dcc8";
    ctx.font = "11px ui-monospace,monospace";
    ctx.fillText("cryptoys", 64, 160);
    const tex = new THREE.CanvasTexture(canvas);
    tex.colorSpace = THREE.SRGBColorSpace;
    return tex;
}

function paper(color, extras = {}) {
    return new THREE.MeshStandardMaterial({
        color,
        roughness: extras.roughness ?? 0.86,
        metalness: extras.metalness ?? 0,
        ...extras,
    });
}

function setMatsOpacity(root, opacity) {
    if (!root) return;
    root.traverse((node) => {
        if (!node.isMesh) return;
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) {
            if (!mat) continue;
            mat.transparent = opacity < 0.999;
            mat.opacity = opacity;
            if ("depthWrite" in mat) mat.depthWrite = opacity > 0.88;
        }
    });
}

function disposeObject(object, { disposeMaps = true } = {}) {
    if (!object) return;
    object.traverse?.((node) => {
        if (!node.isMesh) return;
        node.geometry?.dispose();
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) {
            if (disposeMaps) mat?.map?.dispose?.();
            mat?.dispose?.();
        }
    });
    object.parent?.remove(object);
}

export async function loadHandTextures(anisotropy = 4) {
    const faceImages = await Promise.all(HAND.map((file) => loadImage(cardAssetUrl(file))));
    const backImage = await loadImage(cardAssetUrl("back-red.png"));
    return {
        faces: faceImages.map((image) => paintTexture(image, anisotropy)),
        back: paintTexture(backImage, anisotropy),
    };
}

function cardLocalInSleeve(index, count) {
    const mid = (count - 1) / 2;
    return {
        x: 0,
        y: 0.001,
        z: (index - mid) * CARD_T,
        rx: Math.PI / 2,
        ry: 0,
        rz: 0,
    };
}

export async function createUnboxRig({ anisotropy = 4, textures, sharedMaps = false } = {}) {
    const maps = textures || await loadHandTextures(anisotropy);
    const ownsMaps = !textures;
    const group = new THREE.Group();
    group.name = "unbox-deck";

    const sleeve = new THREE.Group();
    sleeve.name = "sleeve";
    const board = paper(0x6b1e1e, { roughness: 0.84 });
    const liner = paper(0xe8dcc8, { roughness: 0.9 });
    const foil = paper(0xc4a574, { roughness: 0.42, metalness: 0.28 });

    const bottom = new THREE.Mesh(new THREE.BoxGeometry(BW, WALL, BD), board);
    bottom.position.y = -BH / 2 + WALL / 2;
    bottom.castShadow = true;
    bottom.receiveShadow = true;
    sleeve.add(bottom);

    const back = new THREE.Mesh(new THREE.BoxGeometry(BW, BH, WALL), board);
    back.position.z = -BD / 2 + WALL / 2;
    back.castShadow = true;
    sleeve.add(back);

    const frontH = BH * 0.92;
    const front = new THREE.Mesh(new THREE.BoxGeometry(BW, frontH, WALL), board);
    front.position.set(0, -BH / 2 + WALL + frontH / 2, BD / 2 - WALL / 2);
    front.castShadow = true;
    sleeve.add(front);
    const rim = new THREE.Mesh(new THREE.BoxGeometry(BW, WALL * 1.6, BD), board);
    rim.position.y = BH / 2 - WALL;
    sleeve.add(rim);

    const inner = new THREE.Mesh(new THREE.BoxGeometry(BW - WALL * 2.2, frontH * 0.72, 0.0004), liner);
    inner.position.set(0, front.position.y + 0.004, BD / 2 - WALL - 0.0004);
    sleeve.add(inner);

    for (const x of [-BW / 2 + WALL / 2, BW / 2 - WALL / 2]) {
        const side = new THREE.Mesh(new THREE.BoxGeometry(WALL, BH, BD), board);
        side.position.x = x;
        side.castShadow = true;
        sleeve.add(side);
    }

    const label = new THREE.Mesh(
        new THREE.PlaneGeometry(BW * 0.9, BH * 0.72),
        paper(0xffffff, { map: makeLabel("#6b1e1e"), roughness: 0.88 }),
    );
    label.position.set(0, -0.004, BD / 2 + 0.0005);
    sleeve.add(label);

    const flapPivot = new THREE.Group();
    flapPivot.position.set(0, BH / 2 - 0.0004, -BD / 2 + WALL);
    const flap = new THREE.Mesh(
        new THREE.BoxGeometry(BW * 0.97, 0.0032, BD * 0.98),
        [liner, liner, board, liner, liner, liner],
    );
    flap.position.set(0, 0.0016, BD * 0.49);
    flap.castShadow = true;
    flapPivot.add(flap);
    const lip = new THREE.Mesh(new THREE.BoxGeometry(BW * 0.7, 0.0007, 0.003), foil);
    lip.position.set(0, 0.0012, BD * 0.9);
    flapPivot.add(lip);
    sleeve.add(flapPivot);

    const innerGlow = new THREE.PointLight(0xffd2a0, 0, 0.28, 2);
    innerGlow.position.set(0, 0.01, 0.002);
    sleeve.add(innerGlow);

    group.add(sleeve);

    const packet = new THREE.Group();
    packet.name = "packet";
    const cards = [];
    const edge = paper(0xf7f1e6, { roughness: 0.94 });
    for (let i = 0; i < maps.faces.length; i++) {
        const face = paper(0xffffff, { map: maps.faces[i], roughness: 0.84 });
        const back = paper(0xffffff, { map: maps.back, roughness: 0.9 });
        const mesh = new THREE.Mesh(
            new THREE.BoxGeometry(CARD_W, CARD_T, CARD_D),
            [edge, edge, face, back, edge, edge],
        );
        mesh.castShadow = true;
        mesh.receiveShadow = true;
        mesh.userData.index = i;
        packet.add(mesh);
        cards.push(mesh);
    }
    group.add(packet);

    const rest = cards.map((_, i) => cardLocalInSleeve(i, cards.length));

    function applyLocal(mesh, pose) {
        mesh.position.set(pose.x, pose.y, pose.z);
        mesh.rotation.set(pose.rx, pose.ry, pose.rz);
        mesh.quaternion.setFromEuler(mesh.rotation);
    }

    function restow() {
        flapPivot.rotation.x = 0;
        packet.visible = false;
        if (packet.parent !== group) group.add(packet);
        packet.position.set(0, 0, 0);
        packet.rotation.set(0, 0, 0);
        packet.scale.set(1, 1, 1);
        setMatsOpacity(sleeve, 1);
        setMatsOpacity(packet, 1);
        innerGlow.intensity = 0;
        for (let i = 0; i < cards.length; i++) {
            const mesh = cards[i];
            if (mesh.parent !== packet) packet.add(mesh);
            applyLocal(mesh, rest[i]);
            mesh.visible = true;
            mesh.scale.set(1, 1, 1);
            setMatsOpacity(mesh, 1);
        }
        group.scale.set(1, 1, 1);
        group.updateMatrixWorld(true);
    }

    restow();

    return {
        group,
        sleeve,
        flapPivot,
        packet,
        cards,
        innerGlow,
        count: cards.length,
        restow,
        setFlap(t) {
            flapPivot.rotation.x = -2.15 * t;
        },
        releaseTo(parent) {
            if (!parent) return;
            parent.attach(packet);
        },
        attachCard(mesh, parent) {
            parent.attach(mesh);
        },
        dispose() {
            disposeObject(group, { disposeMaps: ownsMaps && !sharedMaps });
        },
    };
}

export { HAND, BW, BH, BD, CARD_T, setMatsOpacity };
