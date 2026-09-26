import * as THREE from "three";
import { GLTFLoader } from "three/addons/loaders/GLTFLoader.js";
import { RGBELoader } from "three/addons/loaders/RGBELoader.js";
import {
    ASSET_BASE,
    DECK_H,
    DEN,
    SHELF_Z,
    SHELF_THICK,
    SHELF_TOP,
    TOP_Y,
    TABLE_R,
    CEIL_Y,
    SHADE_Y,
    CHEST,
    SHELF_Y0,
    SHELF_Y1,
    SLOTS,
    toyHalfHeight,
} from "./constants.js";
import { seatOnSurface } from "./motion.js";

function asset(path) {
    return new URL(path, ASSET_BASE).href;
}

function loadTex(loader, renderer, url, { color = false, repeat = [1, 1] } = {}) {
    return new Promise((resolve, reject) => {
        loader.load(
            url,
            (texture) => {
                if (color) texture.colorSpace = THREE.SRGBColorSpace;
                texture.wrapS = texture.wrapT = THREE.RepeatWrapping;
                texture.repeat.set(repeat[0], repeat[1]);
                texture.anisotropy = Math.min(8, renderer.capabilities.getMaxAnisotropy());
                resolve(texture);
            },
            undefined,
            reject,
        );
    });
}

function loadGltf(loader, url) {
    return new Promise((resolve, reject) => {
        loader.load(url, resolve, undefined, reject);
    });
}

function enableShadows(root, cast = true, receive = true) {
    root.traverse((object) => {
        if (object.isMesh) {
            object.castShadow = cast;
            object.receiveShadow = receive;
        }
    });
}

function fitToSize(root, targetMaxDim) {
    const box = new THREE.Box3().setFromObject(root);
    const size = new THREE.Vector3();
    box.getSize(size);
    const max = Math.max(size.x, size.y, size.z) || 1;
    root.scale.multiplyScalar(targetMaxDim / max);
}

function groundObject(root) {
    const box = new THREE.Box3().setFromObject(root);
    root.position.y -= box.min.y;
}

function contactShadow(parent, width, depth, y) {
    const mesh = new THREE.Mesh(
        new THREE.PlaneGeometry(width, depth),
        new THREE.MeshBasicMaterial({
            color: 0x1a1410,
            transparent: true,
            opacity: 0.2,
            depthWrite: false,
        }),
    );
    mesh.rotation.x = -Math.PI / 2;
    mesh.position.y = y;
    parent.add(mesh);
}

function applyWoodMaps(mat, maps, tint = 0xffffff) {
    if (maps.color) mat.map = maps.color;
    if (maps.normal) mat.normalMap = maps.normal;
    if (maps.rough) mat.roughnessMap = maps.rough;
    mat.color.setHex(tint);
    mat.roughness = 0.68;
    mat.metalness = 0;
    mat.needsUpdate = true;
}

function makeDeckBox(bodyColor, labelText) {
    const group = new THREE.Group();
    const bw = 0.067;
    const bh = DECK_H;
    const bd = 0.020;
    const cardboard = new THREE.MeshStandardMaterial({
        color: bodyColor,
        roughness: 0.82,
        metalness: 0,
    });
    const box = new THREE.Mesh(new THREE.BoxGeometry(bw, bh, bd), cardboard);
    box.castShadow = true;
    box.receiveShadow = true;
    group.add(box);

    const canvas = document.createElement("canvas");
    canvas.width = 128;
    canvas.height = 180;
    const ctx = canvas.getContext("2d");
    ctx.fillStyle = bodyColor === 0x6b1e1e ? "#6b1e1e" : "#1a2a44";
    ctx.fillRect(0, 0, 128, 180);
    ctx.fillStyle = "#e8dcc8";
    ctx.fillRect(10, 18, 108, 28);
    ctx.fillStyle = bodyColor === 0x6b1e1e ? "#6b1e1e" : "#1a2a44";
    ctx.font = "bold 16px Georgia,serif";
    ctx.textAlign = "center";
    ctx.fillText(labelText || "DECK", 64, 38);
    ctx.strokeStyle = "#e8dcc8";
    ctx.lineWidth = 3;
    ctx.strokeRect(8, 8, 112, 164);
    ctx.fillStyle = "#e8dcc8";
    ctx.font = "11px ui-monospace,monospace";
    ctx.fillText("cryptoys", 64, 160);
    const tex = new THREE.CanvasTexture(canvas);
    tex.colorSpace = THREE.SRGBColorSpace;
    const label = new THREE.Mesh(
        new THREE.PlaneGeometry(bw * 0.92, bh * 0.92),
        new THREE.MeshStandardMaterial({ map: tex, roughness: 0.85, metalness: 0 }),
    );
    label.position.z = bd / 2 + 0.0004;
    group.add(label);

    const flap = new THREE.Mesh(
        new THREE.BoxGeometry(bw * 0.98, 0.004, bd * 0.9),
        new THREE.MeshStandardMaterial({ color: 0xe8dcc8, roughness: 0.8 }),
    );
    flap.position.y = bh / 2 - 0.002;
    group.add(flap);
    return group;
}

function makeCubeSlot() {
    const group = new THREE.Group();
    group.name = "cube-slot";
    return group;
}

function placePlant(scene, gltf, x, y, z, maxDim, ry = 0) {
    const root = gltf.scene;
    fitToSize(root, maxDim);
    groundObject(root);
    root.position.set(x, y, z);
    root.rotation.y = ry;
    enableShadows(root, true, true);
    scene.add(root);
    return root;
}

/**
 * Kenney chest: body + sibling `lid`. Hasp/latch lives on model −Z;
 * the authored back seam is +Z. The group yaw is +π/2 against the
 * −X wall, so local −Z (hasp) faces the wall and local +Z faces
 * the table. Hinge on the WALL seam (`min.z`) and swing −X so the
 * cavity opens into the room — hinging on +Z opened into the wall.
 * Reparent with `attach` so the authored closed pose stays put.
 */
function findLidNode(root) {
    let found = null;
    root.traverse((object) => {
        const name = (object.name || "").toLowerCase();
        if (name === "lid" || name.startsWith("lid")) found = found || object;
    });
    return found;
}

function rigChestLid(chestRoot) {
    const lid = findLidNode(chestRoot);
    const pivot = new THREE.Group();
    pivot.name = "chest-lid-pivot";
    // ~83° over the wall-side hinge. Negative X lifts the lid
    // toward the table after the chest's +π/2 yaw.
    pivot.userData.openAngle = -1.45;
    if (!lid) {
        chestRoot.add(pivot);
        return pivot;
    }
    chestRoot.updateMatrixWorld(true);
    const lidWorld = new THREE.Box3().setFromObject(lid);
    const hinge = new THREE.Vector3(
        (lidWorld.min.x + lidWorld.max.x) / 2,
        lidWorld.min.y,
        lidWorld.min.z,
    );
    chestRoot.worldToLocal(hinge);
    pivot.position.copy(hinge);
    chestRoot.add(pivot);
    chestRoot.updateMatrixWorld(true);
    pivot.attach(lid);
    return pivot;
}

export async function mountWorld(canvas) {
    const renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.25));
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.outputColorSpace = THREE.SRGBColorSpace;
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 0.82;

    const scene = new THREE.Scene();
    scene.background = new THREE.Color(0x0e0b09);
    scene.fog = new THREE.Fog(0x0e0b09, 8, 18);

    const camera = new THREE.PerspectiveCamera(40, 1, 0.05, 40);
    camera.up.set(0, 1, 0);

    scene.add(new THREE.HemisphereLight(0xffd8b0, 0x0e0b09, 0.08));
    scene.add(new THREE.AmbientLight(0xffe0d0, 0.03));
    const wallFill = new THREE.DirectionalLight(0xe8dcc8, 0.02);
    wallFill.position.set(-2.2, 2.6, 2.2);
    scene.add(wallFill);
    const backFill = new THREE.DirectionalLight(0xffd8b0, 0.015);
    backFill.position.set(0.4, 2.0, -2.8);
    scene.add(backFill);

    const texLoader = new THREE.TextureLoader();
    const gltfLoader = new GLTFLoader();

    const [
        floorColor, floorN, floorR,
        woodColor, woodN, woodR,
        plasterColor, plasterN, plasterR,
        fabricN, fabricR,
        envTex,
        chestGltf,
        plantAGltf,
        plantBGltf,
        floorPlantGltf,
    ] = await Promise.all([
        loadTex(texLoader, renderer, asset("textures/woodfloor/Color.jpg"), { color: true, repeat: [3.2, 2.6] }),
        loadTex(texLoader, renderer, asset("textures/woodfloor/NormalGL.jpg"), { repeat: [3.2, 2.6] }),
        loadTex(texLoader, renderer, asset("textures/woodfloor/Roughness.jpg"), { repeat: [3.2, 2.6] }),
        loadTex(texLoader, renderer, asset("textures/wood/Color.jpg"), { color: true, repeat: [2, 2] }),
        loadTex(texLoader, renderer, asset("textures/wood/NormalGL.jpg"), { repeat: [2, 2] }),
        loadTex(texLoader, renderer, asset("textures/wood/Roughness.jpg"), { repeat: [2, 2] }),
        loadTex(texLoader, renderer, asset("textures/plaster/Color.jpg"), { color: true, repeat: [2.4, 1.4] }),
        loadTex(texLoader, renderer, asset("textures/plaster/NormalGL.jpg"), { repeat: [2.4, 1.4] }),
        loadTex(texLoader, renderer, asset("textures/plaster/Roughness.jpg"), { repeat: [2.4, 1.4] }),
        loadTex(texLoader, renderer, asset("textures/fabric/NormalGL.jpg"), { repeat: [4, 4] }),
        loadTex(texLoader, renderer, asset("textures/fabric/Roughness.jpg"), { repeat: [4, 4] }),
        new Promise((resolve, reject) => {
            new RGBELoader().load(asset("hdri/solitude_interior_1k.hdr"), resolve, undefined, reject);
        }),
        loadGltf(gltfLoader, asset("models/chest.glb")),
        loadGltf(gltfLoader, asset("models/kenney_pottedPlant.glb")),
        loadGltf(gltfLoader, asset("models/kenney_plantSmall2.glb")),
        loadGltf(gltfLoader, asset("models/houseplant.glb")),
    ]);

    envTex.mapping = THREE.EquirectangularReflectionMapping;
    scene.environment = envTex;
    scene.environmentIntensity = 0.06;

    const woodMaps = { color: woodColor, normal: woodN, rough: woodR };
    const wood = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.68, metalness: 0 });
    applyWoodMaps(wood, woodMaps);
    const woodDark = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.74, metalness: 0 });
    applyWoodMaps(woodDark, woodMaps, 0xb89a7c);

    const plaster = new THREE.MeshStandardMaterial({
        map: plasterColor,
        normalMap: plasterN,
        roughnessMap: plasterR,
        color: 0xb8a890,
        roughness: 0.94,
        metalness: 0,
    });
    const floorM = new THREE.MeshStandardMaterial({
        map: floorColor,
        normalMap: floorN,
        roughnessMap: floorR,
        color: 0xc8b49a,
        roughness: 0.88,
        metalness: 0,
    });
    const feltM = new THREE.MeshStandardMaterial({
        color: 0x1c684a,
        normalMap: fabricN,
        roughnessMap: fabricR,
        roughness: 0.92,
        metalness: 0,
    });
    feltM.normalScale.set(0.55, 0.55);
    const shelfM = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.72, metalness: 0 });
    applyWoodMaps(shelfM, woodMaps, 0xc4a888);
    const rimMat = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.65, metalness: 0 });
    applyWoodMaps(rimMat, woodMaps, 0xd2b090);

    const floor = new THREE.Mesh(new THREE.PlaneGeometry(5.8, 4.8), floorM);
    floor.rotation.x = -Math.PI / 2;
    floor.receiveShadow = true;
    scene.add(floor);

    const ceiling = new THREE.Mesh(
        new THREE.PlaneGeometry(5.8, 4.8),
        new THREE.MeshStandardMaterial({
            color: 0x6a5e52,
            roughness: 0.96,
            metalness: 0,
            side: THREE.DoubleSide,
        }),
    );
    ceiling.rotation.x = Math.PI / 2;
    ceiling.position.y = CEIL_Y + 0.015;
    scene.add(ceiling);

    function wall(w, h, x, y, z, ry = 0) {
        const mesh = new THREE.Mesh(new THREE.PlaneGeometry(w, h), plaster);
        mesh.position.set(x, y, z);
        mesh.rotation.y = ry;
        mesh.receiveShadow = true;
        scene.add(mesh);
    }
    wall(5.8, 2.7, 0, 1.35, SHELF_Z - 0.22);
    wall(4.8, 2.7, -2.85, 1.35, 0, Math.PI / 2);
    wall(4.8, 2.7, 2.85, 1.35, 0, -Math.PI / 2);

    const pendantGroup = new THREE.Group();
    pendantGroup.position.set(DEN.x, 0, DEN.z);
    const roseMat = new THREE.MeshStandardMaterial({ color: 0xcfc3b0, roughness: 0.75, metalness: 0.05 });
    const metalMat = new THREE.MeshStandardMaterial({ color: 0x4a4036, roughness: 0.45, metalness: 0.55 });
    const shadeMat = new THREE.MeshStandardMaterial({ color: 0xd9c4a0, roughness: 0.85, side: THREE.DoubleSide });
    const cordMat = new THREE.MeshStandardMaterial({ color: 0x2a241c, roughness: 0.9, metalness: 0 });
    const rose = new THREE.Mesh(new THREE.CylinderGeometry(0.07, 0.09, 0.03, 24), roseMat);
    rose.position.y = CEIL_Y;
    pendantGroup.add(rose);
    const roseCap = new THREE.Mesh(new THREE.CylinderGeometry(0.025, 0.025, 0.04, 12), metalMat);
    roseCap.position.y = CEIL_Y - 0.03;
    pendantGroup.add(roseCap);
    const cordLen = CEIL_Y - 0.04 - (SHADE_Y + 0.07);
    const cord = new THREE.Mesh(new THREE.CylinderGeometry(0.006, 0.006, cordLen, 8), cordMat);
    cord.position.y = SHADE_Y + 0.07 + cordLen / 2;
    pendantGroup.add(cord);
    const shade = new THREE.Mesh(new THREE.CylinderGeometry(0.1, 0.2, 0.16, 32, 1, true), shadeMat);
    shade.position.y = SHADE_Y;
    shade.castShadow = false;
    pendantGroup.add(shade);
    const shadeRing = new THREE.Mesh(new THREE.TorusGeometry(0.1, 0.008, 8, 32), metalMat);
    shadeRing.rotation.x = Math.PI / 2;
    shadeRing.position.y = SHADE_Y + 0.078;
    pendantGroup.add(shadeRing);
    const bulb = new THREE.Mesh(
        new THREE.SphereGeometry(0.038, 16, 16),
        new THREE.MeshBasicMaterial({ color: 0xffd090 }),
    );
    bulb.position.y = SHADE_Y - 0.02;
    pendantGroup.add(bulb);
    scene.add(pendantGroup);

    const pendant = new THREE.SpotLight(0xffa860, 14.0, 8.0, Math.PI / 3.5, 0.8, 1.0);
    pendant.position.set(DEN.x, SHADE_Y - 0.02, DEN.z);
    pendant.target.position.set(DEN.x, 0.75, DEN.z);
    pendant.castShadow = true;
    pendant.shadow.mapSize.set(512, 512);
    pendant.shadow.bias = -0.0002;
    pendant.shadow.normalBias = 0.03;
    scene.add(pendant);
    scene.add(pendant.target);
    const pendantWash = new THREE.SpotLight(0xffb878, 5.5, 9.0, Math.PI / 2.4, 0.95, 1.0);
    pendantWash.position.set(DEN.x, SHADE_Y - 0.02, DEN.z);
    pendantWash.target.position.set(DEN.x, 0.4, DEN.z);
    scene.add(pendantWash);
    scene.add(pendantWash.target);
    const pendantFill = new THREE.PointLight(0xffa860, 3.5, 2.5, 2);
    pendantFill.position.set(DEN.x, SHADE_Y - 0.08, DEN.z);
    scene.add(pendantFill);

    const sconceMetal = new THREE.MeshStandardMaterial({ color: 0x5a4e42, roughness: 0.45, metalness: 0.55 });
    const sconceShade = new THREE.MeshStandardMaterial({
        color: 0xe8d4b0,
        roughness: 0.88,
        side: THREE.DoubleSide,
        emissive: 0xffb070,
        emissiveIntensity: 0.35,
    });
    const sconceGlow = new THREE.MeshBasicMaterial({ color: 0xffc878 });

    function addWallSconce(x, y, z, faceY) {
        const group = new THREE.Group();
        group.position.set(x, y, z);
        group.rotation.y = faceY;
        const plate = new THREE.Mesh(new THREE.CylinderGeometry(0.045, 0.05, 0.02, 16), sconceMetal);
        plate.rotation.z = Math.PI / 2;
        group.add(plate);
        const arm = new THREE.Mesh(new THREE.BoxGeometry(0.035, 0.012, 0.012), sconceMetal);
        arm.position.x = 0.024;
        group.add(arm);
        const capR = 0.088;
        const capTheta = Math.PI * 0.55;
        const cap = new THREE.Mesh(
            new THREE.SphereGeometry(capR, 24, 16, 0, Math.PI * 2, 0, capTheta),
            sconceShade,
        );
        cap.rotation.z = -Math.PI / 2;
        cap.position.set(0.068, 0, 0);
        cap.castShadow = false;
        group.add(cap);
        const rimX = 0.068 + capR * Math.cos(capTheta);
        const rimR = capR * Math.sin(capTheta);
        const lip = new THREE.Mesh(new THREE.TorusGeometry(rimR, 0.005, 8, 28), sconceMetal);
        lip.rotation.y = Math.PI / 2;
        lip.position.set(rimX, 0, 0);
        group.add(lip);
        const glow = new THREE.Mesh(new THREE.SphereGeometry(0.018, 12, 12), sconceGlow);
        glow.position.set(0.042, 0, 0);
        group.add(glow);
        scene.add(group);
        const light = new THREE.PointLight(0xffb878, 1.15, 3.0, 2);
        light.position.set(x + Math.cos(faceY) * 0.12, y - 0.02, z - Math.sin(faceY) * 0.12);
        scene.add(light);
        return light;
    }
    addWallSconce(-2.78, 1.72, CHEST.z - 0.15, 0);
    addWallSconce(1.35, 1.68, SHELF_Z + 0.08, -Math.PI / 2);

    const shelfWash = new THREE.SpotLight(0xffe0c0, 1.85, 5.2, Math.PI / 2.0, 0.9, 1.35);
    shelfWash.position.set(-0.2, 2.15, SHELF_Z + 1.7);
    shelfWash.target.position.set(-0.5, 1.05, SHELF_Z);
    scene.add(shelfWash);
    scene.add(shelfWash.target);
    // A quiet key on the cube slot so the seated toy reads at rest and
    // the empty ring reads after it lifts — not a hover-only trick.
    const cubeSlotKey = new THREE.SpotLight(0xffd8b0, 2.6, 2.6, Math.PI / 5, 0.45, 1.3);
    cubeSlotKey.position.set(SLOTS.cube.x + 0.12, SHELF_Y1 + 0.62, SHELF_Z + 0.62);
    cubeSlotKey.target.position.set(SLOTS.cube.x, SHELF_Y1 + 0.04, SHELF_Z);
    scene.add(cubeSlotKey);
    scene.add(cubeSlotKey.target);

    const chestKiss = new THREE.PointLight(0xffc090, 0.55, 2.5, 2);
    chestKiss.position.set(CHEST.x + 0.8, 0.18, CHEST.z + 0.3);
    scene.add(chestKiss);

    const tableGroup = new THREE.Group();
    tableGroup.position.set(DEN.x, 0, DEN.z);
    const apron = new THREE.Mesh(
        new THREE.CylinderGeometry(TABLE_R - 0.04, TABLE_R - 0.06, 0.09, 48),
        woodDark,
    );
    apron.position.y = TOP_Y - 0.055;
    apron.castShadow = true;
    tableGroup.add(apron);
    const tableTop = new THREE.Mesh(new THREE.CylinderGeometry(TABLE_R, TABLE_R, 0.04, 64), wood);
    tableTop.position.y = TOP_Y;
    tableTop.castShadow = true;
    tableTop.receiveShadow = true;
    tableGroup.add(tableTop);
    const rim = new THREE.Mesh(new THREE.TorusGeometry(TABLE_R - 0.02, 0.028, 12, 64), rimMat);
    rim.rotation.x = Math.PI / 2;
    rim.position.y = TOP_Y + 0.022;
    rim.castShadow = true;
    rim.receiveShadow = true;
    tableGroup.add(rim);
    const felt = new THREE.Mesh(
        new THREE.CylinderGeometry(TABLE_R - 0.08, TABLE_R - 0.08, 0.012, 64),
        feltM,
    );
    felt.position.y = TOP_Y + 0.026;
    felt.receiveShadow = true;
    tableGroup.add(felt);
    const pedestal = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.16, TOP_Y - 0.08, 24), wood);
    pedestal.position.y = (TOP_Y - 0.08) / 2;
    pedestal.castShadow = true;
    tableGroup.add(pedestal);
    const footRing = new THREE.Mesh(new THREE.CylinderGeometry(0.42, 0.48, 0.04, 32), woodDark);
    footRing.position.y = 0.02;
    footRing.castShadow = true;
    footRing.receiveShadow = true;
    tableGroup.add(footRing);
    [0, 1, 2, 3].forEach((i) => {
        const a = (i / 4) * Math.PI * 2 + Math.PI / 4;
        const foot = new THREE.Mesh(new THREE.BoxGeometry(0.14, 0.035, 0.55), wood);
        foot.position.set(Math.cos(a) * 0.18, 0.025, Math.sin(a) * 0.18);
        foot.rotation.y = -a;
        foot.castShadow = true;
        tableGroup.add(foot);
    });
    contactShadow(tableGroup, 1.05, 1.05, 0.002);
    scene.add(tableGroup);

    const shelf = new THREE.Mesh(new THREE.BoxGeometry(4.4, SHELF_THICK, 0.30), shelfM);
    shelf.position.set(0, SHELF_Y1, SHELF_Z);
    shelf.castShadow = true;
    shelf.receiveShadow = true;
    scene.add(shelf);
    const shelf2 = shelf.clone();
    shelf2.position.y = SHELF_Y0;
    scene.add(shelf2);
    const backboard = new THREE.Mesh(new THREE.BoxGeometry(4.4, 0.95, 0.02), woodDark);
    backboard.position.set(0, 1.0, SHELF_Z - 0.14);
    backboard.castShadow = true;
    scene.add(backboard);
    [-2.0, -0.7, 0.7, 2.0].forEach((x) => {
        const bracket = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.95, 0.04), woodDark);
        bracket.position.set(x, 1.0, SHELF_Z + 0.12);
        bracket.castShadow = true;
        scene.add(bracket);
    });

    function makeSlot(x) {
        const group = new THREE.Group();
        const disk = new THREE.Mesh(
            new THREE.CircleGeometry(0.048, 24),
            new THREE.MeshBasicMaterial({
                color: 0x2a2218,
                transparent: true,
                opacity: 0.4,
                depthWrite: false,
            }),
        );
        disk.rotation.x = -Math.PI / 2;
        group.add(disk);
        const ring = new THREE.Mesh(
            new THREE.RingGeometry(0.048, 0.078, 24),
            new THREE.MeshBasicMaterial({
                color: 0x8a7358,
                transparent: true,
                opacity: 0.55,
                side: THREE.DoubleSide,
                depthWrite: false,
            }),
        );
        ring.rotation.x = -Math.PI / 2;
        group.add(ring);
        group.position.set(x, SHELF_TOP + 0.002, SHELF_Z);
        group.visible = false;
        scene.add(group);
        return group;
    }

    const slots = {
        deck: { ...SLOTS.deck, slot: makeSlot(SLOTS.deck.x) },
        cube: { ...SLOTS.cube, slot: makeSlot(SLOTS.cube.x) },
    };

    const chestGroup = new THREE.Group();
    chestGroup.position.set(CHEST.x, 0, CHEST.z);
    chestGroup.rotation.y = Math.PI / 2;
    const chestRoot = chestGltf.scene;
    fitToSize(chestRoot, 0.95);
    groundObject(chestRoot);
    enableShadows(chestRoot, true, true);
    chestRoot.traverse((object) => {
        if (!object.isMesh) return;
        const isLid = (object.name || "").toLowerCase().includes("lid");
        const mat = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.76, metalness: 0 });
        applyWoodMaps(mat, woodMaps, isLid ? 0xc9a888 : 0xb8926e);
        object.material = mat;
    });
    const chestLidPivot = rigChestLid(chestRoot);
    chestGroup.add(chestRoot);
    {
        const box = new THREE.Box3().setFromObject(chestGroup);
        const pad = 0.04;
        chestGroup.position.x += (-2.85 + pad) - box.min.x;
    }
    contactShadow(chestGroup, 1.05, 0.75, 0.002);
    scene.add(chestGroup);

    const toys = {
        deck: makeDeckBox(0x6b1e1e, "KEY"),
        deck2: makeDeckBox(0x1a2a44, "MSG"),
        cube: makeCubeSlot(),
    };
    Object.values(toys).forEach((toy) => scene.add(toy));

    function feltTopY() {
        return TOP_Y + 0.032;
    }

    // Shared post-scale AABB seat. Lowest measured point lands on the
    // surface — scale changes must not float or clip.
    function seatOn(object, { x, surfaceY, z, rotation, name }) {
        return seatOnSurface(object, {
            x,
            surfaceY,
            z,
            rotation,
            fallbackHalfHeight: toyHalfHeight(name),
        });
    }

    function getChestPose(name) {
        const box = new THREE.Box3().setFromObject(chestGroup);
        const x = Number.isFinite(box.min.x)
            ? box.min.x * 0.42 + box.max.x * 0.58
            : CHEST.x + 0.12;
        const z = Number.isFinite(box.min.z)
            ? box.min.z * 0.52 + box.max.z * 0.48
            : CHEST.z;
        const surfaceY = Number.isFinite(box.min.y) ? box.min.y + 0.055 : 0.08;
        return seatOn(toys[name], {
            x,
            surfaceY,
            z,
            rotation: { x: 0, y: Math.PI / 2 + 0.1, z: 0 },
            name: name === "deck2" ? "deck" : name,
        });
    }

    function getBoxRestPose(name) {
        const side = name === "deck2" ? -1 : 1;
        return seatOn(toys[name], {
            x: DEN.x + side * 0.78,
            surfaceY: feltTopY() + 0.001,
            z: DEN.z - 0.34,
            rotation: { x: 0, y: side * 0.2, z: 0 },
            name: name === "deck2" ? "deck" : name,
        });
    }

    function getShelfPose(name) {
        if (name === "deck2") return getChestPose(name);
        const slot = slots[name];
        if (!slot) return null;
        return seatOn(toys[name], {
            x: slot.x,
            surfaceY: SHELF_TOP + 0.001,
            z: SHELF_Z,
            // Yaw only — pitch was driving corners through the board.
            rotation: { x: 0, y: name === "cube" ? 0.45 : 0.15, z: 0 },
            name,
        });
    }

    function getTablePose(name) {
        if (name === "deck2") return getBoxRestPose(name);
        return seatOn(toys[name], {
            x: DEN.x,
            surfaceY: feltTopY() + 0.001,
            z: DEN.z,
            rotation: { x: 0, y: 0, z: 0 },
            name,
        });
    }

    function applyPose(object, pose) {
        if (!object || !pose) return;
        object.position.set(pose.position.x, pose.position.y, pose.position.z);
        object.rotation.set(pose.rotation.x, pose.rotation.y, pose.rotation.z);
        object.quaternion.setFromEuler(object.rotation);
    }

    function shelfHome(name) {
        const toy = toys[name];
        const pose = getShelfPose(name);
        if (!toy || !pose) return;
        toy.visible = true;
        applyPose(toy, pose);
        toy.userData.seatSurface = "shelf";
        if (slots[name]) slots[name].slot.visible = false;
    }

    function setSlotEmpty(name, empty) {
        if (slots[name]) slots[name].slot.visible = Boolean(empty);
    }

    function replaceToy(name, next) {
        const prev = toys[name];
        if (prev) {
            prev.visible = false;
            if (prev.parent) prev.parent.remove(prev);
            else scene.remove(prev);
        }
        toys[name] = next;
        next.visible = true;
        if (next && !next.parent) scene.add(next);
        return prev;
    }

    function applyEmissive(root, on, { chest = false } = {}) {
        root.traverse((object) => {
            if (!object.isMesh) return;
            const mats = Array.isArray(object.material) ? object.material : [object.material];
            for (const mat of mats) {
                if (!mat || !mat.emissive) continue;
                mat.emissive.setHex(on ? 0xd48630 : 0x000000);
                mat.emissiveIntensity = on ? 0.62 : 0;
            }
        });
        let light = root.userData.rimLight;
        if (!light) {
            light = new THREE.PointLight(0xffc078, 0, chest ? 1.6 : 0.9, 2);
            light.position.set(chest ? 0.15 : 0.06, chest ? 0.22 : 0.08, chest ? 0.12 : 0.12);
            root.add(light);
            root.userData.rimLight = light;
        }
        light.intensity = on ? (chest ? 1.05 : 3.2) : 0;
    }

    function createTravelLight(toy) {
        if (toy.userData.travelLight) return toy.userData.travelLight;
        const light = new THREE.PointLight(0xffd0a0, 0, 1.4, 2);
        light.position.set(0.08, 0.1, 0.12);
        toy.add(light);
        toy.userData.travelLight = light;
        return light;
    }

    function setHighlight(names, on) {
        const list = Array.isArray(names) ? names : [names];
        for (const name of list) {
            if (name === "chest") {
                applyEmissive(chestGroup, on, { chest: true });
                continue;
            }
            const toy = toys[name];
            if (toy) applyEmissive(toy, on);
        }
    }

    shelfHome("deck");
    shelfHome("cube");
    shelfHome("deck2");

    placePlant(scene, plantAGltf, 0.35, SHELF_Y1, SHELF_Z, 0.22, 0.2);
    placePlant(scene, plantBGltf, 1.05, SHELF_Y1, SHELF_Z, 0.18, -0.35);
    placePlant(scene, floorPlantGltf, -2.15, 0, SHELF_Z + 0.35, 0.55, 0.4);

    function setChestLid(t) {
        const k = Math.min(1, Math.max(0, t));
        const angle = chestLidPivot?.userData.openAngle ?? -1.45;
        if (chestLidPivot) chestLidPivot.rotation.x = angle * k;
        chestGroup.userData.lid = k;
    }

    function getChestLid() {
        return chestGroup.userData.lid || 0;
    }

    function setChestOpen(open) {
        setChestLid(open ? 1 : 0);
    }
    setChestOpen(false);

    function resize() {
        const width = canvas.clientWidth || window.innerWidth;
        const height = canvas.clientHeight || window.innerHeight;
        const ratio = Math.min(window.devicePixelRatio || 1, 1.25);
        renderer.setPixelRatio(ratio);
        renderer.setSize(width, height, false);
        camera.aspect = width / Math.max(1, height);
        camera.updateProjectionMatrix();
    }

    function render() {
        // Re-apply Twisty fit after cubing.js's own rAF so a late
        // matrix/scale write cannot stick as the drawn size.
        toys.cube?.userData?.keepFitted?.();
        renderer.render(scene, camera);
    }

    function dispose() {
        renderer.dispose();
    }

    resize();

    return {
        scene,
        camera,
        renderer,
        toys,
        slots,
        table: { group: tableGroup, radius: TABLE_R, topY: TOP_Y, feltTopY: feltTopY(), den: { ...DEN } },
        chest: { group: chestGroup, setOpen: setChestOpen, setLid: setChestLid, getLid: getChestLid },
        getShelfPose,
        getTablePose,
        getChestPose,
        getBoxRestPose,
        setChestLid,
        getChestLid,
        applyPose,
        setSlotEmpty,
        replaceToy,
        setHighlight,
        createTravelLight,
        shelfHome,
        resize,
        render,
        dispose,
    };
}
