// Outward face normals (in the model's own frame) of the Facehunter dice
// (opengameart.org/content/low-poly-3d-dice, CC0), by the number printed on
// each face, read off each model's numeral atlas (demos/bs/assets/models/
// facehunter_*.glb). Opposite faces: a d10's sum to 9, a d12's to 13, a
// d6's to 7. The d10's zero face is printed "0".
export const FACES = {
    d10: {
        0: [0.35, 0.94, 0], 9: [-0.35, -0.94, 0],
        7: [0.87, -0.2, -0.46], 2: [-0.87, 0.2, 0.46],
        4: [-0.12, 0.65, -0.75], 5: [0.12, -0.65, 0.75],
        1: [0.12, -0.65, -0.75], 8: [-0.12, 0.66, 0.74],
        6: [-0.87, 0.19, -0.46], 3: [0.87, -0.19, 0.46],
    },
    d12: {
        1: [-0.53, -0.85, 0], 12: [0.53, 0.85, 0],
        2: [0.53, -0.85, 0], 11: [-0.53, 0.85, 0],
        3: [0, -0.53, 0.85], 10: [0, 0.53, -0.85],
        4: [0, -0.53, -0.85], 9: [0, 0.53, 0.85],
        5: [-0.85, 0, 0.53], 8: [0.85, 0, -0.53],
        6: [-0.85, 0, -0.53], 7: [0.85, 0, 0.53],
    },
    d6: {
        1: [0, 1, 0], 6: [0, -1, 0],
        2: [1, 0, 0], 5: [-1, 0, 0],
        3: [0, 0, 1], 4: [0, 0, -1],
    },
};
