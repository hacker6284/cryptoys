/**
 * Stand-in packet for the DoubleDeal unbox. Eight faces, not the live
 * 4×13 / 104-card cipher grid (`DEAL_SCALE` is a different toy).
 *
 * Indexes match `loadCardTextures` in `doubledeal/table.js`
 * (suit-major: club, heart, spade, diamond × ace…king).
 */

export const HAND = [
    "spade_1.png",
    "heart_king.png",
    "diamond_queen.png",
    "club_jack.png",
    "spade_10.png",
    "heart_9.png",
    "diamond_8.png",
    "club_7.png",
];

export const HAND_FACE_INDEXES = [26, 25, 50, 10, 35, 21, 46, 6];

export function pickHandTextures(cardTextures) {
    if (!cardTextures?.faces || !cardTextures.red) {
        throw new Error("unbox hand needs session card textures");
    }
    return {
        faces: HAND_FACE_INDEXES.map((index) => {
            const face = cardTextures.faces[index];
            if (!face) throw new Error(`unbox hand missing face ${index}`);
            return face;
        }),
        back: cardTextures.red,
    };
}
