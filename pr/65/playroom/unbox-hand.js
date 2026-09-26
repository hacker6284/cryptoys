/**
 * Stand-in packets for the DoubleDeal unbox. Eight faces each, not the
 * live 4×13 / 104-card cipher grid (`DEAL_SCALE` is a different toy).
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

export const MSG_HAND = [
    "heart_1.png",
    "spade_king.png",
    "club_queen.png",
    "diamond_jack.png",
    "heart_10.png",
    "spade_9.png",
    "club_8.png",
    "diamond_7.png",
];

export const MSG_FACE_INDEXES = [13, 38, 11, 49, 22, 34, 7, 45];

function pickFaces(cardTextures, indexes, backKey, label) {
    if (!cardTextures?.faces || !cardTextures[backKey]) {
        throw new Error(`unbox ${label} needs session card textures`);
    }
    return {
        faces: indexes.map((index) => {
            const face = cardTextures.faces[index];
            if (!face) throw new Error(`unbox ${label} missing face ${index}`);
            return face;
        }),
        back: cardTextures[backKey],
    };
}

export function pickHandTextures(cardTextures) {
    return pickFaces(cardTextures, HAND_FACE_INDEXES, "red", "hand");
}

export function pickMsgTextures(cardTextures) {
    return pickFaces(cardTextures, MSG_FACE_INDEXES, "navy", "msg");
}
