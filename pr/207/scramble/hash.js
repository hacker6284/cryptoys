import { scramble_v1, scramble_v2, update, evaluate } from "./generated/scramble.mjs";

export function hashMessage(version, bytes) {
    const state = version === 2 ? scramble_v2() : scramble_v1();
    update(state, bytes);
    return evaluate(state);
}
