// A picked file's Scramble hash, off the main thread: the typed Message
// path's one update + evaluate on the generated module.
import { scramble_v1, scramble_v2, update, evaluate } from "./generated/scramble.mjs";

self.onmessage = ({ data: { version, bytes } }) => {
    const state = version === 2 ? scramble_v2() : scramble_v1();
    update(state, bytes);
    self.postMessage(evaluate(state));
};
