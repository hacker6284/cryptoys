import { mountCube } from "./view.js";
import { createScrambleSession } from "./session.js";

const canvas = document.querySelector("canvas");
const view = mountCube(canvas);

createScrambleSession({
    view,
    specUrl: new URL("./SPEC.md", import.meta.url).href,
    root: document,
    exposeTeach: true,
});
