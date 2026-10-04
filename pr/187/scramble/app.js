import { mountCube } from "./view.js";
import { createScrambleSession } from "./session.js";
import { lucideSvg } from "../shared/icons.js";

const canvas = document.querySelector("canvas");
const view = mountCube(canvas);
document.querySelector("#message-file-btn").innerHTML = lucideSvg("paperclip", 16);

createScrambleSession({
    view,
    specUrl: new URL("./SPEC.md", import.meta.url).href,
    root: document,
    exposeTeach: true,
});
