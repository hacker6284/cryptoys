import { mountTrio } from "./view.js";
import { createMegaDreifachSession } from "./session.js";
import { createSound } from "./sound.js";

const view = mountTrio(document);

// Standalone plays the chime only; the playroom adds turn, deal and card sounds.
createMegaDreifachSession({
    view,
    specUrl: new URL("./SPEC.md", import.meta.url).href,
    root: document,
    exposeTeach: true,
    sound: createSound(),
});
