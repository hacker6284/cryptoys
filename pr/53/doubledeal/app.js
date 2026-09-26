import { textToDecks, textToKey } from "./cards.js";
import { createDoubleDealSession } from "./session.js";
import { mountTable } from "./view.js";

const messageEl = document.querySelector("#message");
const keyEl = document.querySelector("#key");
const view = await mountTable(
    document.querySelector("canvas"),
    textToDecks(messageEl.value)[0],
    textToKey(keyEl.value),
);

createDoubleDealSession({
    view,
    specUrl: new URL("./SPEC.md", import.meta.url).href,
    root: document,
    exposeTeach: true,
});
