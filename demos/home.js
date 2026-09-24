import { mountCube } from "./scramble/view.js";

const STICKER = {
    W: "#f4f1ea",
    Y: "#e2c44b",
    R: "#c13b3b",
    O: "#d46a2e",
    B: "#2f5f9a",
    G: "#2f8a5a",
};

const SUIT_FILE = ["club", "heart", "spade", "diamond"];
const RANK_FILE = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "jack", "queen", "king"];
const FAN_PLAIN = "toy";
const FAN_KEY = "cryptoys";

const canvas = document.querySelector("#cube");
const captionEl = document.querySelector("#cube-caption");
const digestEl = document.querySelector("#cube-digest");
const errorEl = document.querySelector("#home-error");
const input = document.querySelector("#message");
const todayBtn = document.querySelector("#today");
const faceEl = document.querySelector("#scramble-face");
const fanEl = document.querySelector("#fan");
const fanCaption = document.querySelector("#fan-caption");
const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

const view = mountCube(canvas, {
    autoRotate: !reduceMotion,
    autoRotateSpeed: 0.4,
    enableZoom: false,
    enablePan: false,
    minDistance: 6,
    maxDistance: 10,
});

function todayMessage() {
    const now = new Date();
    const year = now.getUTCFullYear();
    const month = String(now.getUTCMonth() + 1).padStart(2, "0");
    const day = String(now.getUTCDate()).padStart(2, "0");
    return `cryptoys · ${year}-${month}-${day}`;
}

function digestHex(bytes) {
    return bytes.map((byte) => byte.toString(16).padStart(2, "0")).join("").toUpperCase().slice(1);
}

function quote(text) {
    return `“${text}”`;
}

function paintFace(facelets) {
    faceEl.replaceChildren();
    for (const letter of facelets.slice(0, 9)) {
        const cell = document.createElement("span");
        cell.style.background = STICKER[letter] || "#141418";
        faceEl.append(cell);
    }
}

function cardSrc(id) {
    return `./twodeck/vendor/cards/${SUIT_FILE[Math.floor(id / 13)]}_${RANK_FILE[id % 13]}.png`;
}

function dealFan(deck) {
    fanEl.replaceChildren();
    const n = deck.length;
    deck.forEach((id, index) => {
        const img = document.createElement("img");
        img.src = cardSrc(id);
        img.alt = "";
        img.width = 62;
        img.height = 87;
        img.decoding = "async";
        img.style.setProperty("--i", String(index));
        img.style.setProperty("--n", String(n));
        img.style.zIndex = String(index + 1);
        fanEl.append(img);
    });
}

function showError(message) {
    errorEl.hidden = !message;
    errorEl.textContent = message || "";
}

let scrambleApi = null;

async function primitives() {
    if (!scrambleApi) {
        scrambleApi = await import("./scramble/generated/scramble.mjs");
    }
    return scrambleApi;
}

function seat(message, kind) {
    const { scramble_v2, update, evaluate } = scrambleApi;
    const bytes = Array.from(new TextEncoder().encode(message));
    const state = scramble_v2();
    update(state, bytes);
    const result = evaluate(state);
    const facelets = result.trace.length ? result.trace[result.trace.length - 1].facelets : "";
    view.paint(facelets);
    if (!reduceMotion) {
        canvas.classList.remove("is-seated");
        void canvas.offsetWidth;
        canvas.classList.add("is-seated");
    }
    const hex = digestHex(result.digest);
    captionEl.textContent = kind === "today"
        ? `Today’s cube is scramble_v2 of ${quote(message)}.`
        : `Live digest · scramble_v2 of ${quote(message)}.`;
    digestEl.textContent = hex;
    paintFace(facelets);
    return hex;
}

async function dealDemoHand() {
    const { ecb_encrypt } = await import("./twodeck/generated/twodeck.mjs");
    const { textToDecks, textToKey } = await import("./twodeck/cards.js");
    const blocks = textToDecks(FAN_PLAIN);
    const key = textToKey(FAN_KEY);
    const cipher = ecb_encrypt(blocks, key);
    dealFan(cipher[0]);
    fanCaption.textContent = `ECB of ${quote(FAN_PLAIN)} under key ${quote(FAN_KEY)}.`;
}

async function refresh() {
    const typed = input.value;
    todayBtn.hidden = typed.length === 0;
    const message = typed.length === 0 ? todayMessage() : typed;
    const kind = typed.length === 0 ? "today" : "live";
    try {
        await primitives();
        seat(message, kind);
        showError("");
    } catch (err) {
        const missing = String(err && err.message).includes("Failed to fetch") || err instanceof TypeError;
        showError(missing
            ? "The compiled primitives are missing. Run tools/build.sh."
            : (err instanceof Error ? err.message : "The cube could not be seated."));
    }
}

input.placeholder = todayMessage();
input.addEventListener("input", () => {
    void refresh();
});
todayBtn.addEventListener("click", () => {
    input.value = "";
    void refresh();
});
document.querySelector(".play").addEventListener("submit", (event) => {
    event.preventDefault();
    input.blur();
});

void (async () => {
    await refresh();
    try {
        await dealDemoHand();
    } catch (err) {
        fanCaption.textContent = "The compiled TwoDeck primitive is missing. Run tools/build.sh.";
        if (!errorEl.textContent) {
            showError(err instanceof Error ? err.message : "The demo hand could not be dealt.");
        }
    }
})();
