import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const growCss = readFileSync(new URL("./grow-field.css", import.meta.url), "utf8");
const growRules = growCss.replace(/\/\*[\s\S]*?\*\//g, "");
assert.match(growCss, /--grow-field-max:\s*8\.5rem/, "cap is documented in CSS tokens");
assert.match(growRules, /--grow-field-radius:\s*8px/, "radius stays fixed; does not scale with height");
assert.match(growRules, /field-sizing:\s*content/);
assert.match(growRules, /overflow-wrap:\s*anywhere/);
assert.match(growRules, /white-space:\s*pre-wrap/);
assert.doesNotMatch(growRules, /text-overflow:\s*ellipsis/);
assert.doesNotMatch(growRules, /white-space:\s*nowrap/);

const growJs = readFileSync(new URL("./grow-field.js", import.meta.url), "utf8");
assert.match(growJs, /export function growField/);
assert.match(growJs, /export function bindGrowFields/);
assert.match(growJs, /8\.5rem/);

const playroomCss = readFileSync(new URL("../playroom/style.css", import.meta.url), "utf8");
assert.match(growRules, /\[data-message-field\][\s\S]*flex-direction:\s*column/, "filename cannot share a row with the paperclip");
assert.match(growRules, /\.file-progress\[hidden\][\s\S]*display:\s*none\s*!important/);
assert.match(growRules, /textarea\.grow-field\[hidden\][\s\S]*display:\s*none\s*!important/, "hidden Message must beat dock display:block");
assert.match(playroomCss, /\.playroom-dock textarea\.grow-field\[hidden\][\s\S]*display:\s*none\s*!important/);
assert.match(playroomCss, /\.playroom-dock textarea\.grow-field/);
assert.match(
    playroomCss,
    /\.playroom-dock textarea\.grow-field[^{]*\{[^}]*border-radius:\s*var\(--grow-field-radius/,
    "dock fields use the small fixed radius, not a pill",
);
assert.doesNotMatch(
    playroomCss,
    /\.playroom-dock textarea\.grow-field[^{]*\{[^}]*border-radius:\s*999px/,
    "tall Message must not use a pill radius",
);
assert.doesNotMatch(
    playroomCss,
    /text-overflow:\s*ellipsis/,
    "dock fields must not clip with ellipsis",
);
assert.doesNotMatch(
    playroomCss,
    /\.playroom-dock textarea[^{]*\{[^}]*white-space:\s*nowrap/,
    "dock textareas must wrap",
);
assert.doesNotMatch(
    playroomCss,
    /html\[data-algo="doubledeal"\] \.playroom-dock textarea[\s\S]*max-height:\s*2\.15rem/,
    "portrait DoubleDeal must not re-lock one-line height",
);
assert.match(
    playroomCss,
    /--io-band:\s*min\(38dvh,\s*20rem\)/,
    "portrait transport-on-stage band stays locked",
);

const adapters = readFileSync(new URL("../playroom/adapters.js", import.meta.url), "utf8");
const digestInputs = adapters.match(/<input[^>]*id="digest"[^>]*>/g) || [];
assert.equal(digestInputs.length, 0, "Digest is a growable textarea, not a one-line input");
assert.match(adapters, /<textarea id="digest" class="digest grow-field"/);
assert.match(adapters, /<textarea id="message" class="grow-field"/);
assert.match(adapters, /<textarea id="key" class="grow-field"/);
assert.match(adapters, /bindGrowFields/);
assert.match(adapters, /id="io-note"/);

const scrambleSession = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
const doubleSession = readFileSync(new URL("../doubledeal/session.js", import.meta.url), "utf8");
assert.match(scrambleSession, /bindGrowFields/);
assert.match(doubleSession, /bindGrowFields/);

const scrambleHtml = readFileSync(new URL("../scramble/index.html", import.meta.url), "utf8");
const doubleHtml = readFileSync(new URL("../doubledeal/index.html", import.meta.url), "utf8");
assert.match(scrambleHtml, /grow-field\.css/);
assert.match(doubleHtml, /grow-field\.css/);
assert.match(scrambleHtml, /class="grow-field"/);
assert.match(doubleHtml, /id="message" class="grow-field"/);
assert.match(doubleHtml, /id="output" class="grow-field"/);

console.log("grow-field tests ok");
