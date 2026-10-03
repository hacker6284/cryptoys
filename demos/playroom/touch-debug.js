// DIAGNOSTIC (do not merge). Loaded by app.js only when the URL has
// ?touchdebug=1. Shows a pointer-events:none text overlay at the top of the
// screen with the last input events seen on window, so an iPhone screenshot
// tells us where a touch drag goes. Throwaway; no tests.
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

const MAX_LINES = 12;
const TYPES = [
    "pointerdown", "pointermove", "pointerup", "pointercancel",
    "touchstart", "touchmove", "touchend", "touchcancel",
    "gesturestart", "lostpointercapture",
];

// Record each OrbitControls instance as it connects (pose controller's is the first).
const controlsSeen = [];
const connect = OrbitControls.prototype.connect;
OrbitControls.prototype.connect = function (...args) {
    if (!controlsSeen.includes(this)) controlsSeen.push(this);
    return connect.apply(this, args);
};

const lines = [];
let camAtDown = null;
let lastHit = "";
let dirty = true;

function describe(node) {
    if (!node) return "null";
    if (node === window) return "window";
    if (node === document) return "document";
    if (node.nodeType !== 1) return node.nodeName.toLowerCase();
    let out = node.tagName.toLowerCase();
    if (node.id) out += `#${node.id}`;
    const cls = typeof node.className === "string" ? node.className.trim() : "";
    if (cls) out += `.${cls.split(/\s+/).slice(0, 2).join(".")}`;
    return out;
}

// Target as seen on window, plus the inner node and shadow hosts if retargeted.
function targetPath(event) {
    const path = event.composedPath?.() || [];
    const inner = path[0];
    let out = describe(event.target);
    if (inner && inner !== event.target) {
        const hosts = path.filter((n) => n?.shadowRoot && path.includes(n.shadowRoot));
        out += ` [in ${describe(inner)}${hosts.length ? ` < ${hosts.map(describe).join(" < ")}` : ""}]`;
    }
    return out;
}

function point(event) {
    const t = event.touches?.[0] || event.changedTouches?.[0];
    const src = t || event;
    return Number.isFinite(src.clientX) ? [Math.round(src.clientX), Math.round(src.clientY)] : null;
}

function controls() {
    return controlsSeen[0] || null;
}

function onCapture(event) {
    const type = event.type;
    const head = lines[0];
    const pid = event.pointerId ?? "";
    // Coalesce runs of the same move type (and pointer) into one line.
    if ((type === "pointermove" || type === "touchmove") && head && head.type === type && head.pid === pid) {
        head.count += 1;
        head.event = event;
        head.dp = "?";
        head.xy = point(event);
        dirty = true;
        return;
    }
    const entry = {
        type,
        pid,
        count: 1,
        event,
        dp: "?",
        target: targetPath(event),
        ptype: event.pointerType || (type.startsWith("touch") ? `touches=${event.touches?.length ?? 0}` : ""),
        xy: point(event),
        hit: "",
        ta: "",
    };
    if ((type === "pointerdown" || type === "touchstart") && entry.xy) {
        const hit = document.elementFromPoint(entry.xy[0], entry.xy[1]);
        entry.hit = describe(hit);
        entry.ta = hit ? getComputedStyle(hit).touchAction : "";
        lastHit = `${type} @${entry.xy.join(",")} -> ${entry.hit} (touch-action ${entry.ta})`;
    }
    if (type === "pointerdown") {
        const cam = controls()?.object;
        camAtDown = cam ? cam.position.clone() : null;
    }
    lines.unshift(entry);
    lines.length = Math.min(lines.length, MAX_LINES);
    dirty = true;
}

// Bubbling listener: by now other handlers have run, so defaultPrevented is real.
// "?" stays if propagation was stopped before window.
function onBubble(event) {
    const entry = lines.find((line) => line.event === event);
    if (entry) {
        entry.dp = event.defaultPrevented ? "YES" : "no";
        dirty = true;
    }
}

for (const type of TYPES) {
    window.addEventListener(type, onCapture, { capture: true, passive: true });
    window.addEventListener(type, onBubble, { passive: true });
}

const box = document.createElement("pre");
box.id = "touchdebug";
box.setAttribute("aria-hidden", "true");
box.style.cssText = [
    "position:fixed", "top:0", "left:0", "right:0", "z-index:2147483647", "margin:0",
    "padding:calc(env(safe-area-inset-top) + 4px) 6px 4px", "pointer-events:none",
    "background:rgba(0,0,0,0.78)", "color:#9f9", "font:10px/1.25 ui-monospace,Menlo,monospace",
    "white-space:pre-wrap", "word-break:break-all", "max-height:55vh", "overflow:hidden",
].join(";");
document.body.append(box);

function fmt(n) {
    return Number.isFinite(n) ? (Math.round(n * 100) / 100).toString() : "-";
}

function render() {
    const c = controls();
    const vv = window.visualViewport;
    const se = document.scrollingElement || document.documentElement;
    let moved = "n/a";
    if (c && camAtDown) {
        const d = c.object.position.distanceTo(camAtDown);
        moved = d > 1e-4 ? `YES (d=${d.toFixed(3)})` : "no";
    }
    const head = [
        `touchdebug  algo=${document.documentElement.dataset.algo || "-"}  pose=${document.documentElement.dataset.pose || "-"}`,
        `orbit: ${c ? `enabled=${c.enabled}` : "no OrbitControls"} (${controlsSeen.length} seen)  cam moved since pointerdown: ${moved}`,
        `innerH=${innerHeight} scrollH=${se.scrollHeight} scrollY=${fmt(scrollY)}  vv scale=${fmt(vv?.scale)} off=${fmt(vv?.offsetLeft)},${fmt(vv?.offsetTop)} h=${fmt(vv?.height)}`,
        `last down hit: ${lastHit || "-"}`,
        "--- newest first: type xN | target | pointerType | defaultPrevented",
    ];
    const body = lines.map((l) => {
        const n = l.count > 1 ? ` x${l.count}` : "";
        const at = l.xy ? ` @${l.xy.join(",")}` : "";
        const hit = l.hit ? ` hit=${l.hit} ta=${l.ta}` : "";
        return `${l.type}${n}${at} | ${l.target} | ${l.ptype || "-"} | dp=${l.dp}${hit}`;
    });
    box.textContent = [...head, ...body].join("\n");
}

let lastPaint = 0;
function tick(now) {
    // Camera/orbit state changes without events, so repaint ~6x/s regardless.
    if (dirty || now - lastPaint > 160) {
        render();
        dirty = false;
        lastPaint = now;
    }
    requestAnimationFrame(tick);
}
requestAnimationFrame(tick);
