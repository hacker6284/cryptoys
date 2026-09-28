import { bindTeachKeys, headingId, nextGroup, setDisabled, stampHeadingIds } from "./teach.js";

export function sessionScope(root) {
    const abort = new AbortController();
    return {
        abort,
        listen: { signal: abort.signal },
        $: (sel) => root.querySelector(sel),
        $$: (sel) => root.querySelectorAll(sel),
    };
}

function renderMarkdown(markdown) {
    const lines = markdown.replace(/\r\n/g, "\n").split("\n");
    let html = "";
    let i = 0;
    const esc = (s) => s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
    const inline = (s) => esc(s)
        .replace(/`([^`]+)`/g, "<code>$1</code>")
        .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
        .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
    const hid = (title) => ` id="${headingId(title)}"`;
    while (i < lines.length) {
        const line = lines[i];
        if (line.startsWith("```")) {
            const buf = [];
            i += 1;
            while (i < lines.length && !lines[i].startsWith("```")) {
                buf.push(lines[i]);
                i += 1;
            }
            i += 1;
            html += `<pre><code>${esc(buf.join("\n"))}</code></pre>`;
            continue;
        }
        if (line.startsWith("|")) {
            const rows = [];
            while (i < lines.length && lines[i].startsWith("|")) {
                rows.push(lines[i]);
                i += 1;
            }
            const cells = (row) => row.split("|").slice(1, -1).map((cell) => cell.trim());
            const head = cells(rows[0]);
            const body = rows.slice(2).map(cells);
            html += "<table><thead><tr>" + head.map((cell) => `<th>${inline(cell)}</th>`).join("")
                + "</tr></thead><tbody>";
            for (const row of body) {
                html += "<tr>" + row.map((cell) => `<td>${inline(cell)}</td>`).join("") + "</tr>";
            }
            html += "</tbody></table>";
            continue;
        }
        if (line.startsWith("### ")) {
            const title = line.slice(4);
            html += `<h3${hid(title)}>${inline(title)}</h3>`;
            i += 1;
            continue;
        }
        if (line.startsWith("## ")) {
            const title = line.slice(3);
            html += `<h2${hid(title)}>${inline(title)}</h2>`;
            i += 1;
            continue;
        }
        if (line.startsWith("# ")) {
            const title = line.slice(2);
            html += `<h1${hid(title)}>${inline(title)}</h1>`;
            i += 1;
            continue;
        }
        if (line.startsWith("- ")) {
            html += "<ul>";
            while (i < lines.length && lines[i].startsWith("- ")) {
                html += `<li>${inline(lines[i].slice(2))}</li>`;
                i += 1;
            }
            html += "</ul>";
            continue;
        }
        if (line.trim() === "") {
            i += 1;
            continue;
        }
        html += `<p>${inline(line)}</p>`;
        i += 1;
    }
    return html;
}

export async function openSpec(root, specUrl, heading, slice = (markdown) => markdown) {
    const specDialog = root.querySelector("#spec");
    const specBody = root.querySelector("#spec-body");
    if (!specDialog || !specBody) throw new Error("The specification dialog is missing.");
    const response = await fetch(specUrl);
    if (!response.ok) throw new Error("The specification file is missing. Run tools/build.sh.");
    specBody.innerHTML = renderMarkdown(slice(await response.text()));
    stampHeadingIds(specBody);
    specDialog.showModal();
    if (heading) {
        const target = specBody.querySelector("#" + CSS.escape(headingId(heading)));
        if (target) target.scrollIntoView();
    }
}

export function renderTeachStep(root, note, showSpec, viewI, count) {
    const teachCard = root.querySelector("#teach-card");
    teachCard.replaceChildren();
    const kicker = document.createElement("p");
    kicker.className = "kicker";
    kicker.textContent = note.kicker;
    const title = document.createElement("h2");
    title.textContent = note.title;
    const math = document.createElement("p");
    math.className = "math";
    math.textContent = note.math;
    const why = document.createElement("p");
    why.className = "why";
    why.textContent = note.why;
    const spec = document.createElement("button");
    spec.type = "button";
    spec.className = "inline-link";
    spec.textContent = `SPEC · ${note.spec}`;
    spec.addEventListener("click", () => showSpec(note.spec));
    teachCard.append(kicker, title, math, why, spec);
    const pos = root.querySelector("#teach-pos");
    if (pos) pos.textContent = `${Math.min(viewI + 1, count)} / ${count}`;
}

export function bindSegmented(root, name, pick, listen) {
    const buttons = root.querySelectorAll(`[data-${name}]`);
    buttons.forEach((button) => {
        button.addEventListener("click", () => {
            buttons.forEach((item) => item.classList.toggle("on", item === button));
            pick(button.dataset[name]);
        }, listen);
    });
}

export function syncJumpButtons(root, cursor, count) {
    const atStart = cursor < 0;
    const atEnd = cursor >= count - 1;
    root.querySelectorAll("[data-jump]").forEach((button) => {
        setDisabled(button, button.dataset.jump.endsWith("back") ? atStart : atEnd);
    });
}

export function bindTransport(root, session, listen) {
    const { play, step, skipToEnd, reset, showSpec } = session;
    const { trace, teaching, viewedIndex, stepBy, jumpTo, stageKey, roundKey } = session;
    const $ = (sel) => root.querySelector(sel);
    const jumpGroup = (key, dir) => void jumpTo(nextGroup(trace(), Math.max(0, viewedIndex()), key, dir) - 1, false);
    const jumps = {
        back: [-1], fwd: [1],
        "stage-back": [-1, stageKey], "stage-fwd": [1, stageKey],
        "round-back": [-1, roundKey], "round-fwd": [1, roundKey],
    };
    $("#play")?.addEventListener("click", () => void play(), listen);
    $("#skip-end")?.addEventListener("click", () => skipToEnd(), listen);
    $("#step")?.addEventListener("click", () => step(), listen);
    $("#reset")?.addEventListener("click", () => reset(), listen);
    $("#spec-btn")?.addEventListener("click", () => showSpec(), listen);
    $("#spec-close")?.addEventListener("click", () => $("#spec")?.close(), listen);

    root.querySelectorAll("[data-jump]").forEach((button) => {
        button.addEventListener("click", () => {
            const [dir, key] = jumps[button.dataset.jump] ?? [];
            if (!dir) return;
            if (key) jumpGroup(key, dir);
            else void stepBy(dir);
        }, listen);
    });

    bindTeachKeys({
        step: (dir) => { if (teaching()) void stepBy(dir); },
        stage: (dir) => {
            if (teaching() && trace().length) jumpGroup(stageKey, dir);
        },
        home: () => { if (teaching()) void jumpTo(-1, false); },
        end: () => { if (teaching() && trace().length) void jumpTo(trace().length - 1, false); },
    }, listen);
}
