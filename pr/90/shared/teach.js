export function headingId(text) {
    return String(text)
        .replace(/\\[()[\]]/g, "")
        .toLowerCase()
        .replace(/[^\w]+/g, "-")
        .replace(/^-|-$/g, "");
}

export function stampHeadingIds(root) {
    root.querySelectorAll("h1, h2, h3").forEach((node) => {
        if (!node.id) node.id = headingId(node.textContent);
    });
}

export function bindTeachKeys(handlers, { signal } = {}) {
    window.addEventListener("keydown", (event) => {
        const tag = event.target && event.target.tagName;
        if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
        if (event.key === "ArrowRight" && event.shiftKey) handlers.stage?.(1);
        else if (event.key === "ArrowLeft" && event.shiftKey) handlers.stage?.(-1);
        else if (event.key === "ArrowRight") handlers.step?.(1);
        else if (event.key === "ArrowLeft") handlers.step?.(-1);
        else if (event.key === "Home") handlers.home?.();
        else if (event.key === "End") handlers.end?.();
        else return;
        event.preventDefault();
    }, signal ? { signal } : undefined);
}

export function firstOfGroup(trace, index, keyOf) {
    const key = keyOf(trace[index]);
    let i = index;
    while (i > 0 && keyOf(trace[i - 1]) === key) i -= 1;
    return i;
}

export function nextGroup(trace, index, keyOf, dir) {
    if (dir < 0) {
        const start = firstOfGroup(trace, index, keyOf);
        if (start === 0) return 0;
        return firstOfGroup(trace, start - 1, keyOf);
    }
    const key = keyOf(trace[index]);
    let i = index + 1;
    while (i < trace.length && keyOf(trace[i]) === key) i += 1;
    return Math.min(trace.length - 1, i);
}

export function setDisabled(el, on) {
    if (!el) return;
    el.disabled = on;
}

export function renderOutline(root, sections, currentKey, onJump) {
    root.replaceChildren();
    for (const section of sections) {
        const wrap = document.createElement("details");
        wrap.open = section.open || section.items.some((item) => item.key === currentKey);
        const mark = document.createElement("summary");
        mark.textContent = section.title;
        wrap.append(mark);
        for (const item of section.items) {
            const button = document.createElement("button");
            button.type = "button";
            button.className = "outline-item" + (item.key === currentKey ? " on" : "");
            button.textContent = item.label;
            button.addEventListener("click", () => onJump(item.index));
            wrap.append(button);
        }
        root.append(wrap);
    }
    const active = root.querySelector(".outline-item.on");
    if (active) active.scrollIntoView({ block: "nearest" });
}

export function cardName(id) {
    const ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];
    const suits = ["♣", "♥", "♠", "♦"];
    return ranks[id % 13] + suits[Math.floor(id / 13)];
}

export function colorName(letter) {
    return { W: "white", Y: "yellow", R: "red", O: "orange", B: "blue", G: "green" }[letter] || letter;
}
