import assert from "node:assert/strict";

function node(dataset = {}) {
    const listeners = [];
    return {
        dataset,
        disabled: false,
        addEventListener(type, fn, opts) {
            listeners.push({ type, fn, opts });
        },
        dispatch(type, event = {}) {
            for (const item of listeners) {
                if (item.type === type && !item.opts?.signal?.aborted) item.fn(event);
            }
        },
        click() {
            this.dispatch("click");
        },
    };
}

function fakeRoot(byId, groups = {}) {
    return {
        querySelector: (sel) => byId[sel.slice(1)] || null,
        querySelectorAll: (sel) => groups[sel] || [],
    };
}

globalThis.window = node();
globalThis.CSS = { escape: (text) => text };

const { bindTransport, openSpec, sessionScope, syncJumpButtons } = await import("./session.js");

// openSpec: fetch, slice, render Markdown, open the dialog, scroll to the heading.
{
    const markdown = [
        "# Scramble v1",
        "Intro with `code`, **bold** and [link](x.md) & <tag>.",
        "",
        "## Rounds",
        "- one",
        "- two",
        "| a | b |",
        "|---|---|",
        "| `x` | **y** |",
        "```",
        "a < b",
        "```",
        "### Tail",
        "DROP",
    ].join("\r\n");
    globalThis.fetch = async (url) => ({ ok: url === "spec.md", text: async () => markdown });
    let opened = 0;
    let scrolled = null;
    const dialog = { showModal: () => { opened += 1; } };
    const body = {
        innerHTML: "",
        querySelectorAll: () => [],
        querySelector: (sel) => ({ scrollIntoView: () => { scrolled = sel; } }),
    };
    const root = fakeRoot({ spec: dialog, "spec-body": body });
    await openSpec(root, "spec.md", "Rounds", (text) => text.replace(/\r\nDROP$/, ""));
    assert.equal(body.innerHTML, [
        '<h1 id="scramble-v1">Scramble v1</h1>',
        "<p>Intro with <code>code</code>, <strong>bold</strong> and ",
        '<a href="x.md">link</a> &amp; &lt;tag&gt;.</p>',
        '<h2 id="rounds">Rounds</h2>',
        "<ul><li>one</li><li>two</li></ul>",
        "<table><thead><tr><th>a</th><th>b</th></tr></thead>",
        "<tbody><tr><td><code>x</code></td><td><strong>y</strong></td></tr></tbody></table>",
        "<pre><code>a &lt; b</code></pre>",
        '<h3 id="tail">Tail</h3>',
    ].join(""));
    assert.equal(opened, 1);
    assert.equal(scrolled, "#rounds");

    await openSpec(root, "spec.md");
    assert.match(body.innerHTML, /<p>DROP<\/p>$/, "no slice renders the whole file");
    await assert.rejects(openSpec(root, "gone.md"), /specification file is missing/);
    await assert.rejects(openSpec(fakeRoot({}), "spec.md"), /specification dialog is missing/);
}

// syncJumpButtons: back buttons stop at the start, forward buttons at the end.
{
    const names = ["back", "stage-back", "round-back", "fwd", "stage-fwd", "round-fwd"];
    const jumps = names.map((jump) => node({ jump }));
    const root = fakeRoot({}, { "[data-jump]": jumps });
    syncJumpButtons(root, -1, 3);
    assert.deepEqual(jumps.map((el) => el.disabled), [true, true, true, false, false, false]);
    syncJumpButtons(root, 2, 3);
    assert.deepEqual(jumps.map((el) => el.disabled), [false, false, false, true, true, true]);
    syncJumpButtons(root, 0, 3);
    assert.deepEqual(jumps.map((el) => el.disabled), [false, false, false, false, false, false]);
}

// bindTransport: buttons, [data-jump] and teach keys reach the session; abort unbinds them.
{
    const calls = [];
    const trace = [
        { stage: "a", round: 1 },
        { stage: "a", round: 1 },
        { stage: "b", round: 1 },
        { stage: "c", round: 1 },
        { stage: "c", round: 2 },
    ];
    let teaching = false;
    const ids = ["play", "skip-end", "step", "reset", "spec-btn", "spec-close"];
    const byId = Object.fromEntries(ids.map((id) => [id, node()]));
    byId.spec = { close: () => calls.push("close") };
    const names = ["back", "fwd", "stage-back", "stage-fwd", "round-back", "round-fwd"];
    const jumps = names.map((jump) => node({ jump }));
    const scope = sessionScope(fakeRoot({}));
    bindTransport(fakeRoot(byId, { "[data-jump]": jumps }), {
        play: () => calls.push("play"),
        step: () => calls.push("step"),
        skipToEnd: () => calls.push("skip"),
        reset: () => calls.push("reset"),
        showSpec: (heading) => calls.push(`spec:${heading}`),
        trace: () => trace,
        teaching: () => teaching,
        viewedIndex: () => 2,
        stepBy: (dir) => calls.push(`stepBy:${dir}`),
        jumpTo: (index, animate) => calls.push(`jumpTo:${index}:${animate}`),
        stageKey: (step) => step.stage,
        roundKey: (step) => step.round,
    }, scope.listen);

    for (const id of ids) byId[id].click();
    assert.deepEqual(calls.splice(0), ["play", "skip", "step", "reset", "spec:undefined", "close"]);

    for (const el of jumps) el.click();
    assert.deepEqual(calls.splice(0), [
        "stepBy:-1", "stepBy:1", "jumpTo:-1:false", "jumpTo:2:false", "jumpTo:-1:false", "jumpTo:3:false",
    ]);

    const keys = [
        { key: "ArrowRight" }, { key: "ArrowLeft" }, { key: "ArrowRight", shiftKey: true },
        { key: "ArrowLeft", shiftKey: true }, { key: "Home" }, { key: "End" },
    ].map((event) => ({ ...event, target: { tagName: "BODY" }, preventDefault() {} }));
    for (const event of keys) window.dispatch("keydown", event);
    assert.deepEqual(calls.splice(0), [], "teach keys wait for teach mode");
    teaching = true;
    for (const event of keys) window.dispatch("keydown", event);
    assert.deepEqual(calls.splice(0), [
        "stepBy:1", "stepBy:-1", "jumpTo:2:false", "jumpTo:-1:false", "jumpTo:-1:false", "jumpTo:4:false",
    ]);

    scope.abort.abort();
    byId.play.click();
    jumps[0].click();
    window.dispatch("keydown", keys[0]);
    assert.deepEqual(calls, [], "abort unbinds the transport");
}

console.log("shared session tests ok");
