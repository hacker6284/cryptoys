#!/usr/bin/env node
/**
 * Headless runner for `?debugCapture=1` proof strips
 * (fixed-Δt grid ∪ beats ∪ camAccel).
 *
 *   CAPTURE_URL=http://127.0.0.1:4173 \
 *   CAPTURE_OUT=/opt/cursor/artifacts/strips \
 *   CAPTURE_TAG=before \
 *   node demos/playroom/run-capture-strips.mjs
 *
 * Needs puppeteer-core + Chrome. Does not change production motion.
 */

import { mkdirSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const here = dirname(fileURLToPath(import.meta.url));

function loadPuppeteer() {
    const paths = [
        "/tmp/pr-capture/node_modules/puppeteer-core",
        join(here, "../../node_modules/puppeteer-core"),
        "puppeteer-core",
    ];
    for (const id of paths) {
        try {
            return require(id);
        } catch {
            // try next
        }
    }
    throw new Error("puppeteer-core not found. npm i puppeteer-core");
}

function writeDataUrl(path, dataUrl) {
    const comma = dataUrl.indexOf(",");
    writeFileSync(path, Buffer.from(dataUrl.slice(comma + 1), "base64"));
}

const puppeteer = loadPuppeteer();
const OUT = process.env.CAPTURE_OUT || "/opt/cursor/artifacts/strips";
const TAG = process.env.CAPTURE_TAG || "run";
const BASE = process.env.CAPTURE_URL || "http://127.0.0.1:4173";
const CHROME = process.env.CHROME || "/usr/bin/google-chrome-stable";

mkdirSync(OUT, { recursive: true });

const browser = await puppeteer.launch({
    executablePath: CHROME,
    headless: "new",
    protocolTimeout: 600000,
    args: [
        "--no-sandbox",
        "--disable-dev-shm-usage",
        "--enable-unsafe-swiftshader",
        "--use-gl=angle",
        "--use-angle=swiftshader",
        "--hide-scrollbars",
        "--window-size=1280,800",
    ],
});

const page = await browser.newPage();
await page.setViewport({ width: 1280, height: 800, deviceScaleFactor: 1 });
page.on("pageerror", (err) => console.warn("pageerror", err.message));

async function waitPred(fn, { timeout, label } = {}) {
    const start = Date.now();
    while (Date.now() - start < timeout) {
        try {
            if (await page.evaluate(fn)) return;
        } catch (err) {
            console.warn(label, "evaluate", err.message);
        }
        const beat = await page.evaluate(() => ({
            beat: document.documentElement.dataset.beat || "",
            seq: document.documentElement.dataset.captureSeq || "",
            frames: document.documentElement.dataset.captureFrames || "",
            peek: window.__playroomCapture?.peek?.() || null,
        })).catch(() => null);
        console.log(label, `${Date.now() - start}ms`, beat);
        await new Promise((resolve) => setTimeout(resolve, 2500));
    }
    throw new Error(`timeout ${label}`);
}

async function dumpSequence(name) {
    const seq = await page.evaluate(async (key) => {
        const cap = window.__playroomCapture;
        if (!cap?.exportSheet) return cap?.sequences?.[key] || null;
        return cap.exportSheet(key);
    }, name);
    if (!seq?.frames?.length) {
        console.warn("missing sequence", name);
        return;
    }
    const dir = join(OUT, TAG, name);
    mkdirSync(dir, { recursive: true });
    seq.frames.forEach((frame, i) => {
        const file = `${String(i).padStart(2, "0")}_${frame.ms}ms_${frame.beat}.jpg`;
        writeDataUrl(join(dir, file), frame.dataUrl);
    });
    if (seq.sheet) {
        const sheet = join(OUT, `${TAG}_${name}_strip.png`);
        writeDataUrl(sheet, seq.sheet);
        console.log("sheet", sheet, "frames", seq.frames.length);
    } else {
        console.log("seq", name, "frames", seq.frames.length, "(no sheet)");
    }
}

try {
    await page.goto(`${BASE}/?debugCapture=1`, { waitUntil: "networkidle0", timeout: 60000 });
    await waitPred(
        () => document.documentElement.dataset.playroomReady === "1"
            && window.__playroomCapture?.enabled,
        { timeout: 60000, label: "ready" },
    );

    console.log("doubledeal enter");
    await page.click('[data-algo="doubledeal"]');
    await waitPred(
        () => document.querySelector("#doubledeal-dock.on")
            && document.documentElement.dataset.playroomTween !== "1"
            && window.__playroomCapture?.sequences?.["doubledeal-enter"],
        { timeout: 480000, label: "doubledeal-enter" },
    );
    await dumpSequence("doubledeal-enter");

    console.log("doubledeal leave");
    await page.click("#back");
    await waitPred(
        () => document.documentElement.dataset.pose === "landing"
            && !document.documentElement.dataset.algo
            && window.__playroomCapture?.sequences?.["doubledeal-leave"],
        { timeout: 360000, label: "doubledeal-leave" },
    );
    await dumpSequence("doubledeal-leave");

    console.log("scramble enter");
    await page.click('[data-algo="scramble"]');
    await waitPred(
        () => document.querySelector("#scramble-dock.on")
            && document.documentElement.dataset.playroomTween !== "1"
            && window.__playroomCapture?.sequences?.["scramble-enter"],
        { timeout: 300000, label: "scramble-enter" },
    );
    await dumpSequence("scramble-enter");

    console.log("scramble leave");
    await page.click("#back");
    await waitPred(
        () => document.documentElement.dataset.pose === "landing"
            && !document.documentElement.dataset.algo
            && window.__playroomCapture?.sequences?.["scramble-leave"],
        { timeout: 300000, label: "scramble-leave" },
    );
    await dumpSequence("scramble-leave");
    console.log("done", join(OUT, TAG));
} catch (err) {
    console.error(err);
    process.exitCode = 1;
} finally {
    await browser.close();
}
