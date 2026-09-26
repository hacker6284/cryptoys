/**
 * Live Pages proof: pick a ~1.54 MiB JPEG on the published playroom
 * dock and wait until #digest is nonempty. Not a CI job.
 *
 *   PAGES_URL=https://hacker6284.github.io/cryptoys/pr/65/?algo=scramble&v=TIP \
 *   node demos/scramble/file-dock-pages-proof.mjs
 */
import { createRequire } from "node:module";
import { writeFileSync, mkdirSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const require = createRequire(import.meta.url);
function loadPuppeteer() {
    const paths = [
        "/tmp/pr-capture/node_modules/puppeteer-core",
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

const puppeteer = loadPuppeteer();
const CHROME = process.env.CHROME || "/usr/bin/google-chrome-stable";
const BASE = process.env.PAGES_URL
    || "https://hacker6284.github.io/cryptoys/pr/65/?algo=scramble";
const BYTES = 1610613;

const jpegPath = join(tmpdir(), "scramble-large-fronalpstock-3840.jpg");
const raw = new Uint8Array(BYTES);
raw[0] = 0xff;
raw[1] = 0xd8;
raw[2] = 0xff;
raw[3] = 0xe0;
writeFileSync(jpegPath, raw);

const browser = await puppeteer.launch({
    executablePath: CHROME,
    headless: "new",
    protocolTimeout: 180000,
    args: ["--no-sandbox", "--disable-dev-shm-usage", "--hide-scrollbars"],
});

async function prove(page, { width, height, label }) {
    await page.setViewport({ width, height, deviceScaleFactor: 1 });
    const url = new URL(BASE);
    url.searchParams.set("algo", "scramble");
    url.searchParams.set("pose", "seated");
    await page.goto(url.href, { waitUntil: "networkidle0", timeout: 60000 });
    await page.waitForFunction(() => {
        const digest = document.querySelector("#digest");
        const input = document.querySelector("#message-file-input");
        const dock = document.querySelector("#scramble-dock");
        return Boolean(digest && input && dock && !dock.hidden);
    }, { timeout: 60000 });

    const started = Date.now();
    const input = await page.$("#message-file-input");
    await input.uploadFile(jpegPath);
    await page.waitForFunction(() => {
        const el = document.querySelector("#digest");
        const hex = el && (el.value || el.textContent || "");
        return hex.startsWith("0x") && hex.length > 4;
    }, { timeout: 90000 });
    const ms = Date.now() - started;
    const report = await page.evaluate(() => {
        const digest = document.querySelector("#digest");
        const progress = document.querySelector("#message-file-progress");
        const name = document.querySelector("#message-file-name");
        return {
            digest: String(digest?.value || digest?.textContent || ""),
            progressHidden: Boolean(progress?.hidden),
            filename: String(name?.textContent || ""),
        };
    });
    if (!report.digest.startsWith("0x") || report.digest.length <= 4) {
        throw new Error(`${label}: Digest stayed empty`);
    }
    if (!/1\.5 MB/.test(report.filename)) {
        throw new Error(`${label}: filename chip missing size, got ${report.filename}`);
    }
    return { label, width, height, ms, ...report };
}

const page = await browser.newPage();
page.on("pageerror", (err) => console.warn("pageerror", err.message));
const results = [];
try {
    results.push(await prove(page, { width: 1280, height: 800, label: "landscape" }));
    results.push(await prove(page, { width: 390, height: 844, label: "portrait" }));
} finally {
    await browser.close();
}

const out = {
    pass: results.every((row) => row.digest.startsWith("0x") && row.ms < 90000),
    url: BASE,
    results,
};
mkdirSync("/tmp", { recursive: true });
writeFileSync("/tmp/file-dock-pages-proof.json", JSON.stringify(out, null, 2));
console.log(JSON.stringify(out, null, 2));
if (!out.pass) process.exit(1);
