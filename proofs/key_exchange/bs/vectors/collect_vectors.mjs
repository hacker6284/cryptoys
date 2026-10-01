// Collect the BS known-answer vectors from a sudoc JS build of
// primitives/key_exchange/bs/bs.sudo, over the inputs in inputs.json. Every
// output below comes from the generated code; this file only converts between
// JSON and the generated host API. Do not hand-edit the JSON this writes;
// regenerate with regen.sh.
//
// Usage: node collect_vectors.mjs <sudoc-js-outdir> > bs_vectors.json
// Env (set by regen.sh): BS_SUDO_SHA256, SUDOCODE_COMMIT.

import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const outDir = process.argv[2];
if (!outDir) {
  console.error("usage: node collect_vectors.mjs <sudoc-js-outdir>");
  process.exit(2);
}
const here = path.dirname(fileURLToPath(import.meta.url));
const bs = await import(pathToFileURL(path.resolve(outDir, "bs.mjs")).href);
const inputs = JSON.parse(readFileSync(path.join(here, "inputs.json"), "utf8"));

function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

// Registers and cell strings: '.WR' = 0/1/2, hole 0 (or the first cell) first.
const toTrits = (s) => [...s].map((c) => ".WR".indexOf(c));
const toPegs = (xs) => xs.map((t) => ".WR"[t]).join("");
const shotName = (s) => s.$;

const ROWS = "ABCDEFGHIJ";
function gridOut(g) {
  const ships = g.ships.map((s) => ({
    kind: s.kind.$,
    lies: s.down ? "down" : "across",
    first: `${ROWS[s.row]}${s.col + 1}`,
    bow: s.bow_last ? "last" : "first",
  }));
  const pegs = [];
  for (let r = 0; r < 10; r++) pegs.push(toPegs(g.pegs.slice(10 * r, 10 * r + 10)));
  return { ships, pegs };
}
function gridIn(g) {
  return {
    ships: g.ships.map((s) => ({
      kind: { $: s.kind },
      down: s.lies === "down",
      row: ROWS.indexOf(s.first[0]),
      col: Number(s.first.slice(1)) - 1,
      bow_last: s.bow === "last",
    })),
    pegs: toTrits(g.pegs.join("")),
  };
}

function buildKey(name, faces) {
  const built = bs.build_key_grid(bs.dice(faces.d12, faces.d6, faces.d10));
  const used = { d12: built.used12, d6: built.used6, d10: built.used10 };
  for (const k of ["d12", "d6", "d10"]) {
    assert(used[k] === faces[k].length,
      `${name}: BUILD read ${used[k]} ${k} faces of ${faces[k].length}`);
  }
  const grid = gridOut(built.grid);
  // The JSON form of the grid must read back to the same grid.
  assert(JSON.stringify(gridOut(gridIn(grid))) === JSON.stringify(grid),
    `${name}: grid JSON round trip`);
  return { grid: built.grid, json: grid };
}

const vectors = [];
for (const v of inputs.vectors) {
  const f = bs.tier(v.tier);
  const out = { ...v };
  if (v.kind === "exchange") {
    const a = buildKey(`${v.name} Alice`, v.dice_a);
    const b = buildKey(`${v.name} Bob`, v.dice_b);
    const e = bs.exchange(f, [a.grid], [b.grid]);
    Object.assign(out, {
      key_a: a.json,
      key_b: b.json,
      cells_a: toPegs(bs.read_key([a.grid])),
      cells_b: toPegs(bs.read_key([b.grid])),
      public_a: toPegs(e.public_a),
      public_b: toPegs(e.public_b),
      shots_a: e.shots_a.map(shotName),
      received_a: toPegs(e.received_a),
      shots_b: e.shots_b.map(shotName),
      received_b: toPegs(e.received_b),
      base_a: toPegs(e.base_a),
      base_b: toPegs(e.base_b),
      secret_a: toPegs(e.secret_a),
      secret_b: toPegs(e.secret_b),
    });
    assert(out.received_a === out.public_a && out.received_b === out.public_b,
      `${v.name}: §3.1 copy differs`);
    assert(out.secret_a === out.secret_b, `${v.name}: K_A != K_B`);
  } else if (v.kind === "multiply") {
    out.product = toPegs(bs.multiply(f, toTrits(v.a), toTrits(v.b), v.nudge));
  } else if (v.kind === "tidy") {
    out.tidy = toPegs(bs.tidy(f, toTrits(v.x)));
  } else if (v.kind === "check") {
    const r = bs.check_received(f, toTrits(v.received));
    out.base = r === null || r === undefined ? null : toPegs(r);
  } else if (v.kind === "call") {
    const c = bs.send_public_value(f, toTrits(v.x));
    out.shots = c.shots.map(shotName);
    out.y = toPegs(c.y);
    assert(out.y === v.x, `${v.name}: §3.1 copy differs`);
  } else {
    throw new Error(`unknown vector kind ${v.kind}`);
  }
  vectors.push(out);
}

const doc = {
  schema: 1,
  generated_by: "proofs/key_exchange/bs/vectors/regen.sh",
  source: "primitives/key_exchange/bs/bs.sudo",
  sudo_sha256: process.env.BS_SUDO_SHA256 || "",
  sudocode_commit: process.env.SUDOCODE_COMMIT || "",
  note:
    "Known-answer vectors evaluated by the sudoc JS target of bs.sudo over inputs.json. " +
    "Cross-checked by check_oracle.py against pow() and the Python evidence harness " +
    "(not a reference).",
  registers: inputs.registers,
  dice: inputs.dice,
  cells:
    "the key's cell string as B7 walks it (READ, SPEC §4.3): start marker, ship pass, " +
    "peg pass; '.WR' = plain/white/red",
  shots:
    "§3.1 answers in call order, hole 0 first: shots_a is Bob calling Alice's X, " +
    "shots_b is Alice calling Bob's X",
  vectors,
};
// One line per list of numbers or of shots.
const oneLine = (m, keep) =>
  "[" + m.slice(1, -1).split(",").map((x) => x.trim()).filter(keep).join(", ") + "]";
const text = JSON.stringify(doc, null, 1)
  .replace(/\[[-0-9,\s]*\]/g, (m) => oneLine(m, (x) => x))
  .replace(/\[(\s*"(?:Hit|Miss|Misfire)",?)+\s*\]/g, (m) => oneLine(m, () => true));
process.stdout.write(text + "\n");
