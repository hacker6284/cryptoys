// Collect the ECBS known-answer vectors from a sudoc JS build of
// primitives/key_exchange/ecbs/ecbs.sudo, over the inputs in inputs.json. Every
// output below comes from the generated code; this file only converts between
// JSON and the generated host API. Do not hand-edit the JSON this writes;
// regenerate with regen.sh.
//
// Usage: node collect_vectors.mjs <sudoc-js-outdir> > ecbs_vectors.json
// Env (set by regen.sh): ECBS_SUDO_SHA256, SUDOCODE_COMMIT.

import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const outDir = process.argv[2];
if (!outDir) {
  console.error("usage: node collect_vectors.mjs <sudoc-js-outdir>");
  process.exit(2);
}
const here = path.dirname(fileURLToPath(import.meta.url));
const E = await import(pathToFileURL(path.resolve(outDir, "ecbs.mjs")).href);
const inputs = JSON.parse(readFileSync(path.join(here, "inputs.json"), "utf8"));

function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

const toTrits = (s) => [...s].map((c) => ".WR".indexOf(c));
const toPegs = (xs) => xs.map((t) => ".WR"[t]).join("");
const ptIn = (p) => ({ x: toTrits(p.x), y: toTrits(p.y) });
const ptOut = (p) => ({ x: toPegs(p.x), y: toPegs(p.y) });
const PHASES = ["base point", "store P", "own walk", "swap", "curve test", "make certificate",
  "rebuild theirs", "shared walk", "fold"];
const OPS = ["mul", "cube", "inv", "chord", "fadd"];
const HOMES = ["across", "up", "bottom", "base across", "base up", "gap", "spare"];
const ROWS = "ABCDEFGHIJ";
const byName = (names, xs) => Object.fromEntries(names.map((k, i) => [k, xs[i]]));

function roll(t, faces) {
  const r = E.roll_key(t, faces);
  assert(r !== null, "roll_key ran out of faces");
  return r;
}

function player(p) {
  return {
    base_hole: p.base_hole,
    sent_C: ptOut(p.sent_c),
    sent_A: ptOut(p.sent_a),
    on_curve: p.on_curve,
    rebuilt_A: ptOut(p.rebuilt),
    matched: p.matched,
    shared: ptOut(p.shared),
    folded: toPegs(p.folded),
    moves: p.moves,
    moves_by_phase: byName(PHASES, p.moves_by_phase),
    peak: p.peak,
    max_bench_hole: p.max_bench_hole,
    ctrl: p.ctrl,
    calls: p.calls,
    ladder: toPegs(p.ladder),
    ladder_moves: p.ladder_moves,
    tally_max: p.tally_max,
    control_highest: p.control_highest,
    script_marker_max: p.script_marker_max,
    ops: byName(OPS, p.ops),
  };
}

const out = {
  schema: 1,
  generated_by: "proofs/key_exchange/ecbs/vectors/regen.sh",
  source: "primitives/key_exchange/ecbs/ecbs.sudo",
  sudo_sha256: process.env.ECBS_SUDO_SHA256 ?? "",
  sudocode_commit: process.env.SUDOCODE_COMMIT ?? "",
  note: "Known-answer vectors evaluated by the sudoc JS target of ecbs.sudo over inputs.json. Cross-checked against PARI/GP by check_oracle.py.",
  numbers: "'.WR' strings, hole 0 first: '.' empty, 'W' white, 'R' red (SPEC §1)",
  tiers: {},
};

for (const [name, tin] of Object.entries(inputs.tiers)) {
  const t = E.tier(name);
  const v = {};
  v.tier = { n: t.n, k: t.k, cells: t.cells, bench: t.benchlen, control: t.control, script: t.script };
  v.base_point = ptOut(E.base_point_of(t));
  v.arith = tin.arith.map(({ x, y }) => ({
    x, y,
    product: toPegs(E.multiply(t, toTrits(x), toTrits(y))),
    cube: toPegs(E.cube_number(t, toTrits(x))),
    inverse: toPegs(E.invert_number(t, toTrits(x))),
  }));
  v.fold = tin.fold.map((x) => ({ x, folded: toPegs(E.fold(t, toTrits(x))) }));
  v.points = tin.points.map((p) => {
    const c = E.make_certificate(t, ptIn(p));
    return { why: p.why, x: p.x, y: p.y, curve_test: E.curve_test(t, ptIn(p)),
      certificate: c === null ? null : ptOut(c) };
  });
  v.walks = tin.walks.map((w) => {
    const r = roll(t, w.faces);
    const k = E.walk_key(t, r.cells, ptIn(w.base));
    return { faces: w.faces, cells: toPegs(r.cells), faces_used: r.used, base: w.base,
      walked: k === null ? null : ptOut(k) };
  });
  v.receive = tin.receive.map((r) => {
    const c = E.receive_check(t, ptIn(r.own), ptIn(r.c), ptIn(r.a));
    return { why: r.why, own: r.own, C: r.c, A: r.a, verdict: c.verdict.$,
      rebuilt: c.verdict.$ === "Accept" ? ptOut(c.rebuilt) : null,
      peak: c.peak, check_moves: c.check_moves };
  });
  v.exchanges = tin.exchanges.map((x) => {
    const ra = roll(t, x.faces_a), rb = roll(t, x.faces_b);
    const r = E.exchange(t, ra.cells, rb.cells, false);
    assert(r instanceof Object && "a" in r, `exchange failed at ${name}`);
    return { faces_a: x.faces_a, faces_b: x.faces_b, cells_a: toPegs(ra.cells), cells_b: toPegs(rb.cells),
      P: ptOut(r.a.base), A: player(r.a), B: player(r.b) };
  });
  v.roll = tin.roll.map((f) => {
    const r = E.roll_key(t, f);
    return { faces: f, rolled: r === null ? null : { cells: toPegs(r.cells), used: r.used, rolls: r.rolls } };
  });
  v.coordinates = {};
  for (let h = 0; h < HOMES.length; h++) {
    const a = E.coordinate(t, h, 0), b = E.coordinate(t, h, t.n - 1);
    v.coordinates[HOMES[h]] = `grid ${a.grid}, ${ROWS[a.row]}${a.col} .. grid ${b.grid}, ${ROWS[b.row]}${b.col}`;
  }
  out.tiers[name] = v;
}

process.stdout.write(JSON.stringify(out, null, 1) + "\n");
