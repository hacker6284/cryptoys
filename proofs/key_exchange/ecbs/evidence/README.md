<!-- Owns: the ECBS evidence drivers, how to run them and their recorded results. Maintenance rules: ../../../../DOCS.md. -->
# ECBS evidence drivers

Every driver here runs the code sudoc generates from [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) (JS target, at the sudocode pin) and checks what it returns against PARI/GP ([`../oracle/`](../oracle/)). The drivers pick inputs, call exported functions and compare; none of them computes a board step. Recorded outputs are in [`results/`](results/) (`.txt` = stdout, `.json` = full data, each with the `.sudo` hash and sudocode commit it ran on).

| File | Role |
| --- | --- |
| [`proofs/sudo_js.py`](../../../sudo_js.py), [`proofs/sudo_js_serve.mjs`](../../../sudo_js_serve.mjs) | Generic runner (any `.sudo`): builds it with the pinned sudoc (`proofs/sudocode.sh`), runs its sudo tests, serves its exported functions over JSON lines (conversion only); temp dirs removed at exit |
| `card_sim.py` | Full exchanges (`exchange()`) checked against PARI; Demo all 64 key pairs, Toy 10 / Hobby 6 / Serious 4 with the Phase-1 keys; phase and op names from the sudo's `phase_names()` / `op_names()`; compares every run with the Phase-1 Python run of the same keys |
| `soundness.py` | Receiver verdicts (`receive_check()`) per attack class at Toy / Hobby / Serious (5000 / 3000 / 1000 per class) and the inversion |
| `demo_exhaustive.mjs`, `soundness_demo.py` | Demo exhaustive: `curve_test()` and `make_certificate()` on all 4,782,969 pairs, then `receive_check()` on every on-curve C and sampled classes; `invert_number()` on every nonzero element |
| `calling_check.py` | `start_calling()` / `call_step()`: resume before every call, stale homes, coordinates; optional tier list (CI runs `Demo,Toy`) |
| `twist_s7.py` | SPEC §7.1 parts A (Demo exhaustive), B (E′, node, every tier), C (key recovery without the curve test; Demo, Toy); provenance per part in `twist_s7.json` |

Every driver prints timings to stderr only, so a rerun's stdout and JSON are byte-identical to `results/` (CI checks `card_sim.py Demo` and `calling_check.py Demo,Toy` this way, in the `generated-fresh` job of `.github/workflows/proofs.yml`). Each JSON records the `.sudo` hash, the sudocode commit and the sudo tests' TAP summary it ran with.

## Run

Node 20, the pinned sudoc (`proofs/sudocode.sh` builds it when `SUDOC` is unset), Python 3 with `cypari2` and `numpy`. From this directory (times: wall clock of the 2026-10-04 reruns on a shared 8-core box under load, so only a guide):

```sh
python card_sim.py Demo > results/card_sim_Demo.txt                          # 2 s
python card_sim.py Toy,Hobby,Serious > results/card_sim_Toy_Hobby_Serious.txt # ~3 min
python soundness.py Toy > results/soundness_Toy.txt                           # ~4 min
python soundness.py Hobby > results/soundness_Hobby.txt                       # ~15 min
python soundness.py Serious > results/soundness_Serious.txt                   # ~36 min
python calling_check.py > results/calling_check.txt                           # ~1.5 min (Demo,Toy: a few s)
ECBS_DEMO_EXHAUSTIVE=/some/dir/demo python soundness_demo.py > results/soundness_demo.txt  # ~15 min, nearly all the 4-way node run
ECBS_DEMO_EXHAUSTIVE=/some/dir/demo python twist_s7.py A > results/twist_s7_A.txt          # ~30 s, reuses that run
python twist_s7.py B,C > results/twist_s7_BC.txt                              # ~2 min
```

The exhaustive Demo run is the slow part: one generated `make_certificate()` is about 0.34 ms and `curve_test()` 0.09 ms in node, so 4,782,969 pairs take about 35 CPU-minutes (`soundness_demo.py` splits them over 4 node processes; 880 s wall in the rerun). With `ECBS_DEMO_EXHAUSTIVE=<prefix>` the run is written to `<prefix>.*` and kept, together with `<prefix>.provenance.json` (sudo hash, sudocode commit); a later `soundness_demo.py` or `twist_s7.py A` with the same prefix reuses it after checking that provenance against its own build. Without the variable the run goes to a temporary directory removed at exit (and `twist_s7.py A` runs its own).

The Phase-1 store-P measurement (P kept on the board between games, peak 9 bands) is history: [`../history/evidence/`](../history/README.md). ECBS has one design, re-deriving P every game.

## Recorded results (ecbs.sudo sha256 `32ef2a04…413c`, sudocode a57e336, sudo tests 16/16)

Rerun on 2026-10-04 after the PR #187 review changes. Against the previous recorded results (sha `0527ebec…a2b9`), every number is identical. The only differences are removed timing fields, the removed `store_P` flag, `same_keys_as_phase1` reading "not recorded" where Phase 1 kept no keys, and the off-curve count renamed from "would pass without the curve test" to `non_empty_run`. That count is what the runs measure; that such a C would then pass is ARGUED in SPEC §7.1, not measured.

Against the Phase-1 Python run (commit ad80f54):

| Driver | Result | vs Phase 1 |
| --- | --- | --- |
| `card_sim` Demo | 64/64 key pairs: shared point = PARI, mean 5,916 moves (5,064–6,788), check 1,890, peak 7, highest control hole 12; the 15-hole-script overrun is the sudo test "§1 Demo's 16-hole control row overruns with a 15-hole script" | identical, run for run (64/64 key pairs, `fits_with_5_hole_script`) |
| `card_sim` Toy / Hobby / Serious | 10 / 6 / 4 exchanges = PARI; mean 141,822 / 1,714,807 / 40,287,769; check 15,293 / 92,867 / 758,385; peak 7; bench 66 / 174 / 534 | identical to the Phase-1 run, 10/10, 6/6, 4/4 (`identical_to_phase1_python`). The keys come from Phase 1's seeded generator, but Phase 1 did not record its Toy–Serious keys, so `same_keys_as_phase1` says "not recorded". Phase-1 docs printed 758,384, the truncation of 758,384.6 |
| `soundness` Toy / Hobby / Serious | 5000 / 3000 / 1000 per class, on boards: honest and outside-⟨P⟩ correct A all accept with A = PARI's π(C) − C; wrong A all mismatch; order-5 C 16/16 empty; off-curve all rejected by the curve test (all with a non-empty run); inversion 0 wrong; peak 7 | **same verdicts, different sampling**: Phase 1 sampled these at field level, with a 30 / 15 / 6 peg-level spot check |
| `soundness_demo` | 4,782,969 pairs: 2,104 on curve (2,100 accept, 4 empty), 420 distinct A ×5, 8,400/8,400 mismatch, 4,780,865 off-curve rejected (4,774,308 with a non-empty run, 6,557 with an empty one), inversion 0/2,186 wrong; board classes 2104/200/200/8/300/300 as expected | identical |
| `calling_check` | resume before every call ok all tiers; stale copy wrong 0/200 with the rule, without clearing **191** / 200 / 200 / 200 of 200; homes disjoint, never row J / a key grid | Demo differs: Phase 1 had 193/200, from different random draws; other tiers the same |
| `twist_s7` A / B / C | A: 4,776,408 pairs, 9 GF(3) curves, 4,757,256 others (2,002 land on E), twist 2,268 points (order 2,271), generated curve test passes only E's own 2,100; B 4/4 (E′) and 6/6 (node) every tier; C Demo and Toy keys recovered | identical for what was rerun |

**Not rerun on the generated code:** Phase 1's `extras_v3` (the C-and-A-called-together home count, [`../history/card/extras_v3.txt`](../history/card/extras_v3.txt)) and twist part C at Hobby (PARI `fflog` in GF(3¹¹⁸)* did not finish within 1,500 s in Phase 1, [`../history/twist/s7_partC.txt`](../history/twist/s7_partC.txt)); SPEC cites both as `[log: …]`.

## Lean

`proofs/emit_lean.sh ecbs` emits `../lean/Generated/` (`Ecbs.lean`) and passes the terminates gate; `proofs/emit_lean.sh --check` confirms it matches a fresh emit (CI). **Lean is emitted, not built:** it does not elaborate in a CI-sized budget at the sudoc pin (a57e336, Lean v4.14.0), so CI does not build it (the `ecbs` row of the `generated` matrix stays commented out). The sudocode issue is https://github.com/hacker6284/sudocode/issues/17. Measured on this shared box, October 2026:

- **Retry after the `Costs` refactor (2026-10-04, `ecbs.sudo` 32ef2a04).** Records are now `Tier` 21, `Board` 26, `Costs` 17 and `Player` 16 fields (they were `Board` 48 and `Player` 31). `timeout 1200 nice -n 10 bash build_test.sh` from 22:03:44Z: `SudoRt` built in seconds, and `Ecbs.lean` was still elaborating when the timeout killed it at 1,200 s wall (exit 124). It ran at about 100 % of one core throughout, with about 0.2 GB resident, so it was CPU-bound, not out of memory. Box load average was 18.5 at the start and 2.4 at the end. **Not built**; `ecbs_test` did not run.
- Earlier (`ecbs.sudo` 0527ebec, before the refactor): `Ecbs.lean` was still elaborating after 95 CPU-minutes (1 h 40 min wall) and was never seen to finish.
- Cause 1, `deriving BEq, Repr` on large records. Every sudo record is emitted with `deriving BEq, Repr`. Alone in a file, `Tier` (21 fields) takes 0 s plain, 1 s with `deriving BEq`, and **180 s with `deriving Repr`**. DHH's rerun gave 0.2 s and about 187 s. The time grows faster than linearly with the field count. The derived `Repr` is one long `String`/`Format` `++` chain per record. Nothing in `Ecbs.lean` or `ecbs_test.lean` uses `repr`. BS records have at most 10 fields, so BS builds in seconds.
- Cause 2, large function bodies. In a scratch copy with `Repr` removed from the deriving lines (pre-refactor; not committed, since generated files are never hand-edited), the file elaborates in 72 s (DHH: 67 s) but three definitions fail. `call_step` and `report` (a `{ p with … }` update of the then 31-field `Player`) hit the 200,000-heartbeat limit. `exchange` (a long string literal emitted as an `Int` array inside a deeply nested `do`) hits `maxRecDepth`. Raising both limits (`maxHeartbeats 0`, `maxRecDepth 100000`) did not get a build. Ours was killed (exit 137, probably out of memory on the overloaded box) after 583 s; DHH's hit `bad_alloc`.
- Fixes proposed to sudocode (https://github.com/hacker6284/sudocode/issues/17; Sniper owns sudoc speedups): emit no `Repr`, or only up to N fields (the three `deriving BEq, Repr` lines of `backends/lean/emit.py`, :2436, :2450, :2489); emit one multi-field update per sudo statement instead of long `{ r with … }` chains; split deep `do` nesting; emit string literals as one `String`. Re-enable the CI row only once `lake build` and `ecbs_test` pass.

The JS target, which all the evidence above uses, is unaffected: its 16 sudo tests pass in under a second.
