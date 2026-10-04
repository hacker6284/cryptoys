<!-- Owns: the ECBS evidence drivers, how to run them and their recorded results. Maintenance rules: ../../../../DOCS.md. -->
# ECBS evidence drivers

Every driver here runs the code sudoc generates from [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) (JS target, at the sudocode pin) and checks what it returns against PARI/GP ([`../oracle/`](../oracle/)). The drivers pick inputs, call exported functions and compare; none of them computes a board step. Recorded outputs are in [`results/`](results/) (`.txt` = stdout, `.json` = full data, each with the `.sudo` hash and sudocode commit it ran on).

| File | Role |
| --- | --- |
| `sudo_js.py` | Builds `ecbs.sudo` with the pinned sudoc (`proofs/sudocode.sh`), runs its sudo tests, and starts `serve.mjs` |
| `serve.mjs` | JSON-lines bridge: one call of an exported function per line (conversion only) |
| `card_sim.py` | Full exchanges (`exchange()`) checked against PARI; Demo all 64 key pairs, Toy 10 / Hobby 6 / Serious 4 with the Phase-1 keys, `store_P` variant; compares every run with the Phase-1 Python run of the same keys |
| `soundness.py` | Receiver verdicts (`receive_check()`) per attack class at Toy / Hobby / Serious (5000 / 3000 / 1000 per class) and the inversion |
| `demo_exhaustive.mjs`, `soundness_demo.py` | Demo exhaustive: `curve_test()` and `make_certificate()` on all 4,782,969 pairs, then `receive_check()` on every on-curve C and sampled classes; `invert_number()` on every nonzero element |
| `calling_check.py` | `start_calling()` / `call_step()`: resume before every call, stale homes, coordinates |
| `twist_s7.py` | SPEC §7.1 parts A (Demo exhaustive), B (E′, node, every tier), C (key recovery without the curve test; Demo, Toy) |

## Run

Node 20, the pinned sudoc (`proofs/sudocode.sh` builds it when `SUDOC` is unset), Python 3 with `cypari2` and `numpy`. From this directory:

```sh
python card_sim.py Demo > results/card_sim_Demo.txt                          # 1 s
python card_sim.py Toy,Hobby,Serious > results/card_sim_Toy_Hobby_Serious.txt # ~80 s
python card_sim.py Toy,Hobby,Serious 1 store_P > results/card_sim_Toy_Hobby_Serious_storeP.txt  # ~30 s
python soundness.py Toy > results/soundness_Toy.txt                           # ~4 min
python soundness.py Hobby > results/soundness_Hobby.txt                       # ~14 min
python soundness.py Serious > results/soundness_Serious.txt                   # ~32 min
python calling_check.py > results/calling_check.txt                           # ~80 s
python soundness_demo.py > results/soundness_demo.txt                         # ~14 min (13 min of it the 4-way node run)
ECBS_DEMO_EXHAUSTIVE=<prefix> python twist_s7.py A > results/twist_s7_A.txt   # ~20 s, reuses the exhaustive run
python twist_s7.py B,C > results/twist_s7_BC.txt                              # ~80 s
```

Times are wall-clock on a shared 8-core box. The exhaustive Demo run is the slow part: one generated `make_certificate()` is about 0.34 ms and `curve_test()` 0.09 ms in node, so 4,782,969 pairs take about 35 CPU-minutes (`soundness_demo.py` splits them over 4 node processes).

`ECBS_DEMO_EXHAUSTIVE=<prefix>` makes `soundness_demo.py` reuse a finished `demo_exhaustive.mjs` run (`ECBS_DEMO_EXHAUSTIVE_SECS` records its wall time).

## Recorded results (ecbs.sudo sha256 `0527ebec…a2b9`, sudocode a57e336)

Every number matches the Phase-1 Python run (commit ad80f54) unless noted.

| Driver | Result | vs Phase 1 |
| --- | --- | --- |
| `card_sim` Demo | 64/64 key pairs: shared point = PARI, mean 5,916 moves (5,064–6,788), check 1,890, peak 7, highest control hole 12; a 15-hole script overruns Demo (trap) | identical, run for run |
| `card_sim` Toy / Hobby / Serious | 10 / 6 / 4 exchanges = PARI; mean 141,822 / 1,714,807 / 40,287,769; check 15,293 / 92,867 / 758,385; peak 7 (`store_P` 9); bench 66 / 174 / 534 | identical, run for run (Phase-1 docs printed 758,384, the truncation of 758,384.6) |
| `soundness` Toy / Hobby / Serious | 5000 / 3000 / 1000 per class, now on boards: honest and outside-⟨P⟩ correct A all accept with A = PARI's π(C) − C; wrong A all mismatch; order-5 C 16/16 empty; off-curve all rejected by the curve test (all would pass without it); inversion 0 wrong; peak 7. 208 s / 834 s / 1,941 s | same verdicts; Phase 1 sampled these at field level, with a 30 / 15 / 6 peg-level spot check |
| `soundness_demo` | 4,782,969 pairs: 2,104 on curve (2,100 accept, 4 empty), 420 distinct A ×5, 8,400/8,400 mismatch, 4,780,865 off-curve rejected (4,774,308 would pass, 6,557 empty without the test), inversion 0/2,186 wrong; board classes 2104/200/200/8/300/300 as expected | identical |
| `calling_check` | resume before every call ok all tiers; stale copy wrong 0/200 with the rule, without clearing 191 / 200 / 200 / 200 of 200; homes disjoint, never row J / a key grid | same (Phase-1 Demo 193/200: different random draws) |
| `twist_s7` A / B / C | A: 4,776,408 pairs, 9 GF(3) curves, 4,757,256 others (2,002 land on E), twist 2,268 points (order 2,271), generated curve test passes only E's own 2,100; B 4/4 (E′) and 6/6 (node) every tier; C Demo and Toy keys recovered | identical |

## Lean

`proofs/emit_lean.sh ecbs` emits `../lean/Generated/` (Ecbs.lean, 283 KB) and passes the terminates gate. **Build not yet confirmed:** on this box `lake build` built SudoRt in seconds but `Ecbs.lean` was still elaborating after more than 50 CPU-minutes (status at commit time; see PROGRESS).
