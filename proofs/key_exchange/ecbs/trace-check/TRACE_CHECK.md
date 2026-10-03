<!-- Owns: the trace (subgroup) check, kept as the LOSING option against the certificate check. Maintenance rules: ../../../../DOCS.md. -->
# LOSING OPTION: the trace check (not the ECBS design)

**ECBS uses the certificate check** ([SPEC §5.3](../../../../primitives/key_exchange/ecbs/SPEC.md), card v3). Zachary signed off on that on 2026-10-03. This directory keeps the receiver-side trace check, which it beat, so the comparison can be re-run. Nothing here is normative. Do not build it into a card or an implementation.

## What it was (2026-09-30 draft §5.2.2, verbatim in substance)
After the curve test on the received B, build the halving ladder from n (a full register of pegs: WRRWWRR at Serious). Compute S_m = B + τB + … + τ^{m−1}B along it: a white rung is S_{2m} = S_m + τ^m S_m; a red rung also adds S_{m+1} = τS_m + B (chord rule). **Accept iff one more Frobenius of S_{n−1} gives the mirror of B.** Reject on any exceptional case. Lazy y: in each chord addition the second point's y is made only after the run is inverted (peak 7 bands, not 8). At Demo it would run as the trace walk: walk n − 1 = 6 all-white cells over B (S ← τS + B), then one more Frobenius must give the mirror of B.

## Evidence
- **Soundness.** It accepts exactly ⟨P⟩∖{O} [proof: ../MATH_REVIEW.md C11]. Demo exhaustively: exactly 420 of the 2104 on-curve points, 0 misclassified [run: ../core/ecbs_fform §2, ../core/ecbs_review_checks (c), ../core/ecbs_walks]. Toy / Hobby / Serious (5000 / 3000 / 1000 trials per class, peg level 30 / 15 / 6 plus the 4 order-5 points): every subgroup point accepted, every non-subgroup point rejected [run: soundness_field_*.json, soundness_peg_*.json, from ../card/soundness.py].
- **Full exchanges on the v2 card** (2 trace exchanges per tier, fixed homes): every exchange matched PARI, peak 7 bands, tally 11 / 29 / 89 for the trace ladder too [run: card_sim.py → card_sim_{Toy,Hobby,Serious}.txt/json; card v2: PLAYER_CARD_v2.md; notes: V2_NOTES.md].
- **Cost per person (curve test + trace chain):** Demo 2,721 / Toy 46.9 k / Hobby 0.390 M / Serious 3.93 M [run: ../core/ecbs_fform]; v2 card measured 46.4 k / 0.391 M / 3.91–3.95 M [run: card_sim.py].
- **Twists with the trace check, if the curve test were skipped** (draft §7) [run: ../core/ecbs_twists; review mr_factor_check, mr_invalid_trace]: the trace check passes exactly the odd part of the node (b′ = 0, index 4) and of E′ (b′ = 2, index 2), so an attacker could learn k mod a 120.3-bit number at Serious for ≈ 2^26.5 work (node) and a further 43.9 bits (E′), and the whole Hobby key for ≈ 2^14 (E′ fully smooth).

## Why it lost
| | trace check | certificate check (SPEC §5.3) |
|---|---|---|
| Who works | the receiver, on every received point | the sender makes A = π(C) − C; the receiver rebuilds and compares |
| Moves per person | 2,721 / 46.9 k / 0.390 M / 3.93 M | 1,890 / 15,293 / 92,867 / 758,384 |
| Extra control | trace ladder (2 / 4 / 5 / 7 holes) and its tally | one phase hole |
| New recipe to learn | the halving chain with a Frobenius rung | none: one Frobenius, one chord, compare |

Same twist mechanism in both: the curve test is what protects; see SPEC §7.1 for the certificate's analysis.

## Files
`card_sim.py` (v2 full exchanges; imports `../card/homes.py`), `extras.py`/`extras.json` (v2 per-op costs), `card_sim_*`, `soundness_{field,peg}_*.json`, `sf_*.txt`/`sp_*.txt` (stdout of `../card/soundness.py` runs), `PLAYER_CARD_v2.md`, `V2_NOTES.md`.
