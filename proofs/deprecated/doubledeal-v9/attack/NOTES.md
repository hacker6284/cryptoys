# v9 reduced-round cryptanalysis notes (the analysis log that found the break)

Filed unchanged from branch `doubledeal-cryptanalysis` (ed8c541) apart from this header; paths are now
relative to this `attack/` folder, and the Python port is `dd_v9.py` (was `../ddport.py`). The
mechanism is analysed in `../README.md` and `mechanism.py` / `mechanism.log`.

Targets: `E{r}` = whitening + r full rounds; `F{r}` = whitening + (r-1) full rounds + final round.
F6 is the real `encrypt`. Keys: real PassKey expansion of a uniformly random master deck
(fresh key per sample) unless noted.

## HEADLINE: F6 (full cipher) has a related-plaintext distinguisher

Swap sigma = (K♣ Q♥) (cards 12, 24), applied to the plaintext. Event: `E(sigma∘m) == sigma∘E(m)`
(exact commutation; also D = 2 positions differ). For an ideal cipher this probability is about 1/52! ≈ 1e-68.

| target | pairs | exact | rate | ratio vs previous F |
|---|---|---|---|---|
| F2 | 1e5 | 1043 | 1.04e-2 | |
| F3 | 2e6 | 873 | 4.4e-4 | 24 |
| F4 | 1.6e7 | 290 | 1.8e-5 | 24 |
| F5 | 1.6e8 | 119 | 7.4e-7 | 24 |
| **F6** | **4e8** | **14** | **3.5e-8** | 21 (predicted 3.1e-8 from the F2–F5 trend) |
| E2 | 4e5 | 691 | 1.7e-3 | |
| E3 | 1.6e7 | 1243 | 7.8e-5 | |

- F6 run: seed 22, 2775 s on 8 cores. All 14 witnesses (master key, plaintext) are in
  `results/F6_KcQh_witnesses.json`. Each is verified against the spec-emitted JS `encrypt`
  (`verify_witness.mjs`, which first matches the 6 committed vectors) AND against pure-Python `ddport`.
  Every exact event is individually decisive. Cost: about 1/3.5e-8 ≈ 3e7 chosen pairs (6e7 encryptions)
  per expected hit under a random key. Per-key variance was not measured.
- Other pairs (A♥K♥ 13,25; K♠Q♦ 38,50) decay at similar per-round factors from lower starting rates.
  In the F2 transposition scan, exact hits concentrate on pairs with equal rank+suit (for example
  K♣Q♥, 9♣8♥, 5♣4♥). The mechanism has not been analysed yet.

## Security-margin table (so far)

| target | broken? | by |
|---|---|---|
| F1 | yes, probability 1 | v9Sym commutes exactly |
| E1 | yes | v9Sym(0,1) agreement statistic; exact commutations |
| E2, F2 | yes | swap statistics; K♣Q♥ exact commutation |
| E3, F3 | yes | K♣Q♥ exact commutation (statistical scans at 50k found nothing at E3) |
| F4, F5 | yes | K♣Q♥ exact commutation |
| **F6** | **yes** | K♣Q♥ exact commutation, 3.5e-8 per pair |

Not done (stopped when F6 broke, per instructions): independent-key setting, fresh-seed repeats for
E3/F3 statistics, (b) single-query χ², (d) peeling and (e) mod-13 write-ups, mechanism analysis.

Reproduce: `python3 check_port.py`; `python3 lowdiff.py witness F6 400000000 22 12,24 out.json`;
`node verify_witness.mjs <doubledeal.mjs> ../../../vectors/doubledeal_vectors.json out.json`.
