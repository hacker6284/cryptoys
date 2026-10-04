<!-- Owns: the ECBS known-answer vectors, how they are generated from ecbs.sudo and how they are cross-checked. Maintenance rules: ../../../../DOCS.md. -->
# ECBS vectors

Known-answer vectors for [`primitives/key_exchange/ecbs/ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo), the runnable form of the [SPEC](../../../../primitives/key_exchange/ecbs/SPEC.md). Every output is computed by the sudoc JS target at the sudocode pin ([`proofs/SUDOCODE_PIN`](../../../SUDOCODE_PIN)); the JSON records the pin and the `.sudo` hash. PARI/GP ([`../oracle/ecbs_oracle.py`](../oracle/)) is the oracle.

| File | Role |
| --- | --- |
| `make_inputs.py` | Writes `inputs.json` (seeded): per tier, field elements, acrosses to fold, points (P, a subgroup point, one outside the subgroup, an order-5 point, an off-curve pair), d10 faces for walks and exchanges, receiver-check classes, roll streams. PARI only picks inputs |
| `inputs.json` | The inputs |
| `collect_vectors.mjs` | Runs the generated `ecbs.mjs` over `inputs.json` (JSON conversion only; the shared helpers are in [`../../vectors_common.mjs`](../../vectors_common.mjs)) |
| `regen.sh` | Wrapper for [`../../vectors_regen.sh`](../../vectors_regen.sh) `ecbs` (one script for BS and ECBS): builds `ecbs.sudo` at the pin, runs its tests and the collector, writes `ecbs_vectors.json`; `--check` fails unless the committed file is byte-identical (run in CI by `.github/workflows/proofs.yml`). About 20 s, most of it one Serious exchange |
| `ecbs_vectors.json` | The vectors. Do not hand-edit |
| `check_oracle.py` | Cross-checks every vector against PARI and the header against the pin and the `.sudo` hash (needs `cypari2`; run in CI) |
| `check_oracle_output.txt` | Its recorded output |

Vectors, every tier (Demo, Toy, Hobby, Serious): the base point by rule; multiply, cube and the ladder-and-tally inverse; the §6 fold; curve test and certificate on five kinds of point; key walks from d10 faces (not Serious: its walks are inside the exchange); the receiver's verdict on honest, A = C, outside-the-subgroup, order-5 and off-curve inputs; full exchanges from dice to the folded key on both sides (Demo 2, Toy 2, Hobby 1, Serious 1) with their move counts, band peaks and control-row use; the d10 row cup, including a re-roll and running out of faces; each home's coordinate range.

## Run

From the repo root (`SUDOC` optional, see `proofs/sudocode.sh`):

```sh
python3 proofs/key_exchange/ecbs/vectors/make_inputs.py      # only when the inputs change (needs cypari2)
proofs/key_exchange/ecbs/vectors/regen.sh                    # or --check
python3 proofs/key_exchange/ecbs/vectors/check_oracle.py > proofs/key_exchange/ecbs/vectors/check_oracle_output.txt
```
