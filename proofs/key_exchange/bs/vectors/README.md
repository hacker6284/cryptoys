<!-- Owns: the BS known-answer vectors, how they are generated from bs.sudo and how they are cross-checked. Maintenance rules: ../../../../DOCS.md. -->
# BS vectors

Known-answer vectors for [`primitives/key_exchange/bs/bs.sudo`](../../../../primitives/key_exchange/bs/bs.sudo), the runnable form of the [SPEC](../../../../primitives/key_exchange/bs/SPEC.md). Every output is computed by the sudoc JS target at the sudocode pin ([`proofs/SUDOCODE_PIN`](../../../SUDOCODE_PIN)); the JSON records the pin and the `.sudo` hash. The Python in `../reference/` and `../ships-pegs/` is used only as an oracle.

| File | Role |
| --- | --- |
| `make_inputs.py` | Writes `inputs.json`: the dice faces (by kind of die) that built the keys of four recorded exchanges in [`../exchange/`](../exchange/README.md), plus arithmetic, check and call-the-shots inputs |
| `inputs.json` | The inputs |
| `collect_vectors.mjs` | Runs the generated `bs.mjs` over `inputs.json` (JSON conversion only) |
| `regen.sh` | Builds `bs.sudo` at the pin, runs its tests and the collector, writes `bs_vectors.json`; `--check` fails unless the committed file is byte-identical (run in CI by `.github/workflows/proofs.yml`) |
| `bs_vectors.json` | The vectors. Do not hand-edit |
| `check_oracle.py` | Cross-checks every vector against `pow()` and the Python evidence harness, which is not a reference: `keygrid.build` / `key_cells` (BUILD, READ) and `bspegs.py` (multiply, tidy, walk, check). It also checks the header against the pin and the `.sudo` hash (run in CI) |
| `check_oracle_output.txt` | Its recorded output |

Vectors: exchanges at T1 (two, one with a public value ending in 6 misfires), T2 (Bob's value ends in 8 misfires) and T6, each from dice to K on both sides with K_A = K_B; worst-case multiplications at T1 and T2; tidy of p and p + 1; the received-value check on 0, 1, p − 1, p + 1 and 3; call-the-shots round trips ending in misfires.

## Run

From the repo root (`SUDOC` optional, see `proofs/sudocode.sh`):

```sh
python3 proofs/key_exchange/bs/vectors/make_inputs.py      # only when the inputs change
proofs/key_exchange/bs/vectors/regen.sh                    # or --check
python3 proofs/key_exchange/bs/vectors/check_oracle.py > proofs/key_exchange/bs/vectors/check_oracle_output.txt
```
