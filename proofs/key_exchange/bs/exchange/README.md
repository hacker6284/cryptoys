<!-- Owns: the full BS exchanges with ships+pegs keys and their recorded outputs. Maintenance rules: ../../../../DOCS.md. -->
# BS exchanges with ships+pegs keys

Status: **a note, not a theorem.** These are simulations: every public value and shared secret is compared with Python's `pow`, and every move is counted.

`exchange.py` runs the BS exchange (SPEC §3 B9) with keys built by the SPEC dice and read "ships, then pegs" ([`../ships-pegs/keygrid.py`](../ships-pegs/keygrid.py), SPEC §4.2–§4.3), through the unchanged peg recipes ([`../reference/bspegs.py`](../reference/bspegs.py)). Checks per exchange: A = 3^a and B = 3^b, A in the order-q subgroup, K_A = K_B = 3^(2ab) = (B²)^a, K canonical. Moves per person = all walks and checks of both parties / 2. Parameters: `../reference/params.json` and, for R512, `../reference/params_323.json` (`n323`).

| Tier | Runs | Seed |
| --- | --- | --- |
| T1 | 20 | 11 |
| T2 | 5 | 12 |
| T6demo | 2 | 13 |
| R512 | 1 | 14 |
| R1024 | 1 | 15 |
| R2048 | 1 | 16 |
| R3072 | 1 | 17 |

Results (`exchange_output.txt`); every exchange is correct:

| Tier | Exchanges | All correct | Mults per person | Moves per mult | Moves per person (mean) | Key cells (mean) |
|---|---|---|---|---|---|---|
| T1 skiff | 20 | yes | 1,053.4 | 464 | 4.89·10⁵ | 211.9 |
| T2 frigate | 5 | yes | 1,047.9 | 1,586 | 1.66·10⁶ | 210.8 |
| T6 demo | 2 | yes | 1,048.8 | 18,797 | 1.97·10⁷ | 211.8 |
| R512 | 1 | yes | 1,034.5 | 182,771 | 1.89·10⁸ | 212.5 |
| R1024 | 1 | yes | 1,065.0 | 738,352 | 7.86·10⁸ | 214.5 |
| R2048 | 1 | yes | 1,027.0 | 2,929,631 | 3.01·10⁹ | 209.5 |
| R3072 | 1 | yes | 1,036.0 | 6,520,196 | 6.75·10⁹ | 209.0 |

## Files

* `exchange.py`: the runs. `exchange_<tier>.json`: every exchange (key cells, hit units, ships, checks, per-phase moves and operation counts). `log_<tier>.txt`: the console output. `exchange_output.json`: the merged summary (`exchange.py summary`); `exchange_output.txt`: its table.

## Run

From this directory (the script finds its inputs relative to itself):

```sh
for t in T1 T2 T6demo R512 R1024 R2048 R3072; do python3 exchange.py $t > log_$t.txt; done
python3 exchange.py summary > exchange_output.txt
```

Run time on one core: T1 3 s, T2 and T6demo under a minute, R512 ≈ 1 min, R1024 ≈ 5 min, R2048 ≈ 21 min, R3072 ≈ 50–70 min (on a shared, loaded machine).
