<!-- Owns: the index of the BS evidence directories and how to rerun them. Maintenance rules: ../../../DOCS.md. -->
# BS evidence

Status: **a note, not a theorem**, except [`lean/`](lean/README.md): the Lean there proves that the code emitted from `bs.sudo` computes what a hand-written model of the arithmetic, the key reader and the exchange says (correctness, not security; the key build is not covered). Nothing else here is proved in Lean. Every figure is a measurement or an exact enumeration by a script that sits beside its recorded output. The rules are normative in [`primitives/key_exchange/bs/SPEC.md`](../../../primitives/key_exchange/bs/SPEC.md) and in [`bs.sudo`](../../../primitives/key_exchange/bs/bs.sudo) beside it, and stated only there; the scripts and READMEs here point to its sections instead of restating them.

**Evidence harness.** The Python in these directories (`bspegs.py`, `bsref.py`, `keygrid.py`, `peg_supply.py`, `combined.py`, `randomizer_kit.py` and the scripts built on them) is an **evidence harness, cross-checked against `bs.sudo` by [`vectors/check_oracle.py`](vectors/check_oracle.py); not a reference.** Where it and `bs.sudo` or the SPEC disagree, the harness is wrong.

**Committed follow-up.** The evidence scripts will be ported to drive the sudoc-generated code of `bs.sudo`, the measurements rerun, and the hand-written Python deleted. That follow-up lands before any further change to the BS evidence. The Python is not a permanent oracle.

| Directory | What it holds | SPEC |
| --- | --- | --- |
| [`reference/`](reference/README.md) | Peg recipes, integer arithmetic, prime search, arithmetic and malicious-value tests, full-size multiplications, toy-tier attacks, parity checksum, peg provisioning, the tier table | §2, §3, §5, §7, §8 |
| [`exchange/`](exchange/README.md) | Full exchanges with ships+pegs keys through the peg recipes, T1 to R3072 | §0, §7, §8 |
| [`ships-pegs/`](ships-pegs/README.md) | The key: a BUILD/READ simulation, exact entropy DP, brute force, injectivity, build-vs-model checks, walk statistics | §4 |
| [`randomizer-kit/`](randomizer-kit/README.md) | The key's dice: face rules, hole-die equality, row-cup counts | §4.2 |
| [`vectors/`](vectors/README.md) | Known-answer vectors generated from `bs.sudo` by sudoc at the pin, cross-checked against `pow()` and the harness (`reference/`, `ships-pegs/keygrid.py`) | §3, §3.1, §4.2, §4.3 |
| [`lean/`](lean/README.md) | Generated Lean of `bs.sudo` (TAP) and the Link 2 proofs: tier, multiply, tidy, check_received, send_public_value, and, given the key reader's cells, public_value, shared_secret and exchange | §2.3, §3, §3.1, B3–B9 |
| [`key-selection/`](key-selection/README.md) | Why the key is ships + pegs: the candidate comparison (analysis only; none of those keys is a SPEC option) | none |

Python 3 with numpy, sympy and gmpy2 (`bsparams.py`), mpmath not needed. Each directory's README gives its run commands; every path in the scripts is built from the script's own directory, so they run from anywhere. Seeds are fixed, so reruns reproduce the recorded outputs except for timings (and the exceptions listed in each README).
