<!-- Owns: the index of the BS evidence directories and how to rerun them. Maintenance rules: ../../../DOCS.md. -->
# BS evidence

Status: **a note, not a theorem.** Nothing here is proved in Lean. Every figure is a measurement or an exact enumeration by a script that sits beside its recorded output. The rules are normative in [`primitives/key_exchange/bs/SPEC.md`](../../../primitives/key_exchange/bs/SPEC.md) and stated only there; the scripts and READMEs here point to its sections instead of restating them.

| Directory | What it holds | SPEC |
| --- | --- | --- |
| [`reference/`](reference/README.md) | Peg recipes, integer reference, prime search, arithmetic and malicious-value tests, full-size multiplications, toy-tier attacks, parity checksum, peg provisioning, the tier table | §2, §3, §5, §7, §8 |
| [`exchange/`](exchange/README.md) | Full exchanges with ships+pegs keys through the peg recipes, T1 to R3072 | §0, §7, §8 |
| [`ships-pegs/`](ships-pegs/README.md) | The key: a literal BUILD/READ implementation, exact entropy DP, brute force, injectivity, build-vs-model checks, walk statistics | §4 |
| [`randomizer-kit/`](randomizer-kit/README.md) | The key's dice: face rules, hole-die equality, row-cup counts (also cited by ECBS) | §4.2 |
| [`key-selection/`](key-selection/README.md) | Why the key is ships + pegs: the candidate comparison (analysis only; none of those keys is a SPEC option) | none |

Python 3 with numpy, sympy and gmpy2 (`bsparams.py`), mpmath not needed. Each directory's README gives its run commands; every path in the scripts is relative to the script's own directory. Seeds are fixed, so reruns reproduce the recorded outputs except for timings (and the exceptions listed in each README).
