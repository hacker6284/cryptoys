<!-- Owns: what the recorded SPEC §7 twist logs are. Maintenance rules: ../../../../DOCS.md. -->
# Twist (SPEC §7.1): recorded logs (history)

Recorded outputs of the Phase-1 `s7_certificate.py` (parts A, B, C: `s7_part{A,B,C}.txt`, `s7_certificate.json`). That script wrote the receiver out at field level; it was deleted when [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) replaced it (git history: commit `ad80f54`). Re-run on the generated code: [`../evidence/twist_s7.py`](../evidence/README.md). `s7_partC.txt` is the record that the Hobby discrete log did not finish within 1,500 s; that run is not repeated.
