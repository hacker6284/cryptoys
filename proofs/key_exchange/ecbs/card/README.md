<!-- Owns: what the recorded card v3 logs are. Maintenance rules: ../../../../DOCS.md. -->
# Card v3: recorded logs (history)

Recorded outputs of the Phase-1 Python simulation of card v3: full exchanges (`card_sim_v3_*.{txt,json}`), certificate soundness at field and board level (`soundness_v3_{field,peg}_*.json`, stdout `sf3_*.txt` / `sp3_*.txt`), per-operation costs (`extras_v3.{txt,json}`) and calling (`calling_check.json`). Notes: [`V3_NOTES.md`](V3_NOTES.md).

The scripts (`homes.py`, `homes_v3.py`, `card_sim_v3.py`, `soundness.py`, `soundness_v3.py`, `extras_v3.py`, `calling_check.py`) were a hand-written model of the board; they were deleted when [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) replaced them (git history: commit `ad80f54`). Exchanges, soundness and calling were re-run on the generated code in [`../evidence/`](../evidence/README.md), which compares itself with the `card_sim_v3_*.json` here run by run. `extras_v3` (per-operation costs and the "C before A" home count) was not re-run; its log stays the record.
