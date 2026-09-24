# MegaDreifach reference (partial)

Landed in this PR:

- `megaminx.py` — group library (technical name **megaminx**)
- `front.py` — pad B=28, φ, `require_permutation`, IV-COOK12, 29-byte digest encode
- `selfcheck.py` — agrees with KAT *metadata* and IV-COOK12 digest hex

Not landed (follow-up PR):

- abs-G2 + F3 runner (`em_spike_r4`)
- `hash_bytes` / `hash_deck` / `hash_deck_body` full compression
- Lean M13 digest equality

Product name **MegaDreifach** is locked. See `SPEC.md`.
