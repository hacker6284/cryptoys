# Scramble v2: security analysis

> **Status: Scramble is broken.** This is a trimmed copy of the stage-3 security review of
> Scramble v2 (review of `origin/main` `e01b982`; the vectors and the specified behaviour are
> unchanged since). It records why the SPEC marks Scramble broken. It is evidence (proofs on
> paper, seeded scripts and their logs), not a Lean theorem, and not a proposal for a new
> version. The design-fix proposals of the original review are not included.

Tags (the same set as the SPEC's Security section):
- **proved (paper)**: proof written out here, on paper. Nothing in this report is kernel-checked.
- **computed**: an exact value from a script in this directory, with its recorded output in
  `logs/`.
- **measured**: the outcome of a seeded run of a script in this directory (work counts, sample
  frequencies, wall times), with its recorded output in `logs/`.
- **heuristic**: a cost model or estimate, not a bound.
- **argued**: argument given, not run.

Citations are marked *literature*, with *(unverified detail)* where the reviewer did not re-read
the source.

## 0. Summary

- **The old SPEC figures were not the real costs.** The SPEC said "The design notes record a
  collision attack around 2^32.6, and a meet-in-the-middle second-preimage attack around
  2^33". Those design notes are not in the tree. The numbers are the *generic* square-root
  costs for a 65-bit state. Scramble v2 has structure that makes all three properties much
  cheaper. End-to-end attacks on the real function (measured). Each result's messages and
  digests were re-checked through the JavaScript that `sudoc` generates from `scramble.sudo`,
  which in the same run reproduces all 10 SPEC vectors
  ([`scramble_sudo_check.mjs`](scramble_sudo_check.mjs) →
  [`logs/scramble_sudo_check.log`](logs/scramble_sudo_check.log)):

  | Attack | Old SPEC figure | Measured | Time (1 Python process) | Log |
  | --- | --- | --- | --- | --- |
  | Collision | ≈2^32.6 | **2^21.88 nybble steps** (≈2^18.29 hash-equivalents) + 2^21.76 edge-only permutations | 17 s | [`logs/scramble_collision.log`](logs/scramble_collision.log) |
  | Second preimage (random 64-byte target) | ≈2^33 | **2^22.94 nybble steps** (≈2^19.35 hash-equivalents) + 2^22.09 edge-only permutations | 37 s | [`logs/scramble_second_preimage.log`](logs/scramble_second_preimage.log) |
  | Preimage of a given digest (hex only) | not stated | **2^22.95 nybble steps** | 37 s | [`logs/scramble_decode_preimage.log`](logs/scramble_decode_preimage.log) |

  Each row is one seeded run (seed 20260930), and each run succeeded. A success rate over
  repeated runs was not measured.

- **Flaw F1, Rule B (proved (paper)): the corner-and-centre sub-state is autonomous.** Rule B reads
  only the up-front-right corner, and face turns never mix corners with edges. So corners and
  the frame evolve on their own, in ≤ 2^29.98 states. Edges are merely permuted by maps chosen
  by (nybble, corner state). This makes Joux multicollisions on a 30-bit chain possible,
  followed by a birthday search or meet-in-the-middle on the edges.
- **Flaw F2, digest (proved (paper) + computed): the digest encoding is not injective.** The edge
  orientation rule ("bit 0 iff the first-axis sticker is W, Y, R or O") cannot see flips of RW,
  OW, RY and OY, since both stickers are in the set.
  - Each digest has 8 or 16 legal seated poses.
  - The image is |G|/12 = 2^61.64, not "about 65.2 bits", so the *generic* birthday bound is
    already ≈2^30.8 rather than 2^32.6.
  - Two real messages with equal digest but different cubes are exhibited.
- **Also:**
  - The walk is invertible step by step (proved (paper)), so a preimage costs the same as a second
    preimage.
  - There is partial length extension: the digest fixes the internal state up to ≤ 384
    candidates (argued, §4).
- **Honest claim for Scramble v2: none.** Collisions, second preimages and preimages are
  practical: the logs record 17 s, 37 s and 37 s of wall time, one Python process each, on
  the one machine that produced them (S8, §5). Even without F1, any single-cube walk with this
  digest encoding is capped by the size of the digest image: generic collisions cost ≈2^30.8
  (birthday on 2^61.64 values; §3.3), below any AES/SHA-level target.

## 1. Files

| Item | Path | Notes |
| --- | --- | --- |
| Spec | [`primitives/hash/scramble/SPEC.md`](../../../primitives/hash/scramble/SPEC.md) | "Rule B", "Digest", `scramble_v2`, "Security" |
| Attack engine | [`scramble_ref.py`](scramble_ref.py) | Fast attack engine: Scramble v1/v2 as a 54-facelet permutation model, written from the SPEC. Not the reference: `scramble.sudo` is normative. Checked against the vectors (computed): all 10 SPEC vectors (digest, facelets and step counts) reproduce |
| sudoc check | [`scramble_sudo_check.mjs`](scramble_sudo_check.mjs) | Builds JS from `scramble.sudo` with `sudoc build --target js` (as `tools/build.sh` does), then checks the 10 SPEC vectors, the attack messages in `logs/`, the `hello` twin and the decoded `cube` pose through it → [`logs/scramble_sudo_check.log`](logs/scramble_sudo_check.log) |
| F1 attacks | [`scramble_attack.py`](scramble_attack.py) `{collision\|second\|preimage}` | `preimage` takes its target pose from hashing `hello`; superseded by `scramble_decode.py` |
| F2 evidence | [`scramble_digest_check.py`](scramble_digest_check.py) | → [`logs/scramble_digest_check.log`](logs/scramble_digest_check.log) |
| Digest decoder + preimage | [`scramble_decode.py`](scramble_decode.py) `[HEX]` | digest→pose decoder (round-trips 2000/2000; invariants hold on 2000/2000 random states) plus a preimage of a digest given only as hex → [`logs/scramble_decode_preimage.log`](logs/scramble_decode_preimage.log) |

All scripts are seeded and single-process (peak RSS ≤ 293 MB). Run one at a time, from this
directory:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scramble_attack.py collision
PYTHONDONTWRITEBYTECODE=1 python3 scramble_attack.py second
PYTHONDONTWRITEBYTECODE=1 python3 scramble_decode.py 132FDCE0BF26E5898
PYTHONDONTWRITEBYTECODE=1 python3 scramble_digest_check.py
SUDOC=/path/to/sudoc node scramble_sudo_check.mjs   # default: <repo>/.sudocode/sudoc/target/release/sudoc
```

CI (the `generated-fresh` job in `.github/workflows/proofs.yml`, which builds `sudoc` at the
pin) runs `scramble_sudo_check.mjs` and requires its output to equal its log byte for byte. CI
does not run the Python scripts (follow-up S7, §5). The logs were regenerated when the printed
corner-bound estimate was corrected to 24·(8!/2)·3^7; the messages, digests and work counts were
unchanged, and only that estimate, wall time and memory differ from the first run. The collision
and second-preimage logs predate the label rename and print "reference self-check" on line 1;
the scripts now print "engine self-check". A rerun reproduced every count, digest and message.

## 2. Structural facts (proved (paper))

The function, as specified: each message nybble n performs two clockwise quarter turns V2[n],
then Rule B (read the colours `up`, `front` of the cubie in slot (1,1,1) on +Y and +Z, and
rotate the whole cube so the centre of `up` goes to +Y and the centre of `front` to +Z). Padding
is marker 8, then `6 0 7 1` cyclically up to 12 nybbles. The closer is F2, B2, then the seat
(W up, G front). The digest is the rank of the seated pose (cp, co, ⌊rank(ep)/2⌋, eo), 9 bytes.
|G| = 8!·3^7·12!/2·2^11 = 2^65.229 (computed), and √|G| = 2^32.615, so the old SPEC's 2^32.6
is the generic birthday bound on |G|.

**P1. Face turns preserve cubie kind.**
- Each map in the SPEC's "Moves" table is a signed coordinate permutation. It keeps the number
  of nonzero coordinates, so it sends corner slots to corner slots, edge slots to edge slots,
  and centre slots to centre slots.
- The same holds for the 24 whole-cube rotations, which are signed permutation matrices.
- Hence every step is a product of three permutations of the 54 facelet slots, each preserving
  the partition {centre, edge, corner}. ∎

**P2. Autonomy of the corner-and-centre sub-state (flaw F1).** Let c = the colours on the 6
centre slots and the 24 corner-facelet slots, and e = the colours on the 24 edge-facelet slots.
The step x ↦ step_n(x) satisfies c′ = Φ_n(c) and e′ = π_{n,c}(e), where π_{n,c} is a
permutation of edge slots depending only on (n, c).

*Proof.*
1. The two quarter turns are fixed slot permutations. By P1 they act on c and e separately.
2. Rule B's rotation is determined by the colours at (1,1,1)'s +Y and +Z facelets, which are
   corner facelets, and by where the centres of those colours are, which are centre facelets.
   So the rotation is a function of the post-turn c.
3. The rotation is again kind-preserving. ∎

**P3. Each symbol is a bijection on the full state space (frame included).**
- Given the post-state y, the pre-rotation state z = ρ^{-1} y must satisfy "ρ is the rotation
  Rule B selects from z".
- The selected rotation sends the centre of colour `up` to +Y and the centre of `front` to +Z.
  After the rotation, the piece formerly at (1,1,1) sits at ρ(1,1,1). Its former +Y and +Z
  stickers now face ρ(+Y) and ρ(+Z) and match the centres there.
- For fixed y, at most one of the 24 ρ is consistent. Chirality of corner pieces rules out the
  others: the pair (sticker on +Y, sticker on +Z) of a corner, read in the slot's handed axis
  order, determines the piece and its twist.
- The scripts use this constructively: `prepad_states_from_seated` in `scramble_attack.py`
  inverts steps this way and asserts that each result hashes back to the given seated pose.
- Consequence: the walk can be run backwards from any state. This is why generic MITM
  preimages cost ≈ √(state), and preimage ≈ second preimage. ∎

**P4. Corner permutation parity.**
- A quarter turn is a 4-cycle on corners, which is odd, so each symbol's two turns are even.
- Each of the 24 rotations is even on corners: 90° gives two 4-cycles; 120° gives two
  3-cycles; 180° about a face axis gives four 2-cycles; 180° about an edge axis gives four
  2-cycles.
- So the corner arrangement in space is always even, and |{c}| ≤ 24·(8!/2)·3^7 = 2^29.98. ∎

**P5. Pre-padding states per digest.**
- For messages of ≥ 11 nybbles the padding is the single nybble 8. For a byte message, "≥ 6
  bytes" suffices.
- The seat is one of 24 rotations. Undoing the seat, B2, F2 and symbol 8 (by P3) gives exactly
  24 pre-padding states per seated pose.
- Under F2 each digest has 8 or 16 seated poses, so there are 192 or 384 pre-padding states
  per digest. ∎

**P6. Non-injective digest (flaw F2).**
- In the SPEC's encoding, the edge bit is 0 iff the first-axis sticker ∈ {W, Y, R, O}.
- For edge pieces RW, OW, RY and OY both stickers are in that set, so the bit is 0 in both
  orientations.
- Flipping two of them (a legal move: an even number of flips) changes the cube but not the
  digest.
- The 12th edge bit is not encoded; it is implied only for the true orientation.
- Exact count (computed, `logs/scramble_digest_check.log` [3]):
  - 8 legal seated poses share a digest when slot 11 holds one of the four ambiguous pieces;
  - otherwise 16;
  - so the image is |G|/12 = 2^61.644;
  - sample of 300 (measured): {8: 109, 16: 191}, matching probabilities 1/3 and 2/3.
- Instances:
  - solved and RW+OW-flipped both give digest 00000000000000700; the control RW+GW gives …702;
  - a real message whose seated pose is `hello`'s pose with RW+OW flipped (so its digest is
    `hello`'s, `052A3C7D12291D140`, but its cube differs);
  - the decoder in `logs/scramble_decode_preimage.log` [3] returns a pose for the `cube`
    vector's digest whose facelets differ from the SPEC's listed facelets, but which has the
    same digest.
  - Both instances are re-checked through the sudoc-generated JS
    (`logs/scramble_sudo_check.log` [3]): the `hello` twin and the hex-only preimage are hashed
    there, and their final facelets each differ from the SPEC's `hello` and `cube` rows in
    exactly 4 stickers (the RW+OW flip).

## 3. The attacks (measured)

Work unit: one **nybble step** (two quarter turns plus Rule B). Corner-only steps are counted as
full steps, which is an over-count. One hash of a ≥ 11-nybble message is ≥ 12 nybble steps, so
"hash equivalents" = steps/12. This is conservative: it compares against the cheapest possible
hash.

### 3.1 Collision (F1 plus Joux)

1. **Joux stages (literature: Joux, "Multicollisions in iterated hash functions", CRYPTO 2004,
   LNCS 3152).** From the current corner state c_i, try random 8-nybble blocks. Stop at the
   first two blocks b, b′ that reach the same c_{i+1}.
   - By P2, b and b′ then induce two edge permutations g_b, g_{b′}.
   - After t stages there are 2^t messages with the *same* corner state, whose edge states are
     g(e_0) for 2^t products g.
2. **Edge birthday.** The edge part has ≤ 12!·2^11 ≈ 2^39.8 values, and fewer are reachable
   with parity constraints (≈2^38.8). Store the edge outcomes until two coincide, which needs
   2^t ≳ 2^19.4.
3. Two messages with equal full pre-padding state have equal digests. This holds when both
   messages have the same length ≥ 11 nybbles, so they get the same padding.

Measured, with t = 22 (`logs/scramble_collision.log`):
- mean stage cost 2^14.42 blocks;
- the first edge match came after 1,769,627 ≈ 2^20.75 stored outcomes;
- a verified 88-byte collision, digest `0AFB0BE3439EF6892`;
- total 2^21.88 nybble steps plus 2^21.76 edge-only permutation applications.

The stage cost is *below* the uniform-model birthday estimate √(π/2·2^29.98) ≈ 2^15.3. The
8-nybble walk from a fixed state is non-uniform on the corner states. This helps the attacker
and is not a model error.

**Cost model (heuristic):** it uses the measured mean stage cost 2^{14.4}, so it is a fit to
the run, not an independent prediction.
C_coll ≈ t·8·2^{14.4} + 2^{t} edge applications, with t ≈ ½·log2(edge space) ≈ 19.4–22.
This gives ≈2^{21.9}.

### 3.2 Second preimage and preimage

1. Target: the full pre-padding state x* = (c*, e*). For a digest-only target it is one of the
   192/384 candidates of P5, obtained with the decoder `scramble_decode.py`.
2. Run t = 42 Joux stages from the IV, giving a common corner state c_t.
3. **Corner bridge.** Meet in the middle between c_t (forward 4 nybbles) and c* (backward 4
   nybbles, using P3). There are 16^4 = 2^16 ends per side in ≤ 2^30 corner states. The runs
   found 5 (second preimage) and 2 (hex-only preimage) meets. The bridge block induces a known
   edge permutation g_β, so the edge target after the stages is e** = g_β^{-1}(e*).
4. **Edge MITM.** Split the 42 stages into 21 + 21. Tabulate the 2^21 forward edge outcomes of
   the first half. Walk the second half backwards from e**. The expected number of matches is
   2^{42}/2^{38.8} ≈ 9.
5. Verified results:
   - a 172-byte second preimage of a random 64-byte message (digest `0A38700830D1C599C`), in
     2^22.94 steps (`logs/scramble_second_preimage.log`);
   - a 172-byte preimage of the digest **given only as hex** `132FDCE0BF26E5898` (the SPEC's
     `cube` vector), in 2^22.95 steps, 37 s (`logs/scramble_decode_preimage.log`).

**Cost model (heuristic):** C_pre ≈ t·8·2^{14.4} + 2·2^{t/2} + 2·16^{4} with t ≈ 40.
The dominant term is the Joux stages, ≈2^{23}. Like the collision model, it uses the measured
stage cost 2^{14.4}, so it is a fit to the runs. No reduced-size extrapolation is needed: every
number is measured on full-size Scramble v2.

### 3.3 Generic attacks (what would remain without F1/F2)

| Attack | Generic cost | Status |
| --- | --- | --- |
| Collision, current encoding (image 2^61.64) | ≈2^30.8 | computed count + standard birthday (literature) |
| Collision, injective encoding | ≈2^32.6 | as above |
| Preimage / second preimage by MITM over the invertible walk (P3), 192–384 target states | ≈2·2^{32.6} steps, with ≈2^{32.6} memory; a low-memory variant via parallel collision search (literature: van Oorschot–Wiener, J. Cryptology 12(1), 1999) at a small constant factor | heuristic (standard) |
| Brute-force preimage | ≈2^{61.6}/384 per target digest | trivial |

The old SPEC sentence gave the first-order generic numbers (2^32.6 and "≈2^33 MITM"). It
omitted that the MITM applies to preimages too (P3), that the encoding shrinks the image to
2^61.6, and that F1 makes all three attacks far cheaper than generic.

## 4. Other attacks considered

- **Length extension (argued, not run).** Scramble has no length encoding and no finalisation
  beyond F2 B2 plus the seat, both invertible. From a digest, P5 gives ≤ 384 candidate states
  after m‖8. Continuing each candidate with a suffix gives the digests of m‖(0x8X)‖s (the
  marker nybble becomes the high nybble of a data byte). So a secret-prefix MAC H(k‖m) would be
  forgeable with probability ≥ 1/384 per attempt. Scramble is keyless, and the SPEC offers no
  MAC mode; noted for completeness.
- **Cayley-graph / group-theoretic attacks (literature).** Walk hashes in groups are vulnerable when
  short relations or subgroup structure can be exploited (Tillich–Zémor: Grassl, Ilić,
  Magliveras, Steinwandt, J. Cryptology 24 (2011) *(unverified detail)*; survey: Petit,
  Quisquater, "Rubik's for cryptographers", Notices AMS 60(6), 2013 *(unverified detail)*).
  Here Rule B makes the walk state-dependent, not a Cayley walk, but P2 shows that the
  dependence factors through a small quotient (the corner states), which is what §3 exploits.
  Short-relation collisions were not searched; they are not needed given §3.
- **Solver-based preimages (heuristic).** A cube solver reaches any pose in ≤ 20 face turns (literature:
  Rokicki, Kociemba, Davidson, Dethridge, SIAM J. Discrete Math. 27(2), 2013 *(unverified
  detail)*), but that does not directly give a *message*, because Rule B interleaves rotations
  and each nybble fixes a pair of turns. Not pursued.
- **Fixed points / cycles of Rule B, slide-type self-similarity.** Not searched. They would not
  change the verdict.
- **v1 (superseded).** v1 uses the same Rule B (after 8-move blocks) and the same digest
  encoding. P2 and P6 apply verbatim, so F1 and F2 hold for v1 too (proved (paper), by the
  same arguments). The attacks were not run on v1.

## 5. Open

- Short-relation and solver-assisted attacks (§4).

Tracked follow-ups from the review of this write-up:

- **S5.** Keep one home for the attack table. It is currently in both the SPEC's Security
  section and §0 here.
- **S6.** The SPEC banner should also say that the vectors, the conformance tests and the
  generated-Lean TAP still hold.
- **S7.** A `scramble-attack-logs` CI job that re-runs the seeded scripts and checks their logs
  (the scripts are seeded and deterministic). Only `scramble_sudo_check.mjs` runs in CI so far
  (§1).
- **S8.** The wall times come from one unnamed machine. The reviewer measured 97–202 s under
  load.
