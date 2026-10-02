# MegaDreifach v3 (candidate)

> **Status: candidate.** v2 ([`../SPEC.md`](../SPEC.md)) stays the current version until a separate change makes v3 current and deprecates v1/v2. HMAC-MegaDreifach and DoubleDeal-CBC-HMAC keep using v2. The Lean package models v2 only (§7).

**What v3 changes.** v3 changes one thing: the card phase `W` inside `E_m`. The v2 card rule (grips, visual noon, slot reads, 36 F3 rounds) is replaced by **ZP26**:
- colour-named card steps with a last-face register;
- the deck dealt once, keeping card 52 in hand;
- 26 echoes of that card.

These are unchanged from v2: pad, φ, card ids, the face-turn tables, chaining, Davies–Meyer `h' = compose(h, E_m(h)) = h·W·h` with the unchanged 3-solve, IV-COOK12, the digest encoding, and the public API. All digests change (`../kats/megaminx_hash_kats_v3.json`).

**Why.** The v2 compression function is not a PRF, and it is far from one: it can be distinguished outright. A v2 block reads only the pieces that pass its read slots, on average 41.2 of 50. Unread pieces never steer `W`. So flipping two unread edges of `h` leaves `W` unchanged, and the output is then predictable exactly:
- 5.18% of free-start flip pairs give an exact prediction;
- P(fixE ≥ 2) of the quotient is +0.080 above ideal;
- see v2 SPEC §8 for the pseudo-collisions.

v3's card phase names every piece by its colours and reads all 50 pieces in every block (PROVED, §5.8). The measured quotient statistics are at ideal within ±0.00016 (COMPUTED, §8). Evidence: [`proofs/megadreifach/security/v3/`](../../../../proofs/megadreifach/security/v3/README.md).

This document is normative for v3. `megadreifach.sudo` in this directory is the runnable spec and the conformance implementation; a mismatch between the two is a bug in the sudo. Where a v2 section is cited "unchanged", the v2 text is normative for v3 too. MegaDreifach is a toy three-megaminx Merkle–Damgård hash. It makes no cryptographic security claim, and it is not for protecting anything.

---

# 1. Scope and non-goals

As v2 §1, with these differences:

- **`E_m` is ZP26 (§5).**
  - The hand procedure needs no grip, no re-grip, no sheet, no lookup table, no XOR, and nothing remembered from one step to the next (§5.8).
  - It does need the **rank order of the twelve centre colours**: A, 2, …, 10, J, Q (centre ids 0…11). A person learns it, or puts a small rank label on each centre of puzzle A; centres never move.
  - It also needs "count up by a rank" on that 12-cycle. This replaces v2's "no colour-to-number arithmetic": counting up colours is the only arithmetic.
- **Non-goals added.**
  - No claim that v3's compression function is a PRF; §8 is evidence against named distinguishers only.
  - No Lean model of v3 (§7).
  - No human trials (§5.6).

# 2. Public API

Unchanged from v2 §2: `Hash` / `MegaDreifach`, `HashDeck` / `MegaDreifachDeck`, `HashDeckBody` / `MegaDreifachBody`, `HashDeckBodyFrom` / `MegaDreifachBodyFrom`.

`HashDeckBodyFrom` remains a free-start analysis surface, not a security API.

# 3. Parameters (locked for v3)

| Item | Value |
| --- | --- |
| Version | **v3** (candidate). v2 is current; v1 is deprecated |
| Pad, φ, card ids | v2 §3, unchanged. Card id → rank = id // 4 (A, 2, …, 10, J, Q, K = 0…12), suit = id % 4 (Clubs, Hearts, Spades, Diamonds), amount k = suit + 1 |
| E_m | **ZP26**: 52 card steps from the Ace face, then 26 echoes of card 52 (§5). No grip, no F3 rounds |
| Chaining, IV, DM, digest | v2 §3, unchanged: final position only, IV-COOK12, `h' = compose(h, E_m(h))`, 29-byte rank |

# 4. The megaminx group

Unchanged from v2 §4: positions, legality, `compose(g, h)` (h first), and face turns, using the same tables.

v3 uses these from v2 §4:
- **Colours** are centre ids 0…11. A face is named by its centre colour. Colour r also carries **rank** r: A = 0, 2 = 1, …, 10 = 9, J = 10, Q = 11.
- `face_nbrs(f)`: the five neighbours of f, clockwise seen from outside f.
- `opposites`.
- The corner triples.
- The edge-slot table of v2 §5.6.

The hand procedure needs none of these tables.

---

# 5. Compression

1. φ(chunk) → a 52-card deal.
2. `e ← E_m(h) = W·h`: start at position h. Run the 52 card steps (§5.3), then the 26 echoes (§5.4).
3. `h ← compose(h, e)`.

Merkle–Damgård and the digest are as in v2 §5.

§5.1–§5.4 are the hand procedure. §5.5 states the same rule for software. If they ever disagree, §5.5 and the sudo are normative, and the prose is a bug.

## 5.1 Words

- **Turn X +n**: turn face X by n clicks clockwise, looking straight at X from outside. A click is a fifth of a turn. (As v2 §5.1.)
- **Count up from face X by rank r**: go r steps up the rank order of the centre colours, starting at X's colour; after Q comes A again. An Ace is X itself, a 2 is the next rank up, and a Q is eleven up. The result is a face.
- **Opposite** face: the face parallel to it, across the puzzle.
- **The x-coloured sticker of a piece**: the piece's sticker of colour x. A face turn keeps the turned face's own colour on that face.
- **Clockwise around a face**: as you look straight at the face from outside.
- **Last face**: the face you turned last in the previous step. At the start of a block it is the **Ace face**.

## 5.2 A card's two pieces

Take a card with rank r and suit amount k (Clubs 1, Hearts 2, Spades 3, Diamonds 4, as in v2). Its **colour** is the colour of rank r; a King uses the Ace colour.

- Look at the five centres around the face of the card's colour. The lowest-ranked of them is the **Clubs neighbour**. Going clockwise, the next three are the Hearts, Spades and Diamonds neighbours.
- The suit picks **n**: the Clubs neighbour for Clubs, and so on.
- **The card's edge** is the edge piece coloured (card colour, n).
- **The card's corner** is the corner piece coloured (card colour, n, the neighbour after n going clockwise).

These are pieces named by their colours. Find them wherever they are now. The face of the card's colour is usually not the face you just turned.

## 5.3 Card step

Hold the card. Let r be its rank and k its suit amount.

1. **Turn.** Count up from the last face by the card's rank and turn that face +k. A King turns the face **opposite** the last face +k.
2. **Name** the card's edge and corner (§5.2).
3. **Edge.** Find the card's edge.
   - Turn the face its card-coloured sticker is on +1.
   - Then turn the face its n-coloured sticker is now on +1.
4. **Corner.** Find the card's corner.
   - Turn the face its card-coloured sticker is on +1.
   - Then turn the face its n-coloured sticker is now on +1.
5. **Edge again.** Look at the card's edge once more. Turn the face its n-coloured sticker is now on +1. **That face is the new last face.**

A step makes 6 turns: k clicks, then five single clicks.

## 5.4 Deal once, then 26 echoes

**Deal.** Do the card step for each of the 52 cards in deal order, putting each card face up on the dealt pile.

**Keep the 52nd card in your hand** instead of putting it on the pile. Call it the **held card**: its rank r, suit amount k, colour c (Ace colour for a King), and its edge (c, n) and corner (c, n, next) as in §5.2.

**Echoes.** Count 26 cards off the dealt pile into a counter pile, without reading them. For each counter card, do one echo:

1. **Look.**
   - Find the held card's edge. **X** is the face its n-coloured sticker is on.
   - Find the held card's corner. **Y** is the face its n-coloured sticker is on.
2. **Echo colour.** Count up from X by Y's rank; an Ace-coloured Y means X itself. The result is the **echo colour P**.
3. **Echo step.** Do the card step (§5.3) with the held card, with P in two places:
   - **Step 1:** count up from **P** by the held card's rank and turn that face +k. A held King turns the face opposite P +k.
   - **Steps 2–5:** "the card's colour" is **P**. The edge is (P, n′) and the corner is (P, n′, next), where n′ is P's neighbour picked by the held card's suit.

After the 26th echo, `W` is done. The board of puzzle A is `W·h`.

**3-solve.** Unchanged (v2 §5.7). The output is h·W·h.

## 5.5 Software form (normative, equal to §5.1–§5.4)

Notation:
- `turn(g, f, n)` is the face turn of v2 §4 (n clicks of face f).
- `edge_face_of(g, a, b, x)` is the face carrying the x-coloured sticker of the edge piece coloured {a, b}, found by its slot in g and read with the v2 edge-slot table (§5.6 there).
- `corner_face_of(g, a, b, c, x)` is the same for the corner piece coloured {a, b, c}.

**Suit neighbours.** `nb = face_nbrs(c)`, and i is the index of `min(nb)`.
- `n = nb[(i + k − 1) mod 5]`
- `n2 = nb[(i + k) mod 5]`

**Card step.** `step(g, last, rank, k, c)`:
1. `f = opposites[last]` if `rank = 12`, else `(last + rank) mod 12`; then `g ← turn(g, f, k)`.
2. `(n, n2)` = suit neighbours of c.
3. `g ← turn(g, edge_face_of(g, c, n, c), 1)`, then `g ← turn(g, edge_face_of(g, c, n, n), 1)`.
4. `g ← turn(g, corner_face_of(g, c, n, n2, c), 1)`, then `g ← turn(g, corner_face_of(g, c, n, n2, n), 1)`.
5. `last ← edge_face_of(g, c, n, n)`, then `g ← turn(g, last, 1)`.

Return `(g, last)`.

**Block.** `E_m(h, deal)`:
- `g = h`, `last = 0`.
- For each card: `(g, last) ← step(g, last, card // 4, card % 4 + 1, colour(card))`, where `colour(card) = card // 4` for non-Kings and 0 for Kings.
- Let `held = deal[51]`, `c = colour(held)`, and `(n, n2)` its suit neighbours.
- Repeat 26 times:
  - `P = (edge_face_of(g, c, n, n) + corner_face_of(g, c, n, n2, n)) mod 12`;
  - `(g, last) ← step(g, P, held // 4, held % 4 + 1, P)`.
- Return g.

Face ids are colours and ranks, so "count up from X by rank r" is `(X + r) mod 12`.

## 5.6 Cost per block (PROVED counts, exact for every block)

| | v2 (C36) | **v3 (ZP26)** |
| --- | --- | --- |
| Deck dealt | once | once (card 52 held for the echoes) |
| Steps | 52 card steps + 36 F3 rounds | 52 card steps + 26 echoes |
| Face turns | 192 | **468** (78 × 6) |
| Clicks | 270 | **520 + 26k** = 546–624, mean 585 (k = the held card's suit amount) |
| Pieces looked up | 88 slot reads | **156 piece finds + 52 register looks** |
| Whole-puzzle re-grips | 88 | **0** |
| Carried between steps | the grip | nothing (§5.8) |

**Clicks.**
- The suit amounts of a whole deck sum to 130, so the 52 card turns are 130 clicks.
- Each card step adds 5 single clicks.
- Each echo adds k + 5 clicks.
- Total: 130 + 260 + 26(k + 5) = 520 + 26k.

`proofs/megadreifach/security/v3/check_v3.py` counts these on the eight `HashDeckBody` vectors.

v3 costs about 2.4× v2's face turns and **about 2.2× v2's clicks** (585 / 270 on average). No human trials have been run, so error rates and wall time by hand are unknown.

## 5.7 Hand details unchanged from v2

- IV-COOK12 by hand.
- The 3-solve.
- Puzzles (A, B, C) = (h, h⁻¹, id).

All as in v2 §5.7. E_m runs on A, held any way.

## 5.8 Coverage and what a person must keep track of (PROVED)

**Coverage.**
- The 48 non-King cards name 48 (edge, corner) pairs that together contain all 30 edges and all 20 corners (enumeration; sudo test "coverage: the 48 non-King cards name all 30 edges and all 20 corners").
- A deal holds each card once.
- So every block finds and reads **all 50 pieces** in its card steps, whatever the deal and the state.
- Echo reads are extra.

**Every input difference changes W.**
- For a fixed deal, take two start positions h ≠ h′. Common turns keep the same set of pieces in different (slot, orientation) states, so that set stays non-empty.
- Each of its pieces is read in the card pass.
- For every piece and every ordered pair of its colours, the 60 states of the piece give 60 distinct two-turn read words (steps 3 and 4).
- So at the first read of a differing piece the turned words differ. The unread-piece predictor of v2 is gone for every perturbation, not only edge flips. (Two different words can still give the same group element. That rate is measured in §8.)

**No grip.** Every face is named by a colour, by counting up colours, or as an opposite. How puzzle A is held never matters.

**Nothing carried between steps.**
- **During the deal:** the last face is the face carrying the n-coloured sticker of the edge of the **top card of the dealt pile**. Step 5 turns exactly that face, and a turn keeps that sticker on it. So if you lose track, re-derive it (sudo test "card pass: the last face is re-derivable from the board and the top dealt card").
- **During the echoes:** step 1 of every echo re-reads X, Y and P from the board and the held card. The previous P is not needed.
- **Within one echo:** P is held only from the look until the echo's edge and corner have been found. Both carry P as a sticker.
- **Visible state:** the board, the dealt pile, the held card and the counter pile.

---

# 6. Digest encoding

Unchanged from v2 §6.

---

# 7. Test vectors

`../kats/megaminx_hash_kats_v3.json` holds the **v3** vectors:
- `vectors`: the same eight message inputs and layout as the v1 and v2 files;
- `hash_deck`: the identity deal;
- `body_vectors`: eight `HashDeckBody` vectors on seeded deals. Four of them hold a King as card 52, and between them the held cards cover all four suits.

The pad lengths, block counts, IV-COOK12 digest and `|G|` are as in v2.

How the vectors are made and checked:
- **Generated** from the runnable spec: `../kats/regen_v3.mjs` imports the sudoc JS build of `megadreifach.sudo` and writes the file. With `--check` it confirms that a fresh run reproduces the file byte for byte. CI does this in `tools/generate-demos.sh`.
- **Hand transliteration.** `proofs/megadreifach/security/v3/check_v3.py` is a literal Python transliteration of §5.3–§5.4, on the Em.lean tables through `m9_search`. It reproduces every digest in the file (CI: `proofs.yml`, megadreifach-lean). It also checks that the fast engine the §8 statistics were computed with equals that transliteration on random blocks.
- **Sudo tests** assert:
  - pad, φ, IV-COOK12, the rank, the group law, the API and the edge table (all as v2);
  - the piece-colour reads;
  - the suit neighbours;
  - coverage;
  - the re-derivable card-pass last face;
  - the King turn;
  - the eight `Hash` digests and the `HashDeck` vector;
  - two `HashDeckBody` vectors, one of them with K♦ held.

**Lean coverage: none for v3.** The Lean package `proofs/megadreifach/` and its emitted `Generated/` model v2 (v2 SPEC §7), and the frozen v1 package models v1. No Lean statement is about v3, and porting is open.

---

# 8. Security status

Nothing here is a security claim. All statistics are about **one compression block** of `E_m` and **named distinguishers** only. Evidence, scripts, seeds and unedited logs are in [`proofs/megadreifach/security/v3/`](../../../../proofs/megadreifach/security/v3/README.md); the analysis, including the rejected variants, is in [`ANALYSIS.md`](../../../../proofs/megadreifach/security/v3/ANALYSIS.md) there.

**Tags.**
- **PROVED**: an argument or a finite enumeration.
- **COMPUTED**: seeded, with 95% intervals. For 0 hits, the exact one-sided 95% bound.
- **HEUR**: a heuristic.

**Tests.** Q is the quotient of two related `W`s. The ideal is a uniform element of G: P(fix ≥ 2) = 0.264241, mean fixed pieces 1, mean moved 49.1667.
- **D1** is a free start with a 2-edge flip of h, on the left: `W(h)⁻¹W(gh)`.
- **D1′** is the same flip on the right: `W(hg)W(h)⁻¹`. D1 and D1′ have the same law (PROVED).
- **D2** is a secret uniform start, with cards 51 and 52 swapped.
- **D3** is telescoping card pairs at 51/52.
- **Merge** swaps adjacent cards at 8 positions and looks for state merges and output collisions.

**Results.**

| Test | v2 (C36): D1′ at 1M, coverage at 100k blocks | **v3 (ZP26)**: D1 + D1′ at 16M per side (pooled), D2 at 4M |
| --- | --- | --- |
| Pieces read per block | 41.2 of 50 on average (COMPUTED) | **50 of 50 (PROVED)** |
| Free start, exact prediction (Δ = id, or W unchanged) | **5.18%** [5.14, 5.23] | 0 in 32M quotients (≤ 9.4e-8) |
| Free start, P(fixC ≥ 2) above ideal | +0.0550 | **−0.00004 ± 0.00016** (HEUR pooling of four 8M samples) |
| Free start, P(fixE ≥ 2) above ideal | +0.0796 | **−0.00005 ± 0.00016** |
| Free start, mean moved − ideal | −2.80 | +0.00006 ± 0.00032 |
| D2 at 4M, P(fixE ≥ 2) / P(fixC ≥ 2) above ideal (±0.00043) | — | −0.0001 / +0.0003. Histogram p .29 / .65, cycle-type p .19 / .68 |
| Merge, 400k adjacent swaps | — | 0 state merges, 0 output collisions (≤ 7.5e-6 per pair) |
| D3, 8 × 50k | — | 0 positions equal, 0 collisions (≤ 6.0e-5 per cell) |
| End-of-W diagnostic, 2M | — | no last-two-step excess beyond ±0.00022. Fully fixed corners of Q +0.00101 ± 0.00080 (2.5σ, not confirmed at 8M, HEUR) |

**Power** (normal approximation):
- D1 + D1′ at 16M: 90% power at |adv| ≥ 0.00026 on P(fix ≥ 2).
- D2 at 4M: 90% power at 0.0007.

Effects smaller than these are not excluded. For comparison, NRk52's free-start corner bias of +0.00060 ± 0.00022 was detected at 8M and is absent here (difference z ≈ 4.6).

**Known, unchanged from v2.**
- `W` is a function of what the block reads. A free-start observer who sees h and the output learns `W = h⁻¹·y·h⁻¹` (DM shape).
- `HashDeckBodyFrom` is a free-start surface: no free-start resistance is claimed.
- Length extension on bare `Hash` is accepted by design.

**Not done.**
- No second-preimage, preimage or IV-anchored collision search on v3 beyond D3 and merge.
- No multi-block tests.
- No tests from chosen non-uniform starts other than IV-COOK12 in merge/D3.
- No human trials.

# 9. What this does not claim

As v2 §9, and also:
- that v3's `E_m` or compression function is a PRF or ideal cipher. §8 shows only that the named distinguishers, which separate v2 from a random function, do not separate v3 at the stated power;
- any Lean result about v3 (there is none, §7);
- anything about human error rates or hand timing.
