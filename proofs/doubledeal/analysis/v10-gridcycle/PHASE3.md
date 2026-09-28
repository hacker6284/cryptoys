# DoubleDeal v10 GridCycle, Phase 3: "bump the occupant" (analysis only)

**Kind:** analysis. Nothing here changes the spec or `main`; the algorithm decision is Zachary's.
Setting and metric as in [README.md](README.md) (Phase 1) and [PHASE2.md](PHASE2.md).

**Idea (Zachary's parked rule).** When a card's target seat is taken, the new card takes the target
and the card already there (the *occupant*) is lifted and moved to an overflow seat. At the table a
blocked step becomes "lift, place, move". The set of filled seats grows exactly as in v10 (one new
seat per card), but which card sits where changes, and cards already placed can move again later.

## Result

**None of the bump variants is invertible.** For each one there are two different decks that give
exactly the same GridCycle output, so no decryption procedure can exist, at the table or otherwise.
Witnesses are verified by two independent implementations (C `p3bump.h`, Python `p3trace.py`). Small
analogues (grids up to 3×3, all n! decks) show the maps are far from injective, and no small tweak
tried restores invertibility. So Step 2 (strength measurements) does not apply: survival numbers for a
map that cannot be decrypted would be meaningless. The ranked table below records this.

## Variants (the ids are those used in the scripts)

| id | rule when the target is taken | next step |
|---|---|---|
| 40 (a) | occupant goes to the v10 scan seat (marker row, from the target column, first free), marker +1 | from the target, by the new card |
| (b) | (a) + ghost finger | the new card now always sits on the target, so the ghost finger changes nothing: **(b) is the same map as (a)** |
| 41 (c) | occupant sends itself: row = marker + occupant's suit, start column = target column + occupant's rank, first free, marker +1 (Phase-2 rule 1 applied to the occupant) | from the target, by the new card. With or without ghost finger is again the same map, since the new card sits on the target |
| 42 (d) | as (a) | "follow the bumped card": from the occupant's new seat, driven by the occupant |
| 43 (d) | as (c) | from the occupant's new seat, driven by the occupant |
| 45 (tweak) | as (a) | from the target, driven by the occupant |
| 46 (tweak) | as (a) | from the occupant's new seat, driven by the new card |
| 47/48 (tweak) | occupant leaves the table onto a side pile; at the end the pile fills the empty seats in reading order (first-bumped first / last-bumped first) | from the target, by the new card |

## Step 1: why decryption is not well defined

### The argument

A GridCycle-style walk is decryptable exactly when the decryptor can, at every step, tell which card
drives the next step. In v10 and in Phase-2 rules 1 and 2, a placed card never moves again. So the card
the decryptor sees on the target in the final layout is the card placed there, and the walk can be
replayed forward (that is the whole inverse).

With a bump, the card placed at step *i* drives step *i+1*, but it can be lifted off its seat by
some later step. The final layout records only where each card **ended**, not in which order cards
arrived and were pushed on. Two different arrival orders can then produce the same final layout, the
same marker and the same finger, after which the two walks are identical. The concrete mechanism in the
most common case uses K♣ (its step is (0, 0), so the card after it always targets K♣'s seat):

* **Deck A** has K♣, y at walk positions p, p+1. K♣ lands on seat T. y targets T (K♣'s zero step)
  and bumps K♣ to the first free seat O of the marker row, scanning from T's column. y sits on T;
  the next target is U = T + step(y).
* **Deck B** has y, K♣ at p, p+1. y lands on T (the landing seat of walk position p does not depend
  on which card it is). K♣ targets U. If U is free, K♣ sits on U, and the next card z targets U
  again (zero step) and bumps K♣ to the first free seat of the marker row, scanning from U's column.
* Both decks now have y on T, z on U, the finger on U driven by z, and the marker advanced once. K♣
  ends in the same seat whenever the marker-row scans from T's column and from U's column meet at
  the same free seat (for example, when the seats between them in that row are all taken). From then
  on the walks are identical, so **bump(A) = bump(B) with A ≠ B**.

Rule (c) behaves the same, because the occupant in both decks is K♣: its suit adds 0 rows and its
rank 0 columns. Traced witness, rule (a), from `p3/trace.log` (full decks in `p3trace.py`):

```
deck A: 21 K♣ -> (1,9) bumps K♠ to (2,9)   22 J♠ -> (1,9) bumps K♣ to (3,10)   23 Q♣ -> (3,7) free
deck B: 21 J♠ -> (1,9) bumps K♠ to (2,9)   22 K♣ -> (3,7) free               23 Q♣ -> (3,7) bumps K♣ to (3,10)
```

After step 23 both tables are identical (J♠ on (1,9), Q♣ on (3,7), K♣ on (3,10), marker ♣, finger (3,7)
driven by Q♣), and so is everything after. A decryptor reaching step 21 sees J♠ lying on (1,9) and cannot
tell whether it arrived at step 21 (deck B) or at step 22 by bumping K♣ (deck A). Both are consistent
with the whole table.

K♣ is the most common trigger but not the only one. Collisions without K♣ among the swapped cards exist
for every variant, and for the "follow the bumped card" variants they are the majority (table below).
Making K♣'s step non-zero would therefore not fix it.

### Evidence

Explicit 52-card witnesses (C `p3collide.c`, re-verified by the independent Python `p3trace.py`):

| variant | witness (two decks, same output) | decks (of 2000 random) with a colliding single swap | colliding swaps found: involving K♣ / adjacent positions |
|---|---|---|---|
| (a) 40 | swap walk positions 21, 22 (K♣, J♠) | **386 (19%)** | 375 / 405 of 411 |
| (c) 41 | swap walk positions 14, 15 (K♣, A♥) | **486 (24%)** | 460 / 534 of 537 |
| (d) 42 | swap walk positions 3, 4 (A♥, K♥) | 16 (0.8%) | 5 / 13 of 16 |
| (d) 43 | swap walk positions 10, 11 (K♥, K♦) | 43 (2.2%) | 1 / 29 of 44 |

These counts only look at decks one transposition apart, so they are lower bounds on how often a table
has more than one possible preimage.

Exhaustive small analogues (`p3small.c`, `p3/small_injectivity.log`: R×C grid, n = R·C cards, same
walk/step/marker structure, all n! decks). v10 and rule 1 are injective on every grid; every bump
variant loses most of the information:

| grid (n!) | v10 | rule 1 | 40 (a) | 41 (c) | 42 | 43 | 45 | 46 | 47 pile | 48 pile |
|---|---|---|---|---|---|---|---|---|---|---|
| 2×3 (720) | 720 | 720 | 166 | 174 | 442 | 453 | 414 | 440 | 160 | 175 |
| 3×2 (720) | 720 | 720 | 172 | 163 | 433 | 438 | 452 | 422 | 177 | 164 |
| 2×4 (40 320) | 40 320 | 40 320 | 8 719 | 8 294 | 23 862 | 23 768 | 23 591 | 24 267 | 8 541 | 8 537 |
| 4×2 (40 320) | 40 320 | 40 320 | 8 625 | 8 103 | 21 207 | 21 739 | 23 616 | 23 920 | 8 474 | 8 549 |
| 3×3 (362 880) | 362 880 | 362 880 | 68 729 | 64 492 | 205 130 | 204 959 | 211 684 | 217 338 | 66 409 | 66 200 |

(Entries are the number of distinct outputs; injective iff it equals n!.)

100 000-deck round trip (`p3roundtrip.c`, `p3/roundtrip.log`). The natural table decryptor lays the
output row-major and replays the walk, reading the card of each step from the target and applying the
same bump rule to its bookkeeping. It recovers **0 of 100 000** decks for each of 40–43. With ~25 bumps
per deck, some placed card is almost always pushed on later, so the card read at its target is the wrong
one. This only shows that the natural procedure fails; the collisions show that every procedure must fail.

### Can a small tweak fix it?

Not with any tweak I found. Tried: driving the next step by the occupant instead of the new card
(45); stepping from the occupant's new seat (42, 43, 46); and taking the occupant off the table onto a
side pile that fills the gaps at the end (47, 48). All are non-injective on every small grid. The root
cause is the one in the argument: a card that has already steered the walk can be moved later, and the
final layout does not say whether it was. Any bump rule in this walk family would have to record the
arrival order somewhere outside the card layout (a mark, an extra pile that the output also carries, …).
That is a new gesture and a change to what GridCycle outputs, not a small tweak, so it was not pursued.
Removing K♣'s zero step is not enough either (see above).

## Step 2: measurements

Not applicable: no invertible bump variant. Hand-cost figures for the bump variants are given only for
completeness (`p3/roundtrip.log`).

| rank | candidate | invertible | worst pair [95% CI] | pairs > 1/64 | worst 3-cycle | worst full round | seats checked per blocked placement (mean / p90 / max) | extra mental work |
|---|---|---|---|---|---|---|---|---|
| **1** | **rule 1: ghost finger + blocker sends you** (PHASE2 #1) | yes (argument + 100k round trip) | **0.0062** [0.0059, 0.0066] | 0 | ≤ 2.4e-4 | 1.0e-4 | 7.0 / 20 / 52 | read blocker; row +suit, column +rank |
| 2 | rule 2: ghost finger + blocker picks the row (PHASE2 #2) | yes | 0.0119 [0.0114, 0.0124] | 0 | ≤ 8.6e-4 | 1.6e-4 | 7.0 / 19 / 52 | read blocker; row +suit |
| ref | v10 | yes | 0.262 [0.260, 0.264] | 1311 | 0.086 | 1.4e-3 | 6.05 / 15 / 52 | none |
| – | (a) bump + v10 scan (= (b) bump + ghost) | **no** (witness; 19% of decks collide with a one-swap neighbour) | – | – | – | – | 6.05 per bump, 25.5 bumps/deck; plus a lift and move | lift, place, move |
| – | (c) bump, occupant sends itself (with/without ghost: same map) | **no** (witness; 24%) | – | – | – | – | 6.9 per bump, 25.5 bumps/deck | read occupant, row +suit, column +rank, lift, move |
| – | (d) bump, follow the bumped card (42 / 43) | **no** (witness; 0.8% / 2.2%) | – | – | – | – | 4.7 / 4.8 per bump, 32 bumps/deck | as (a)/(c) |
| – | tweaks 45, 46, side pile 47/48 | **no** (small-grid collisions) | – | – | – | – | – | – |

## Table walkthrough of the best-feeling bump rule, (c), and where decryption breaks

For the record, since Zachary asked how it would play:

1. As in v10: clear the table, marker chip on ♣, first card at row 2, column 0, finger there.
2. Step from your finger by the card you just placed (down by suit, right by rank) to the target.
3. If the target is empty, place the card there.
4. If it is taken: lift the card that is there (the occupant) and put the new card on the target. The
   occupant goes to the first empty seat to the right in row (marker + occupant's suit), starting at
   the target's column + occupant's rank. Move the marker on one suit.
5. Your finger is on the target, now holding the new card; step from there with the new card.

**Decryption would have to** lay the packet out, start at row 2, column 0 and follow the steps. At step 2,
though, the card lying on the target may not be the one that was placed there at that moment: it can be
a later card that bumped it. The walkthrough above (deck A vs deck B) is a real case where both histories
give the identical table. There is no way to tell them apart, so the rule cannot be adopted as a
GridCycle layer.

## Recommendation (proposal; Zachary decides)

Keep "bump the occupant" parked: it is not decryptable, and that is structural, not a detail of the
overflow scan. If the lift-and-place feel is what appeals, Phase-2 rule 1 keeps the same "the card in
the way decides" spirit. The blocker's suit and rank send the new card instead of moving the old one,
so every placed card stays put and decryption stays a plain replay. It is also the strongest measured
candidate (worst pair 1/161).

## Files (Phase 3)

| file | what |
|---|---|
| `p3bump.h` | 52-card bump variants 40–43 (C) |
| `p3collide.c` → `p3/collide_*.log` | explicit collisions (single swaps) and rates |
| `p3trace.py` → `p3/trace.log` | independent Python implementation; verifies the four witnesses; traces one |
| `p3small.c` → `p3/small_injectivity.log` | exhaustive injectivity on small grids, incl. tweaks 45–48, v10 and rule 1 as controls |
| `p3roundtrip.c` → `p3/roundtrip.log` | 100k round trip with the natural decryptor; bump counts and scan cost |
| `run_phase3.sh` | reproduces all of the above (not CI; about a minute) |
