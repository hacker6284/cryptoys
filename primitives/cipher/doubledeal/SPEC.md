# DoubleDeal

> **v11 is superseded** and frozen at `v11/SPEC.md` + `v11/doubledeal_v11.sudo`. It is **not attacked**. The finding is a related-key property of the PassKey \(F\) (§3.7): its suit cut and rank cut add, so the 68 swaps of two cards with equal suit + rank commute with one pass of \(F\) with probability ≥ 196/221 ≈ 0.887 for the worst pairs (closed-form lower bound, and tight; measured values in `proofs/doubledeal/analysis/passkey-related-key/README.md` §2), and about 48% of keys \(K\) give six round keys related to those of \(\tau K\) by exactly \(\tau\) (2♥↔A♠, measured). On the full 6-round cipher, 10M related-key samples showed no effect (0 hits). It is not a single-key or related-plaintext attack. Write-up: `proofs/deprecated/doubledeal-v11/`; analysis: `proofs/doubledeal/analysis/passkey-related-key/`. v12 (below) replaces the part of \(F\) that caused it.

**This is DoubleDeal v12.** One change from v11: the PassKey step \(F\) (§3.7, §4.6). The suit rotation of the hand is replaced by a **deal**: after the controller \(C\) is popped, deal \(\mathrm{suit}(C)+2\) cards one at a time off the top of the hand (so they come out reversed) and put that packet under the hand, if \(\mathrm{suit}(C)+2\) is less than the hand size; otherwise do the same on the key pile, if \(\mathrm{suit}(C)+2\) is less than the key-pile size; otherwise skip. The rank cut with key-pile fallback and "controller on top of the key pile" are unchanged. The suit step and the rank step no longer add, so the v11 suit + rank collision is gone: no two cards ever make the same move at the same step. Toy evidence only (`proofs/doubledeal/analysis/passkey-related-key/` §9): measured worst single-swap pass-through of one \(F\) ≈ 0.00198 ≈ 1/506 (2♣↔A♥; v11: ≥ 196/221 ≈ 0.887 for its worst pairs, closed-form lower bound), no swap above 1/64, and 0 of 200k keys with six related round keys for the worst pair. GridCycle, SumRanks, ShiftRows, Compose, the round count and the modes are unchanged from v11. These are measurements, not a security claim.

v11 (superseded, frozen) made one change from v10, kept in v12: GridCycle (§3.5, §4.4). The walk's finger is now a *ghost*: each step starts from the previous **target** seat, even when the card had to sit elsewhere. A free target is handled exactly as in v10. A target that is already taken is resolved by the card sitting on it (the *blocker*): scan the row marker + blocker's suit, starting at the target column + blocker's rank, for the first empty seat to the right (dropping to the next row if that row is full); advance the marker one suit; and the next step starts from the target moved by the blocker's step. SumRanks, ShiftRows, Compose, PassKey, the round count and the modes were unchanged in v11. The rule was chosen from the measurements in `proofs/doubledeal/analysis/v10-gridcycle/` (PHASE2 "rule 1" plus PHASE6 "tweak B"; toy evidence, not a proof).

v10 is deprecated and frozen at `v10/SPEC.md` + `v10/doubledeal_v10.sudo`. The reason is a per-layer parity shortfall in GridCycle, not a working attack on the full cipher: v10 GridCycle lets its worst swap, K♣↔K♦, through unchanged with probability 0.262 (measured), and 1311 of the 1326 swaps are above the 1/64 bar that SumRanks meets, while the 6-round product-formula estimate for the worst swap trail stays about \(2\times10^{-17}\). Write-up and kernel-checked single-deck witness: `proofs/deprecated/doubledeal-v10/`. v9 is deprecated and frozen at `v9/SPEC.md` + `v9/doubledeal_v9.sudo`; a related-plaintext distinguisher breaks the full 6-round v9 (K♣↔Q♥ at about \(3.5\times10^{-8}\) per pair; `proofs/deprecated/doubledeal-v9/`). v8 is deprecated too, frozen at `v8/SPEC.md`, with its vulnerability proof in `proofs/deprecated/doubledeal-v8/`. Formerly TwoDeck (TDSPN elegant-v8).

This document is the normative specification. `doubledeal.sudo` is the conformance implementation, and a mismatch is a bug in the implementation. DoubleDeal is a toy block cipher on a 52-card deck, AES in spirit and not in security. It makes no cryptographic security claim and is not for protecting anything. The v10 SumRanks (kept in v11 and v12) was chosen from the candidate measurements in `proofs/doubledeal/analysis/v10-sumranks/`, the v11 GridCycle (kept in v12) from `proofs/doubledeal/analysis/v10-gridcycle/`, and the v12 PassKey deal from `proofs/doubledeal/analysis/passkey-related-key/` (toy evidence, not proofs).

The demo at `demos/doubledeal/` plays `trace_encrypt` and `trace_decrypt`. It does not contain a second copy of the rounds. `decrypt` may keep the round-key list from `expand_keys`. The decrypt trace does not: it passes the master key forward 6 times to \(K_6\), then un-passes once per remaining round back to \(K_0\). Ciphertext is the same either way; only the key-derivation choreography differs.

---

# 1. Scope and non-goals

## In scope

- A single-block SPN on permutations of a 52-card CHaSeD deck.
- Unkeyed layers: **SumRanks** (SubBytes stand-in), **ShiftRows**, **GridCycle** (MixColumns stand-in).
- Keyed layer: **Compose** (AddRoundKey stand-in), using a 52-card round key as core.
- **AES role map.** No layer changes a card's face; every layer only moves cards between seats, so "nonlinear" means "the move depends on the cards", not an S-box table.

  | Layer | AES role | What it does |
  | --- | --- | --- |
  | SumRanks | SubBytes | The data-dependent, nonlinear step. Rows read ranks with position weights; columns read suits as GF(4) elements with position weights. Each step is chained to its neighbour. |
  | ShiftRows | ShiftRows | Fixed row rotations 0, 1, 2, 3. |
  | GridCycle | MixColumns | Diffusion: each card's suit and rank steer where the next card lands. |
  | Compose | AddRoundKey | Moves seats by the round key. |

- Key schedule: **PassKey** — forward iteration \(K_r = F(K_{r-1})\) with \(F =\) `pass_to_key_cut_fallback`.
- Round count \(N_r = 6\): whitening with \(K_0\), five full rounds with \(K_1,\ldots,K_5\), final round with \(K_6\) (no MixColumns).
- Modes: **ECB**, **CTR**, and **CBC**. CTR counter encoding is pinned: Diamonds in seats 39–51 via factoradic; Clubs+Hearts+Spades in seats 0–38 as nonce. CBC is byte-domain on the §5.3 28-byte encoding (§5.4).
- Authenticated encryption: **DoubleDeal-CBC-HMAC** — CBC, then Encrypt-then-MAC with HMAC-MegaDreifach. Normative AEAD rules live in `primitives/aead/doubledeal-cbc-hmac/SPEC.md`.
- A byte encoding outside `encrypt` / `decrypt` (§5.3). It is not a second block size. One block is still one deck.

## Non-goals

- No claim of AES-class security, MDS MixColumns, or cryptographically strong key schedule.
- No CFB / OFB. DoubleDeal-SCM / SMAC stay later; they are not this CBC-HMAC product.
- No jokers (unlike the older 54-card Solitaire-style schedule).
- GridCycle is **not** MDS; SumRanks is **not** an AES S-box / \(\mathrm{GF}(2^8)\) inverse.
- Hand/math “refinement” obligations are agenda items, not proved here.
- No AES-style 16-byte blocks. One block is one deck, about 28 bytes of injective message capacity.
- No base-52 strings that allow duplicate card ids as plaintext blocks.
- No claim that a 28-byte chunk carries the full entropy of \(S_{52}\). \(2^{224} < 52!\), so some decks have no 28-byte form. The 29-byte form covers every deck.

---

# 2. Objects and indexing

## Domains

Let \(\mathrm{Fin}\,52 = \{0,1,\ldots,51\}\).

- A **deck** is a list \(D = (D[0],\ldots,D[51])\) with \(\{D[i]\} = \mathrm{Fin}\,52\) (a permutation of card ids).
- **Top** = index \(0\); **bottom** = index \(51\).
- Message \(M\) and master key \(K_0\) are both decks (52 cards, no jokers).

## CHaSeD card ids

| Suit | Indices | Suit code |
|------|---------|-----------|
| Clubs ♣ | \(0..12\) | \(0\) |
| Hearts ♥ | \(13..25\) | \(1\) |
| Spades ♠ | \(26..38\) | \(2\) |
| Diamonds ♦ | \(39..51\) | \(3\) |

Within each suit, Ace‥King occupy the 13 consecutive ids.

\[
\begin{aligned}
\mathrm{suit}(c) &= \lfloor c/13\rfloor \in \{0,1,2,3\}, \\
\mathrm{rank}(c) &= (c \bmod 13) + 1 \in \{1,\ldots,13\}
\quad\text{(A=1, …, 10=10, J=11, Q=12, K=13)}.
\end{aligned}
\]

Names: rank char `A23456789TJQK` + suit `CHSD` (e.g. `AC=0`, `AS=26`, `AD=39`, `KD=51`).

## Grid

- Table size: \(4 \times 13\) (rows \(\times\) columns).
- Row indices \(0..3\); column indices \(0..12\).
- **GridCycle start seat:** \((r,c) = (2,0)\) (Ace-of-Spades home seat, positional — not “find the AS card”).
- **Overflow suit order (CHaSeD):** \(\mathtt{CHASED} = (0,1,2,3)\) = ♣→♥→♠→♦.

## Parameters

\[
N_r = 6,\qquad \mathrm{SHIFT} = (0,1,2,3).
\]

---

# 3. Mathematical definitions (formal)

Notation: decks are 0-indexed lists. Grid cells hold card ids. All modular arithmetic on row/column indices uses moduli \(4\) and \(13\) respectively.

### Bijectivity summary (status)

| Map | Bijective on decks / grids? | Claim status |
|-----|------------------------------|--------------|
| `lay_column_major` / `scoop_column_major` | Yes (inverses) | Claimed; property-tested |
| `lay_row_major` / `scoop_row_major` | Yes (inverses) | Claimed; property-tested |
| SumRanks / inv SumRanks | Yes (on \(4\times13\) filled grids) | Claimed; RT in self_test |
| ShiftRows / inv ShiftRows | Yes | Claimed |
| GridCycle / inv GridCycle | Yes (as packet maps) | Proved in `proofs/doubledeal/` (`invMixColumns_mixColumns` / `mixColumns_invMixColumns`, both on every packet); RT also in self_test |
| Compose / InverseCompose (fixed \(K\)) | Yes | Claimed |
| Full / final round (fixed round key) | Yes | Claimed via layer RT |
| Encrypt / Decrypt (fixed \(K_0\)) | Yes | Claimed; RT in self_test |
| PassKey \(F\) / \(F^{-1}\) | Yes (on \(S_{52}\)) | Proved in `proofs/doubledeal/` (`passKey_leftInverse` / `passKey_rightInverse`); cycle structure still evidence only |

---

## 3.1 Lay / scoop — column-major

Used for the SumRanks + ShiftRows table.

\[
\begin{aligned}
\mathrm{lay}_{\mathrm{cm}}(D)[\,k\bmod 4,\; \lfloor k/4\rfloor\,] &= D[k],
\quad k=0..51, \\
\mathrm{scoop}_{\mathrm{cm}}(G) &= \bigl(G[0,0],G[1,0],G[2,0],G[3,0],\;
G[0,1],\ldots,G[3,12]\bigr).
\end{aligned}
\]

Equivalently: fill / read **column 0 top→bottom**, then column 1, …, column 12.

**Claim:** \(\mathrm{scoop}_{\mathrm{cm}} \circ \mathrm{lay}_{\mathrm{cm}} = \mathrm{id}\) on decks; \(\mathrm{lay}_{\mathrm{cm}} \circ \mathrm{scoop}_{\mathrm{cm}} = \mathrm{id}\) on filled grids.

## 3.2 Lay / scoop — row-major

Used for GridCycle **output** scoop and GridCycle **inverse** lay.

\[
\begin{aligned}
\mathrm{lay}_{\mathrm{rm}}(D)[i] &= D[13i \,{:}\, 13(i+1)],
\quad i=0..3, \\
\mathrm{scoop}_{\mathrm{rm}}(G) &= G[0]\mathbin{+\mskip-4mu+} G[1]\mathbin{+\mskip-4mu+} G[2]\mathbin{+\mskip-4mu+} G[3]
\quad\text{(row 0 left→right, then row 1, …)}.
\end{aligned}
\]

**Claim:** mutual inverses on decks / filled grids.

## 3.3 SumRanks and inverse

Operate on a filled \(4\times13\) grid \(G\). SumRanks reads each card twice: its rank (rows) and its suit (columns). Both stages are **chained**. Each row or column turns by an amount read from a *neighbouring* row or column, as that neighbour is at the moment. So every turn can be undone as long as the neighbour is put back first.

**Row weight.** For a row \(x = (x_0,\ldots,x_{12})\),

\[
U(x) = \sum_{j=0}^{12} (13-j)\,\mathrm{rank}(x_j),
\qquad
\mathrm{turn}(x) = U(x) \bmod 13 .
\]

The leftmost card has weight \(13 \equiv 0\) and the rightmost has weight 1. By hand, keep two running totals left to right: \(T \mathrel{+}= \mathrm{rank}(x_j)\), then \(U \mathrel{+}= T\) (§4.2).

**Row stage (forward).** For \(i = 1, 2, 3, 0\) in that order, left rotate row \(i\) by \(\mathrm{turn}(G[i-1 \bmod 4])\), reading row \(i-1\) as it is at that moment. Row 0 therefore reads row 3 after row 3 has turned.

**Suits as GF(4).** Label ♣ = 0, ♦ = 1, ♥ = \(w\), ♠ = \(w^2\), written as the two-bit numbers 0, 1, 2, 3, with \(w^2 = w + 1\). Addition \(\oplus\) is XOR of the two bits: a pair cancels, ♣ changes nothing, and two different non-club suits make the third. Multiplying by \(w\) maps ♦ → ♥ → ♠ → ♦ and fixes ♣. Write \(\ell(c)\) for the label of card \(c\)'s suit.

**Column stage (forward).** For a column \(y = (y_0, y_1, y_2, y_3)\), top to bottom:

\[
V(y) = 0\cdot\ell(y_0) \oplus 1\cdot\ell(y_1) \oplus w\,\ell(y_2) \oplus w^2\,\ell(y_3),
\qquad
S(y) = \ell(y_0) \oplus \ell(y_1) \oplus \ell(y_2) \oplus \ell(y_3).
\]

For \(j = 1, 2, \ldots, 12, 0\) in that order, rotate column \(j\) top→bottom (\(\mathrm{new}[i] = \mathrm{col}[(i-s_j) \bmod 4]\)) by

\[
s_j = V\bigl(G[\cdot, j-1 \bmod 13]\bigr) \oplus S\bigl(G[\cdot, j]\bigr) \in \{0,1,2,3\},
\]

reading column \(j-1\) as it is at that moment (column 0 reads column 12 after it has turned). The four weights \(0, 1, w, w^2\) are distinct, so swapping two different suits inside a column always changes \(V\). \(S\) gives the top card, which has weight 0 in \(V\), a say. \(S\) does not change when column \(j\) itself rotates.

Then \(\mathrm{SumRanks}(G)\) is the resulting grid. **Order:** all rows, then all columns.

**Inverse.** Undo the stages in reverse, each in reverse order:

1. For \(j = 0, 12, 11, \ldots, 1\): recompute \(s_j\) from column \(j-1\) (still as the forward pass left it) and column \(j\)'s own \(S\) (unchanged by its rotation). Rotate column \(j\) bottom→top by \(s_j\): \(\mathrm{new}[i] = \mathrm{col}[(i+s_j) \bmod 4]\).
2. For \(i = 0, 3, 2, 1\): recompute \(\mathrm{turn}(G[i-1 \bmod 4])\) and right rotate row \(i\) by it.

This works because when a row or column is undone, the neighbour it reads is exactly as it was when that row or column turned forward: later in the forward order means earlier in the inverse order.

**Claim:** \(\mathrm{invSumRanks} \circ \mathrm{SumRanks} = \mathrm{id}\) on filled grids. Not an involution; order matters.

## 3.4 ShiftRows and inverse

With \(\mathrm{SHIFT}=(0,1,2,3)\):

\[
\mathrm{ShiftRows}(G)[i] = G[i][s_i{:}] + G[i][{:}s_i],
\quad s_i = \mathrm{SHIFT}[i]\bmod 13
\quad\text{(left by \(s_i\))}.
\]

Inverse: right by \(s_i\).

**Claim:** bijection; involution only for the zero-shift row.

## 3.5 GridCycle (MixColumns stand-in)

Maps a **packet** (deck) to a packet. Walk places cards onto an empty \(4\times13\) grid; scoop is **row-major**.

**Step** from seat \((r,c)\) using card \(x\):

\[
\mathrm{step}(x,(r,c)) = \bigl((r + \mathrm{suit}(x))\bmod 4,\;
(c + \mathrm{rank}(x))\bmod 13\bigr).
\]

**Ghost finger (v11).** The walk keeps a *finger* seat \(f\), separate from where cards land. The next target is \(\mathrm{step}(\text{previous card}, f)\). After a free target the finger moves to that target (where the card now sits, as in v10). After a blocked target the finger does **not** follow the card; it moves to the target shifted by the blocker's step (below).

**Blocked placement (v11).** State \(t \in \{0,1,2,3\}\) (the marker), initially \(0\). If the target \(T=(r^\ast, c^\ast)\) is already taken, let \(b\) be the card on \(T\) (the *blocker*). Scan row \((t + \mathrm{suit}(b)) \bmod 4\) from column \((c^\ast + \mathrm{rank}(b)) \bmod 13\) rightward with wrap for the first empty seat; if that whole row is full, drop to the next row (\(+1 \bmod 4\)) and scan it from the same column. Then \(t \leftarrow (t+1) \bmod 4\) (once per blocked placement, however many rows were dropped) and \(f \leftarrow \mathrm{step}(b, T)\).

```
overflow_seat(occupied, row, start):
  repeat up to 4 times:
    for k in 0..12:
      col ← (start + k) mod 13
      if not occupied(row, col):
        return (row, col)
    row ← (row + 1) mod 4
  fail  # unreachable on a 52-seat grid with <52 occupied
```

Why: in v10 the finger followed the card, so a swapped pair of cards often rejoined the same walk (K♣↔K♦ passed unchanged at 0.262 per layer). With the ghost finger the two walks' fingers differ by \(\mathrm{step}(a) - \mathrm{step}(b)\), which is never zero for distinct cards, and the blocker makes the overflow seat depend on card values, not just occupancy. The blocker's nudge of the finger makes the path depend on order. The inverse can repeat all of it: \(T\) is already visited in its table, so it can read the blocker.

**Forward** `mix_columns(D)`:

```
grid ← empty 4×13
t ← 0
for i, card in enumerate(D):
  if i = 0:
    pos ← AS_START = (2, 0); f ← pos
  else:
    T ← step(prev_card, f)
    if grid[T] is empty:
      pos ← T; f ← T
    else:
      b ← grid[T]
      pos ← overflow_seat(λ(r,c). grid[r,c] occupied,
                          (t + suit(b)) mod 4, (T.col + rank(b)) mod 13)
      t ← (t + 1) mod 4
      f ← step(b, T)
  place card at pos
  prev_card ← card
return scoop_row_major(grid)
```

**Inverse outline** `inv_mix_columns(D)`:

```
grid ← lay_row_major(D)      # recover placement
visited ← all false
t ← 0; f ← AS_START; hand ← []
for i in 0..51:
  choose pos (and update t, f) by the same AS_START / ghost-finger / blocker rule,
    treating “occupied” as “visited”; a visited target's blocker is grid[T]
  append grid[pos] to hand; mark visited[pos]
return hand
```

**Proved** (Lean, `proofs/doubledeal/`): \(\mathrm{invMix} \circ \mathrm{Mix} = \mathrm{id}\) and \(\mathrm{Mix} \circ \mathrm{invMix} = \mathrm{id}\) on every 52-entry packet (`invMixColumns_mixColumns`, `mixColumns_invMixColumns`), in particular on decks. Not MDS; toy diffusion only.

## 3.6 Compose / InverseCompose

Let \(K\) be a 52-card deck (no jokers; \(K\) *is* the core). Let \(\mathrm{pos}_K(c)\) be the unique index \(i\) with \(K[i]=c\).

Reference order is CHaSeD ids \(j \in 0..51\):

\[
\begin{aligned}
\mathrm{Compose}(M,K)[j] &= M\bigl[\mathrm{pos}_K(j)\bigr], \\
\mathrm{InverseCompose}(C,K)\bigl[\mathrm{pos}_K(j)\bigr] &= C[j].
\end{aligned}
\]

Equivalently: \(\mathrm{Compose}(M,K) = \bigl(M[\mathrm{pos}_K(0)],\ldots,M[\mathrm{pos}_K(51)]\bigr)\).

**Claim:** for fixed \(K\), Compose is a bijection on decks; InverseCompose is its inverse. (Only keyed step per round.)

## 3.7 PassKey \(F\)

\(F =\) `pass_to_key_cut_fallback`. Round-index-free. Content-preserving: output is a permutation of the same 52 ids.

```
F(deck):
  hand ← copy(deck); key ← []
  while hand nonempty:
    C ← pop front of hand
    d ← suit(C) + 2                         # 2..5
    # deal only if d < len(packet); NO mod wrap
    if d < len(hand):
      hand ← deal_under(hand, d)            # deal hand
    else if d < len(key):
      key ← deal_under(key, d)              # deal key pile
    else:
      skip deal
    # proper cut only if rank < len(packet); NO mod wrap
    if hand nonempty and rank(C) < len(hand):
      hand ← left_rotate(hand, rank(C))     # cut hand
    else if key nonempty and rank(C) < len(key):
      key ← left_rotate(key, rank(C))       # cut key pile
    else:
      skip cut
    insert C at front of key                # key[0] ← C
  return key                                # key[0] = last controller dealt
```

**Deal under / undeal.** `deal_under(xs, d)` deals the top \(d\) cards one at a time onto a new packet, so the packet is those cards reversed, and puts the packet under the rest: \(\mathrm{deal\_under}(xs,d) = xs[d{:}] \mathbin{+\!\!+} \mathrm{reverse}(xs[{:}d])\). `undeal_under(xs, d)` takes the bottom \(d\) cards and deals them back onto the top one at a time: \(\mathrm{reverse}(xs[n-d{:}]) \mathbin{+\!\!+} xs[{:}n-d]\) with \(n = \mathrm{len}(xs)\). They are inverses for \(d \le n\). In a 52-card pass the "skip deal" branch never happens (\(d \ge\) hand size means hand \(\le 4\), so the key pile has \(\ge 47 > 5\) cards); it is written so the rule is total on any pile sizes. At the last step (empty hand) the controller deals from the key pile.

**Left rotate / right rotate.** Top = index \(0\). Left rotate by \(k\) moves the top \(k\) cards to the bottom. Right rotate by \(k\) moves the bottom \(k\) cards to the top. They are inverses (empty list and \(k=0\) are fixed).

```
F^{-1}(deck):
  key ← copy(deck); hand ← []
  while key nonempty:
    C ← pop front of key
    n ← len(hand)                 # hand size just after C was popped in F
    if n > 0 and rank(C) < n:
      hand ← right_rotate(hand, rank(C))
    else if key nonempty and rank(C) < len(key):
      key ← right_rotate(key, rank(C))
    else:
      skip cut
    d ← suit(C) + 2
    if d < n:
      hand ← undeal_under(hand, d)
    else if d < len(key):
      key ← undeal_under(key, d)
    else:
      skip deal
    insert C at front of hand
  return hand
```

**Claim:** \(F\) is a bijection on \(S_{52}\). \(F^{-1}\circ F=\mathrm{id}\) and \(F\circ F^{-1}=\mathrm{id}\). Deterministic; preserves the card multiset.

**Why:** at step \(i\) the controller \(C\) is on top of the key pile, so the inverse can read it. Every branch (deal: hand / key pile / skip; cut: hand / key pile / skip) depends only on \(C\) and the pile sizes (hand \(=51-i\) after the pop, key \(=i\)), never on hidden card identities, and neither the deal nor the cut changes a pile's size. The inverse undoes the cut first, then the deal. Each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. Lean: `proofs/doubledeal/lean/DoubleDeal/PassKey.lean`, theorems `passKey_leftInverse` and `passKey_rightInverse` (on `main` via PR #2). Cycle structure / orbit lengths of \(F\) on \(S_{52}\) are not claimed.

## 3.8 expand_keys

\[
\mathrm{expand\_keys}(K_0, N_r) = [K_0,K_1,\ldots,K_{N_r}],
\quad K_r = F(K_{r-1})\ \text{for}\ r=1..N_r,
\quad K_{r-1} = F^{-1}(K_r).
\]

The functions may keep the list. At the table, one key deck is enough: encrypt passes forward; decrypt passes forward to \(K_6\) and then un-passes (§4.8). Ciphertexts do not change.

## 3.9 Rounds, encrypt, decrypt

**Unkeyed stem** (full round, before Compose):

```
unkeyed_full(M):
  G ← lay_cm(M)
  G ← SumRanks(G)
  G ← ShiftRows(G)
  return MixColumns(scoop_cm(G))    # Mix scoops row-major internally
```

**Full round / inverse:**

```
full_round(M, K_r)      = Compose(unkeyed_full(M), K_r)
inv_full_round(C, K_r)  =
  M ← InverseCompose(C, K_r)
  M ← inv_MixColumns(M)             # recovers col-major-scooped packet
  G ← lay_cm(M)
  G ← inv_ShiftRows(G)
  G ← inv_SumRanks(G)
  return scoop_cm(G)
```

**Final round** (no MixColumns):

```
final_round(M, K_nr) =
  G ← lay_cm(M); G ← SumRanks(G); G ← ShiftRows(G)
  return Compose(scoop_cm(G), K_nr)

inv_final_round(C, K_nr) =
  M ← InverseCompose(C, K_nr)
  G ← lay_cm(M); G ← inv_ShiftRows(G); G ← inv_SumRanks(G)
  return scoop_cm(G)
```

**Encrypt / decrypt** (\(N_r=6\)):

```
encrypt(M, K_0):
  keys ← expand_keys(K_0, 6)
  M ← Compose(M, keys[0])                 # whitening
  for r in 1..5:
    M ← full_round(M, keys[r])
  return final_round(M, keys[6])

decrypt(C, K_0):
  keys ← expand_keys(K_0, 6)
  M ← inv_final_round(C, keys[6])
  for r in 5..1:
    M ← inv_full_round(M, keys[r])
  return InverseCompose(M, keys[0])
```

Same ciphertext, walking the one key deck (what `decrypt` and §4.8 do):

```
decrypt_walk(C, K_0):
  K ← K_0
  for r in 1..6:
    K ← F(K)                          # now K_6
  M ← inv_final_round(C, K)
  for r in 5..1:
    K ← F^{-1}(K)                     # K_r
    M ← inv_full_round(M, K)
  K ← F^{-1}(K)                       # K_0
  return InverseCompose(M, K)
```

**Claim:** \(\mathrm{decrypt}(\mathrm{encrypt}(M,K_0),K_0)=M\) for all valid decks (self_test; pressure harness). \(\mathrm{decrypt}=\mathrm{decrypt\_walk}\).

`expand_keys` is how the list form names \(K_0,\ldots,K_6\). At the table there is one key deck: whitening uses it as \(K_0\), and each PassKey turns that same deck into the next round key before the round that uses it (§4.7). Decrypt un-passes that deck from \(K_6\) back to \(K_0\) (§4.8). The round-key values, and therefore every ciphertext, are the same either way.

### Alternating majors (choreography invariant)

| Region | Lay | Scoop |
|--------|-----|-------|
| SumRanks + ShiftRows | column-major | column-major |
| GridCycle walk output | — (place by walk) | row-major |
| GridCycle inverse entry | row-major | — (read by walk) |

Deal col-major → SumRanks → ShiftRows → scoop col-major → GridCycle walk → scoop row-major → Compose → next round col-major again.

---

# 4. Hand instructions (stranger-playable)

Parallel to §3. Conventions match `PLAYER_SHEET_ELEGANT_V8.md`.

**Decks:** \(M\) = 52. \(K\) = 52 (no jokers). Top = face you deal first.  
**Ranks:** A=1 … 10=10, J=11, Q=12, K=13.  
**Suits (GridCycle / Compose / PassKey):** ♣=0 ♥=1 ♠=2 ♦=3. SumRanks columns use the GF(4) labels of §4.2 instead (♣=0 ♦=1 ♥=\(w\) ♠=\(w^2\)).

## 4.1 Deal / scoop conventions

- **Column-major deal:** fill column 0 top→bottom, then column 1, … column 12 (down the columns).
- **Column-major scoop:** reverse of that — gather column 0 top→bottom, then column 1, …
- **Row-major scoop:** across row 0 left→right, then row 1, … (GridCycle output only).
- **Row-major lay (decrypt GridCycle):** place the packet into the table in that same reading order.

Do **not** use the same cascade motion for col-major and row-major; the majors are part of the teaching story.

## 4.2 SumRanks (SubBytes)

On the column-major table. Rows first, then columns.

1. **Rows, in the order 1, 2, 3, 0** (top row is row 0). For row \(i\), read the row **above** it (row 0 reads row 3, which has already turned) left to right, keeping two running totals: add the card's rank to \(T\), then add \(T\) to \(U\). After 13 cards, rotate row \(i\) **left** by \(U \bmod 13\). You may reduce \(T\) and \(U\) mod 13 as you go. The first card read contributes \(13 \equiv 0\), so you can skip adding \(T\) to \(U\) on the first card.
2. **Columns, in the order 1, 2, …, 12, 0.** Suit labels: ♣ = 0, ♦ = 1, ♥ = \(w\), ♠ = \(w^2\). Card table:
   - Adding two labels: a **pair cancels** (♥ + ♥ = ♣), **♣ does nothing**, and **two different non-club suits make the third** (♦ + ♥ = ♠, ♥ + ♠ = ♦, ♠ + ♦ = ♥).
   - Multiplying by \(w\): **♦ → ♥ → ♠ → ♦**, and ♣ stays ♣. Multiplying by \(w^2\) is doing that twice.

   For column \(j\):
   - From the column to its **left** (column 0 reads column 12, which has already turned), take the row-1 suit as it is, the row-2 suit shifted once, and the row-3 suit shifted twice. Ignore the row-0 suit. Add the three.
   - Add the four suits of column \(j\) itself.
   - The result is ♣, ♦, ♥ or ♠. Rotate column \(j\) **top→bottom** by 0, 1, 2 or 3 respectively.

**Inverse:** columns first, in the order 0, 12, 11, …, 1. Each column reads the same neighbour and its own suits (unchanged by its own rotation) and rotates **bottom→top**. Then rows, in the order 0, 3, 2, 1, each reading the row above and rotating **right**. Enter and exit with the same column-major deal and scoop.

## 4.3 ShiftRows

- Row 0: no move (optional idle pulse so you notice it was considered).
- Row 1: move leftmost 1 card to the right end.
- Row 2: leftmost 2 → right end.
- Row 3: leftmost 3 → right end.

Then **scoop column-major** into a packet (full round continues to GridCycle; final round goes to Compose).

## 4.4 GridCycle (MixColumns)

1. Clear the 4×13 table. Keep an **overflow marker** chip that starts on ♣ and rotates ♣→♥→♠→♦→♣… when used.
2. Place the **first** hand card on the start seat **(row 2, column 0)**.
3. Keep a **finger** on the table. It starts on the start seat. For each next hand card, step from the **finger** using the card you just placed:  
   `new_row = (row + suit) mod 4`, `new_col = (col + rank) mod 13`. Call that seat the **target**.  
   - If the target is **empty**, place the card there and move the finger to it.  
   - If the target is **taken**, the card sitting there is the **blocker**. It sends you: go to the row named by the marker's suit plus the blocker's suit (mod 4), start at the target's column plus the blocker's rank (mod 13), and scan right (wrapping from column 12 back to column 0) for the first empty seat; place the card there. If that whole row is full, drop to the next row and scan it from the same column. Advance the marker one suit. The finger does **not** follow the card: move it from the target by the blocker's step (rows + blocker's suit, columns + blocker's rank, which is the column you just started the scan from).
4. Scoop **row-major** → packet.

*Example* (from `proofs/doubledeal/analysis/v10-gridcycle/PHASE6.md`; seats are r(row)c(col)). The finger is on r0c4 and you just placed 5♠: the target is r0c4 + 5♠ = r2c9, but J♠ sits there. J♠ sends the next card, 3♦, to row marker ♣ + ♠ = 2, scanning from column 9 + J = 7; r2c7 is empty, so 3♦ sits there. The marker moves ♣ → ♥. The finger moves from the target r2c9 by J♠'s step, rows + 2 (r2 → r0) and columns to 7, so it lands on r0c7, and the next card (Q♥) steps from there: r0c7 + 3♦ → r3c10.

**Inverse:** lay the packet **row-major**. Use visited markers, a finger and the marker chip. The start seat's card was first in the hand; tick it and put the finger there. Step from the finger with the card you just recovered. If the target is **not** ticked, its card is the next hand card; tick it and move the finger there. If the target is **already ticked**, a blocked placement happened here: read the blocker (the card on the target), run the same scan over **unticked** seats (row marker + blocker's suit, from target column + blocker's rank, dropping a row if full), take that seat's card as the next hand card and tick it, advance the marker, and move the finger to target + blocker's step. In the example, the decryptor finds r2c9 already ticked, reads J♠, scans row 2 from column 7 over unticked seats, gets r2c7 = 3♦, and moves the finger to r0c7.

## 4.5 Compose (AddRoundKey)

\(K\) is face-up as a 52-card reference. For each reference id \(j = 0..51\) in CHaSeD order (AC, 2C, …, KD): find where \(j\) sits in \(K\); take the card of \(M\) at that same seat; that is output position \(j\).

Practical table procedure: fan \(K\); build the output by reading \(M\) through \(K\)’s seat map. InverseCompose puts each output card back to the seat where its reference id sits in \(K\).

## 4.6 PassKey (between rounds)

No jokers. No round number. One full pass turns this round’s \(K\) into the next:

1. Hold \(K\) as a **hand** (top = face you deal first). Start an empty **key pile**.
2. For each controller **C** dealt from the hand:
   - Deal C (remove from top of hand).
   - **Deal** C’s **suit + 2** cards (♣=2 ♥=3 ♠=4 ♦=5), only if that count is **strictly less** than the packet size (do **not** wrap with mod):
     - If the count \(<\) hand size: deal that many cards one at a time off the top of the **hand** onto the table (so they reverse), then put that little packet **under** the hand.
     - Else if the count \(<\) key-pile size: do the same with the **key pile** (deal off its top, packet under it).
     - Else skip the deal (this cannot happen with 52 cards).
   - **Proper cut** only (count **strictly less** than packet size — do **not** wrap with mod):
     - If the hand still has cards and C’s **rank** \(<\) hand size: cut the **hand** by that rank.
     - Else if the key pile is nonempty and C’s rank \(<\) key-pile size: cut the **key pile** by that rank.
     - Else skip the cut.
   - Place C **on top** of the key pile.
3. When the hand is empty, the key pile **is** the next round key (its top is the last C you dealt).

On encrypt, do this once per step \(K_0 \to K_1 \to \cdots \to K_6\), on the same deck, after that deck has been used and before the next round. Whitening is the use that happens before the first pass.

**Un-pass** (\(F^{-1}\)). Start with the current round key as the **key pile** and an empty **hand**. Repeat 52 times:

1. Lift the top card **C** off the key pile.
2. Undo the cut: if the hand has cards and C’s rank \(<\) hand size, move that many cards from the **bottom** of the hand to the top; else if the key pile is nonempty and C’s rank \(<\) key-pile size, do the same on the key pile; else nothing.
3. Undo the deal: let \(d = \mathrm{suit}(C)+2\). If \(d <\) hand size, take the bottom \(d\) cards of the **hand** and deal them one at a time back onto its top (so they reverse again); else if \(d <\) key-pile size, do the same on the key pile; else nothing.
4. Put C on top of the hand.

When the key pile is empty, the hand is the previous round key. Forward “deal \(d\) under” moves the top \(d\) cards, reversed, to the bottom, so this undo deals the bottom \(d\) back onto the top. Decrypt uses un-pass (§4.8).

Near the end of a (forward) pass, emphasize **key-pile** deals and cuts — that fallback is intentional so short hands do not force silent no-ops.

## 4.7 Full encrypt walkthrough

**Given:** message deck \(M\), and one master key deck. That deck is \(K_0\). PassKey replaces it; there is not a second copy to set aside.

1. **Whitening.** Compose \(M\) with the key deck. Call the result \(M\). The key deck has not been passed yet.
2. **Full rounds \(r = 1..5\).** For each \(r\):
   1. PassKey the key deck once. It is now \(K_r\).
   2. Deal \(M\) **column-major** onto the 4×13 table.
   3. SumRanks (rows, then columns).
   4. ShiftRows.
   5. Scoop **column-major** → packet.
   6. GridCycle place; scoop **row-major** → packet.
   7. Compose with the key deck.
3. **Final round.** PassKey the key deck once. It is now \(K_6\). Deal column-major → SumRanks → ShiftRows → scoop column-major → Compose with the key deck. **Skip GridCycle.**
4. The message deck is the ciphertext \(C\).

Those decks are \(K_0,\ldots,K_6\) from `expand_keys`. Encrypt at the table never holds more than the one key deck.

## 4.8 Decrypt sketch

One key deck. Pass it forward to \(K_6\), then un-pass back. Ciphertext is the same as if you had kept every \(K_r\) from `expand_keys`.

1. Arrange the key deck as \(K_0\). PassKey **6** times. The deck is \(K_6\). InverseCompose the ciphertext with it; lay column-major; inverse ShiftRows; inverse SumRanks; scoop column-major.
2. For \(r = 5, 4, 3, 2, 1\): un-pass **once**. The deck is \(K_r\). InverseCompose with that deck; inverse GridCycle (row-major lay and walk); lay column-major; inverse ShiftRows; inverse SumRanks; scoop column-major.
3. Un-pass **once** more. The deck is \(K_0\). InverseCompose with it.

That is 6 forward passes and 6 un-passes: **12** passes on one deck. If a separate copy of the master key is kept, the last un-pass can be skipped (**11**).

Matching majors throughout: col-major around SumRanks+ShiftRows; row-major around GridCycle.

---

# 5. Modes

ECB and CTR stay deck-domain in `doubledeal.sudo`. CBC is byte-domain on the §5.3 encoding (§5.4). DoubleDeal-CBC-HMAC is the AEAD (§5.5). CFB / OFB / SCM / SMAC are not in this family.

## 5.1 ECB

\[
\mathrm{ECB\text{-}encrypt}([B_0,\ldots,B_{n-1}], K) = [\mathrm{encrypt}(B_i,K)]_{i=0}^{n-1}.
\]

Blocks are independent. **Teaching leak:** identical plaintext blocks → identical ciphertext blocks. Fine for unrelated single-block demos; bad for related / repeated decks.

## 5.2 CTR (pinned)

**Pin (headline):**

> **Diamonds = counter** (13 cards, seats 39–51).  
> **Clubs+Hearts+Spades = nonce** (39 cards, seats 0–38).

(The earlier Spades-middle sketch was superseded by Diamonds-at-end for CHaSeD fit. Rejected: LCG Fisher–Yates shuffle of all 52 for the counter block.)

### Counter encoding

Let \(\mathtt{DIAMOND\_CARDS} = [39..51]\) (AD‥KD), \(\mathtt{CHS\_CARDS} = [0..38]\). Let \(\mathrm{unrank}(S, i)\) be factoradic / Lehmer unranking of \(i \bmod |S|!\) over the ordered list \(S\):

```
unrank(items, rank):
  items ← copy(items); rank ← rank mod (|items|)!
  out ← []
  for k = |items| down to 1:
    f ← (k-1)!
    idx ← rank // f; rank ← rank % f
    out.append(items.pop(idx))
  return out
```

\[
\begin{aligned}
\mathrm{diamond\_perm}(i) &= \mathrm{unrank}(\mathtt{DIAMOND\_CARDS},\, i \bmod 13!), \\
\mathrm{nonce\_order} &= \text{a fixed 39-permutation of CHS for the session}, \\
\mathrm{counter\_deck}(\mathrm{nonce\_order},\, i)
  &= \mathrm{nonce\_order}\mathbin{+\mskip-4mu+}\mathrm{diamond\_perm}(i).
\end{aligned}
\]

So seats \(0..38\) hold the nonce order; seats \(39..51\) hold the diamond ordering for block index \(i\). Consecutive counters differ **only** on diamond seats (nonce never moves between blocks).

### Combine

\[
\begin{aligned}
S &= \mathrm{encrypt}(\mathrm{counter\_deck}(\mathrm{nonce\_order},\, i),\, K), \\
C &= \mathrm{Compose}(M,\, S), \\
M &= \mathrm{InverseCompose}(C,\, S).
\end{aligned}
\]

### Hand play of large \(i\)

Factoradic unranking of \(i\) among \(13! = 6{,}227{,}020{,}800\) orderings is awkward by hand. Allowed teaching alternatives:

1. **Software-aided:** compute \(\mathrm{diamond\_perm}(i)\) once, then place diamonds into seats 39–51.
2. **Published list:** advance to the “next diamond ordering” from a printed fragment of the factoradic table (or any agreed enumeration of \(S_{13}\) on AD‥KD).
3. Session rule: fix CHS nonce by one shuffle; only reorder the 13 diamonds between blocks.

### Nonce-reuse warning

Under \(\mathrm{Compose}(M,S)[j] = M[S.\mathrm{index}(j)]\), known plaintext \((M_1,C_1)\) recovers \(S\) uniquely when the same \((\mathrm{nonce\_order}, i)\) is reused: \(S.\mathrm{index}(j) = M_1.\mathrm{index}(C_1[j])\). Then \(M_2 = \mathrm{InverseCompose}(C_2,S)\). **Classic CTR failure.** Require unique \((\mathrm{nonce\_order}, i)\) per block under a key.

## 5.3 Bytes ↔ deck

The cipher domain is a deck: a permutation of the fixed CHaSeD order \(S_0 = [0, 1, \ldots, 51]\). Bytes are an encoding layer outside `encrypt` / `decrypt`. A key is still a deck. This section does not encode keys or nonces.

The digit convention is the §5.2 loop. At size \(k\), the digit is \(d = n \mathbin{//} (k-1)!\), and that digit picks the remaining item at index \(d\). `unrank(S_0, n)` and `rank(S_0, π)` are mutual inverses between \(\{0, \ldots, 52! - 1\}\) and the permutations of \(S_0\). Unlike the counter unrank, these two do not reduce \(n\) modulo \(52!\). An integer outside that range is rejected.

\(52! \approx 2^{225.58}\).

### A. Wire format (52 bytes)

A deck may be written as 52 bytes \(b_0, \ldots, b_{51}\) with \(b_j \in \{0, \ldots, 51\}\) equal to the card id in seat \(j\). It is valid exactly when \(\{b_j\} = \{0, \ldots, 51\}\). This form is for vectors and for handing someone a deck. It is not compact.

### B. Factoradic message encoding

| Direction | Rule |
| --- | --- |
| 28-byte message → deck | Read the bytes as a big-endian integer \(n\). Require \(0 \le n < 2^{224} < 52!\). The deck is \(\pi = \mathrm{unrank}(S_0, n)\). |
| Deck → 28-byte message | \(n = \mathrm{rank}(S_0, \pi)\). Require \(n < 2^{224}\), and write \(n\) as 28 big-endian bytes. If \(n \ge 2^{224}\), reject this form and use the 29-byte form. |
| Full range (29 bytes) | Any deck: \(n = \mathrm{rank}(S_0, \pi)\) as 29 big-endian bytes, zero-padded on the left. Decode parses 29 bytes to \(n\), requires \(n < 52!\), then `unrank(S_0, n)`. |

**ECB byte streams.** Split the plaintext into 28-byte blocks. Pad by appending the byte `0x80`, then appending `0x00` until the length is a multiple of 28. A plaintext whose length is already a multiple of 28 gains one whole extra block (`0x80` followed by 27 zero bytes). Each block is unranked, encrypted, and ranked back out as a 29-byte ciphertext block, so every ciphertext deck round-trips. Decrypt reverses that: 29 bytes to a deck, decrypt, rank to 28 bytes, then strip the pad. Stripping requires the recovered bytes to end in `0x80` followed only by `0x00`, and removes that suffix. Any other ending is rejected.

**CTR byte payloads.** Build \(S = \mathrm{encrypt}(\mathrm{counter\_deck}(\mathrm{nonce\_order}, i), K)\) as in §5.2. Map each padded 28-byte plaintext block to a deck \(M\) by unrank. \(C = \mathrm{Compose}(M, S)\). Emit \(C\) as 29 bytes, or as the 52-byte wire form. The same \((\mathrm{nonce\_order}, i)\) uniqueness rule applies.

### C. What this encoding is not

Twenty-eight bytes is not “the whole of \(S_{52}\)”. \(2^{224} < 52!\) leaves decks that only the 29-byte form can name. Use the 29-byte form whenever every deck must be representable. Ciphertext does.

`52!` does not fit in a sudocode `int`, and `std.bigint` cannot cross a module boundary, so this encoding is not in `doubledeal.sudo`. The loop above is the one in §5.2. `demos/doubledeal/cards.js` is the software copy for 52-card ranks. The rounds stay in `doubledeal.sudo`.

## 5.4 CBC (byte domain)

AES-spirit CBC: XOR in the 28-byte message encoding, then `unrank` → `encrypt` → 29-byte rank. Compose-CBC on decks is not this mode. IV is 28 bytes and must be unique under the encryption key. The next chaining value is the last 28 bytes of the previous 29-byte ranked ciphertext (drop the most-significant byte). Pad is the same `0x80` / `0x00` rule as ECB.

Full rules, IV misuse, and the rank-truncation honesty note are in `primitives/aead/doubledeal-cbc-hmac/SPEC.md` §3.

## 5.5 DoubleDeal-CBC-HMAC

CBC, then Encrypt-then-MAC. The MAC is HMAC with MegaDreifach as the hash (\(B=28\), tag = 29-byte digest). The master secret is split into an encryption deck and an HMAC key; they are not the same bytes. AAD is in the MAC, length-delimited. Decrypt verifies the tag before releasing plaintext.

Normative specification: `primitives/aead/doubledeal-cbc-hmac/SPEC.md`. Conformance sudo: `doubledeal_cbc_hmac.sudo`. This is not DoubleDeal-SCM.

---

# 6. Formal verification and analysis agenda (“stones”)

Prioritized backlog. Tags: **Lean** (machine-checked proof), **property-test** (randomized RT / invariants), **cryptanalysis script** (toy search / stats), **TLA** (temporal / mode protocol). Mark **proof** vs **evidence**.

| # | Stone | Priority | Effort tag | Proof / evidence | Notes |
|---|-------|----------|------------|------------------|-------|
| S1 | Layer bijections: lay/scoop cm & rm; SumRanks; ShiftRows; GridCycle; Compose | P0 | Lean + property-test | **Proof** target (Lean); evidence already in `self_test` | Port from existing Lean Compose / Basic patterns |
| S2 | Round-trip: `inv_full_round ∘ full_round`, `inv_final ∘ final`, `decrypt ∘ encrypt` | P0 | Lean + property-test | **Proof** target; evidence green (self_test, pressure B1) | Depends on S1 |
| S3 | PassKey determinism + content-preservation (\(\{F(K)\}=\{K\}\) as sets) | P0 | Lean + property-test | **Proof** (easy content); determinism trivial | Soft-lock companion |
| S4 | PassKey injectivity on \(S_{52}\) | P0 | Lean + property-test | **Proof** | Constructive \(F^{-1}\) in §3.7; Lean `passKey_leftInverse` / `passKey_rightInverse` in `proofs/doubledeal/`. Cycle structure / orbit lengths remain evidence only. |
| S5 | CTR factoradic unranking is a bijection \(\mathbb{Z}/13!\mathbb{Z} \leftrightarrow S_{13}\) (and 39! ↔ \(S_{39}\) for software nonce helper) | P1 | Lean + property-test | **Proof** target | Classic combinatorics; pin exact digit convention to `unrank_perm` |
| S6 | CTR merge: `counter_deck` always a full CHaSeD perm; consec \(i,i+1\) agree on seats 0..38 | P1 | property-test + Lean | **Proof** / evidence | Already demonstrated in pressure C |
| S7 | Hand↔math refinement: player-sheet procedures refine §3 ops (esp. overflow scan, proper-cut fallback, col vs row scoop) | P1 | TLA or Lean refinement + checklist | **Proof** of refinement obligations; interim: manual audit checklist | Ambiguity surface for stranger play |
| S8 | Differential toy search (2-swaps / low-weight); avalanche tables vs Nr | P1 | cryptanalysis script | **Evidence** only | Existing spikes / pressure B2–B6; keep toy-labelled |
| S9 | Slide probes (unkeyed stem commuting with encrypt) | P2 | cryptanalysis script | **Evidence** | Pressure B5 toy sample: 0 hits — not a proof |
| S10 | Permutation / randomness tests on CT under random M,K (seat Hamming, same-rank) | P2 | cryptanalysis script | **Evidence** | SUMRANKS_LOCK metrics (~51 mean at Nr=6) |
| S11 | Mode lemmas: ECB identical-block leak; CTR KP recovery under nonce reuse | P1 | Lean (algebra of Compose) + script demo | **Proof** for Compose KP algebra; evidence for end-to-end demo | Pressure C already shows KP path |
| S12 | Unkeyed peel: full_round = Compose(unkeyed(M), K) | P0 | Lean + property-test | **Proof** / evidence (pressure B4) | Structural teaching lemma |
| S13 | §5.3 bytes ↔ deck: 28-byte unrank is injective; 29-byte rank/unrank is a bijection with \(\{0,\ldots,52!-1\}\); `0x80` padding strips uniquely | P1 | property-test | **Evidence** (`demos/doubledeal/cards.js`) | Same digit convention as §5.2. `52!` does not fit in a sudocode `int` |
| S14 | DoubleDeal-CBC-HMAC: CBC round-trip; tag-tamper reject; AAD / IV in the MAC | P1 | property-test | **Evidence** (`primitives/aead/doubledeal-cbc-hmac/`) | Not a MAC/PRF theorem. SCM / Lean refinement out of scope |
| S15 | AES-style argument: diffusion notion, multi-round trail bound, linear analogue | P2 | Lean + cryptanalysis script | **Proof** of single-layer bounds, and of a multi-round characteristic bound in the independent-uniform-round-key model only; full argument open | Roadmap: the milestone list in `proofs/doubledeal/security/README.md` (section "Roadmap"). Status (v12): the Hamming branch number of GridCycle is exactly the trivial floor 4 (proved), so it gives no wide-trail bound. For the relabelling (value-difference) notion, proved: every relabelling outside `v10Sym` survives SumRanks on ≤ 1/64 of the decks, and every nontrivial `v10Sym` survives GridCycle on ≤1/4420: heavy library (kernel `decide!`); default library proves ≤1/26 unconditionally and ≤1/4420 only given the two finite checks (it also proves, unconditionally, that 50 of the 51 survive on no deck). In the independent-uniform-round-key model only (count over all (52!)^R key tuples, every fixed starting deck, R mix rounds without the final no-mix round, not linked to `encryptN`), the constant-σ characteristic has probability ≤ (1/64)^R for every σ ≠ 1 (heavy library, kernel `decide!`; default library: (1/26)^R unconditionally, (1/64)^R given the two finite checks). One characteristic, not a differential. Linear analogue: none is defined; the note argues no direct analogue exists for permutation-valued state. It proposes a representation-theoretic analogue and records one sampled single-card position statistic at noise level (`proofs/doubledeal/analysis/v12-linear/`). The covariant round conjecture (no nontrivial relabelling σ has a τ with round(σ·m) = τ·round(m)) is still open. It is now proved for every transposition (heavy library, kernel `decide!`) and for every nontrivial `v10Sym`, and it is reduced to σ of prime order (reduction theorems whose hypotheses are not proved; `CovariantNarrow`, `proofs/doubledeal/analysis/v12-covariant/`). Exact Python enumeration, not formalised: the GridCycle prefix-survival values A_2, A_3 and A_4 (`proofs/doubledeal/analysis/v12-diffusion/prefix_survival.py`; Lean proves only the upper bounds above). Measured only: full per-layer survival values (`proofs/doubledeal/analysis/v12-diffusion/`). No multi-round statement for the real PassKey schedule, and no bit-security claim |

**Suggested order of attack:** S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7, S13 as a property-test of the byte encoding, S14 as AEAD evidence (not a theorem), and S8–S10 as living evidence notebooks — never promoted to “security results.” Cycle structure of PassKey stays evidence.

Lean for DoubleDeal layers, including the PassKey inverse, lives under `proofs/doubledeal/lean`.

---

# 7. 3D digital demo — rendering notes

Briefing for a graphics engineer building a **beautiful teaching demo** (not a game HUD dump). Goal: make each AES analogue readable as a physical gesture on felt.

## Scene grammar

- **Felt table** — deep green or burgundy cloth; soft contact shadows under cards and chips.
- **Two decks** \(M\) and \(K\) with **distinct backs** (e.g. navy geometric vs warm linen) so whitening / Compose never confuse sources.
- **Ghost 4×13 grid** that fades in when a deal begins and fades out after scoop; seat ticks faintly numbered for column-major teaching overlays.
- Cards as **thin boxes** with rounded corners; slight thickness so lifts read; **readable pip LOD** (rank/suit stay legible at table scale; simplify only when very far).
- Soft key light + gentle rim; avoid disco bloom.

## Camera language

- Default: **¾ overhead** — readable grid, hands in frame.
- **Dolly in** on the active region (one row, one column, start seat, key pile) — never whip-pan.
- **Focus racks** when attention moves hand → grid → key pile.
- Hold still during pause chips (§ pacing).

## Per-operation choreography

### Deal column-major

Cards fly from packet to grid seats in **column order** (col 0 top→bottom, then col 1, …) with a light **deal cascade** stagger (~30–50 ms). Optional short motion trails. Ghost grid fades in as the first card lands.

### SumRanks — row rotate

Entire row slides as a **rigid ribbon** on a slight arc (felt friction, not ice). Highlight the row **above** (the one being read) while the two running totals count up across it. The weighted total, then total mod 13, appears above the moving row and dissolves. Show the mod-13 amount as **tick marks** along the row edge before and during the slide. Rows move in the order 1, 2, 3, 0.

### SumRanks — column rotate

Column **lifts slightly** (hover), then cycles **top→bottom like a belt**. Flash the suit pips of the column to the left (rows 1–3, the row-2 and row-3 pips shifted once and twice), then the column's own four pips. Show the resulting suit (0–3) as **four dots** with the active count filled. Settle with a soft drop-shadow pulse. Columns move in the order 1 … 12, 0.

### ShiftRows

Rows 1–3 slide left-to-right-end with overlapping ease (row 1 starts first, then 2, then 3). **Row 0 stays** with a subtle idle pulse so viewers see it was considered. Optional ghost labels `s=0,1,2,3`.

### Scoop column-major

**Reverse cascade** into the packet (col 0 top→bottom gather, …). Trails optional; opposite direction feel from deal.

### GridCycle

- Empty grid; **start seat (2,0)** highlights.
- Each placement: card arcs from hand to seat along the \((\Delta\mathrm{row}=\mathrm{suit},\,\Delta\mathrm{col}=\mathrm{rank})\) step as a visible **polyline on the grid**, suit **color-coded**.
- On a **blocked target**: highlight the **blocker**, show the **CHaSeD marker chip** plus the blocker's suit picking the row, and a **scan-line** that starts at the target column + blocker's rank and sweeps right (wrapping) for the empty seat. A marker for the finger (target + blocker's step after a block) would help but is optional; the current demo narrates it in the caption and does not animate it — make overflow **readable, not embarrassing**. No error flash; treat overflow as a first-class rule.
- After 52 placements: scoop **row-major** (see below).

### Scoop row-major

Cascade **across rows** (row 0 L→R, then row 1, …). Distinct motion vocabulary from column scoop so alternating majors teach themselves.

### Compose

Prefer **permutation arcs in 3D**: each card in \(M\) arcs from its old seat to its new seat under the \(K\)-induced reindex, with a translucent permutation diagram. Avoid busy “beams” from every reference card. Alternate acceptable metaphor: \(K\) ribboned above \(M\); brief seat highlight on \(K\), then \(M\)’s card at that seat flies to output slot \(j\) — keep it sparse.

### PassKey

One key deck. Whitening uses it as dealt. Each later encrypt round is preceded by one pass of that same deck; the pile at the end of the pass is the round key about to be used. Do not deal \(K_1,\ldots,K_6\) out before whitening. Decrypt passes that deck forward six times to \(K_6\), then un-passes once per remaining round back to \(K_0\). Do not re-deal the master key for each round key. Un-pass: controller lifts off the key pile; cut undo (bottom packet to top on hand or key pile); deal undo (bottom suit + 2 cards dealt back onto the top of the hand or key pile); controller settles on the hand.

**Split view** — hand left, key pile right. Forward: controller lifts from the hand, flashes **suit** (deal suit + 2 cards one at a time off the top of the hand **or** key pile, packet under that pile) then **rank** (cut target glow on hand **or** key pile). Cut = clean packet lift-and-rejoin. Controller settles on the **key pile** with a soft thud. Un-pass: controller lifts from the key pile; cut undo (bottom packet to top on hand or key pile); deal undo (bottom suit + 2 cards dealt back onto the top of that pile); controller settles on the **hand**. **Near end of pass:** key-pile deals and cuts use a **different accent color** so the fallback rule is teachable (not a failure state).

### CTR diamond counter

Seats **39–51** glow as a **counter rail**. Diamonds snap into the rail in factoradic (or published-list) order while **CHS nonce stays put** up front (seats 0–38 dimly locked). Then the whole deck compresses into the Encrypt animation. Advancing \(i\) only re-animates the rail.

## Pacing / pedagogy

- After each named AES analogue (**SubBytes / SumRanks**, **ShiftRows**, **MixColumns / GridCycle**, **AddRoundKey / Compose**), drop a **pause chip** with an on-felt label matching this spec’s names.
- Optional **“math ghost”** overlay toggling the formulas from §3 (row sum mod 13, step rule, Compose definition).
- Whitening and final-round “no MixColumns” get explicit callouts.

## What not to do

- Particle explosion spam; confetti on overflow.
- Random shuffles that do not match the true operation.
- **Identical** animation for column-major vs row-major scoops.
- Treating PassKey key-pile fallback as an error / red flash.
- Implying MDS, “military grade,” or real-world secrecy.

---

# 7a. Version history

| Version | Status | Change |
| --- | --- | --- |
| v8 (TDSPN elegant-v8) | **Deprecated**, frozen at `v8/SPEC.md` + `v8/doubledeal_v8.sudo` | SumRanks read ranks only, and the GridCycle overflow scanned each marker row from column 0. Same-rank relabellings (e.g. K♣↔K♦) commuted with every layer except GridCycle, giving a chosen-plaintext distinguisher (~\(10^{-3}\) per pair). Vulnerability proof: `proofs/deprecated/doubledeal-v8/`. |
| v9 | **Deprecated**, frozen at `v9/SPEC.md` + `v9/doubledeal_v9.sudo` | SumRanks columns sum \((\mathrm{rank}+\mathrm{suit}) \bmod 4\); GridCycle overflow scans from the blocked column. Toy evidence only: the same relation family measured at 0 hits in \(2\times10^6\) full-cipher pairs for the worst transposition found by a one-round screen (95% upper bound \(1.5\times10^{-6}\)). That is not a security claim. Superseded: a transposition the one-round screen did not rank first, K♣↔Q♥, commutes with the full cipher at about \(3.5\times10^{-8}\) per pair (14 hits in \(4\times10^8\) pairs, below what \(2\times10^6\) pairs can see). Vulnerability proof: `proofs/deprecated/doubledeal-v9/`. |
| v10 | **Deprecated**, frozen at `v10/SPEC.md` + `v10/doubledeal_v10.sudo` | SumRanks rows turn by the index-weighted rank total \(\sum (13-j)\,\mathrm{rank} \bmod 13\) of the row above; columns turn by the GF(4) suit value \(0 s_0 + s_1 + w s_2 + w^2 s_3\) of the column to the left plus the column's own suit sum; both chained in a fixed order (§3.3). Everything else as v9. Toy evidence only (`proofs/doubledeal/analysis/v10-sumranks/`): over uniformly random decks, SumRanks alone lets a card swap through unchanged with measured worst probability ≈ 1/221 over all 1326 swaps (measured 1/220.8; exactly 1/221 for a same-suit swap; v9: 1/4.2). Over relabellings more generally (subfolder `sbox-search/`: exhaustive over low-weight relabellings, plus hill-climbs), the worst non-symmetry one measured is a same-suit 3-cycle at exactly 9/1105 ≈ 1/123 (exact by enumeration, agreeing with 20M-deck samples), and none measured exceeds 1/64 except the 51 exact v10Sym symmetries. The 1/64 bound is proved in Lean for every non-symmetry relabelling of SumRanks alone (`sumRanksV10_survival_le`, `proofs/doubledeal/security/SUMRANKS_DP.md`); the value 9/1105 is proved exactly for the one 3-cycle A♣→2♣→3♣ (`sumRanksV10_survival_threeCycle`), but that it is the worst case is computer-assisted and not formalised. The product-formula 6-round estimate for the worst swap is about \(2\times10^{-17}\) (v9: \(3.6\times10^{-8}\)). These are measurements and extrapolations, not a security claim. The remaining survivors are same-suit swaps and cycles. Deprecated for a GridCycle per-layer parity shortfall (not a full-cipher attack): GridCycle, unchanged since v9, lets K♣↔K♦ through unchanged at 0.262 per layer and 1311/1326 swaps exceed 1/64 (write-up: `proofs/deprecated/doubledeal-v10/`). |
| v11 | **Superseded** (not attacked), frozen at `v11/SPEC.md` + `v11/doubledeal_v11.sudo` | GridCycle only (§3.5, §4.4): ghost finger (each step starts from the previous target) and blocker-driven blocked placement (row = marker + blocker's suit, start column = target column + blocker's rank, first empty seat to the right, drop a row if full, marker + 1), and after a blocked placement the finger moves to target + blocker's step. Everything else as v10. Toy evidence only (`proofs/doubledeal/analysis/v10-gridcycle/`, PHASE2 + PHASE6 variant B): measured worst single-swap survival through GridCycle alone ≈ 0.0049 (≈ 1/205; v10: 0.262), 0 of 1326 swaps above 1/64 (v10: 1311), worst swap through one full round (v10 SumRanks) ≈ 1.0e-4. These are sampled measurements, not a security claim and not a bound. Superseded for a related-key property of PassKey (suit + rank collisions; 0 hits on the full cipher in 10M related-key samples), not for an attack (write-up: `proofs/deprecated/doubledeal-v11/`). |
| v12 | **Current** | PassKey \(F\) only (§3.7, §4.6): the suit rotation of the hand (\(\mathrm{suit} \bmod\) hand size) is replaced by dealing \(\mathrm{suit}+2\) cards one at a time under the hand, else under the key pile, else skip, before the unchanged rank cut with key-pile fallback. Everything else as v11. Toy evidence only (`proofs/doubledeal/analysis/passkey-related-key/` §9): no exact per-step collision (v11: 68 suit + rank swaps, worst ≥ 196/221), measured worst single-swap pass-through of one \(F\) ≈ 1/506 (2♣↔A♥), mean over the 1326 swaps 0.00003, 0 of 200k keys with six related round keys for the worst pair. Measurements, not a security claim. \(F\) stays a proved bijection (`passKey_leftInverse` / `passKey_rightInverse`). |

---

# 8. In this repository

| Artifact | Path | Role |
| --- | --- | --- |
| This specification | `primitives/cipher/doubledeal/SPEC.md` | Normative rules (v12) |
| Deprecated v8 | `primitives/cipher/doubledeal/v8/` | Frozen v8 SPEC and sudo; vulnerability proof in `proofs/deprecated/doubledeal-v8/` |
| Deprecated v9 | `primitives/cipher/doubledeal/v9/` | Frozen v9 SPEC and sudo; vulnerability proof in `proofs/deprecated/doubledeal-v9/` |
| Deprecated v10 | `primitives/cipher/doubledeal/v10/` | Frozen v10 SPEC and sudo; GridCycle parity write-up and single-deck witness in `proofs/deprecated/doubledeal-v10/` |
| Superseded v11 | `primitives/cipher/doubledeal/v11/` | Frozen v11 SPEC and sudo; PassKey related-key write-up (not an attack) in `proofs/deprecated/doubledeal-v11/` |
| Conformance implementation | `primitives/cipher/doubledeal/doubledeal.sudo` | The only copy of the rounds |
| Byte encoding | `demos/doubledeal/cards.js` | §5.3, outside `encrypt` / `decrypt`. A demo box is the text you type, as UTF-8, then this encoding. A leading `0x` means the rest of the box is hex bytes. Ciphertext is written with that prefix. The key box is one deck: those bytes are a single 28-byte block, filled with the §5.3 pad when shorter than 28 bytes, used as-is when exactly 28, and rejected when longer. The nonce box is not §5.3. §5.2's nonce is a 39-card order; the page unranks up to 19 bytes into cards \(0..38\) and rejects an integer \(\ge 39!\). |
| Demo | `demos/doubledeal/` | Three.js table. Plays `trace_encrypt` and `trace_decrypt` from the sudo module |
| Correctness proofs | `proofs/doubledeal/` | Lean 4 algebraic stones (bijections, round-trip, content-preservation). Not bit-security. |
| v10 SumRanks analysis | `proofs/doubledeal/analysis/v10-sumranks/` | Candidate measurements that led to v10 (empirical; not proofs) |
| v10 GridCycle analysis | `proofs/doubledeal/analysis/v10-gridcycle/` | Candidate measurements that led to the v11 GridCycle (empirical; not proofs) |
| PassKey related-key analysis | `proofs/doubledeal/analysis/passkey-related-key/` | The v11 PassKey suit + rank collision, its key-schedule and full-cipher measurements, and the candidate rules measured for v12, including the chosen key-pile fallback (§9) (empirical and closed-form; not Lean proofs) |
| DoubleDeal-CBC-HMAC | `primitives/aead/doubledeal-cbc-hmac/` | CBC + HMAC-MegaDreifach AEAD. Not SCM. |

---

*Toy teaching cipher. Not MDS. No security claim.*
