# DoubleDeal

Formerly TwoDeck (TDSPN elegant-v8). This document is the normative specification. `doubledeal.sudo` is the conformance implementation. A mismatch is a bug in the implementation. DoubleDeal is a toy block cipher on a 52-card deck, AES in spirit and not in security. It makes no cryptographic security claim. It is not for protecting anything.

The demo at `demos/doubledeal/` plays `trace_encrypt` and `trace_decrypt`. It does not contain a second copy of the rounds. `decrypt` may keep the round-key list from `expand_keys`. The decrypt trace does not: it passes the master key forward 6 times to \(K_6\), then un-passes once per remaining round back to \(K_0\). Ciphertext is the same either way; only the key-derivation choreography differs.

---

# 1. Scope and non-goals

## In scope

- A single-block SPN on permutations of a 52-card CHaSeD deck.
- Unkeyed layers: **SumRanks** (SubBytes stand-in), **ShiftRows**, **GridCycle** (MixColumns stand-in).
- Keyed layer: **Compose** (AddRoundKey stand-in), using a 52-card round key as core.
- Key schedule: **PassKey** — forward iteration \(K_r = F(K_{r-1})\) with \(F =\) `pass_to_key_cut_fallback`.
- Round count \(N_r = 6\): whitening with \(K_0\), five full rounds with \(K_1,\ldots,K_5\), final round with \(K_6\) (no MixColumns).
- Modes: **ECB** and **CTR** only. CTR counter encoding is pinned: Diamonds in seats 39–51 via factoradic; Clubs+Hearts+Spades in seats 0–38 as nonce.
- A byte encoding outside `encrypt` / `decrypt` (§5.3). It is not a second block size. One block is still one deck.

## Non-goals

- No claim of AES-class security, MDS MixColumns, or cryptographically strong key schedule.
- No CBC / CFB / OFB / AEAD. No authentication.
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
| GridCycle / inv GridCycle | Yes (as packet maps) | Claimed; RT in self_test |
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

Operate on a filled \(4\times13\) grid \(G\). Ranks only; suits unused here.

**Row stage (forward).** For each row \(i=0..3\):

\[
t_i = \Bigl(\sum_{j=0}^{12} \mathrm{rank}(G[i,j])\Bigr) \bmod 13,
\qquad
G'[i] = G[i][t_i{:}] + G[i][{:}t_i]
\quad\text{(left rotate by \(t_i\))}.
\]

**Column stage (forward).** For each column \(j=0..12\), let \(\mathrm{col} = (G'[0,j],\ldots,G'[3,j])\):

\[
s_j = \Bigl(\sum_{i=0}^{3} \mathrm{rank}(\mathrm{col}[i])\Bigr) \bmod 4,
\qquad
\mathrm{new}[i] = \mathrm{col}[(i - s_j)\bmod 4]
\quad\text{(top→bottom by \(s_j\))}.
\]

Write \(\mathrm{new}\) back into column \(j\). Then \(\mathrm{SumRanks}(G)\) is the resulting grid.

**Order:** row-then-column (locked hand-feel revision: separates SumRanks row rotate from ShiftRows).

**Inverse.** Rank-sums are invariant under their own rotates, so the same \(t_i,s_j\) can be recomputed after the forward move.

1. Undo columns: \(\mathrm{new}[i] = \mathrm{col}[(i + s_j)\bmod 4]\).
2. Undo rows: right rotate by \(t_i\): \(G[i] = G[i][-t_i{:}] + G[i][{:}-t_i]\).

**Claim:** \(\mathrm{invSumRanks} \circ \mathrm{SumRanks} = \mathrm{id}\) on filled grids. Not an involution — order matters.

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

**Step** from seat \((r,c)\) using card \(x\) just placed:

\[
\mathrm{step}(x,(r,c)) = \bigl((r + \mathrm{suit}(x))\bmod 4,\;
(c + \mathrm{rank}(x))\bmod 13\bigr).
\]

**Overflow machine.** State \(t \in \{0,1,2,3\}\), initially \(0\). On overflow, seek the next free seat:

```
overflow_seat(occupied, t):
  repeat up to 4 times:
    row ← CHASED[t]          # 0,1,2,3 = ♣♥♠♦
    for col in 0..12:
      if not occupied(row, col):
        return (row, col), (t+1) mod 4
    t ← (t+1) mod 4
  fail  # unreachable on a 52-seat grid with <52 occupied
```

**Forward** `mix_columns(D)`:

```
grid ← empty 4×13
t ← 0
for i, card in enumerate(D):
  if i = 0:
    pos ← AS_START = (2, 0)
  else:
    target ← step(prev_card, prev_pos)
    if grid[target] is empty:
      pos ← target
    else:
      pos, t ← overflow_seat(λ(r,c). grid[r,c] occupied, t)
  place card at pos
  prev_card, prev_pos ← card, pos
return scoop_row_major(grid)
```

**Inverse outline** `inv_mix_columns(D)`:

```
grid ← lay_row_major(D)      # recover placement
visited ← all false
t ← 0; hand ← []
for i in 0..51:
  choose pos by the same AS_START / step / overflow rule,
    treating “occupied” as “visited”
  append grid[pos] to hand; mark visited[pos]
return hand
```

**Claim:** \(\mathrm{invMix} \circ \mathrm{Mix} = \mathrm{id}\) on decks. Not MDS; toy diffusion only.

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
    if hand nonempty:
      k ← suit(C) mod len(hand)
      if k > 0: hand ← left_rotate(hand, k)
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
    if n > 0:
      k ← suit(C) mod n
      if k > 0: hand ← right_rotate(hand, k)
    insert C at front of hand
  return hand
```

**Claim:** \(F\) is a bijection on \(S_{52}\). \(F^{-1}\circ F=\mathrm{id}\) and \(F\circ F^{-1}=\mathrm{id}\). Deterministic; preserves the card multiset.

**Why:** at step \(i\) the controller \(C\) is on top of the key pile, so the inverse can read it. Every branch depends only on \(C\) and the pile sizes (hand \(=51-i\) after the pop, key \(=i\)), never on hidden card identities. Each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. Lean: `proofs/doubledeal/lean/DoubleDeal/PassKey.lean`, theorems `passKey_leftInverse` and `passKey_rightInverse` (on `main` via PR #2). Cycle structure / orbit lengths of \(F\) on \(S_{52}\) are not claimed.

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
**Suits (GridCycle / Compose / PassKey):** ♣=0 ♥=1 ♠=2 ♦=3.

## 4.1 Deal / scoop conventions

- **Column-major deal:** fill column 0 top→bottom, then column 1, … column 12 (down the columns).
- **Column-major scoop:** reverse of that — gather column 0 top→bottom, then column 1, …
- **Row-major scoop:** across row 0 left→right, then row 1, … (GridCycle output only).
- **Row-major lay (decrypt GridCycle):** place the packet into the table in that same reading order.

Do **not** use the same cascade motion for col-major and row-major; the majors are part of the teaching story.

## 4.2 SumRanks (SubBytes)

On the column-major table:

1. For each **row** of 13: sum the thirteen ranks; rotate that row **left** by (sum mod 13) — move that many cards from the left end to the right end.
2. For each **column** of 4: sum the four ranks; rotate that column **top→bottom** (sum mod 4) times.

Rows first, then columns (separates the row stage from ShiftRows).

**Inverse:** sums unchanged under rotate. Undo columns first (rotate the other way by sum mod 4), then undo rows (rotate the other way by sum mod 13). Enter/exit with the same column-major deal/scoop.

## 4.3 ShiftRows

- Row 0: no move (optional idle pulse so you notice it was considered).
- Row 1: move leftmost 1 card to the right end.
- Row 2: leftmost 2 → right end.
- Row 3: leftmost 3 → right end.

Then **scoop column-major** into a packet (full round continues to GridCycle; final round goes to Compose).

## 4.4 GridCycle (MixColumns)

1. Clear the 4×13 table. Keep an **overflow marker** chip that starts on ♣ and rotates ♣→♥→♠→♦→♣… when used.
2. Place the **first** hand card on the start seat **(row 2, column 0)**.
3. For each next hand card: from the seat you just filled, using the card you just placed, step  
   `new_row = (row + suit) mod 4`, `new_col = (col + rank) mod 13`.  
   - If that seat is **empty**, place there.  
   - If **full** (overflow): in the row named by the overflow marker’s suit, scan left→right for the first empty seat; place there; advance the marker one suit. If that whole row is full, advance the marker and try the next suit’s row the same way.
4. Scoop **row-major** → packet.

**Inverse:** lay the packet **row-major**. Use visited markers. Start seat’s card was first in the hand. Walk with the same step; if the stepped seat is already visited, use the same CHaSeD overflow on **unvisited** seats. Each chosen seat’s card is the next hand card.

## 4.5 Compose (AddRoundKey)

\(K\) is face-up as a 52-card reference. For each reference id \(j = 0..51\) in CHaSeD order (AC, 2C, …, KD): find where \(j\) sits in \(K\); take the card of \(M\) at that same seat; that is output position \(j\).

Practical table procedure: fan \(K\); build the output by reading \(M\) through \(K\)’s seat map. InverseCompose puts each output card back to the seat where its reference id sits in \(K\).

## 4.6 PassKey (between rounds)

No jokers. No round number. One full pass turns this round’s \(K\) into the next:

1. Hold \(K\) as a **hand** (top = face you deal first). Start an empty **key pile**.
2. For each controller **C** dealt from the hand:
   - Deal C (remove from top of hand).
   - If cards remain in hand: rotate the hand **left** by C’s **suit** places (♣=0 ♥=1 ♠=2 ♦=3), wrapping; use suit **mod** how many cards are left.
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
3. Undo the suit rotation: if the hand has cards, move \((\mathrm{suit}(C)\bmod\text{hand size})\) cards from the bottom of the hand to the top.
4. Put C on top of the hand.

When the key pile is empty, the hand is the previous round key. Forward “rotate left by \(k\)” moves the top \(k\) cards to the bottom, so this undo moves the bottom \(k\) to the top. Decrypt uses un-pass (§4.8).

Near the end of a (forward) pass, emphasize **key-pile** cuts — that fallback is intentional so short hands do not force silent no-ops.

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

Spec family allows **ECB + CTR only**.

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

**Suggested order of attack:** S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7, S13 as a property-test of the byte encoding, and S8–S10 as living evidence notebooks — never promoted to “security results.” Cycle structure of PassKey stays evidence.

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

Entire row slides as a **rigid ribbon** on a slight arc (felt friction, not ice). A temporary **numeral** (the rank-sum, then sum mod 13) appears above the row and dissolves. Mod-13 amount shown as **tick marks** along the row edge before/during the slide.

### SumRanks — column rotate

Column **lifts slightly** (hover) then cycles **top→bottom like a belt**. Sum mod 4 shown as **four dots** with the active count filled. Settle with a soft drop shadow pulse.

### ShiftRows

Rows 1–3 slide left-to-right-end with overlapping ease (row 1 starts first, then 2, then 3). **Row 0 stays** with a subtle idle pulse so viewers see it was considered. Optional ghost labels `s=0,1,2,3`.

### Scoop column-major

**Reverse cascade** into the packet (col 0 top→bottom gather, …). Trails optional; opposite direction feel from deal.

### GridCycle

- Empty grid; **start seat (2,0)** highlights.
- Each placement: card arcs from hand to seat along the \((\Delta\mathrm{row}=\mathrm{suit},\,\Delta\mathrm{col}=\mathrm{rank})\) step as a visible **polyline on the grid**, suit **color-coded**.
- On **overflow**: show the **CHaSeD marker chip** walking suits and a **scan-line** seeking the empty seat in that row — make overflow **readable, not embarrassing**. No error flash; treat overflow as a first-class rule.
- After 52 placements: scoop **row-major** (see below).

### Scoop row-major

Cascade **across rows** (row 0 L→R, then row 1, …). Distinct motion vocabulary from column scoop so alternating majors teach themselves.

### Compose

Prefer **permutation arcs in 3D**: each card in \(M\) arcs from its old seat to its new seat under the \(K\)-induced reindex, with a translucent permutation diagram. Avoid busy “beams” from every reference card. Alternate acceptable metaphor: \(K\) ribboned above \(M\); brief seat highlight on \(K\), then \(M\)’s card at that seat flies to output slot \(j\) — keep it sparse.

### PassKey

One key deck. Whitening uses it as dealt. Each later encrypt round is preceded by one pass of that same deck; the pile at the end of the pass is the round key about to be used. Do not deal \(K_1,\ldots,K_6\) out before whitening. Decrypt passes that deck forward six times to \(K_6\), then un-passes once per remaining round back to \(K_0\). Do not re-deal the master key for each round key. Un-pass: controller lifts off the key pile; cut undo (bottom packet to top on hand or key pile); suit undo on the hand; controller settles on the hand.

**Split view** — hand left, key pile right. Forward: controller lifts from the hand, flashes **suit** (hand rotate) then **rank** (cut target glow on hand **or** key pile). Cut = clean packet lift-and-rejoin. Controller settles on the **key pile** with a soft thud. Un-pass: controller lifts from the key pile; cut undo (bottom packet to top on hand or key pile); suit undo on the hand; controller settles on the **hand**. **Near end of pass:** key-pile cuts use a **different accent color** so the fallback rule is teachable (not a failure state).

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

# 8. In this repository

| Artifact | Path | Role |
| --- | --- | --- |
| This specification | `primitives/cipher/doubledeal/SPEC.md` | Normative rules |
| Conformance implementation | `primitives/cipher/doubledeal/doubledeal.sudo` | The only copy of the rounds |
| Byte encoding | `demos/doubledeal/cards.js` | §5.3, outside `encrypt` / `decrypt`. A demo box is the text you type, as UTF-8, then this encoding. A leading `0x` means the rest of the box is hex bytes. Ciphertext is written with that prefix. The key box is one deck: those bytes are a single 28-byte block, filled with the §5.3 pad when shorter than 28 bytes, used as-is when exactly 28, and rejected when longer. The nonce box is not §5.3. §5.2's nonce is a 39-card order; the page unranks up to 19 bytes into cards \(0..38\) and rejects an integer \(\ge 39!\). |
| Demo | `demos/doubledeal/` | Three.js table. Plays `trace_encrypt` and `trace_decrypt` from the sudo module |
| Correctness proofs | `proofs/doubledeal/` | Lean 4 algebraic stones (bijections, round-trip, content-preservation). Not bit-security. |

---

*Toy teaching cipher. Not MDS. No security claim.*
