# Elliptic Curve Battleship v3: play card

Toy, Hobby and Serious as written; Demo changes are listed in the last section, "Demo".

**Pegs.** A hole is empty, white or red. A dropped white peg turns a hole one step round: empty, white, red, empty. A red peg turns it one step back. To mirror, swap white and red.

**Board.** A number fills a lane band less its last hole, hole 0 first, in reading order. Lanes: Toy 8 wide by 3 rows; Hobby 20 by 3 and Serious 20 by 9, over two grids. The workbench is three bands; grids are numbered from its first. Homes, from the top: across, up, bottom, base across, base up, gap, spare. The control row is the workspace grids' bottom rows, run on: 15 script holes, phase hole, calling hole, ladder, parking hole, tally. Keys: 16, 51 or 162 cells.

## Moves
1. **Add:** drop every peg of one number onto the same holes of the other. **Take away:** drop it mirrored.
2. **This times that** (on the workbench): lift that number's highest peg and lay this number from that hole, mirrored for a red peg, until that band is empty. "A copy of" that: copy it into the spare and lift the copy. "Onto" a number: slide it onto the workbench first. Fold, then slide the result "into" the band named, clearing it.
3. **Fold:** from the far end, lift each peg beyond the number and drop it one band up and one hole on, and again one row up (Serious: six). One on from a row's end is the next row's start.
4. **Cube:** comb each row, top first, into the next workbench band, a peg on every third hole, a cursor ship keeping your place. Fold. **Frobenius:** cube every part of the point.
5. **Ladder** (once): lay a number's pegs less one in the spare; pair them off. A leftover makes a red rung, none a white one. Throw the leftover away, keep one of each pair, and repeat down to one peg.
6. **Tally:** "once per tally peg" means turning a white tally peg red after each go, until none is white. To double it, drop red on each red, then lay as many whites again. **Curve side** of a number: a copy of it cubed, take away it times a copy of itself, white peg in hole 0.
7. **Invert the bottom:** copy it into the gap; start a tally of one white peg. Climb the ladder from the last rung made, parking each rung while you work it. At each rung, cube a copy of the gap in the spare once per tally peg, do the gap times the spare, into the gap, and double the tally. On a red rung, also cube the gap into the spare, do the bottom times the spare, into the gap, and add a tally peg. At the last rung, skip the doubling and the extra peg. Cube the gap once more. The gap times a copy of the bottom must be one peg in hole 0; if red, mirror the gap. Clear the tally.
8. **Script marker:** in a walk or the root strip, move it one hole on per cube or multiply, from the first script hole; lift it at each new cell.

## Play
9. **Base point:** a white peg in hole 1 of the base across; its curve side in the bottom; the bottom times a copy of itself in the gap; a white peg in hole 0 of the up. In the across, lay the root strip, one hole short: red, empty, red, empty and so on, ending red, white. At each strip hole, under a cursor ship, cube the up, then on red do the up times a copy of the gap, on white of the bottom, into the up. Clear the gap; put the up times a copy of itself there. Not the bottom? Clear everything, move the white peg one hole on, and restart. Otherwise clear the gap, bottom and strip, and slide the up into the base up. Walk white, red, white, red, laid in the first key cells (steps 11 to 13); clear them, and slide the result into the base bands.
10. **Roll your key** row by row: throw the five d10s, rethrowing any 0; they go along the row in rainbow order, two holes each. On a phone keypad, the number's row gives the first hole's peg and its column gives the second's. The top row or left column means no peg, the middle means white, and the bottom row or right column means red: 6 gives white then red. Roll the whole key in one sitting and don't let go until it is done: an unrolled hole looks like an empty one.
11. **Start:** keep your key cell on the rails. At the first non-empty cell, copy the base bands into the across and up (the up mirrored for red), and put a white peg in hole 0 of the bottom.
12. **Walk:** at each later cell, Frobenius the point. Unless the cell is empty, add the base point, with the base up mirrored throughout for red:
    - **Run:** mirror the across; lay the base across times a copy of the bottom onto it. Empty? Reroll your key.
    - **Rise:** mirror the up; lay the base up times a copy of the bottom onto it.
    - **Gap:** the up times a copy of itself, into the gap; the bottom times the gap, into the gap; the across times a copy of itself, into the spare; the spare times the bottom, into the bottom. Lay the across times the spare onto the gap; drop the bottom onto the gap.
    - **Bottom:** the across times the bottom, into the bottom.
    - **New across:** the gap times the across, into the across; lay the base across times a copy of the bottom onto it.
    - **New up:** the gap times the up, into the up; lay the base up times a copy of the bottom onto it, both mirrored. Clear the gap.
13. **Finish:** invert the bottom. Do the gap times the across, into the across, and the gap times the up, into the up. Clear the gap, bottom and base bands. Your point is the across and up.
14. **Exchange** by the check card. **Shared key:** walk your key over the base bands (steps 11 to 13). Fold the across: Serious drops rows F to I onto A to D, Toy and Hobby row C onto A. The key is rows A to E (Serious) or A to B.

**Hands:** a finger may hold your place, but park the cursor ships before you let go. Never let go while rolling your key (step 10) or calling.

---

# Elliptic Curve Battleship v3: check card

**Certificate** of a point ("its" bands are the point's own): copy its across into the bottom, cube it, mirror it and add its across. If the bottom is empty, the certificate is empty. Invert the bottom. Copy its up into the spare, cube it, add its up and mirror it. Do the gap times the spare, into the gap, and Frobenius the point. Do the gap times a copy of itself, drop a white peg in hole 0, add its across, take away the bottom, and put it into the bottom. Take the bottom away from its across. Mirror its up and lay the gap times its across onto it. Clear the gap and slide the bottom into its across.

**Calling:** clear the homes named and stand a peg in the calling hole. Call the matching hole of your partner's band aloud by grid and coordinate ("grid 3, B7"): hole 0 first in number order, every hole, never the key or the control row. Red hits, white misses, empty misfires: lay each answer in the same hole of your home. After the last, lift the calling peg.

1. **Send:** after your walk, call their across and up (their point) into your base bands. The base up times a copy of itself, in the gap, must match the base across's curve side, in the bottom, or reject. Clear both. Make the certificate of your across and up, and drop a white peg in the phase hole.
2. **Check:** make the certificate of the base bands; if it is empty, reject. Drop a white peg in the phase hole. Once theirs shows a peg, call their across into your bottom and their up into your gap. Unless they match the base across and base up peg for peg, reject. Clear the bottom and gap and, once you have both called, the across and up.
3. **Shared key:** play card, step 14.

---

# Demo (n = 7, one kit (½ set))

Everything above holds at Demo except these lines.

- **Board.** One target grid in five lanes two holes wide (columns 1–2, 3–4, 5–6, 7–8, 9–10). Lane 1, all ten rows, is the workbench. A number fills four rows of a lane less its last hole, hole 0 first. Homes: rows A–D of lanes 2 to 5 hold the across, up, bottom and base across; rows E–H of lanes 2 to 4 hold the base up, gap and spare (lane 5, rows E–H, stays free). The control row is rows I and J of lanes 2 to 5, row I first, run on: 5 script holes, phase hole, calling hole, ladder, parking hole, tally. Key: 2 cells of the ocean grid (grid 2); white-red-white-red uses its first four. Calls name grid 1 ("grid 1, A3").
- **Cube:** a row is two holes, so a finger keeps your place; no cursor ship.
- **Start** (step 11): copy the base bands into the across and up (the up mirrored for red). No peg goes in the bottom.
- **Walk** (step 12): at each later cell, Frobenius the point (cube the across and the up). Unless the cell is empty, add the base point by the chord rule, with the base up mirrored throughout for red:
  - **Run:** copy the base across into the bottom and take the across away. Empty? Reroll your key. Invert the bottom.
  - **Rise:** copy the base up into the spare and take the up away.
  - **Then as in the certificate:** do the gap times the spare, into the gap. Do the gap times a copy of itself, drop a white peg in hole 0, add the across, take away the bottom, and put it into the bottom. Take the bottom away from the across. Mirror the up and lay the gap times the across onto it. Clear the gap and slide the bottom into the across.
  - The script marker moves one hole per cube or multiply of the walk and stands still while you invert.
- **Finish** (step 13): nothing to invert; the point is already in the across and up. Clear the base bands.
- **Shared key** (step 14): drop rows C and D onto rows A and B; the key is rows A and B (4 trits).
