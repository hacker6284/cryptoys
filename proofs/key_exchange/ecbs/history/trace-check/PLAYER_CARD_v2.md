# Elliptic Curve Battleship: player's card v2 (Toy, Hobby, Serious)

**Pegs.** A hole is empty, white or red. Dropping a white peg turns a hole one step round: empty, white, red, empty. A red peg turns it one step back. To mirror, swap white and red.

**Bands.** Each number fills one band of the lane, less its last hole. Toy uses 8 wide by 3 rows; Hobby 20 by 3 and Serious 20 by 9, both across two grids. The workbench is three bands. From the top, the number homes are across, up, bottom, base across, base up, gap and spare. The key has 16 cells (Toy), 51 (Hobby) or 162 (Serious). [GAP: which control holes hold the ladders, the tally, the parking pegs and the script marker.]

## Moves
1. **Add:** drop every peg of one number onto the same holes of the other. **Take away:** drop it mirrored.
2. **This times that** (on the workbench): lift that number's highest peg and lay this number from that hole, as it is for a white peg and mirrored for a red one. Repeat until that band is empty. "A copy of" means copy it into the spare and lift the copy. "Onto" a number means slide that number onto the workbench first. Fold, then slide the result "into" the band named, clearing what is left there.
3. **Fold:** from the far end, lift each peg beyond the number and drop it one band up and one hole on, and again one row up (Serious: six). One on at a row's end is the next row's first hole.
4. **Cube:** comb each row, top first, into the next workbench band, one peg on every third hole, keeping your place with a cursor ship. Then fold. **Frobenius:** cube every part of the point.
5. **Ladders** (build both once): lay a number's worth of pegs, less one for the inversion ladder. Pair them off. A leftover makes a red rung and none makes a white one. Throw the leftover away, keep one of each pair, and repeat down to one peg. Climb from the last rung made, with a parking peg beside your rung.
6. **Tally:** "once per tally peg" means turning one white peg red after each go, until all are red. To double it, drop a red peg on each red, then lay as many white pegs again. **Curve side** of a number: a copy of it cubed, take away it times a copy of itself, and drop a white peg in hole 0.
7. **Invert the bottom:** copy it into the gap and start a tally of one white peg. At each rung, cube a copy of the gap in the spare once per tally peg, then do the gap times the spare, into the gap, and double the tally. On a red rung, also cube the gap into the spare, do the bottom times the spare, into the gap, and add a white peg to the tally. Skip the doubling and the extra peg at the last rung. Then cube the gap once more. The gap times a copy of the bottom must be one peg in hole 0; if it is red, mirror the gap. Clear the tally.
8. **Chord add** (in the check): the first point is in across and up. Put the run, second across take away first across, in the bottom; if it is empty, reject. Invert the bottom. Only then put the rise, second up take away first up, in the spare. Do the gap times the spare, into the gap. Do the gap times a copy of itself, drop a white peg in hole 0, add the across, take away the bottom, and put it into the bottom. Take the bottom away from the across. Mirror the up and lay the gap times the across onto it. Clear the gap, then slide the bottom into the across.

## Play
9. **Roll your key:** fill the key grid row by row. Throw the five d10s, rethrowing any 0. The dice go along the row in rainbow order, two holes each. On a phone keypad, the number's row gives the first hole's peg and its column gives the second's. The top row or left column means no peg, the middle means white, and the bottom row or right column means red: 6 gives white then red.
10. **Base point:** put a white peg in hole 1 of the base across, and its curve side in the bottom. Do the bottom times a copy of itself, into the gap. Start the up as a white peg in hole 0. Lay the root strip, one hole shorter than a number: red, empty, red, empty and so on, ending red, white. At each strip hole, cube the up, then do the up times a copy of the gap on red, or of the bottom on white, into the up. Clear the gap. Do the up times a copy of itself, into the gap. If it isn't the bottom, clear everything, move the white peg one hole on and start again. Otherwise clear the gap and bottom, and slide the up into the base up. Walk the cells white, red, white, red (steps 11 to 13) and slide the result into the base bands.
11. **Start the walk:** at your first non-empty key cell, copy the base across into the across and the base up into the up (mirrored for a red cell). Put a white peg in hole 0 of the bottom.
12. **Walk:** at each later key cell, Frobenius the point. If the cell isn't empty, add the base point, using the base up mirrored throughout for a red cell. Move the script marker one hole after every cube or multiply: 3 cubes, then run 1, rise 1, gap 5, bottom 1, new across 2, new up 2.
    - **Run:** mirror the across and lay the base across times a copy of the bottom onto it. If it's empty, reroll your key.
    - **Rise:** mirror the up and lay the base up times a copy of the bottom onto it.
    - **Gap:** do the up times a copy of itself, into the gap, and the bottom times the gap, into the gap. Do the across times a copy of itself, into the spare, and the spare times the bottom, into the bottom. Lay the across times the spare onto the gap, then drop the bottom onto the gap.
    - **Bottom:** the across times the bottom, into the bottom.
    - **New across:** the gap times the across, into the across. Then lay the base across times a copy of the bottom onto it.
    - **New up:** the gap times the up, into the up. Then lay the base up times a copy of the bottom onto it, laying both mirrored. Clear the gap.
13. **Finish:** invert the bottom. Do the gap times the across, into the across, and the gap times the up, into the up. Clear the gap, the bottom and the base bands. Your point is the across and up.
14. **Swap:** your partner copies your across and up into their base bands, peg for peg. Then clear yours.
15. **Check theirs:** put the base up times a copy of itself in the gap, and the base across's curve side in the bottom. If they don't match, reject; otherwise clear both. Then copy their point into the across and up; this is the sum. Climb the check ladder. A rung's tally is one white peg, doubled for each rung already climbed, plus one after each red one. Rebuild it when you need it and clear it before each inversion.
    - **At each rung:** chord-add a copy of the sum, Frobeniused once per tally peg, to the sum.
    - **Then, on the last rung:** Frobenius the sum. If it isn't their point with the up mirrored, reject. Clear the sum; the check is done.
    - **On any other red rung:** Frobenius the sum and chord-add their point to it.
16. **Shared key:** walk your key over their point (steps 11 to 13). Fold the across: Serious drops rows F to I onto rows A to D, and Toy and Hobby drop row C onto row A. The key is rows A to E (Serious) or A to B (Toy and Hobby).

**Hands:** a finger may hold your place, but park the cursor ships before you let go.
