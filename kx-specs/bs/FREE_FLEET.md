# Free-fleet Battleship: how many layouts fit on a 10x10 grid

Script: `free_fleet_count.py` (it runs everything: `python3 free_fleet_count.py`, about 5 min for the exact stage plus a few min of Monte Carlo).
Raw output: `run.log`, `results_exact.json`, `results_mc.json` (the MC file also holds a second 300k-sample run, `mc2.json`).

Rules: kinds D2, S3, C3, B4, A5 (Sub and Cruiser are different kinds). You can place any number of ships. Ships are straight (H or V), stay inside the grid, don't overlap and may touch. There are no 1-cell ships, and empty cells are allowed.

## Results (10x10, 100 holes)

| count | exact value | log2 | bits/hole |
|---|---|---|---|
| **A** placements with a bow on each ship (= Σ 2^#ships) | 1625293215817106661401142990327492500859040945 | **150.1875** | 1.5019 |
| **B** placements, no bow | 658589750414677416564297551258722656 | **118.9869** | 1.1899 |
| **C** B with no same-kind ships end-to-end in line | not computed exactly (see below) | **116.002 ± 0.006** (MC) | 1.1600 |
| **D** full tilings (B, no empty holes) | 33121211791731215537932202 | **84.7760** | 0.8478 |
| D_A full tilings with bows | 14616444583902939896182008565616082944 | 123.4589 | 1.2346 |
| A' distinct *(kind, part k)* labellings (see caveat) | not computed exactly | **148.835 ± 0.002** (MC) | 1.4883 |
| standard fleet (one of each kind), no bow | 30093975536 | 34.8088 | 0.348 |
| standard fleet with bows (×2^5) | 963007217152 | 39.8088 | 0.398 |

Comparisons: 3-state pegs in every hole give log2(3^100) = 158.50 bits. Yes/no in every hole (1-hole ships) gives 100 bits. A free fleet with bows (150.19) is 8.3 bits below the 3-state pegs. Without bows (118.99) it is 19 bits above yes/no. Full tilings (84.78) are below yes/no.

Standard fleet: I get 30,093,975,536 layouts (34.81 bits), not the ~33.6 bits in the brief. This DP matches brute force on smaller fleets and boards. If Sub and Cruiser are treated as the same kind the count halves, giving 33.81 bits. So the 33.6 figure probably uses different rules (e.g. no touching).

## Caveat: "part k of kind K" labels do NOT identify the placement uniquely
If every hole is labelled only with (kind, part-number-from-bow), two different placements can give the same labelling. The smallest example is a 2x2 block of destroyers:

    D1 D2        two horizontal destroyers with opposite bows
    D2 D1   ==   two vertical destroyers with opposite bows

Brute force shows the gap: on 2x2 there are 17 placements but 15 labellings, and on 4x4 there are 3,996,513 placements but 3,387,007 labellings. So A counts placements (equivalently, labellings where each label also records H/V orientation). With H/V included the labels are unique; brute force checks this on all test grids. For B, the labels (kind, H/V, index) are unique, and B is simply the number of sets of ships.
The number of distinct pure (kind, part) labellings A' was estimated as A·E[1/multiplicity]. That average was taken over 400k exact samples from the A-distribution, and for each sample the multiplicity was found exactly by a backtracking solver: E = 0.39156 ± 0.00051, which gives 148.835 ± 0.002 bits (1.35 bits below A). The estimator matches the brute-force values on 3x3, 3x4 and 4x4.

## Variant C (no same-kind collinear end-to-end neighbours)
Here that means two ships of the same kind and orientation, in one line, with end cells touching. Parallel side-by-side ships are still allowed. This variant turned out not to be easy for 10x10:
- Direct: each column has to remember the kind of the vertical ship that just ended, which gives about 15–18 states per column (15^10 in all).
- Inclusion–exclusion: a chain of m same-kind ships becomes one piece of length mL with weight (-1)^(m-1). The net piece weights are len2 +1, 3 +2, 5 +1, 6 −1, 8 −2, 9 +2 (lengths 4, 7 and 10 cancel to 0). Pieces go up to length 9, so the profile needs 9^10 ≈ 3.5e9 states, which is too big.

What was done instead:
- Exact C values on small squares, from the inclusion–exclusion DP (checked against brute force up to 4x4):
  4x4 102876, 5x5 146561528, 6x6 1103907322973, 7x7 45209257299060475 (C/B = 0.806, 0.678, 0.532, 0.397).
- Exact C on 10 x w strips for w ≤ 7, and a float run for w = 8 (log2 C = 9.28, 20.21, 32.37, 44.27, 56.25, 68.20, 80.15, 92.09).
- 10x10 by Monte Carlo: P_B(layout passes C) = 0.12634 ± 0.00053 from 400k exact samples of B, so **log2 C ≈ 116.002 ± 0.006**. The same sampler matches the exact C/B on 4x4, 3x4, 7x7, 10x7 and 10x8 to within 1σ.
  Extrapolating the strips in w gives 115.98. The same method is off by only 0.001 on B, but the C increments converge more slowly, so trust the MC figure.

## Method
- Row-major broken-profile DP. The digit for each column is how many cells the vertical ship through it still has to cover below the current row. The kind is paid for as a weight when the ship starts, so it doesn't need to be stored. That leaves values 0..4, i.e. 5^10 = 9.8M states instead of 13^10. Sub and Cruiser share the length-3 weight of 2 (×2 again for bows in A).
- A horizontal ship starting at (i,j) checks that the next L−1 columns are free and jumps straight to position j+L, so no extra state is needed.
- Arithmetic is done with numpy int64 modulo 4–5 primes near 2^58, then rebuilt with CRT. One extra prime beyond the float-estimated size is used, and the result must not change when it is dropped. Each prime takes about 10 s on 10x10.
- Checks:
  - Brute-force enumeration of every placement on 1x2, 2x1, 2x2, 1x5, 2x3, 3x2, 1x7, 1x10, 3x3, 2x5, 2x6, 3x4 and 4x4 agrees with a separate big-int dict DP and with the numpy DP for A, B, C, D and D_A.
  - The dict DP and the numpy DP agree on 5x5, 6x4 and 4x7.
  - The standard-fleet DP agrees with brute force on 4x4, 5x5 and 5x6.
  Small values: 1x2 A=3 B=2 D=1; 2x2 A=17 B=7 D=2; 1x5 A=55 B=21 D=5; 2x3 A=139 B=38 D=7; 4x4 A=3996513 B=127694 D=1778.
- Monte Carlo: stored float32 forward DP (about 3.9 GB), exact backward sampling, 400k samples per distribution.
