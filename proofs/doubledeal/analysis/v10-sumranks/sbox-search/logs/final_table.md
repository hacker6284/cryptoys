| # | kind | difference | class | (a) same-diff survival: hits/N, rate, 95% CI | exact | (b) best output diff: hits, rate | vs 1/64 | vs 1/221 |
|---|---|---|---|---|---|---|---|---|
| 1 | value | rank+1 on every card (any of the 51 v10Sym elements) | exact symmetry (proved, SumRanksV10Iff) | 20000000/20000000 = 1 (1/1) [1, 1] | 1 = 1/1.0 | 20000000 = 1 (same as input) | ABOVE | ABOVE |
| 2 | value | 3-cycle of three same-suit cards, e.g. AC->2C->3C | same-suit 3-cycle | 162525/20000000 = 0.008126 (1/123) [0.00809, 0.00817] | 9/1105 = 1/122.8 | 162525 = 0.00813 (same as input) | below | ABOVE |
| 3 | value | 4-cycle of same-suit cards AC->2C->3C->4C | same-suit 4-cycle | 55888/20000000 = 0.002794 (1/358) [0.00277, 0.00282] | 761/270725 = 1/355.7 | 55888 = 0.00279 (same as input) | below | below |
| 4 | value | two swaps of same-suit pairs, unequal gaps, e.g. (AC 2C)(AH 3H) | same-suit double swap | 51205/20000000 = 0.00256 (1/391) [0.00254, 0.00258] | 691/270725 = 1/391.8 | 51205 = 0.00256 (same as input) | below | below |
| 5 | value | swap of two same-suit cards, e.g. 2C<->7C | same-suit swap (old worst) | 90072/20000000 = 0.004504 (1/222) [0.00447, 0.00453] | 1/221 = 1/221.0 | 90072 = 0.0045 (same as input) | below | below |
| 6 | value | 3-cycle of three same-rank cards, e.g. 2C->2H->2S | same-rank 3-cycle | 23698/20000000 = 0.001185 (1/844) [0.00117, 0.0012] | 1/850 = 1/850.0 | 23698 = 0.00118 (same as input) | below | below |
| 7 | value | GF(4) suit map on one rank, e.g. 2C<->2D, 2H<->2S | subset relabelling | 2898/20000000 = 0.0001449 (1/6901) [0.00014, 0.00015] | 3/20825 = 1/6941.7 | 2898 = 0.000145 (same as input) | below | below |
| 8 | position | position swap cells (1,2)<->(3,6) | best position swap (scan+hill-climb) | 0/20000000 = 0 (1/inf) [0, 1.92e-07] |  | 13673 = 0.000684 (a different output diff) | below | below |
| 9 | position | position swap cells (0,0)<->(1,0) (weight-0 column) | position swap | 6859/20000000 = 0.000343 (1/2916) [0.000335, 0.000351] |  | 7030 = 0.000351 (a different output diff) | below | below |
| 10 | position | rotate every row left by 1 | all-rows rotation | 1672/20000000 = 8.36e-05 (1/11962) [7.97e-05, 8.77e-05] |  | 1744 = 8.72e-05 (a different output diff) | below | below |
