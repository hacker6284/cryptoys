# DoubleDeal v10 SumRanks: every non-symmetry relabelling survives on at most 52!/64 decks

Status: a paper proof, checked numerically against the C model of v10 SumRanks in
`../../analysis/v10-sumranks/sbox-search/` (`verify_proof.py`, output in `verify_output.txt`, 0 failures).
The Lean formalisation of the $52!/64$ bound is `../DoubleDealSecurity/SumRanksDP/` (see §9); the constant
$0.012768$ below is the paper's (§3 (A3), §5) and is not itself a Lean statement. The main line uses no computer search. The few places that use one are explicit sums over a
single integer parameter (41 values for Case A, 37 for Case B), each evaluated exactly in rational arithmetic. Two sharper
side-results (§8) do use exhaustive computation. They are not needed for the theorem.

## Theorem

Write $\mathrm{SR}$ for `sumRanksV10` (SPEC §3.3, W5c). For every relabelling $\tau$ of the 52 cards with
$\tau\notin\mathrm{v10Sym}=\{\mathrm{v10Sym}(a,x)\}$,
$$
\#\{d \text{ deck} : \mathrm{SR}(\tau\circ d)=\tau\circ \mathrm{SR}(d)\}\;\le\; 0.01277\cdot 52!\;<\;\frac{52!}{78}\;<\;\frac{52!}{64}.
$$
If $\tau$ changes every rank by the same amount (Case B below), the bound improves to $52!/425$.

For comparison, the true worst case is the same-suit 3-cycle at $9/1105\approx 1/122.8$
(`../../analysis/v10-sumranks/README.md`; measured, and derived in §5b with a computer-checked lemma). In Case B the true worst is the same-rank 3-cycle at $1/850$.

---

## 0. Conventions

* `layColumnMajor` is a bijection from decks to filled grids and commutes with relabelling (`relG`). So we count **grids** $G$
  (bijections from the 52 cells to the 52 cards) and write $\Pr$ for the uniform measure on these $52!$ grids.
* Cells are $(r,j)$ with $r\in\{0,1,2,3\}$ and $j\in\mathbb Z_{13}$. A card $c$ has rank $\rho(c)\in\mathbb Z_{13}$ (only rank mod 13 matters) and GF(4) label $\ell(c)$: ♣ $=0$, ♦ $=1$, ♥ $=w$, ♠ $=w^2$.
* SR as specified (checked against SPEC §3.3 and `DoubleDeal/SumRanksV10.lean`):
  * **Rows.** Rows turn in the order $1,2,3,0$. Row $i$ is rotated **left** by $\mathrm{turn}(\text{row } i-1)$, where
    $\mathrm{turn}(x)=U(x)=\sum_{j}(13-j)\rho(x_j)\bmod 13$. The row it reads is taken **as it is at that moment**. Row 1 therefore reads row 0
    **before** row 0 turns (row 0 turns last), and rows 2, 3, 0 read rows 1, 2, 3 **after** those have turned.
  * **Columns.** Then columns turn in the order $1,\dots,12,0$. Column $j$ is rotated **down** ($\mathrm{new}[i]=\mathrm{col}[i-s]$) by
    $s_j=V(\text{col } j-1)\oplus\Sigma(\text{col } j)$, where $V(y)=\ell(y_1)+w\ell(y_2)+w^2\ell(y_3)$ and
    $\Sigma(y)=\ell(y_0)+\ell(y_1)+\ell(y_2)+\ell(y_3)$. Column 1 reads column 0 **unrotated**. Columns $2..12$ and $0$ read the previous
    column **after** it has turned. $\Sigma(\text{col } j)$ does not change when column $j$ rotates.

**Difference data.** For a relabelling $\tau$ define, for each card $c$,
$$\delta(c)=\rho(\tau c)-\rho(c)\in\mathbb Z_{13},\qquad \varepsilon(c)=\ell(\tau c)+\ell(c)\in \mathrm{GF}(4).$$
Because $\tau$ is a bijection, $\sum_c\delta(c)=0$ and $\sum_c\varepsilon(c)=0$. A card is determined by its rank mod 13 and its label
(Lean: `card_eq_of_rank_label`), and $\mathrm{v10Sym}(a,x)$ is the relabelling with $\delta\equiv a$ and $\varepsilon\equiv x$ (`v10SymFn_rank`,
`v10SymFn_label`). Hence
$$\tau\notin\mathrm{v10Sym}\iff \delta \text{ is not constant, or } \varepsilon \text{ is not constant.}\tag{0.1}$$

**Row functionals.** For a row $x=(x_0,\dots,x_{12})$ let
$S(x)=\sum_j j\,\delta(x_j)$ and $D(x)=\sum_j\delta(x_j)$ in $\mathbb Z_{13}$. Since $13-j\equiv -j$,
$$U(\tau x)-U(x)\equiv -S(x)\pmod{13}.\tag{0.2}$$
For the left rotation $(L^t x)_j=x_{j+t}$ we have $S(L^tx)=\sum_i (i-t)\delta(x_i)$, so
$$S(L^t x)=S(x)-t\,D(x).\tag{0.3}$$

**Column functionals.** $V$ and $\Sigma$ are $\mathrm{GF}(2)$-linear in the labels, so
$V(\tau y)+V(y)=V(\varepsilon(y))$ and $\Sigma(\tau y)+\Sigma(y)=\Sigma(\varepsilon(y))$, where $\varepsilon(y)$ is the vector of $\varepsilon$
values down the column.

---

## 1. Per-deck reduction

View SR as 17 steps with states $X_0=G, X_1,\dots,X_{17}=\mathrm{SR}(G)$. Step $n$ turns one line by
$\kappa_n(X_{n-1})$, the turn function applied to the neighbour line (and, for a column, its own line) in the **current** state. Let
$a_n(G)=\kappa_n(X_{n-1}(G))$ be the applied amounts (Lean: `rowAmt`, `colAmt`).

**Lemma 1.** For every grid $G$ the following are equivalent:
1. $\mathrm{SR}(\tau G)=\tau\,\mathrm{SR}(G)$;
2. $a_n(\tau G)=a_n(G)$ for all 17 steps (row amounts mod 13, column amounts mod 4);
3. $\kappa_n(\tau X_{n-1})=\kappa_n(X_{n-1})$ for all $n$, where $X$ is **$G$'s own** trajectory.

*Proof.* (1⇒2): `sumRanksChain_eq` writes $\mathrm{SR}(g)=\mathrm{colRotate}(\mathrm{rowRotate}(g,\mathrm{rowAmt}\,g),\mathrm{colAmt}(\mathrm{rowsDone}\,g\,4))$.
With `relG_colRotate_rowRotate`, the hypothesis becomes an equality of two row-then-column rotations of $\tau G$. `amounts_match`
(through `rot_match` and `grid_inj`, which uses that a deck's cards are distinct) then gives equal amounts mod 13 and mod 4. This is exactly the
`obtain ⟨hr, hs⟩` step inside `sumRanksV10_turns_of_commute`.
(2⇒1): substitute into `sumRanksChain_eq` and use `rowRotate_congr`, `colRotate_congr` and `relG_colRotate_rowRotate`.
(2⇔3): induction on $n$. If the first $n-1$ amounts agree, then $X_{n-1}(\tau G)=\tau X_{n-1}(G)$, because relabelling commutes with
turning a line (`turnRow_rel`, `turnCol_rel`). So $a_n(\tau G)=\kappa_n(\tau X_{n-1}(G))$. This is the per-deck form of the
`hrows`/`hcols` inductions in `sumRanksChain_commutes`. $\square$

**Corollary 1 (explicit conditions).** Let $A_0,\dots,A_3$ be the rows of $G$ and let $G$'s own row turns be $t_1=U(A_0)$,
$t_2=U(L^{t_1}A_1)$, $t_3=U(L^{t_2}A_2)$. Put $\theta_0=0$ and $\theta_r=t_r$ for $r=1,2,3$; this is how far row $r$ has turned when it
is read. By (0.2) and (0.3), survival requires the four **row conditions**
$$(R_r)\qquad S(A_r)\equiv\theta_r\,D(A_r)\pmod{13},\qquad r=0,1,2,3.$$
Note that $\theta_r$ depends only on $A_0,\dots,A_{r-1}$.

If all four hold, $\tau G$ and $G$ turn their rows identically. Write $H=X_4(G)$ for the grid after the row stage, with columns
$Y_0,\dots,Y_{12}$ and column turns $s_j$ along $G$'s trajectory. Survival then additionally requires the 13 **column conditions**
$$(K_j)\qquad V\big(\varepsilon(\text{column } j-1 \text{ as read})\big)=\Sigma(\varepsilon(Y_j)),$$
where "as read" means $Y_0$ itself for $j=1$, and $Y_{j-1}$ rotated down by $s_{j-1}$ for $j\in\{2,\dots,12,0\}$.
**Survival holds if and only if all 17 conditions hold.** (Tested on 10,500 decks, 1,902 of them surviving: §1 of `verify_output.txt`.)

**Case split.** *Case A:* $\delta$ is not constant. We drop the $K_j$ and bound $\Pr[R_0\wedge\dots\wedge R_3]$.
*Case B:* $\delta\equiv a$. Then every $R_r$ holds automatically ($S=78a\equiv 0$ and $D=13a\equiv0$), so survival is equivalent to the $K_j$, and by
(0.1) $\varepsilon$ is not constant.
This split is the right one; "τ changes some card's rank" is not. For example, $\mathrm{v10Sym}(1,0)\circ(2♣\,2♦)$ changes every rank but is Case B.

---

## 2. One row (the switching lemma)

Fix a set $B$ of 13 cards to occupy a row, and let the arrangement $x:\mathbb Z_{13}\to B$ be uniform among the $13!$ bijections. Let $M$ be the
multiset $\delta(B)$ and $D=D(B)$, which does not depend on the order.

**Lemma 2.**
* **(a) $D\neq0$: exact equidistribution.** For every $c\in\mathbb Z_{13}$, $\Pr[S(x)=c]=1/13$.
* **(b) One-card switching.** Suppose $M$ is not constant and some value $v$ occurs $z\ge1$ times in $M$. Then
  $\Pr[S(x)=c]\le 1/(z+1)$ for every $c$.
* **(c) Cancelling pair.** If $M=\{v^{11},v+u,v-u\}$ with $u\ne0$, then $S(x)\neq0$ always.

*Proof.* (a) The cyclic shift $x\mapsto L^kx$ acts freely on arrangements (the cards are distinct), and by (0.3)
$S(L^kx)=S(x)-kD$. With $D\ne0$, each orbit of size 13 meets every residue exactly once.

(b) Double counting. Pick a card $c^\ast\in B$ with $\delta(c^\ast)=u\neq v$, and let $W\subset B$ be the $z$ cards of value $v$. Join $x$ to
$x'=(c^\ast\ w)\circ x$ (swap the seats of $c^\ast$ and $w$) for each $w\in W$. This graph is symmetric, every vertex has degree $z$, and
$$S(x')-S(x)=(u-v)\big(\mathrm{pos}_x(w)-\mathrm{pos}_x(c^\ast)\big).$$
The $z$ differences are nonzero and pairwise distinct, because the seats $\mathrm{pos}_x(w)$ are distinct and $u-v$ is a unit mod 13.
So every neighbour of a good vertex ($S=c$) is bad, and every bad vertex has at most one good neighbour. Counting the good–bad edges gives
$z\cdot\#\text{good}\le\#\text{bad}$, hence $\#\text{good}\le 13!/(z+1)$.
This is the "move a changed card across the columns of its row" idea. The weights $-j$ are distinct, and **column 0 (weight 0)
is not special**: the argument uses only differences of seats.

(c) $S=78v+u(j_1-j_2)\equiv u(j_1-j_2)\neq0$. $\square$

Define $\rho(B)=1/13$ if $D(B)\neq0$, and $\rho(B)=\Pr[S(x)=0]$ if $D(B)=0$. In particular $\rho(B)=1$ when $M$ is constant.

**Lemma 3 (row chain, exact).** Fix the ordered partition $(B_0,\dots,B_3)$ of the cards into row sets. Then
$$\Pr[R_0\wedge R_1\wedge R_2\wedge R_3\mid \text{row sets}]=\prod_{r=0}^3\rho(B_r).$$
*Proof.* Given the row sets, the four arrangements are independent and uniform, and
$\#\{G\}=\sum_{x_0}[R_0]\sum_{x_1}[R_1]\sum_{x_2}[R_2]\sum_{x_3}[R_3]$. In the innermost sum, $\theta_3$ is fixed because it depends only on
$x_0,x_1,x_2$. So the count of good $x_3$ is exactly $\rho(B_3)\,13!$: by Lemma 2(a) if $D\neq0$ (any target), and by definition if $D=0$
(then the target $\theta_3D=0$). Work outwards in the same way. $\square$

This is how the **chaining** is handled. A row's turn amount is a function of the rows read before it, so it is a constant when we average over that row's own order, and (0.3) turns "read after rotation" into a shifted target.
Tested: with row sets fixed and shuffling only inside rows, the model agrees with $\prod\rho$ (§2b).

---

## 3. Case A ($\delta$ not constant)

Let $v^\ast$ be a most common $\delta$-value, $n^\ast$ its multiplicity, and $m=52-n^\ast$. Then $4\le n^\ast\le 50$: $n^\ast=51$
is impossible because $\sum\delta=0$. By Lemma 3, $\Pr[\text{survive}]\le \mathbb E\big[\prod_r\rho(B_r)\big]$ over a uniform ordered partition.

**(A1) $n^\ast=50$ (exactly two cards off the majority).** Their values are $v^\ast\pm u$, because the sum is 0. In the same row
(probability $12/51$) they give $\rho=0$ by Lemma 2(c). In different rows, each of those two rows has $D=\pm u\ne0$ (so $\rho=1/13$), and the other rows
are constant. So $\Pr\le\frac{39}{51}\cdot\frac1{169}=\frac1{221}$. This equals the known same-suit swap value exactly.

**(A2) $9\le n^\ast\le 49$.** Let $z_r$ be the number of $v^\ast$-cards in row $r$. If $1\le z_r\le 12$, the row is not constant, and Lemma 2(b) with
$v=v^\ast$ gives $\rho(B_r)\le 1/(z_r+1)$. If $z_r\in\{0,13\}$, use the trivial bound 1. With $h(z)=1/(z+1)$ for $z\le12$ and $h(13)=1$:
$$\Pr\le E_A(n^\ast):=\sum_{z_0+\dots+z_3=n^\ast}\frac{\prod_r\binom{13}{z_r}}{\binom{52}{n^\ast}}\prod_r h(z_r).$$
The seats of the $v^\ast$-cards form a uniform $n^\ast$-subset, so $(z_r)$ is multivariate hypergeometric. This sum depends only on $n^\ast$. Evaluated
exactly (`alt_analytic_bigm_output.txt`):

| $n^\ast$ | 9 | 10 | 12 | 13 | 20 | 26 | 39 | 45 | 48 | 49 |
|---|---|---|---|---|---|---|---|---|---|---|
| $E_A$ | 0.012651 | 0.009204 | 0.005169 | 0.003975 | 0.000899 | 0.000349 | 0.000133 | 0.000558 | 0.003437 | 0.008416 |

The maximum over $9\le n^\ast\le 49$ is $0.012651$, at $n^\ast=9$. (At $n^\ast=49$, which covers the 3-cycles, the value $0.008416$ is close to the true
$9/1105=0.008145$.)

**(A3) $4\le n^\ast\le 12$ (high entropy).** No row can be constant. A row with a repeated $\delta$-value has $\rho\le1/3$ by Lemma 2(b) with its most
common value ($z\ge2$). A row with no repeat holds all 13 values, and this happens with probability
$\prod_v n_v/\binom{52}{13}\le 4^{13}/\binom{52}{13}=1.057\cdot10^{-4}$ (AM–GM on $\sum n_v=52$). So
$\Pr\le 3^{-4}+4\cdot 4^{13}/\binom{52}{13}=0.012768$.

**Case A total:** $\le 0.012768<1/64$. $\square$

How the degenerate cases are handled:
* **Very few changed cards:** (A1), plus the $z$-counting in (A2).
* **Changes that cancel across a whole row:** a row whose cards all have the same $\delta$ gets factor $\rho=1$. The bound never relies on such a row. It only uses rows containing both $v^\ast$-cards and other cards, and a genuine symmetry has no such row.
* **Column 0:** not special (Lemma 2).
* **Chaining:** Lemma 3.
* **Row/column interaction:** irrelevant here, since the columns are dropped.

---

## 4. Case B ($\delta\equiv a$, $\varepsilon$ not constant)

The row stage acts identically on $G$ and $\tau G$. $G\mapsto H=X_4(G)$ is a bijection of grids (`rowsUndo_rowsDone`,
`rowsDone_rowsUndo`), so **$H$ is uniform**, and survival is equivalent to $K_0,\dots,K_{12}$ on $H$.

**Lemma 4 (one column; finite check of 35 multisets × 24 orders).** Let a column have $\varepsilon$-multiset $E$ and a uniform order. Then:

| type | $E$ | $\Sigma(E)$ | law of $V(\varepsilon)$ |
|---|---|---|---|
| Z | constant | 0 | $V=0$ surely (since $1+w+w^2=0$) |
| P | $\{x,x,y,y\}$, $x\ne y$ | 0 | uniform on the 3 nonzero values |
| F | $\{0,1,w,w^2\}$ | 0 | $0$ w.p. $1/2$, each nonzero value $1/6$ |
| U | everything else | $\neq0$ | uniform on GF(4) |

Let $\varphi(E,\sigma)=\Pr[V(\varepsilon)=\sigma]$ for a target $\sigma$. Then $\varphi(Z,\sigma)=[\sigma=0]$,
$\varphi(P,\sigma)=\tfrac13[\sigma\ne0]$, $\varphi(F,0)=\tfrac12$, $\varphi(F,\sigma\ne0)=\tfrac16$, and $\varphi(U,\cdot)=\tfrac14$.

**Lemma 5 (column chain, exact).** Fix the column sets $C_0,\dots,C_{12}$ of $H$. Then
$$\Pr[K_0\wedge\dots\wedge K_{12}\mid\text{column sets}]=\prod_{j=0}^{12}\varphi\big(\varepsilon(C_j),\Sigma(\varepsilon(C_{j+1}))\big)\quad(\text{indices mod }13).$$
*Proof.* The conditions read, in order, $K_1$ (fresh randomness: the order of column 0), $K_2$ (order of column 1), …, $K_{12}$ (column 11), and
$K_0$ (column 12, target $\Sigma(\varepsilon(C_0))$). The rotation $s_j$ applied to column $j$ before it is read depends only on earlier orders and on the
set $C_j$, and a fixed rotation is a bijection on orders. Then nest the sums as in Lemma 3. $\square$

So in Case B the survival probability is **exactly** $\mathbb E[\prod_j\varphi]$, and it depends only on the counts of the four $\varepsilon$-values.
The row/column interaction is fully accounted for: the columns act on $H$, which is uniform.

**Theorem B.** In Case B, $\Pr[\text{survive}]\le 1/425$.

*Proof.* Let $\varepsilon^\ast$ be a most common $\varepsilon$-value, $m'$ the number of cards with $\varepsilon\ne\varepsilon^\ast$, and $y_j$ the number of such
cards in $C_j$. Then $2\le m'\le 39$: $m'\ne1$ because $\sum\varepsilon=0$, and $n_{\varepsilon^\ast}\ge13$. By Lemma 4, $\varphi\le f(y_j,y_{j+1})$, where:
* $f(0,y')=[y'\ne1]$: a column with no off cards is Z, so it needs $\Sigma(C_{j+1})=0$, and a column with exactly one off card is U;
* $f(1,\cdot)=\tfrac14$ (U), $f(2,\cdot)=\tfrac13$ (P or U), $f(3,\cdot)=\tfrac12$ (F or U), and $f(4,\cdot)=1$.

This is checked over all $4^4\times4^4\times4$ cases (§6).
* *$m'=2$:* the two off cards have equal value (the sum is 0). In one column they form P, which is followed by a no-off column with $\Sigma=0$, so $\varphi=0$. In two columns, each is U, so each must be preceded by the other's column, which would need $2\equiv0\pmod{13}$. **Survival is impossible.** This covers every same-rank swap, also when composed with a symmetry (0 in 400k model decks).
* *$m'\ge3$:* $(y_j)$ is multivariate hypergeometric. $\mathbb E[\prod_j f(y_j,y_{j+1})]$ is computed exactly by a 13-step transfer matrix over (cards left, $y_{\rm first}$, $y_{\rm prev}$), one run per value of $m'$ (`caseB_analytic_output.txt`). The maximum is $1/425$ at $m'=3$; the values are $1.4\cdot10^{-3}$ at $m'=4$, $\le 5.5\cdot10^{-4}$ for $5\le m'\le 39$, and $\le 3\cdot10^{-5}$ for $10\le m'\le 29$. $\square$

**Why the suit side is easy.** A naive estimate treats each column equation as worth only about 1/4, so three independent ones
would be needed. The cyclic chain is much stronger than that. A Z column followed by a U column is fatal, so the off-majority cards must cluster
into runs that start with a P or F column. That clustering is rare.

---

## 5. Main theorem

By (0.1), every $\tau\notin\mathrm{v10Sym}$ is in Case A or Case B. So
$\Pr[\text{survive}]\le\max(0.012768,\,1/425)=0.012768<1/78.3<1/64$. Multiply by $52!$. $\blacksquare$

### 5b. Corollary: the exact supremum is 9/1105

**Corollary.** $\max_{\tau\notin\mathrm{v10Sym}}\Pr[\text{survive}]=9/1105\approx1/122.8$. It is attained by every same-suit 3-cycle.

This uses the computer-checked Lemma R of §8 ($p_0\le1/11$ for every nonconstant row with $D=0$), but only in the first regime below. The theorem above does not need it.

*Proof.* Case B gives $\le1/425<9/1105$ (Theorem B). In Case A, split by $n^\ast$:
* $n^\ast\le12$: all four rows are nonconstant, so by Lemma 2(a) and Lemma R every $\rho(B_r)\le1/11$, and $\Pr\le11^{-4}$.
* $13\le n^\ast\le48$: $\Pr\le E_A(n^\ast)\le E_A(13)=0.003975$ (the maximum of the exact values over this range is at $n^\ast=13$; see §7 of the output).
* $n^\ast=49$: normalise $v^\ast=0$ by composing with a rank-shift symmetry. The three off values $a,b,c$ are nonzero with $a+b+c=0$. Up to scaling by units there are 3 classes, $(1,1,11)$, $(1,2,10)$ and $(1,3,9)$. For each class the exact row-only probability $\mathbb E[\prod_r\rho(B_r)]$ (Lemma 3; exact enumeration over which rows the 3 cards fall in, with $\rho$ computed exactly) is **exactly $9/1105$**. Full survival is at most row-only survival.
* $n^\ast=50$: exactly $1/221$ (A1).

Every regime except $n^\ast=49$ is strictly below $9/1105$. A same-suit 3-cycle has $\varepsilon\equiv0$, so every column condition holds and full survival equals row-only survival, $9/1105$. $\square$

(Checked: `verify_output.txt` §7.)

---

## 6. What was checked numerically (`verify_proof.py` → `verify_output.txt`, about 110 s, 0 failures)

0. `model.py` equals `sbox.c` (the verified model) on 3000 grids, all 17 amounts included. The inverse row stage inverts the row stage, and v10Sym survives.
1. Lemma 1 / Corollary 1: survival ⇔ equal amounts ⇔ the 17 trajectory conditions, on 10,500 decks (1,902 surviving, including planted ones). Identity (0.3) holds on 3000 random rows.
2. Lemma 2, three independent checks:
   * **Exhaustive for $p=13$:** every nonconstant 13-multiset of $\mathbb Z_{13}$ (33,429 affine classes; all three statements are invariant under $v\mapsto mv+t$). For each class, the exact distribution of $S$ over all arrangements by DP (`p0scan.c`) shows:
     * (a) exact uniformity when $D\neq0$;
     * (b) $\max_c\Pr[S=c]\le1/(z_v+1)$ for **every** value $v$ occurring in the multiset (226,002 checks);
     * (c) no cancelling-pair row ever passes.
   * **Brute force for the prime analogues $p=5,7$:** all multisets × all arrangements.
   * **Independent Python DP:** 300 random 13-rows.

   Lemma 3 was tested against the model with fixed row sets and shuffling inside rows. The 3-cycle cards were placed so that the predicted value is large ($1/11$, $1/169$, $1/2197$; 131 to 5,521 hits per placement), and so that the rows with $D\neq0$ sit downstream of rows whose order sets their target $\theta_rD$. All $|z|\le1.6$.
3. Case A:
   * **Main route (§3c of the output).** The per-partition inequalities behind (A2) ($\prod\rho\le\prod h(z^\ast_r)$) and (A3) ($\prod\rho\le1/81$ when every row repeats a value) were checked on random partitions for six τ, with $n^\ast$ from 4 to 49. The full-model survival of 11 concrete τ is at most the main-route bound for their $n^\ast$.
   * **Section 3 of the output** checks the side route of §8.
   * The exact row-only formula $\mathbb E[\prod\rho]$ reproduces the exact values in `../../analysis/v10-sumranks/README.md`: **9/1105** (same-suit 3-cycle), **1/221** (swap), **761/270725** (4-cycle), **621/270725** (equal-gap double swap). It matches model Monte Carlo on seven classes, and full survival ≤ row-only ≤ bound. The partition facts behind the constants were checked by brute force over all partitions of 52.
4. Case B: Lemma 4's table (all 35 multisets). The transfer matrix matches the model on six rank-preserving classes and reproduces `sbox-search/exact.py` (**1/850**, **3/20825**, 0). Lemma 5 was tested with fixed column sets. The bound $\varphi\le f$ was checked on all cases.
5. The one-parameter tables for (A2), (A3) and Theorem B.
6. The full model on 43 more non-symmetry τ: the maximum observed is 0.0082 < 1/64.
7. Corollary 5b (§7 of the output): all three $n^\ast=49$ classes give exactly $9/1105$, and $\max_{13\le n^\ast\le48}E_A=E_A(13)$.

The Case B scan's maximum is also reported restricted to count vectors compatible with $\sum\varepsilon=0$ (§8).

---

## 7. Remarks on the route

* **Case split.** The split is "δ constant or not", not "some rank changes or not". This is needed so that rank-shift∘suit-map differences land in the suit case.
* **Exact conditioning instead of a switching approximation.** Conditioning on the row sets (or column sets) and nesting the sums turns the chained process into an **exact** product formula. Switching (Lemma 2(b)) is used only inside a single row.
* **Two independent rank constraints.** This is where the needed factor comes from. A nonconstant row gives at most $1/(z+1)$, where $z$ is the size of the majority class inside the row, and it gives exactly $1/13$ when the row's change-sum is nonzero. The averaging over where the majority cards fall is an exact one-parameter hypergeometric sum. High-entropy δ (every value used by at most 12 cards) is handled by pigeonhole.
* **Suit case.** It needs no "three independent 1/4 constraints". The chain structure gives $\le1/425$.

Nothing failed. No τ class is left open.

---

## 8. Sharper, computer-assisted side results (not needed above)

* **Row lemma R.** For every nonconstant 13-multiset of $\mathbb Z_{13}$ with $D=0$, $\Pr[S=0]\le 1/11$. Equality holds for $\{0^{10},a,b,-a-b\}$ and $\{0^9,1,1,-1,-1\}$ types, and every class with majority $\le8$ is $\le 1/12.69$. This was checked exhaustively over all 33,429 affine classes (`p0scan.c`, 6 s). Using it instead of (A2)/(A3) gives the bound $(10q_m+1)/121\le0.01254$ with $q_m=4\binom{13}{m}/\binom{52}{m}$ for $3\le m\le12$, and $\le0.0106$ for $m\ge13$.
* **Exact Case B.** The exact Case B probability for all 1284 sorted $\varepsilon$-count vectors (the scan also includes vectors that no τ can produce: $\sum\varepsilon=0$ forces the number of odd counts to be 0 or 4. The listed argmax $(49,3,0,0)$ is one of these. This is harmless, since over-covering only weakens a maximum. Restricted to the 374 compatible vectors, the maximum is the same $1/850$, at $(49,1,1,1)$) (`caseB_tm.c`, double precision, all values far from the threshold): the maximum is **exactly 1/850** (the same-rank 3-cycle). It is $\le 2.4\cdot10^{-5}$ once $m'\ge5$ and about $1.49\cdot10^{-8}$ for balanced ε. An independent **computer-free** bound for $m'\ge20$ is $\beta^{m'}\,\mathbb E[\beta^{-4z_4}]$ with $\beta=2^{-1/3}$, where $z_4$ counts constant off-majority columns (§4 of the output).

---

## 9. Lean formalisation

The $52!/64$ bound (not the constant $0.012768$, and not the corollary $9/1105$ of §5b) is formalised in
`../DoubleDealSecurity/SumRanksDP/` (Lean 4.14 + Mathlib, part of the default `DoubleDealSecurity` build):

```lean
theorem sumRanksV10_survival_le (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    64 * (survivors τ).card ≤ Fintype.card (Equiv.Perm (Fin 52))
```

`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. The lemma map is `../SUMRANKS_DP.md`.
The Lean route follows §§0–5 with two changes:

* **Case A** splits as $n^\ast\le12$ ((A3), the constant $0.012768$), $13\le n^\ast\le49$ ((A2), with the
  coarser table bound $E_A\le1/100$) and $n^\ast=50$ ((A1), $1/221$).
* **Case B** uses the column conditions alone, with the refinement $f(2,0)=1/4$, and proves only
  $E_B(m')\le1/64$ for $2\le m'\le39$ (maximum $E_B(2)=1/68$), not the paper's $1/425$.

The tables are checked in the kernel with `decide!` (no `native_decide`). The sharper side results of §8
are not formalised.
