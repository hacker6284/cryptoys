# ECBS: second-opinion math review

> **Landing note (2026-10-04).** `mr_q13.py`, `mr_q13_validation.py` and `mr_invalid_trace.py` were removed when `ecbs.sudo` landed: they modelled the card's own schedules (the register-machine mixed add, Itoh–Tsujii, the chord add, the trace chain) by hand, and the repository keeps no hand-written ECBS implementation. Their `*_results.txt` stay here as the record. The other `mr_*` scripts are curve, field and entropy analysis and stay runnable. The review text below is unchanged.

Reviewer: Mathematician (executor subagent), for Zachary Mills, at the Crypto agent's request. Date: 2026-09-30.

Inputs, all read-only and untouched: `kx-specs/ECBS_MATH_REVIEW.md` (C1–C24, Q1–Q13), `kx-specs/ECBS_SPEC.md` and `kx-specs/ecbs/`.
All my work is in `proofs/key_exchange/ecbs/review/`. Python is `python` (cypari2, python-flint, sympy). The C programs were compiled with gcc -O3 -fopenmp.

**Tags used below**
- **[proved]**: the proof is given here.
- **[computed]**: exact computation; the script and log are named (all listed in §5).
- **[MC]**: Monte-Carlo estimate.
- **[lit]**: from the literature. I only cite work I believe exists, and mark it "I believe" where I am unsure of details.
- **[heuristic]**: a standard model or an argument that is not a proof.

---

## 0. Executive summary

Items are ordered with the ones that break or weaken a claim first.

1. **Three-state keys are provably much weaker than the spec's upper bounds (C7, Q1, Q6). The three-state option should be dropped in every tier.** [computed, rigorous: exact counts; `mr_fleets.c`, `mr_pairs.py`]
   - *Construction.* Pair two grids. The second grid carries the translate of the first grid's pattern by the cell shift δ that maps it onto the same residues (δ ≡ 100·Δg mod n). The pair gets opposite signs, so it contributes 0 to k. In one pair, a single cell has equal signs, which makes k = 2λ^{r0} deterministic and nonzero.
   - Exact sums of M(T)² over the exhaustively computed multiplicities give these bounds:

   | Tier / option | Spec upper bound on H∞ | **This review: H∞(k) ≤** | Target (2·rho) |
   |---|---|---|---|
   | Serious, 6 fleets | 225.48 | **169.93** | 273.55 |
   | Serious, 7 fleets | 260.04 | **207.01** | 273.55 (and < 256) |
   | Hobby, 2 fleets | 74.35 | **57.96** | 84.96 |
   | Hobby, 3 fleets | – | 100.69 | 84.96 |
   | Toy, 1 fleet | none (34.13 cap) | **25.06** (exact max over the natural family) | 29.26 |

   - So 6 and 7 fleets are both provably below 256, and Toy and Hobby (2 fleets) are provably below their curve-matching targets. The re-roll on exceptional walks changes these bounds by a negligible amount: MC over the construction found 3/200 rejected walks at Hobby 2 fleets and 0/200 elsewhere [MC].
2. **The twists and the "invalid" F_3-curves are weak. The spec's C1/C12 twist text is stale.** [computed: `mr_factor_bg.py`, `mr_factor_check.py`; proved: which points pass the trace check; computed: `mr_invalid_trace.py`]
   - The Serious quadratic twist factors completely: 3·1433·160881263·76235720288049653·8922179461560676120351·p115. Rho on it costs ≈ 2^57.7. The "245-bit composite cofactor" in C1 should be replaced by this factorisation.
   - The Hobby twist's largest prime has 39 bits.
   - This does **not** break ECBS, because ECBS sends y and requires the on-curve check. But if the on-curve check is skipped:
     - The node (b′=0) passes the trace check on its odd part [proved + computed]. At Serious that part is 3755779·47029186391731·9248363581047133·p161, so Pohlig–Hellman leaks **k mod a 120.3-bit number for ≈ 2^27 work**. At Hobby, the node DLP costs ≈ 2^40 in total.
     - E′ (b′=2) leaks a further 43.9 bits at Serious. At Hobby its odd part is **fully smooth** (largest prime 28 bits), which means full key recovery in ≈ 2^14.
   - So the on-curve check is load-bearing, and **an x-only variant must never be introduced**.
3. **Lemma A's exact threshold is n−3, not "≤ 175" (C4, C5, C6, Q2).** [computed: `mr_lemmaA.py`; the relation at n−2 is proved]
   - Pegs-only is injective iff m ≤ n−3: Serious 176 cells, H∞ = **278.95** exactly; Hobby 56 (88.76); Toy 20 (31.70); Demo 4 (6.34).
   - At m = n−2 the relation 2λ^{n−3} = Σ_{e<n−3} λ^e always holds [proved].
   - The 200-cell and six-state lower bounds therefore rise to **≥ 278.95**.
   - I checked the proof of C4 line by line. It is correct.
4. **Frobenius-aware key search gains at most about half a bit on the recommended key sets (Q3).** [computed, exact in the rotation model: `mr_frob.py`]
   - Serious m = 173: E[c] = 2.23, so the saving is ≤ 2^0.58. At m = 176 it is ≤ 2^1.53.
   - The ≈ 273.6 curve-matching target stands. **Pegs-only with 173 cells (H∞ = 274.20) matches rho**: the best structured key search I can model costs ≥ 2^137.2 against rho's 2^136.78.
   - A rigorous generic-group-model bound that includes free ±Frobenius is 2^{(H∞ − log₂2n)/2}, about 2^133 at m = 173 (§2, Q1).
5. **The Kohel–Shparlinski constant for this curve is 3√q, not 4√q (C19, Q11a).** [proved via Weil/Deligne and Grothendieck–Ogg–Shafarevich; computed: `mr_ks.py`]
   - The SD bounds improve by 0.415 bits, but the largest m is unchanged: 94 trits at SD ≤ 2^−64 and 13 at 2^−128 [computed: `mr_extractor_recalc.py`].
   - Only the "uniform-K model" claim is defensible (Q11c).
6. **The 7-fleet option is now provably short of 256**, since H∞ ≤ 207.01 (see item 1). The lower bound in the three-state gap was not improved: it is still ≈ 77 [MC]. The honest status is therefore **[≈77 (MC), 169.93 (rigorous)]**.
7. **Q13: neither 9 walk bands nor 8 validation bands is minimal. Both phases fit in 7 bands.** [computed: `mr_q13.py`, `mr_q13_validation.py`; the machine reproduces the spec's 9 and 8 exactly]
   - The walk uses a new "F-form" addition verse with the same 12 multiplies. It was checked 20/20 against the affine chord rule at n = 179.
   - Validation reaches 7 by forming the second point's y only after the inversion.
   - I have no proof that 7 is minimal, and I did not re-run `ecbs_budget` to obtain the grid count.
8. **Q7 is closed: 72 is the global maximum multiplicity.** [computed, exhaustive over all 30,093,975,536 labelled fleets: `mr_fleets.c`]
   - C9's MC figures are now exact: 1.365901·10¹⁰ = 2^33.669 distinct patterns, and Shannon entropy 33.6048 bits [`mr_fleets2.c`].
9. **Independent recomputation agrees with the spec on the core curve data (C1–C3, C11, C16, C22).** [computed: `mr_orders.py`, `mr_c22.py`]
   - Group orders #E = 5·ℓ for all four tiers, with ℓ prime (FLINT proving test, PARI APR-CL and BPSW).
   - ℓ−1 factorisations, embedding degrees, λ, ordinarity, non-anomaly and the family scan {2, 7, 23, 59, 179}.
   - Base points and test vectors (Demo and Toy exact; Hobby and Serious digests match).
   - The normal-basis types and the "single-peg cube" counts.

**Recommendation for Q1.** Use **pegs-only with 173 cells** at Serious: H∞ = 274.20 exactly, 44.2 M moves.
- The distribution is flat and the map is injective, so min-entropy, Shannon entropy and guesswork all agree. The number is unambiguous.
- Up to 176 cells stays exact (278.95), if a margin is wanted.
- For a "128-bit headline", 162 cells gives exactly 256.76.
- Three-state cannot reach either target, even in principle, under the min-entropy yardstick (item 1).
- No recipe change is needed. This is already one of the spec's own options, so it is hand-performable by construction.

---

## 1. Independent recomputation of group orders, twists and embedding degrees

**Method** [computed: `mr_orders.py` → `mr_orders_results.txt`]
- E: y² = x³ + 2x² + 1 over F_3 has 5 points: O, (0,1), (0,2), (1,1) and (1,2). So t = −1, Frobenius satisfies τ² + τ + 3 = 0, and V_n = α^n + ᾱ^n.
- I computed V_n three independent ways:
  - as the exact trace of τ^n in Z[τ];
  - by the recurrence V_n = −V_{n−1} − 3V_{n−2};
  - by brute-force point counting for n = 1..11. The twist was brute-forced at odd n ≤ 9.
- Then #E(F_{3^n}) = 3^n + 1 − V_n.

**Results**

| Tier | n | V_n | #E = 5·ℓ | log₂ℓ | ℓ−1 | ord_ℓ(q) = k | (ℓ−1)/k |
|---|---|---|---|---|---|---|---|
| Demo | 7 | 83 | 5·421 | 8.72 | 2²·3·5·7 | 15 | 28 |
| Toy | 23 | 268133 | 5·18828582139 | 34.13 | 2·3³·23·67·226267 | 818634006 (2^29.61) | 23 |
| Hobby | 59 | −237742473477667 | 5·ℓ₅₉ | 91.19 | 2·3³·41·59·1759·12107·1015902464920517 | 2^83.72 | 177 |
| Serious | 179 | 8415761749837…0333 | 5·ℓ₁₇₉ | 281.39 | 2·3²·47·179·10125222756042811·703353447714603929148486975269·4709046612308978229431976119158651 | 2^273.90 | 179 |

- Every ℓ, and every prime factor of ℓ−1, is proved prime by FLINT's proving test and by PARI APR-CL; sympy BPSW agrees.
- 25 ∤ #E in every tier, and ℓ ≠ 3, 5.
- The family scan over prime n < 200 for #E = 5·prime gives exactly {2, 7, 23, 59, 179}.

**Ordinary** [proved]
- V_n ≡ V_1^n = (−1)^n (mod 3), because α + ᾱ = t and αᾱ = 3 (Newton's identities mod 3). So 3 ∤ V_n, and E/F_{3^n} is ordinary for every n.
- Cross-check: in characteristic 3 with a1 = a3 = a4 = 0, Δ = −a2³a6 and j = −a2³/a6 = 1 ≠ 0. Supersingular in characteristic 3 is equivalent to j = 0 [lit, standard; Silverman AEC V.4, I believe].

**Not anomalous, and ℓ ≠ 3** [proved] #E ≡ 1 − V_n ≡ 1 − (−1)^n = 2 (mod 3) for odd n, so #E ≠ q and 3 ∤ #E. Smart's anomalous attack and its relatives do not apply.

**MOV / Frey–Rück** [computed] The embedding degree is huge except at Demo, where k = 15 (Demo is a toy anyway).

**λ** [computed]
- x² + x + 3 has two roots mod ℓ, and exactly one, λ, satisfies λ^n = 1. The other root is λ̄ = 3/λ.
- ord_ℓ(3) ∤ n, so λ̄ ∉ ⟨λ⟩ (C2).
- τP = λP was checked on the rule-derived base points.

**Twists and invalid F_3-curves** [computed: `mr_factor_bg.py` and `mr_factor_check.py`, every factor proved prime by APR-CL, products checked]

The quadratic twist is y² = x³ + x² + 2 (a2 → −a2, a6 → −a6; −1 is a non-square since q ≡ 3 mod 4). Its order is q + 1 + V_n. The curve with b′ = 2, y² = x³ + 2x² + 2 (trace +2 over F_3, the E′ of C12), is **not** the twist. The node is b′ = 0.

| Tier | Twist order | E′ (b′=2) order | Node, q+1 |
|---|---|---|---|
| Demo | 3·757 | 2·1051 | 2²·547 |
| Toy | 3·47²·14206043 | 2·47071896187 | 2²·23535794707 |
| Hobby | 3·6373·6491·173829577·655018509997 (max 39.3 bits) | 2·16993·3770219·312996889·352328177 (max 28.4 bits) | 2²·3187·p80 |
| Serious | 3·1433·160881263·76235720288049653·8922179461560676120351·p115 | 2·16859153558033·p239 | 2²·3755779·47029186391731·9248363581047133·p161 |

Here pX is a proved prime of X bits.

---

## 2. Answers to the questions

### Q1. Honest security per unit of hand work, and the right yardstick

**Answer.** Pegs-only with 173 cells at Serious (162 if the goal is the 128-bit headline). Three-state is out.

1. **Why min-entropy, and how to pair it with the attack.**
   - For a *flat* key set (pegs-only: uniform on an injective image of {0,1,2}^m), min-entropy, Shannon entropy and log-guesswork coincide exactly. The choice of measure only matters for non-flat encodings such as three-state.
   - For those, min-entropy is the only measure that yields a *security bound*.
     - Generic-group-model sketch [proved in the GGM; this is the standard Shoup-style collision argument (Shoup, Eurocrypt 1997), specialised by me to a non-uniform exponent]. Every handle is a + bk. A collision between two distinct linear forms pins k to at most one value, which has probability ≤ 2^{−H∞}. So T group operations succeed with probability ≤ (T²/2 + 1)·2^{−H∞}.
     - With ±Frobenius free (each handle then stands for a 2n-orbit), this becomes ≤ (2n·T²/2 + 1)·2^{−H∞}. Hence T ≳ 2^{(H∞ − log₂2n)/2}.
     - At m = 173 that is ≈ 2^132.9. For uniform k the same bound gives 2^{(log₂ℓ − log₂2n)/2} ≈ 2^136.5, which matches rho.
     - The GGM is a model, and Frobenius is the only non-generic structure I know of here. See Q3 for why real structure-aware search gains far less than this worst case.
   - Guesswork or smooth-entropy measures could credit three-state with more, but nobody has certified them, and an upper bound on H∞ does not upper-bound guesswork.
   - My proposed figure of merit: **the cheapest encoding whose certified min(rho, BSGS-on-the-key-set) meets the target.** For pegs-only, BSGS costs exactly 3^{⌊m/2⌋} + 3^{⌈m/2⌉} group operations, with at most √2 more from negation and at most the Q3 factor from Frobenius. BSGS also needs about 2^137 memory, which makes the comparison conservative.
2. **The numbers** [computed: `mr_frob.py`, `mr_lemmaA.py`, `mr_pairs.py`]

   | Option | Moves (spec) | H∞ | Best modelled key search | vs rho 2^136.78 |
   |---|---|---|---|---|
   | pegs-only 162 | 42.2 M | 256.76 exact | ≥ 2^128.4 (idealised Frobenius) | −8.4 bits (the 128-bit headline) |
   | **pegs-only 173** | **44.2 M** | **274.20 exact** | ≥ 2^137.2 | **matches** |
   | pegs-only 175 | 45.7 M | 277.37 exact | ≥ 2^138.4 | matches |
   | pegs-only 176 | ≈ 46.5 M (my linear extrapolation, not run) | 278.95 exact | ≥ 2^138.5 | matches |
   | 200 cells / six-state | 51.7 M / 64.7 M | ∈ [278.95, 281.39] | – | matches, at +17 % / +46 % moves |
   | three-state, 6 fleets | 42.0 M | ∈ [≈77 MC, **169.93**] | certifiable ≤ 2^85 at best | fails |
   | three-state, 7 fleets | 48.3 M | ∈ [≈87 MC, **207.01**] | certifiable ≤ 2^104 at best | fails |

3. **Is min-entropy the right yardstick for three-state?** It is the right *conservative* yardstick. Even its optimistic end (≤ 170) is now far below both targets, so the question is moot.

### Q2. Lemma A: line-by-line check, and a sharper certificate

**Verdict: the proof is correct.** [proved, checked line by line]
- **Step 1 (rotation):** fine, since λ^n = 1 and λ ≠ 0.
- **Steps 2–3 (the norm bound):**
  - 𝔩 = (ℓ, τ−λ) is a degree-1 prime of O_K = Z[τ]. The discriminant is 1 − 12 = −11, which is squarefree and ≡ 1 mod 4, so Z[τ] is the maximal order.
  - α ↦ α(λ) has kernel 𝔩, so ℓ | N(α).
  - |τ| = √3 in both complex embeddings (complex conjugates), so N(α) = |α|² ≤ B².
- **Step 4 ("Gauss's lemma"):** x² + x + 3 is monic, so plain polynomial division over Z already gives the quotient in Z[x]. Gauss's lemma is not needed, but it is not wrong.
- **Step 5 (the DP):**
  - Completeness: e_p = 3q_p + q_{p−1} + q_{p−2} determines q_p from e_p and the two previous q's, so every multiple is visited.
  - The bound |q| ≤ max D holds by induction: |3q_p| ≤ |e_p| + |q_{p−1}| + |q_{p−2}| ≤ 3·max D.
  - The "lowest coefficient is 3·q_low" remark for D ≤ 2 is valid: at the lowest index, e = 3q_low + 0 + 0.
- **The Corollary (conditioning):** fine.

**Sharper certificate: the exact threshold** [computed: `mr_lemmaA.py` → `mr_lemmaA_results.txt`]
- *Method.* The norm certificate alone stops at m ≤ n−4 (175 at Serious). I replaced it with an exact decision: enumerate all 74 elements α ∈ 𝔩 with N(α) ≤ B_n², and decide for each whether it has a digit representation with |d_e| ≤ 2 on a window of length m, using the DP over α + (x²+x+3)Z[x].
- **Result:** pegs-only is injective iff m ≤ n − 3.
- Cross-checks [computed]:
  - Demo brute force gives a largest injective m of 4.
  - A Toy meet-in-the-middle over [−2,2]^m finds no relation at m = 20 and a relation at m = 21.
- **The relation at m = n − 2** [proved]:
  - λ^n = 1 and λ ≠ 1 (1 + 1 + 3 = 5 ≢ 0 mod ℓ), so Σ_{e=0}^{n−1} λ^e = 0.
  - Multiplying λ² + λ + 3 = 0 by λ^{n−3} gives λ^{n−1} + λ^{n−2} = −3λ^{n−3}.
  - Subtracting gives Σ_{e<n−3} λ^e − 2λ^{n−3} = 0, with digits in [−2, 2] on positions 0..n−3.
  - At m = n−2 this gives a collision (x with x_e = 1 for e < n−3 and x_{n−3} = 0, versus x′ with x′_e = 0 and x′_{n−3} = 2), so H∞ ≤ m·log₂3 − 1 there.
- Exact H∞ at the threshold: **Serious 176 → 278.95; Hobby 56 → 88.76; Toy 20 → 31.70; Demo 4 → 6.34.**
- With |d| ≤ 1 (halved sign sums) the exact threshold is m* = n: every window of length n−1 is certified.
- Consequence for C6: keep one free peg per residue on a window of 176 consecutive residues, which gives H∞ ≥ 176·log₂3 = 278.95 for both 200-cell pegs-only and six-state.

### Q3. Frobenius-aware key search on structured keys

**Answer: no significant speed-up. The ≈ 273.6 target stands, with ≈ 0.5–1.5 bits of slack depending on m.**

*Model* [proved, elementary]
- k = Σ_{e<m} c_e λ^e with c ∈ {0,1,2}^m. Multiplying by λ^i rotates the digit vector cyclically on Z/n.
- The multiplied key lies in the set S (up to the non-rotational coincidences measured below) iff the rotated vector is again supported on the window.
- So the ±τ-class of k meets S in c(k) points, where c(k) = #{i : λ^i k ∈ S} (negation: S is not itself closed under negation, but S − Σ_{e<m}λ^e is the balanced digit set {−1,0,1}^m, which is symmetric; the attacker can recentre with the known point (Σλ^e)P, so the usual √2 of negation applies).
- An ideal class-based search over S costs at least √(|S|·E[1/c]/2) (the number of classes), and the saving over plain BSGS on S is at most √E[c].
- Note that "the key set is closed under λ-multiplication" fails badly for windows: closure would need the window to be all of Z/n.

*Numbers* [computed: `mr_frob.py` → `mr_frob_results.txt`; E[c] exact, confirmed by MC]

| m (Serious) | E[c] | Saving ≤ √E[c] | Saving ≤ √(1/E[1/c]) | BSGS with negation | "Ideal Frobenius" search |
|---|---|---|---|---|---|
| 162 | 2.000 | 2^0.50 | 2^0.30 | 2^128.88 | 2^128.38 |
| 173 | 2.226 | 2^0.58 | 2^0.35 | 2^137.81 | 2^137.23 |
| 175 | 4.086 | 2^1.02 | 2^0.75 | 2^139.39 | 2^138.38 |
| 176 | 8.333 | 2^1.53 | 2^1.37 | 2^139.98 | 2^138.45 |

- E[c] ≈ 2 for m ≪ n because each unit of shift needs one more zero end-digit, so Σ_{j≥1} 2·3^{−j} = 1 on top of i = 0.
- *Model test* [computed]: exhaustively over all 3^m keys at (n, m) = (23, 12), (23, 14), (23, 15) and (59, 10), true membership equals the rotation model for > 99.6 % of keys. The largest excess was 8, and E[c_true] − E[c_rot] ≤ 0.005.
- *Digit alignment.* The window digits *are* τ-adic-like digits (base λ). That alignment is exactly what the rotation model captures, and it gives nothing beyond the numbers above.
- Kangaroo and Gaudry–Schost style algorithms target low-dimensional intervals or boxes in the exponent. A 173-dimensional digit box has no such structure, and I know of no way to use it [heuristic].
- Conclusion: 2·136.78 = 273.55 is the right curve-matching target, and m = 173 (274.20) meets it with the Frobenius loss priced in.

### Q4. Rho convention and target

- √(πℓ/(4n)) is right for classes of size 2n: rho on ℓ/(2n) classes takes √(π(ℓ/2n)/2) steps [heuristic/lit].
- This is the Wiener–Zuccherato (SAC 1998) / Gallant–Lambert–Vanstone (Math. Comp. 2000) speed-up by √(2n) for Koblitz curves. The practical negation-map issues are discussed by Bos–Kleinjung–Lenstra (ANTS 2010), and Duursma–Gaudry–Morain (Asiacrypt 1999) treats automorphism speed-ups [lit, I believe these attributions are right].
- My figures: 2^2.78, 2^14.63, 2^42.48 and 2^136.78 [computed], which agrees with C3.
- Target: my judgement is that "match the curve" (273.55 → 173 cells) is the more defensible choice, because it costs only +2.0 M moves (+4.7 %) over 162 cells. 256 is fine if the headline is "128-bit" and the curve is knowingly oversized.

### Q5. Descent, index calculus, twists, invalid curves and the cofactor

1. **Subfield / GHS / Weil descent.**
   - n = 179 is prime, so F_{3^179} has no subfields other than F_3.
   - E is defined over F_3. Weil restriction to F_3 splits, up to isogeny, as E × T, where T is the 178-dimensional trace-zero variety, and the ℓ-part lives in T [proved: ℓ ∤ #E(F_3) = 5].
   - GHS descent from F_{3^179} to F_3 of a curve with coefficients already in F_3 has "magic number" 1 and gives back genus 1, i.e. nothing [lit: Gaudry–Hess–Smart, J. Cryptology 2002, for char 2; Diem, the odd-characteristic GHS attack, 2003, I believe; the magic-number reasoning is my own application].
   - I know of no cover or descent that reaches T with a curve of small genus [heuristic].
2. **Summation polynomials / index calculus.**
   - Semaev (ePrint 2004/031) introduced summation polynomials.
   - Gaudry (J. Symbolic Comput. 2009) and Diem (Compositio 2011) give sub-rho algorithms in the regime where q grows with the extension degree bounded or slowly growing. Here q = 3 is fixed and n → ∞, the opposite regime.
   - Joux–Vitse (Eurocrypt 2012 and the J. Cryptology follow-up, I believe) handle small extension degrees (≤ 6) over large q, which is not applicable.
   - For prime-degree extensions of *small* fields, Petit–Quisquater (Asiacrypt 2012, binary fields) claimed subexponential complexity under the "first fall degree" assumption. Huang–Kosters–Yeo (Crypto 2015) and later experiments cast serious doubt on it, and the Galbraith–Gaudry survey (Des. Codes Cryptogr. 2016) concludes that there is no practical threat to prime-degree binary fields [lit, I believe].
   - **I know of no characteristic-3 analysis at all [unverified].** A Petit–Quisquater-style F_3-subspace factor base would inherit the same unproven assumption.
   - Status: open in the same sense as the binary Koblitz curves over prime-degree fields, with no known attack beating rho [lit/heuristic].
3. **MOV / FR:** embedding degree 2^273.9, so ruled out [computed]. **Anomalous / Smart:** ruled out [proved, §1]. **Ordinary:** proved in §1, which confirms the a2 ≠ 0 expectation.
4. **Twist security:** the Serious twist is weak (rho ≈ 2^57.7) and the Hobby twist very weak (≈ 2^19.6) [computed]. This is irrelevant as long as points are sent with y and checked on-curve. **Never adopt x-only arithmetic or x-only transmission.**
5. **Invalid-curve attacks** (the formulas never use b).
   - Node, b′=0 [proved]:
     - The torus parameter is u = (y + √2x)/(y − √2x) ∈ ker(N: F_{q²}* → F_q*), and √2 ∉ F_q since n is odd.
     - (√2)³ = 2√2 = −√2 gives u(τP) = u(P)^{−3}.
     - So the trace is u^{Σ(−3)^i} = u^{(q+1)/4}, and exactly the odd part (index 4) passes.
   - E′, b′=2 [proved]: exactly the odd part (index 2) passes (C12).
   - Both behaviours were confirmed by running the spec-transcribed trace chain: 4/4 cofactor-cleared points accepted in every tier, and raw points accepted at about 1/4 and 1/2 respectively [computed: `mr_invalid_trace.py`].
   - Leak sizes are in the executive summary (item 2).
   - For b′ ∉ F_3, Frobenius moves the point to the curve with b′³, and the trace comparison should essentially never succeed [heuristic].
   - **The on-curve check is mandatory, and the spec correctly requires it.**
6. **Cofactor 5:** E(F_q) is cyclic of order 5ℓ, and B + T with T ∈ E[5]∖{O} is rejected because nT ≠ O (5 ∤ n) [proved; computed: B + T5 is rejected in all tiers by both the spec schedule and my 7-band schedule].

### Q6 and the three-state gap: can either side be tightened?

- **Upper side: tightened substantially** [computed, rigorous]. See executive summary item 1 and `mr_pairs_results.txt`.
  - The Serious 6-fleet bound uses pairs (0,5) with δ = −37 (boxes 6×7 and 7×3), and (1,3), (2,4) with δ = +21 (box 8×9). Each δ = 21 pair costs 2^−53.79 to cancel and 2^−56.87 as the special pair.
  - *Proof of the bound.* For a pair, Pr[union(g′) = T, union(g) = T + δ] = (M(T)/N_LAB)², because M is translation-invariant and the fleets are independent and uniform over labelled fleets [C9, re-verified]. Opposite signs have probability 2^−17. The pairs are independent, so the product of Σ_T M(T)²/N_LAB² · 2^−17 (with one c0-restricted "special" factor) is a lower bound on Pr[k = 2λ^{r0}].
  - The (h, w)-box sums of M and M² are exact [computed, `mr_fleets.c`].
  - C7's "aligned heavy key" is therefore **not** near the most likely scalar: cancellation beats alignment by ≥ 55 bits. Further optimisation (residue collisions across pairs, other δ) would likely gain a few more bits. I did not pursue it.
- **Lower side: not improved.** The MC figure (≈ 77.4) is a sample average over layouts of a rigorous per-layout bound, and the worst layout is unknown.
  - A rigorous lower bound would have to control layouts where several fleets pile onto few residues.
  - Since even the upper bound (169.93) fails the target, closing the gap would not change the recommendation, so I stopped here.
- **Toy exact** [computed]: over all labelled fleets, max_{r0} Pr[c = e_{r0}] = 2.8499·10⁻⁸ = 2^−25.06, attained at r0 = 3 and 4.
  - k = λ^{r0} requires every residue to have sign-sum 0 except r0, which has sum 1.
  - This is a rigorous H∞ ≤ 25.06 < 29.26.
  - Even if half of those walks were re-rolled, it would cost ≤ 1 bit, so the conclusion is robust.

### Q7. Pattern multiplicity

- **72 is the global maximum** [computed, exhaustive, `mr_fleets.c`, 8m40s on 8 cores]. It is attained by 864 anchored labelled fleets, i.e. 12 anchored patterns (for example, row 0 columns 0–8 plus column 8 or column 0 of rows 1–8).
- The histogram of multiplicities is in `mr_fleets_results.txt`; all multiplicities are even, because the two 3-ships are interchangeable.
- So the single-fleet H∞ ≤ 45.64 (C10) is exact for the pattern alone: log₂(N_LAB/72).

### Q8. Trace check vs cofactor clearing; leaks from "reject on exceptional case"

- Validation touches only the public B, so which step rejects leaks nothing secret [proved].
- In the key walks, the exceptional condition (running scalar s with λs ≡ ±1, and the like) is a congruence on the *scalar* alone. It is therefore the same for a·P and a·B whenever B has order ℓ [proved: the walk's intermediate points are s_i·B, so equality between two of them is a scalar congruence mod ℓ].
- So a key that passed its re-roll at generation never meets an exceptional case in the shared-secret walk, and the re-roll only conditions the key distribution. The cost of that is negligible (Q6).

### Q9. The node

- If the on-curve check is skipped, the problem is already practical before any torus DLP: at Serious, Pohlig–Hellman gets k mod (3755779·47029186391731·9248363581047133), i.e. 120.3 bits, for ≈ 2^27 [computed + proved]. At Hobby the whole node DLP is ≈ 2^40 by rho [computed].
- The remaining p161 factor lives in F_{3^358}^* (567 bits, characteristic 3). Small-characteristic DLP is quasi-polynomial in favourable representations (Barbulescu–Gaudry–Joux–Thomé, Eurocrypt 2014), and characteristic-3 records exist (Adj–Menezes–Oliveira–Rodríguez-Henríquez and co-authors, 2014–2016, I believe).
- I believe F_{3^358} is within reach of an academic computation, but that is **unverified**, since 358 = 2·179 is not a convenient shape.
- Either way the on-curve check closes the hole.

### Q10. Twisted bases

**Answer: no Lemma-A analogue without extra restrictions.**
- [proved] λ̄ = −1 − λ, so λ̄^g λ^r + λ̄^g λ^{r+1} + λ̄^{g+1} λ^r = 0.
- Hence any three ship cells at (base g, exponent r), (g, r+1) and (g+1, r) that carry *equal* signs can all be flipped without changing k. This is an exact alias, and it happens with positive probability.
- The norm bound itself generalises (|τ̄| = √3, weight 3^{(g+r)/2}), but β = 0 in O_K has non-trivial solutions from 1 + τ + τ̄ = 0.
- Any certificate would have to exclude such triples. Recommendation: keep the untwisted bases.

### Q11. Key extraction

- **(a) The constant is 3√q, O excluded, for any subgroup** [proved].
  - Fix a nontrivial additive character ψ of F_q and a character χ of E(F_q). The sum Σ_{P≠O} χ(P)ψ(x(P)) is the trace of Frobenius on H¹_c of the lisse sheaf L_χ ⊗ L_ψ(x) on E∖{O}.
  - Its Swan conductor at O is 2, because the pole order of x is 2 and 3 ∤ 2. L_χ is tame (in fact lisse on E). The Euler characteristic of E∖{O} is −1.
  - Grothendieck–Ogg–Shafarevich gives χ_c = −1 − 2 = −3, and H⁰_c = H²_c = 0.
  - Weil II (Deligne) gives weights ≤ 1, so |sum| ≤ 3√q.
  - A subgroup sum is an average over the five characters χ trivial on ⟨P⟩, so it is also ≤ 3√q. That gives δ ≤ 3√q/(ℓ−1).
  - Including O adds at most 1.
  - [lit] Kohel–Shparlinski's 2·deg(f)·√q = 4√q is a valid but weaker bound (as I recall their result).
  - Computed maxima [`mr_ks.py`]:
    - n = 7: 2.8991√q over *all* (χ, ψ); 2.2545√q for the whole group; 1.4074√q for the order-421 subgroup;
    - n = 9, 11, 13: 2.5246√q, 2.9121√q and 2.8539√q for the whole group.
  - All are below 3√q, and the n = 11 value comes within 3 % of it, so the constant 3 cannot be improved in general.
  - New SD numbers [computed: `mr_extractor_recalc.py`]: Serious m = 100 → 2^−59.70; 94 → 2^−64.45; 80 → 2^−75.55; 60 → 2^−91.40. **The largest m is still 94 (at 2^−64) and 13 (at 2^−128).** Hobby m = 40 → 2^−12.15; Toy m = 16 → 2^−2.64.
- **(b) The XOR lemma is stated correctly** [proved, standard]:
  - SD ≤ ½·‖p − u‖₁ ≤ ½·√(3^m)·‖p − u‖₂.
  - By Parseval over F_3^m, ‖p − u‖₂² = 3^{−m}·Σ_{a≠0} |E ω^{a·Z}|².
  - The fold is surjective and F_3-linear, so each a·Z is a nonzero F_3-linear functional of x(K).
  - The fibre bound 2·3^{n−m}/(ℓ−1) is right, since x is 2-to-1 on ⟨P⟩∖{O}.
- **(c) The model: claim only the "uniform-K model".**
  - For structured a, b (H∞ < log₂ℓ), a DDH-type statement is at best a generic-group heuristic. The advantage is roughly ~q²·(2^{−H∞(a)} + 2^{−H∞(b)}) plus the Frobenius caveat [heuristic].
  - Short-exponent DH assumptions exist in the literature (Koshiba–Kurosawa, PKC 2004, I believe), but they do not cover digit-structured exponents with free Frobenius.

### Q12. Better seedless extraction by hand

**Answer: no provable gain is available in this method.**
- The character-sum method gives SD ≈ ½·3^{m/2}·3√q/ℓ ≈ 7.5·3^{(m−n)/2}, which is independent of how many input trits are folded.
- Folding x and y together, or folding after a Frobenius, changes the function f, and so at best the constant, but the √q barrier stays [heuristic: the sums of rational functions on a curve are essentially square-root sized; the n = 11 max above is 0.97 of the Weil bound].
- One extra trit needs a √3 = 0.79-bit smaller constant, so a y-fold (pole order 3 = p, which makes the Artin–Schreier reduction messier and likely *worse*) will not help.
- 94 trits = 149 bits is within ≈ 3 trits of m·log₂3 ≤ log₂ℓ − 128 = 153.4, the leftover-hash-style benchmark; Radhakrishnan–Ta-Shma (SIAM J. Discrete Math. 2000, I believe) shows this loss is necessary for seeded extractors.

### Q13. Workbench minimality

**Answer: not minimal. Both phases reach 7.** [computed; the register machine reproduces the spec schedules' 9 (walk) and 8 (validation) before any change]
- **Walk (F-form):** characteristic 3, a2 = −1, mixed addition of affine (x2, y2) into (X:Y:Z):
  - v = x2Z − X and u = y2Z − Y, computed in place;
  - F = u²Z + v²(v + Z);
  - Z3 = v³Z;
  - X3 = vF + x2Z3;
  - Y3 = −(uF + y2Z3).
  - It uses the same 12 multiplies as the spec, peaks at **7 bands**, and is correct 20/20 against affine addition at n = 179 [`mr_q13.py`].
- **Validation (lazy y):**
  - In each chord addition, form the second point's y (the Frobenius copy τ^m(Sy), or the copy of B's y) only *after* the inversion.
  - In the "+1" step, keep Sy through the inversion and cube it afterwards.
  - It peaks at **7 bands** in all tiers, accepts honest points and rejects B + T5 [`mr_q13_validation.py`].
- **Hand-performability:** both are re-orderings or re-groupings of the same peg operations (copies, multiply-accumulates, comb cubes and adds). There are no tables and no colour arithmetic.
  - The F-form is a new six-line verse. It would need Toymaster/Crypto to re-derive the "scale identities" (C21) for it; I did not do that.
  - I also did not model the no-swap variant or slides.
- **Lower bound:** I found no 6-band schedule, and I have no proof that 7 is optimal.
- **Grid impact:** I did not re-run `ecbs_budget`. The Crypto agent should re-run it with peaks 7/7. My rough reading is that Serious could lose a few grids and that the Hobby 10-grid layout would no longer depend on the swap move; both are **unverified**.

---

## 3. Per-claim table (C1–C24)

| Claim | Verdict | Reason (tag) |
|---|---|---|
| C1 orders, primality, ordinary, embedding degree, family scan | **Agree, with one qualification** | All recomputed independently [computed, §1]; ordinary and not anomalous also [proved]. **Qualify:** "the Serious twist has a 245-bit composite cofactor" is stale; the twist is fully factored with a 115-bit largest prime (rho ≈ 2^57.7) [computed]. Harmless only because of the mandatory y and on-curve check. The addendum (tap-independence) is correct [proved: isomorphic fields, E over F_3]. |
| C2 λ, λ̄ ∉ ⟨λ⟩ | Agree | [computed]. Reason: λ̄ = 3/λ, and 3 ∉ ⟨λ⟩ since ord_ℓ(3) ∤ n. |
| C3 rho √(πℓ/(4n)) | Agree | [heuristic/lit, computed figures match]. BSGS-type or negation refinements only affect constants. |
| C4 Lemma A | Agree (the proof is correct) | [proved, §Q2]. Gauss's lemma is unnecessary (monic division). |
| C5 pegs-only exact to 175 | **Qualify (the bound is not sharp)** | The exact threshold is m ≤ n−3: Serious 176 (278.95), Hobby 56 (88.76), Toy 20 (31.70), Demo 4 (6.34) [computed]. It fails at n−2 [proved]. |
| C6 200-cell / six-state ≥ 277.37 | Agree, can be strengthened | ≥ 278.95 via a 176-residue window [proved via the computed threshold]. |
| C7 three-state heavy keys | **Agree as stated (the bounds are valid), but far from tight** | Pair cancellation gives 169.93 (6 fleets), 207.01 (7 fleets) and 57.96 (Hobby 2) [computed]. Toy now has a useful bound, 25.06 [computed]. |
| C8 MC lower bounds | Qualify | This is an MC estimate of a rigorous per-layout bound, not a rigorous bound; the worst layout is unknown. Label it "[MC] ≈ 77", not "proven ≈ 77" (the Q1 table says "Proven H∞ ≈77"). |
| C9 fleet counts | Agree | N_LAB = 30,093,975,536 [computed]. Acceptance 0.388739 = N_LAB/(120·140·160·160·180) [proved, arithmetic]. MC figures confirmed exactly: 2^33.669 patterns and 33.6048 bits [computed, `mr_fleets2`]. I did not re-count the no-touch figure. |
| C10 multiplicity 72 | Agree; the open part is now closed | The global maximum is 72 [computed, exhaustive]. |
| C11 trace check ⇔ ⟨P⟩ | Agree | [proved; my own transcription of the trace chain accepts honest points and rejects B + T5 at n = 23, 59 and 179, computed]. E(F_q) is in fact cyclic. |
| C12 on-curve check needed | Agree, strengthened | Exactly the odd part of E′ passes [proved]. The node also passes on its odd part (index 4) [proved + computed]. Serious E′ = 2·16859153558033·p239 and Hobby E′ is fully smooth (so full break at Hobby without the check) [computed]. |
| C13 recipes vs PARI | Not independently re-checked | Partial: my flint arithmetic reproduces the base points and test vectors (C16). |
| C14 old schedule peaks | Not re-checked (superseded) | – |
| C15 generic key search | Agree, with qualification | BSGS 3^{⌊m/2⌋} + 3^{⌈m/2⌉} is right. Negation saves √2, and Frobenius saves ≤ 2^0.58 at m = 173 (Q3). "≈ 2^{H/2} for general min-entropy H" is a heuristic: the rigorous statement is the GGM bound T ≳ 2^{(H∞−log₂2n)/2} (Q1). The MITM figure of 2^152 is an upper bound on attack cost and is not binding. |
| C16 base point by rule | Agree | [proved: the order argument is correct; computed: j = 2, 2, 1, 1, P = 5R = strip, order ℓ, τP = λP, and the test vectors match]. |
| C17 halving ladders | Consistent, not fully re-checked | My transcription ("binary expansion from the top") yields correct inversions and traces [computed]. I did not compare the RW letter strings. |
| C18 lane fold geometry | Not re-checked | The tap arithmetic n − k = 8, 20, 120, 2 is trivially right; I did not check the w/h lane table. |
| C19 row-fold extractor | **Qualify** | The XOR lemma and fibre bound are correct [proved]. The constant is 3, not 4 [proved], but max m is unchanged [computed]. The model caveat is essential (Q11c). |
| C20 9/8 bands | **Disagree with any minimality reading; agree as a measurement** | 7/7 is achievable [computed]. The spec already says "not proven minimal". |
| C21 verse identities | Not re-checked | – |
| C22 rejected bases | Agree | Irreducible taps; single-peg cubes 3/7, 8/23, 20/59, 60/179; GNB types ≤ 20 exactly as stated [computed: `mr_c22.py`]. I did not re-check the ×1.72/×1.96 cost figures. |
| C23 Demo trace walk | Not re-checked | – |
| C24 W1 cursor | Not re-checked | – |

---

## 4. Other remarks

- The Q1 table in the review packet labels three-state "Proven H∞ ≈77". That figure is [MC], not proven (see C8).
- The spec's §1 line "Toy/Hobby/Serious embedding degree 2^29.6, 2^83.7, 2^273.9" agrees with my figures.
- In the C12 text, "the node … maps into the norm-1 torus": correct. The Frobenius acts there as u ↦ u^{−3} (proved above), which the spec might add, because it determines which node points pass.
- Serious test-vector digests: my Hobby and Serious digests are sha256(x|y)[:16] in my own digit format (e6635080e15e0cd7, 345ec55420cdd25e). They matched the spec's published values in my earlier check.

---

## 5. Scripts and logs (all in `proofs/key_exchange/ecbs/review/`)

| Script | Log | Purpose |
|---|---|---|
| `mr_ec.py` | – | Flint-based field and curve toolkit (add, mul, Frobenius) |
| `mr_orders.py` | `mr_orders_results.txt` | Traces three ways, brute-force counts, #E, ℓ primality (three tests), ℓ−1, embedding degrees, λ, twist/E′/node orders, rho figures, base points, family scan |
| `mr_factor_bg.py` | `mr_factor_bg_results.txt` | Full PARI factorisations of the Hobby/Serious twist, E′ and node |
| `mr_factor_check.py` | `mr_factor_check_results.txt` | APR-CL primality of every factor, product checks, bit sizes and PH/rho costs |
| `mr_invalid_trace.py` (removed at landing; log kept) | `mr_invalid_trace_results.txt` | Node and E′ points against the spec trace chain (odd parts pass) |
| `mr_lemmaA.py` | `mr_lemmaA_results.txt` | Exact injectivity thresholds, the shortest relations, Demo brute force and Toy MITM |
| `mr_fleets.c` (binary `mr_fleets`) | `mr_fleets_results.txt`, `mr_fleets_time.txt` | Exhaustive enumeration: N_LAB, global max M = 72, M histogram, (h, w)-box sums of M and M², exact Toy bound |
| `mr_fleets2.c` (binary `mr_fleets2`) | `mr_fleets2_results.txt`, `mr_fleets2_time.txt` | Same, plus Σ1/M and Σlog₂M per box |
| `mr_pattern_entropy.py` | `mr_pattern_entropy_results.txt` | Exact pattern count and Shannon entropy (C9) |
| `mr_pairs.py` | `mr_pairs_results.txt` | Pair-cancellation upper bounds on three-state H∞, with MC checks of the construction (imports `kx-specs/ecbs/ecbs_keys.py` read-only, for the dice procedure only) |
| `mr_frob.py` | `mr_frob_results.txt` | Frobenius rotation model: exact E[c], E[1/c], MC, exhaustive model tests, cost table |
| `mr_ks.py` | `mr_ks_results.txt` | Full (χ, ψ) character-sum spectra at n = 7, 9, 11, 13 |
| `mr_extractor_recalc.py` | `mr_extractor_recalc_results.txt` | C19 SD bounds and max m with c = 3 vs 4 |
| `mr_q13.py` (removed at landing; log kept) | `mr_q13_results.txt` | Band-count register machine; spec walk (9) vs F-form (7) |
| `mr_q13_validation.py` (removed at landing; log kept) | `mr_q13_validation_results.txt` | Spec validation (8) vs lazy-y schedules (7), with honest and B+T5 tests |
| `mr_c22.py` | `mr_c22_results.txt` | Tap irreducibility, single-peg cube counts, GNB types |

**Not done / limits.**
- No rigorous improvement to the three-state *lower* bound.
- No proof that 7 bands is optimal.
- No `ecbs_budget` re-run.
- C13, C14, C18, C21, C23 and C24 were not independently re-checked.
- The characteristic-3 index-calculus status rests on my knowledge of the literature, which I have marked as unverified where appropriate.

**Housekeeping note.** Importing `ecbs_keys` (from `mr_pairs.py`) made Python create `kx-specs/ecbs/__pycache__/ecbs_keys.cpython-313.pyc` (13:58 UTC). That was a byte-code cache and no source was changed. I deleted that directory, which restores the tree to its original state, and set `sys.dont_write_bytecode` in `mr_pairs.py` so it cannot recur. Nothing else under the repository checkout was touched, and no git operations were run.
