# ECBS: math review packet (for Mathematician)

Companion to `ECBS_SPEC.md`. All scripts and results files are in `kx-specs/ecbs/`.

> **Note (2026-10-04, ECBS landing).** This packet is a record of the 2026-09-30 draft. Most `[code: …]` scripts it names (the peg recipes, `ecbs_physical`, `ecbs_workbench`, `ecbs_fform`, `ecbs_validation`, `ecbs_entropy`, `fleet_*`, …) were removed when `primitives/key_exchange/ecbs/ecbs.sudo` replaced the hand-written implementation; their recorded outputs stay in `core/*_results.txt` / `.json`, and the scripts are in git history (commit `ad80f54`). The exchange, soundness, calling and twist evidence now runs on the generated code: see `evidence/`.

**Updated 2026-09-30 after Mathematician's review** (`proofs/key_exchange/ecbs/review/REVIEW.md`, scripts `mr_*`). Every correction is folded in below. Where I re-ran or re-derived a review result with my own code, the tag says [code: my script]. Where I rely on the reviewer's computation without re-running it, the tag says **[review: mr_script]**. Zachary has chosen the key encoding: **pegs-only, 162 cells at Serious, "128-bit security, key-limited"** (C27). The three-state encoding is **dropped in every tier** (C7).

**Status tags:**
- **[code]**: computed exactly by the named script.
- **[proof]**: argument given here; please check it.
- **[MC]**: Monte-Carlo estimate.
- **[heuristic]**: a standard model, not proven.
- **[open]**: not known to me.
- **[review: mr_…]**: computed or proved by Mathematician (REVIEW.md); not re-run by me unless also tagged [code].

**Notation.**
- E: y² = x³ + 2x² + 1 over F_q, q = 3^n; #E = 5ℓ. (Also written y² = x³ − x² + 1: the same curve, since 2 = −1 in F_3.)
- Field bases (changed 2026-09-30): Demo x^7 = x^5 + 1, Toy **x^23 = x^15 + 1** (was x^3 + 1), Hobby **x^59 = x^39 + 1** (was x^17 + 1), Serious x^179 = x^59 + 1.
- τ = Frobenius, with τ² + τ + 3 = 0; O_K = Z[τ], K = Q(√−11).
- λ = the eigenvalue of τ on ⟨P⟩ (λ^n ≡ 1 mod ℓ).
- 𝔩 = (ℓ, τ − λ).

---

## Claims

**C1 [code: ecbs_curve].** For n ∈ {7, 23, 59, 179}:
- #E = 3^n + 1 − V_n (the trace recurrence), cross-checked with PARI `ellcard` for small n.
- ℓ = #E/5 is prime (PARI `isprime`, proven).
- E is ordinary and not anomalous.
- The embedding degree ord_ℓ(q) is 15, 818634006, ≈2^83.7 and ≈2^273.9.
- ℓ−1 is fully factored.
- **Twist (corrected 2026-09-30; the earlier "245-bit composite cofactor" wording was stale).** The quadratic twist y² = x³ + x² + 2 has order q + 1 + V_n. At Serious it **factors completely**: 3·1433·160881263·p57·p73·p116, with the largest prime 115.4 bits, so rho on the twist costs ≈ 2^57.7. At Hobby the largest twist prime is 39.3 bits (≈ 2^19.6) [code: ecbs_twists, which re-checks the factorisation (exact division, product = order, every factor proven prime by PARI); review: mr_factor_bg, mr_factor_check].
- This is harmless **only because** ECBS sends y and the receiver checks the curve equation (C12). **Sending y and checking the curve equation is mandatory. An x-only variant (x-only transmission or x-only ladder arithmetic) must never be adopted.**
- The family scan of prime n < 200 with cofactor exactly 5 and ℓ prime gives n ∈ {2, 7, 23, 59, 179}.
- **Addendum (taps changed).** x^23 − x^15 − 1 and x^59 − x^39 − 1 are irreducible over F_3 [code: ecbs_layout §1, PARI]. Any two irreducible polynomials of degree n give isomorphic fields, and E is defined over F_3, so #E, ℓ, the embedding degree, λ and the rho figures do not depend on the tap. Re-running ecbs_curve with the new taps reproduces every number above [code]. H∞ of the key sets is a property of the scalar, so C4–C10 are unaffected. The base points and test vectors are **not** preserved by the isomorphism in digit form; they have been regenerated (C16), and all earlier test vectors are void.

**C2 [code].** x² + x + 3 has two roots mod ℓ, and exactly one, λ, satisfies λ^n = 1. The other root λ̄ = −1 − λ does not lie in ⟨λ⟩, because the embedding degree is large.

**C3 [code + heuristic].** Expected rho iterations, using equivalence classes under ⟨−1, τ⟩ of size 2n: √(πℓ/(4n)). This gives 2^2.78, 2^14.63, 2^42.48 and 2^136.78.
- The draft's √(πℓ/4)/√(2n) is 0.50 bit lower, because it applies the negation factor twice.
- The class-size convention is confirmed by the review (Q4).

**C4 Lemma A [proof, instances checked by code: ecbs_entropy].**

*Statement.*
- Let d ∈ Z^n be supported on a set W of residues, with |d_r| ≤ D_r.
- Fix s and put p_r = (r + s) mod n.
- If B := Σ_{r∈W} D_r 3^{p_r/2} satisfies B² < ℓ, and no nonzero Q ∈ Z[x] makes (x² + x + 3)·Q have |coef_p| ≤ D (with D = 0 off W),
- then Σ d_r λ^r ≡ 0 (mod ℓ) implies d = 0.

*Proof.*
1. Because λ^n = 1, Σ d_r λ^r ≡ 0 ⇔ λ^s Σ d_r λ^r = Σ d_r λ^{p_r} ≡ 0.
2. Put α = Σ d_r τ^{p_r} ∈ Z[τ]. Under the map Z[τ] → F_ℓ, τ ↦ λ (kernel 𝔩, norm ℓ), the congruence says α ∈ 𝔩, so ℓ | N(α).
3. |τ| = √3 in every complex embedding, so N(α) = |α|² ≤ B² < ℓ. Hence N(α) = 0 and α = 0.
4. So E(x) := Σ d_r x^{p_r} is divisible in Q[x] by the minimal polynomial x² + x + 3. Because that polynomial is monic, Gauss's lemma gives divisibility in Z[x].
5. The DP enumerates every Q with (x² + x + 3)Q inside the coefficient box:
   - It tracks q_{p−1}, q_{p−2} and uses e_p = 3q_p + q_{p−1} + q_{p−2}.
   - The bound |q| ≤ max D holds by induction.
   - It requires the state to end at (0, 0) with some q ≠ 0.
   - An unreachable end state means no nonzero d. ∎
- When every D_r ≤ 2 the DP is automatic: the lowest nonzero coefficient of such a multiple is 3·q_low, which has absolute value ≥ 3 > 2.
- The B² < ℓ test is exact integer arithmetic: B = A + C√3 [code].

*Corollary (conditioning).* If the c_r are independent, then H∞(k) ≥ Σ_{r∈W} H∞(c_r) for any certified W. The reason: given everything outside W, the map c_W ↦ k is injective, and max_k Pr[k] ≤ max Pr[c_W].

**C5 [proof via C4; code].** Pegs-only with m ≤ 175 i.i.d. uniform trits (positions 0..m−1, D = 2) has H∞(k) = m·log₂3 exactly. Concretely: 162 → 256.76, 173 → 274.20, 175 → 277.37. For Hobby m ≤ 55 (87.17), for Toy m ≤ 19 (30.11), for Demo m ≤ 3. (With the all-empty key re-rolled, H∞ = log₂(3^m − 1), which differs only at Demo: 2 cells → 3.00 bits.)
- **Exact threshold (review, 2026-09-30): pegs-only is injective iff m ≤ n − 3.** At the threshold: **Serious 176 cells → 278.95 bits; Hobby 56 → 88.76; Toy 20 → 31.70; Demo 4 → 6.34** [review: mr_lemmaA, exact decision over the 74 short elements of 𝔩, Toy MITM cross-check].
  - At m = n − 2 the relation 2λ^{n−3} = Σ_{e<n−3} λ^e always holds [review: proved; code: ecbs_review_checks (a), all four tiers].
  - Demo brute force: injective for m ≤ 4, not for m = 5 [code: ecbs_review_checks (b)].
- The chosen cell counts (Serious 162, Hobby 51, Toy 16, Demo 2) all lie inside my own C4 certificate range, so their exactness does not depend on the new threshold.

**C6 [proof via C4].** Pegs-only with 200 cells, and six-state with 2 grids, both have H∞(k) ≥ 277.37. **Strengthened by the review to ≥ 278.95** via a window of 176 consecutive residues [review: via mr_lemmaA].
- Keep one free peg cell per residue and condition on every other cell and on the ship layer; the ship layer is independent of the pegs.
- Every residue receives a peg in both layouts (six-state pegs sit on odd exponents 1..399, all distinct mod 179 up to 357).
- The upper bound is log₂ℓ = 281.39.

**C7 [code: ecbs_entropy §4; rigorous given exact counts]. Three-state heavy keys: SUPERSEDED, three-state DROPPED in every tier.**
- **Pair-cancellation bounds (review, rigorous from exact counts)** [review: mr_fleets.c exhaustive, mr_pairs.py; not re-run by me]. Two grids carry translated patterns with opposite signs, so the pair contributes 0; one special cell makes k = 2λ^{r0}:
  - **Serious 6 fleets: H∞(k) ≤ 169.93**; **7 fleets: ≤ 207.01**;
  - **Hobby 2 fleets: ≤ 57.96**;
  - **Toy 1 fleet: ≤ 25.06** (exact maximum over the natural family, attained at r0 = 3, 4).
- All four are below the curve-matching targets (273.55, 84.96, 29.26), and 6 and 7 fleets are below 256. **Three-state is therefore dropped in all tiers.**
- My own annealed bounds below remain valid but are far from tight:
- For any fixed patterns T_g and target sums c*, Pr[k = κ] ≥ Π_g M(T_g)/N_LAB · Π_r C(m_r, ⌊m_r/2⌋)/2^{m_r}. Here M(T) is the number of labelled fleets with union T (counted exactly by backtracking), and m_r is the number of ship cells on residue r.
- Simulated annealing found:
  - 6 fleets: **H∞ ≤ 225.48**, using the same multiplicity-38 pattern in all grids, aligned so that grids g, g+2 and g+4 share residues (34 residues × 3 cells);
  - 7 fleets: ≤ 260.04;
  - Hobby, 2 fleets: **≤ 74.35**;
  - Toy: 38.47, which is above the 34.13 cap and so gives nothing.
- The alignment geometry: grid g+2 cell p has the residue of grid g cell p + 21, i.e. two rows down and one column right.

**C8 [MC of a rigorous per-layout bound; NOT a proof].** Three-state lower bounds from the signs alone, given the patterns. **The ≈ 77-bit Serious figure is a Monte-Carlo estimate, never "proven"** (the earlier Q1 table wrongly said "Proven H∞ ≈ 77"). Honest three-state status: Serious 6 fleets ∈ [≈ 77 (MC), 169.93 (rigorous)]. Moot, since three-state is dropped.
- Per layout: a certified window with one free sign per residue (D = 1 after halving, since sign-sum differences are even) or an odd number of free signs (hsum).
- Averaged as −log₂ E_T[2^{−h(T)}] over 300 to 400 layouts.
- Results: Toy ≈ 12.5, Hobby (2 fleets) ≈ 26.0, Serious (6) ≈ 77.4, Serious (7) ≈ 86.7.
- The only non-rigorous part is the sampling. The worst layout is unknown.

**C9 [code: fleet_count.c, exhaustive].**
- Labelled fleets (5, 4, 3, 3, 2) on 10×10 with no overlap: 30,093,975,536. The dice procedure's acceptance rate is 0.388739.
- With no touching, even diagonally: 3,851,502,784.
- Distinct covered patterns: **1.365901·10¹⁰ = 2^33.669 exactly**, and the pattern's Shannon entropy is **33.6048 bits exactly** [review: mr_fleets2.c, exhaustive over all labelled fleets; my earlier MC values 2^33.67 and ≈ 33.605 agree]. **C9 is now exact.**

**C10 [code: fleet_maxmult].**
- A 17-cell L-shaped pattern (a 9-cell arm plus an 8-cell arm meeting at a corner) has multiplicity 72, versus 34 in the draft. So the single-fleet H∞ ≤ 45.64.
- Exhaustive search inside boxes up to 5×6, 4×8 and 3×9 found at most 46, and separated straight segments give at most 36.
- **The global maximum is 72** (Q7 closed) [review: mr_fleets.c, exhaustive over all 30,093,975,536 labelled fleets; attained by 12 anchored patterns]. So the single-fleet H∞ ≤ 45.64 is exact for the pattern alone.

**C11 [proof + code: ecbs_validation].** The trace check (the chain in SPEC §5) accepts a point B ∈ E(F_q)∖{O} iff B ∈ ⟨P⟩.
- E(F_q) ≅ Z/5 × Z/ℓ, and its 5-part is E(F_3), on which τ = 1.
- So Tr(B′ + T) = Tr(B′) + nT = O + (n mod 5)·T, and 5 ∤ n.
- Honest points never meet an exceptional case: every chain step adds s₁B + s₂B with s₁ ≢ ±s₂ and s_i ≢ 0 mod ℓ. The congruences were checked for all four tiers, and likewise for the cofactor strip.
- Demo exhaustive: of 2104 affine points, exactly the 420 subgroup points are accepted.

**C12 [proof + code].** The on-curve check cannot be dropped.
- The addition formulas use a but not b.
- On E′: y² = x³ + 2x² + 2 (trace 2 over F_3), the image of (τ′ − 1) lies in the kernel of the trace map. So half of E′(F_q) passes the trace check.
- #E′ = 2·1051 (Demo), 2·47071896187 (Toy), **2·16993·3770219·312996889·352328177 (Hobby, fully smooth, largest prime 28.4 bits)**, **2·p44·p239 (Serious)** [code: ecbs_twists; review: mr_factor_check].
- The node y² = x²(x + 2) is non-split, since 2 is a non-square and n is odd. Its group has order 3^n + 1 and maps into the norm-1 torus of F_{3^{2n}}; Frobenius acts there as u ↦ u^{−3} [review: proved]. Exactly its odd part (index 4) passes the trace check, and exactly the odd part of E′ (index 2) [review: proved + mr_invalid_trace].
- **What skipping the on-curve check would leak** (an active attacker who sends a point of the wrong curve and can test the resulting key) [code: ecbs_twists; review: mr_factor_check]:
  - Serious, node (b′ = 0): odd part 3755779·p46·p54·p162, so Pohlig–Hellman gives **k mod a 120.3-bit number for ≈ 2^26.5 work**.
  - Serious, E′ (b′ = 2): a further **43.9 bits** (the p44 factor) for ≈ 2^22.
  - **Hobby, E′: the odd part is fully smooth (92.5 bits > log₂ℓ = 91.19), so the whole key falls for ≈ 2^14.2 work.** Hobby's node falls for ≈ 2^40 (p80).
- **So the on-curve check is load-bearing: sending y and checking the curve equation are mandatory, and an x-only variant must never be adopted.**

**C13 [code: ecbs_exchange, ecbs_physical].** Peg recipes versus PARI:
- 20/20 random multiplies, cubes and inversions per tier.
- Full exchanges for all tiers and all encodings. The public points equal k·P, and both shared secrets equal ab·P.

**C14 [code: ecbs_physical; for this schedule only, not proven minimal].** Peak live registers in the original no-paper schedule: 10 (walk) and 9 (validation), plus overflow areas. Superseded by C20 and C26.

**C15 [heuristic].**
- Generic key search on a key set of min-entropy H costs ≈ 2^{H/2}. **Qualified by the review:** that is a heuristic. For pegs-only the concrete attack is baby-step giant-step (BSGS): 3^{⌊m/2⌋} + 3^{⌈m/2⌉} group operations, √2 fewer with the negation map, and at most √E[c] fewer with Frobenius (C27). The rigorous statement is a generic-group-model floor with free ±Frobenius: T ≳ 2^{(H∞ − log₂2n)/2} [review: GGM sketch, Shoup-style].
- MITM grid-split for three-state costs ≤ 2^152.0 (6 fleets); this is an upper bound on attack cost and not binding (three-state is dropped).

**C16 Base point by rule [proof + code: ecbs_basepoint].**
- Rule: take x = t^j for the smallest j ≥ 1 for which y = rhs(x)^((q+1)/4) satisfies y² = rhs(x); then P = 5R, where R = (x, y).
- q = 3^n ≡ 3 (mod 4) for odd n, so y is a square root whenever rhs is a square.
- 5 as a Frobenius strip: τ² = −τ − 3 gives τ³ = 3 − 2τ, so τ³ − τ² + τ − 1 = 5. That is the white-red-white-red strip.
- Order [proof]: #E(F_3) = 5, and E(F_3) ⊆ E(F_q). Since #E(F_q) = 5ℓ with ℓ ≠ 5 prime, E(F_q)[5] = E(F_3). So 5R = O iff R ∈ E(F_3). R ∉ E(F_3) because t^j ∉ F_3 for 1 ≤ j < n. Hence 5R has order exactly ℓ.
- [code]:
  - The first working hole is j = 2, 2, 1, 1 (Demo, Toy, Hobby, Serious).
  - 5R = the strip result, and PARI confirms order ℓ in all four tiers.
  - The base-3 digits of (q+1)/4 have the "red, empty … red, white" pattern.
  - Test vectors are in ecbs_basepoint_results.txt.

**C17 Halving ladders [code: ecbs_basepoint].**
- The ladder that builds the exponent chain from n − 1 (for inversion) is identical, step for step, to the Itoh–Tsujii addition chain: RW, WRRW, RRWRW, WRRWWRW.
- The ladder from n (for the trace chain) is likewise identical: RR, WRRR, RRWRR, WRRWWRR.
- Both are the binary expansion read from the top. This is a statement about these four n, checked by code, not a general theorem about all chains.

**C18 Lane fold and comb cube geometry [proof + code: ecbs_workbench A].**
- Lanes are w wide, and a band is h rows less its last hole, so n = wh − 1. Then "n holes back" = h rows up and one hole on.
- The tap n − k is a whole number r of rows (n − k = wr): Toy 8 = 1·8, Hobby 20 = 1·20, Serious 120 = 6·20, Demo 2 = 1·2.
- So the reduction x^n = x^k + 1 becomes "drop it one band up and one hole on, and again r rows up".
- Comb cube: x^(3i) lands at hole 3i. Before reduction this is a 3-row-per-row expansion (a peg on every third hole), and it is then folded as above.
- [code]:
  - fold and comb cube equal PARI-checked multiplication in 300/300 random inputs per tier;
  - the parked patrol boat never covers a peg (0 clashes);
  - the cube strip plus a 2-hole comb gap fits the workbench (Toy 69 ≤ 72, Hobby 177 ≤ 180, Serious 537 ≤ 540).
- Cube cost rises with the new taps: Toy 80 → 105 moves, Hobby 195 → 273 moves per cube; multiply unchanged [code: ecbs_layout §5].

**C19 x-register extractor ("row fold") [proof + review + code: ecbs_extractor, re-run 2026-09-30 with constant 3].**
- Recipe: drop rows of the shared x-register onto the top rows, adding trits mod 3. This is a surjective F_3-linear map F_3^n → F_3^m, so every character of the output is a character of x.
- Model **[assumption]: the uniform shared-point model**, K uniform on ⟨P⟩∖{O}. **This is the only claim made.** No DDH-type statement is claimed: for structured keys with H∞ < log₂ℓ it would be at best a generic-group heuristic [review Q11c].
- XOR lemma (F_3 version) [proof, standard]:
  - SD(Z, U_m) ≤ ½·√(Σ_{a≠0} |E ω^{a·Z}|²) ≤ ½·√(3^m − 1)·δ,
  - where δ = max over nonzero F_3-linear ψ of |E ω^{ψ(x(K))}|.
- Character sum bound: **|Σ_{R∈H, R≠O} ψ(c·x(R))| ≤ 3√q for any subgroup H**, so **δ ≤ 3√q/(ℓ − 1)** [review Q11a: proof via Weil II and Grothendieck–Ogg–Shafarevich (Swan conductor 2 at O, Euler characteristic −1, so χ_c = −3); not re-derived by me]. Including O adds at most 1.
  - The older Kohel–Shparlinski form 2·deg(f)·√q = 4√q [lit, ANTS-IV 2000] is valid but weaker.
  - Every computed spectrum is below 3√q; the reviewer's n = 11 whole-group maximum (2.91√q) is within 3 % of it, so 3 cannot be improved in general [review: mr_ks; my ecbs_extractor §2 gives the same maxima].
  - The same approach for DH elements: Chevalier–Fouque–Pointcheval–Zimmer (Eurocrypt 2009) and Ciss–Sow (on randomness extraction in elliptic curves) **[lit, not re-derived here]**.
- Fibre bound [proof, elementary]: Pr[Z = z] ≤ 2·3^(n−m)/(ℓ − 1). This gives the H∞ lower bounds.
- [code, under the model]:
  - Serious: H∞(x) = log₂((ℓ−1)/2) = 280.39 bits.
    - m = 100: SD ≤ 2^−59.7, H∞ ≥ 155.2.
    - m = 80: SD ≤ 2^−75.5, H∞ ≥ 126.8.
    - m = 60: SD ≤ 2^−91.4.
    - The largest m with SD ≤ 2^−64 is still 94, and with SD ≤ 2^−128 still 13 (the constant gains 0.415 bit, not a whole trit).
  - Hobby: m = 40 → SD ≤ 2^−12.2; m = 20 → SD ≤ 2^−28.0.
  - Toy: m = 16 → SD ≤ 2^−2.6; m = 8 → SD ≤ 2^−9.0.
  - Demo: vacuous.
- [code, exact at Demo]: over all 420 points of ⟨P⟩∖{O} and all 2186 nonzero functionals, the largest character sum is 1.407√q. The exact SD of the m-trit fold ranges from 0.0048 (m = 1) to 0.904 (m = 7).
- [code, empirical constant]: whole-group maxima are 2.25√q, 2.91√q and 2.85√q at n = 7, 11, 13, all below 3√q. The prime subgroups at n = 11 and 13 are smaller than 3√q, so they test nothing.
- [MC]: Toy, 200,000 uniform K, 5-trit fold. χ² = 240.3 (df 242, p = 0.519); max per-trit deviation 0.0020 (1/√N = 0.0022).

**C20 Workbench peak of the OLD schedule [code: ecbs_workbench C, ecbs_workbench_noswap; measured, not minimal]. Superseded by C26 (7 + 7).**
- Registers live outside the workbench peak at **9 bands for the projective walk and 8 for validation**, in every tier.
- This relies on two things:
  - the swap move **[assume; confirmed by Zachary]**: exchange two registers hole by hole, one peg in each hand;
  - fresh-empty targets.
- Without the swap it is 10 bands (Demo, Toy and Hobby measured).
- Demo chord walk: 6 bands; validation 8 (trace chain) or 6 (trace walk).
- All runs produced correct exchanges, checked against PARI.

**C21 Old verse identities [code: ecbs_verse] (the 4-line verse is retired in favour of C25, but remains correct).** The "chord rule kept over a bottom" (projective chord/tangent with a common denominator) satisfies all five scale identities and equals PARI's sum in 50/50 random additions per tier.

**C22 Rejected bases [proof + code: ecbs_layout §2–3, ecbs_verse §2].**
- Rigid motion: in the polynomial basis, x^(3i) reduces to a single peg only for 3/7, 8/23, 20/59 and 60/179 holes. The other holes' single pegs cube to 2 or more pegs. So no permutation of holes is the cube.
- Gaussian normal bases:
  - types ≤ 20 are 7: {4, 6, 10, 16, 18}; 23: {2, 6, 12, 20}; 59: {12, 14, 18}; 179: {2, 8, 20};
  - so an optimal (type 1 or 2) basis exists only at n = 23 and 179.
- Palindromic type-II basis: the multiply is correct 30/30, but costs ×1.72 (n = 23) and ×1.96 (n = 179) the polynomial-basis moves. Rejected on cost.

**C23 Demo trace walk [code, exhaustive: ecbs_walks].**
- Validation by walk: S ← τS + B over n − 1 = 6 cells, then one more Frobenius must give the mirror of B.
- Over all 2104 affine points of E(F_{3^7}), it accepts exactly 420, all in ⟨P⟩, with 0 misclassified.
- For honest inputs, none of the performed steps m = 1..5 is exceptional (λ·s_m ≢ ±1 mod ℓ).
- 268 exchanges correct; 32 of 300 key draws were re-rolled for an exceptional chord.

**C24 W1 cursor [code: ecbs_workbench B].**
- Walk position is marked by a marker peg or parking hole on the ship grid.
- 300/300 trials give correct digits, with 0 ambiguous moments, and the grid is restored each time.
- Assumes one peg hole per ship cell, with ships covering grid holes **[assume; confirmed by Zachary]**, and fleet keys only.

**C25 F-form addition verse [proof + code: ecbs_fform §1, §3; from the review's Q13, re-derived here].**
- Mixed addition (X:Y:Z) + (x₂, y₂) in characteristic 3 with a₂ = −1. With v = x₂Z − X and u = y₂Z − Y (so v = Z·(x₂ − x₁), u = Z·(y₂ − y₁), slope λ = u/v):
  - F = u²Z + v²(v + Z) = v²Z·(λ² + 1 + x₂ − x₁) = **v²Z·(x₃ − x₂)** [proof: x₃ = λ² + 1 − x₁ − x₂ and −2x₂ = x₂];
  - Z₃ = v³Z; X₃ = vF + x₂Z₃, so X₃/Z₃ = x₂ + (x₃ − x₂) = x₃;
  - Y₃ = −(uF + y₂Z₃), so Y₃/Z₃ = −(y₂ + λ(x₃ − x₂)) = λ(x₂ − x₃) − y₂ = y₃ (the chord line through the base point).
- In words: **"the chord rule told from the base point"**: gap = slope² + 1 + run; new x = x₂ + gap; new y = −(y₂ + slope·gap).
- [code] All six identities (run, rise, gap, X₃/Z₃, Y₃/Z₃, equal to PARI's sum) hold in 50/50 random additions per tier.
- [code] The peg schedule (12 multiplies, X and Y overwritten by v and u in place) gives correct full exchanges against PARI: Demo 20/20, Toy 10/10, Hobby 5/5, Serious 5/5 (pegs-only keys).

**C26 Workbench peak with the F-form and the lazy-y trace chain [code: ecbs_fform §3; measured, not proven minimal].**
- **Walk: 7 bands; validation: 7 bands**, in every tier (Demo, Toy, Hobby, Serious), against 9 and 8 for the old schedule on the same keys.
- Lazy y: in each chord addition of the trace chain, the second point's y is made only after the run is inverted; on a red rung the first point's y (τ of S's y) is also made after the inversion.
- The receiver check still accepts honest points and rejects B + T₅ (T₅ = (1, 1)) at Toy, Hobby and Serious [code: ecbs_fform §2]; Demo exhaustive: accepts exactly the 420 points of ⟨P⟩∖{O} out of 2104, 0 misclassified [code: ecbs_review_checks (c)].
- **The swap move is not needed:** the no-swap variant gives the same 7 bands and identical moves (Toy, Hobby, Serious).
- Moves change by −0.2 % to −0.9 % (same keys) [code].
- **Grid effect** [code: ecbs_budget_fform, the unchanged ecbs_budget bookkeeping]: **Serious 26 → 22 grids**; Toy (5) and Hobby (9) unchanged, because register bands pack three to a (double) grid there and ⌈7/3⌉ = ⌈9/3⌉. Demo keeps the chord walk (6 bands); the lazy-y chain (7 bands) fits the ½ set with control 17/24.
- Not shown: that 7 is minimal (the reviewer found no 6-band schedule either).

**C27 Key-limited pegs-only cell counts [code: ecbs_tiers; the rotation model is the review's, recomputed here].**
- Zachary's choice: the key is deliberately the weak link. Headline "**128-bit security, key-limited**": Serious 162 cells.
- Quantities, for m cells with the all-empty key re-rolled:
  - H∞ = log₂(3^m − 1), exact for m ≤ n − 3 (C5);
  - plain BSGS 3^{⌊m/2⌋} + 3^{⌈m/2⌉} (a concrete attack);
  - "modelled best key search" = BSGS / √2 (negation) / √E[c] (Frobenius rotation model, E[c] computed exactly as Σ_i (3^{|W∩(W−i)|} − 1)/(3^m − 1); my values match the review's 2.000 at 162, 2.226 at 173, 8.333 at 176);
  - GGM floor with free ±Frobenius, 2^{(H∞ − log₂2n)/2};
  - rho, C3.
- **Rule used for every tier:** "key-limited" means the *plain* BSGS count is below rho, so the key is the weak link even against an attacker who uses no negation or Frobenius tricks; the cell count is the smallest with H∞ ≥ 2 × (headline).

  | Tier | Cells | H∞ (exact) | Plain BSGS | Modelled best key search | GGM floor | Rho | Margin (rho − plain BSGS) |
  |---|---|---|---|---|---|---|---|
  | Serious | **162** | 256.76 | 2^129.38 | **2^128.38** | 2^124.14 | 2^136.78 | +7.40 |
  | Hobby | **51** | 80.83 | 2^41.62 | 2^40.62 | 2^36.98 | 2^42.48 | +0.86 |
  | Toy | **16** | 25.36 | 2^13.68 | 2^12.68 | 2^9.92 | 2^14.63 | +0.95 |
  | Demo | **2** | 3.00 | 2^2.58 (6 ops) | 2^1.79 | – | 2^2.78 (≈ 6.9) | +0.20 |

- The n − 3 thresholds are **not** key-limited below Serious: Hobby 56 (plain BSGS 2^45.38), Toy 20 (2^16.85) and Demo 4 (2^4.17) all exceed their rho. Serious 176 is not key-limited either (2^140.48 > 2^136.78).
- The "128-bit" headline rests on the rotation model (Q3); the GGM floor is 4.2 bits lower (2^124.1). Both are stated in the spec.

**C28 Pegs-only walks never meet the exceptional case for m ≤ n − 3 [proof via C4; code].**
- A walk addition is exceptional iff the accumulator after Frobenius is ±P, i.e. λ·s ≡ ±1 (mod ℓ), where λ·s = Σ_{e=1..j} c_e λ^e with c_e ∈ {−1, 0, 1}.
- Then λ·s ∓ 1 is a nonzero digit vector with |d| ≤ 1 on a window of j + 1 ≤ m ≤ n − 3 positions, which C4/C5 (|d| ≤ 2) excludes.
- So the only re-roll is the all-empty key (probability 3^{−m}: 1/9 at Demo with 2 cells). [code: ecbs_tiers, Demo exhaustive for m = 2, 3, 4: 0 exceptional keys.]

**C29 Twists and invalid curves re-checked [code: ecbs_twists].**
- Orders from the traces agree with PARI `ellcard` at n = 3, 5, 7 for E, the twist and E′.
- Hobby's twist, E′ and node were factored from scratch by PARI; the Serious factorisations stated in the review were confirmed exactly (every factor proven prime, product = order).
- Figures as in C1 and C12.

---

## Questions: status after Mathematician's review (2026-09-30)

The original questions Q1–Q13 are answered below. The review's own tags carry over; "folded in" means the spec and the claims above now say this.

**Q1. Honest security per unit of hand work.** *Answered; Zachary chose.* Pegs-only is flat and injective, so min-entropy, Shannon entropy and guesswork coincide. Zachary picked **pegs-only 162 cells at Serious, "128-bit security, key-limited"**: the key is deliberately the weak link, brute force at ≈ 2^128 is the best attack, and the curve's rho (2^136.78) is margin. Other tiers: C27. Updated data (moves are the workbench runs with slides; ecbs_fform):

  | Option | Moves per person | H∞ | Best modelled key search | Status |
  |---|---|---|---|---|
  | **pegs-only 162 (chosen)** | **44.89 M** (F-form, 22 grids) | = 256.76 | 2^128.38 (GGM floor 2^124.14) | key-limited, margin 7.4 bits |
  | pegs-only 173 | 44.2 M (old schedule, no slides) | = 274.20 | 2^137.23 | matches rho (review's recommendation) |
  | pegs-only 176 (n − 3) | not run | = 278.95 | 2^138.45 | matches rho |
  | pegs-only 200 / six-state 2 | 51.7 M / 64.7 M (old, no slides) | ∈ [278.95, 281.39] | – | matches rho |
  | three-state 6 / 7 fleets | 42.0 M / 48.3 M (old, no slides) | ∈ [≈ 77 (MC), **169.93**] / [≈ 87 (MC), **207.01**] | – | **dropped** |

**Q2. Lemma A.** *Answered.* The proof is correct (Gauss's lemma is unnecessary: monic division suffices). Exact threshold m ≤ n − 3 (C5).

**Q3. Frobenius-aware key search.** *Answered: the gains are small.* In the rotation model the saving is ≤ √E[c]: 2^0.50 at 162 cells, 2^0.58 at 173, 2^1.02 at 175, 2^1.53 at 176 [review: mr_frob, exhaustive model tests at (23, 12–15) and (59, 10) agree for > 99.6 % of keys; E[c] re-computed exactly in ecbs_tiers]. Kangaroo / Gaudry–Schost do not apply to a high-dimensional digit box [review: heuristic].

**Q4. Rho convention.** *Answered.* √(πℓ/(4n)) is right for classes of size 2n [review: heuristic/lit]. Target: Zachary chose 128-bit key-limited (Q1).

**Q5. Descent and index calculus.** *Partly answered.*
- **No GHS/Weil descent applies:** n = 179 is prime, E is defined over F₃, the Weil restriction splits as E × T with the ℓ-part in the 178-dimensional trace-zero variety T, and GHS from F_{3^179} to F₃ has magic number 1, giving back genus 1 [review: lit + the reviewer's own application; not re-derived by me].
- **Summation polynomials / index calculus in characteristic 3: the point rests on the literature and is unverified.** The known sub-rho results (Gaudry, Diem) are for the opposite regime; the prime-degree small-field claims (Petit–Quisquater, char 2) are doubted in the later literature; the reviewer knows of no characteristic-3 analysis at all [review: lit, marked "I believe" / unverified]. Status: open, with no known attack beating rho.

**Q6. Three-state gap.** *Moot:* three-state is dropped (C7). The upper side was tightened to 169.93; the lower side is still ≈ 77 [MC] only.

**Q7. Pattern multiplicity.** *Closed:* 72 is the global maximum (C10).

**Q8. Reject on exceptional case.** *Answered:* validation touches only the public B, so which step rejects leaks nothing secret; in the key walks the exceptional condition is a congruence on the scalar alone [review: proved]. For the chosen pegs-only keys it never happens except for the all-empty key (C28).

**Q9. The node.** *Answered:* without the on-curve check the node already leaks 120.3 bits of k for ≈ 2^26.5 at Serious and the whole key at Hobby (C12). The on-curve check closes it.

**Q10. Twisted bases.** *Answered: no.* Equal-sign triples at (g, r), (g, r+1), (g+1, r) alias exactly, since λ̄ = −1 − λ [review: proved]. Keep untwisted bases.

**Q11. Key extraction.** *Answered:* (a) the constant is 3√q, O excluded, for any subgroup [review: proved; not re-derived by me]; (b) the XOR lemma is stated correctly [review]; (c) **claim only the uniform shared-point model**, not DDH. Folded into C19 and the spec §6.

**Q12. Better seedless extraction by hand.** *Answered: no provable gain in this method* [review: heuristic]. 94 trits (149 bits) at SD ≤ 2^−64 is within ≈ 3 trits of the leftover-hash-style benchmark.

**Q13. Workbench minimality.** *Answered and adopted:* the F-form walk and lazy-y validation reach 7 + 7 bands (C25, C26), verified with my own harness; Serious saves 4 grids. Minimality of 7 is not shown.

### Still open

1. Is 7 bands minimal for walk and validation (C26)?
2. Characteristic-3 summation-polynomial / index-calculus attacks on prime-degree extensions (Q5): literature-based and unverified.
3. The 3√q constant (Q11a) is the reviewer's proof; an independent check of the Swan-conductor argument would be welcome.
4. The 128-bit headline uses the Frobenius rotation model (2^128.38); the rigorous GGM floor with free ±Frobenius is 2^124.14. Is there a sharper rigorous bound for digit-window key sets?
