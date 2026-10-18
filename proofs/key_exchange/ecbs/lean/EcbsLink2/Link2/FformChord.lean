/-
  SPEC.md §3 R7 lines 149–154, told projectively. A live cell cubes the
  denominator, and a white or red cell adds the base point on that common
  denominator. `Z` stays right-invertible. Irreducibility of `X^n − X^k − 1`
  is not a hypothesis.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformProj
import EcbsLink2.Link2.FieldNeg

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem addLen (n : Nat) (a b : List Nat) : (fieldAdd n a b).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem mirLen (xs : List Nat) : (mirrorTrits xs).length = xs.length := by
  simp [mirrorTrits]

private theorem subLen (n : Nat) (a b : List Nat) : (fieldSub n a b).length = n := by
  simp [fieldSub, fieldAdd, List.length_map, List.length_range]

private theorem mulT (n k bench : Nat) (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (x y : List Nat) (hx : allTritList x) (hy : allTritList y) :
    allTritList (fieldMul n k bench x y) := by
  rw [fieldMul_eq_mulVal n k bench x y hn hk hb h2 hx hy]
  exact mulVal_trits n k hn hk x y hx hy

private theorem addT (n : Nat) (a b : List Nat) : allTritList (fieldAdd n a b) :=
  fieldAdd_trits n a b

/-- Adding the zero home on the right does nothing. -/
theorem fieldAdd_zero_right (n : Nat) (xs : List Nat)
    (ht : allTritList xs) (hlen : xs.length = n) :
    fieldAdd n xs (zeroPeg n) = xs := by
  apply List.ext_getElem
  · simp [fieldAdd, zeroPeg, List.length_map, List.length_range, List.length_replicate, hlen]
  · intro i hi _
    unfold fieldAdd at hi ⊢
    simp only [List.getElem_map, List.getElem_range, coeff_zeroPeg] at hi ⊢
    have hiN : i < n := by
      simpa [List.length_map, List.length_range] using hi
    have hixs : i < xs.length := by rw [hlen]; exact hiN
    rw [coeff_eq_get xs i hixs]
    exact tritAdd_zero_right _ (ht _ (List.getElem_mem hixs))

/-- Equal sums with the same right addend have equal left addends. -/
theorem fieldAdd_cancel_right (n : Nat) (a b c : List Nat)
    (ha : allTritList a) (hb : allTritList b) (hc : allTritList c)
    (haL : a.length = n) (hbL : b.length = n) (_hcL : c.length = n)
    (h : fieldAdd n a c = fieldAdd n b c) : a = b := by
  have hmir : fieldAdd n (fieldAdd n a c) (mirrorTrits c) =
      fieldAdd n (fieldAdd n b c) (mirrorTrits c) := congrArg (fun t =>
        fieldAdd n t (mirrorTrits c)) h
  rw [fieldAdd_assoc n a c (mirrorTrits c), fieldAdd_mirror n c hc,
    fieldAdd_zero_right n a ha haL,
    fieldAdd_assoc n b c (mirrorTrits c), fieldAdd_mirror n c hc,
    fieldAdd_zero_right n b hb hbL] at hmir
  exact hmir

theorem add3_rot (n : Nat) (a b c : List Nat) :
    fieldAdd n (fieldAdd n a b) c = fieldAdd n (fieldAdd n a c) b := by
  rw [fieldAdd_assoc, fieldAdd_comm n b c, ← fieldAdd_assoc]

/-- `v = x₂Z − X` is `(x₂ − x) · Z` when `X = x · Z`. -/
theorem run_over_z (n k bench : Nat) (x x2 z : List Nat)
    (hb : n ≤ bench) (hx : allTritList x) (hx2 : allTritList x2) (hz : allTritList z) :
    fformRun n k bench x2 z (fieldMul n k bench x z) =
      fieldMul n k bench (fieldSub n x2 x) z := by
  unfold fformRun fieldSub
  rw [(fieldMul_mirror_left n k bench x z hx hz).symm]
  rw [(fieldMul_left_add n k bench z (mirrorTrits x) x2 hz (mirror_trits x) hx2 hb).symm]
  rw [fieldAdd_comm n (mirrorTrits x) x2]

/-- `u = y₂Z − Y` is `(y₂ − y) · Z` when `Y = y · Z`. -/
theorem rise_over_z (n k bench : Nat) (y y2 z : List Nat)
    (hb : n ≤ bench) (hy : allTritList y) (hy2 : allTritList y2) (hz : allTritList z) :
    fformRise n k bench y2 z (fieldMul n k bench y z) =
      fieldMul n k bench (fieldSub n y2 y) z := by
  unfold fformRise fieldSub
  rw [(fieldMul_mirror_left n k bench y z hy hz).symm]
  rw [(fieldMul_left_add n k bench z (mirrorTrits y) y2 hz (mirror_trits y) hy2 hb).symm]
  rw [fieldAdd_comm n (mirrorTrits y) y2]

/-- Cancelling a right inverse: `(a · g) · (r · b) = a · b` when `g · r = 1`. -/
theorem mul_inv_right (n k bench : Nat) (a g r b : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (ha : allTritList a) (hg : allTritList g) (hr : allTritList r) (hbT : allTritList b)
    (haL : a.length = n)
    (hinv : fieldMul n k bench g r = onePeg n) :
    fieldMul n k bench (fieldMul n k bench a g) (fieldMul n k bench r b) =
      fieldMul n k bench a b := by
  have hagT := mulT n k bench hn hk hb h2 a g ha hg
  have hstep1 :=
    (fieldMul_assoc n k bench (fieldMul n k bench a g) r b hn hk hb h2 hagT hr hbT).symm
  have hstep2 := fieldMul_assoc n k bench a g r hn hk hb h2 ha hg hr
  rw [hstep1, hstep2, hinv, fieldMul_one_right n k bench a hn hk hb h2 ha haL]

/-- A square of a product is the product of the squares. -/
theorem sq_mul (n k bench : Nat) (a b : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (ha : allTritList a) (hbT : allTritList b) :
    fieldMul n k bench (fieldMul n k bench a b) (fieldMul n k bench a b) =
      fieldMul n k bench (fieldMul n k bench a a) (fieldMul n k bench b b) := by
  have habT := mulT n k bench hn hk hb h2 a b ha hbT
  have hbaT := mulT n k bench hn hk hb h2 b a hbT ha
  have haaT := mulT n k bench hn hk hb h2 a a ha ha
  have hbbT := mulT n k bench hn hk hb h2 b b hbT hbT
  have habbT := mulT n k bench hn hk hb h2 (fieldMul n k bench a b) b habT hbT
  have haabbT := mulT n k bench hn hk hb h2 a (fieldMul n k bench b b) ha hbbT
  have e1 := fieldMul_assoc n k bench a b (fieldMul n k bench a b) hn hk hb h2 ha hbT habT
  have e2 :=
    (fieldMul_assoc n k bench b a b hn hk hb h2 hbT ha hbT).symm
  have e3 := fieldMul_comm n k bench b a hbT ha
  have e4 := fieldMul_assoc n k bench a b b hn hk hb h2 ha hbT hbT
  have e5 :=
    (fieldMul_assoc n k bench a a (fieldMul n k bench b b) hn hk hb h2 ha ha hbbT).symm
  rw [e1, e2, e3, e4, e5]

/-- Cubing is the field product of a list with itself, twice. -/
theorem cube_as_mul (n k bench : Nat) (x : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hx : allTritList x) :
    fieldCube n k bench x = fieldMul n k bench x (fieldMul n k bench x x) := by
  rw [fieldCube_cu n k bench hn hk hb h2 h3 x hx]
  have hxx := fieldMul_eq_mulVal n k bench x x hn hk hb h2 hx hx
  have hxxT : allTritList (fieldMul n k bench x x) := by
    rw [hxx]; exact mulVal_trits n k hn hk x x hx hx
  rw [hxx.symm]
  exact (fieldMul_eq_mulVal n k bench x (fieldMul n k bench x x) hn hk hb h2 hx hxxT).symm

/-- The new bottom is `v³ · Z`. -/
theorem bottom_as_cube (n k bench : Nat) (v z : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hv : allTritList v) (hz : allTritList z) :
    fformBottom n k bench v z =
      fieldMul n k bench (fieldCube n k bench v) z := by
  unfold fformBottom
  have hvvT := mulT n k bench hn hk hb h2 v v hv hv
  have hassoc :=
    (fieldMul_assoc n k bench v (fieldMul n k bench v v) z hn hk hb h2 hv hvvT hz).symm
  rw [hassoc, cube_as_mul n k bench v hn hk hb h2 h3 hv]

/-- `(λ² + 1 + x) − run`, minus `x₂`, is `λ² + 1 + run`. This is `x₃ − x₂`. -/
theorem x3_minus_x2 (n k bench : Nat) (slope x x2 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hs : allTritList slope) (hx : allTritList x) (hx2 : allTritList x2)
    (hxL : x.length = n) (hx2L : x2.length = n) :
    let run := fieldSub n x2 x
    let s2 := fieldMul n k bench slope slope
    let x3 := fieldAdd n
      (fieldAdd n (fieldAdd n s2 (whiteHole0 n)) x) (mirrorTrits run)
    fieldSub n x3 x2 = fieldAdd n (fieldAdd n s2 (onePeg n)) run := by
  intro run s2 x3
  have hrunT : allTritList run := addT n x2 (mirrorTrits x)
  have hs2T := mulT n k bench hn hk hb h2 slope slope hs hs
  have honeT := onePeg_trits n
  have honeL : (onePeg n).length = n := by
    unfold onePeg
    simp [List.length_replicate]
    omega
  have hmT : allTritList (mirrorTrits x2) := mirror_trits x2
  have hmL : (mirrorTrits x2).length = n := by rw [mirLen, hx2L]
  have hxTm : allTritList (mirrorTrits x) := mirror_trits x
  have hrunM : mirrorTrits run = fieldAdd n (mirrorTrits x2) x := by
    have hrun : run = fieldAdd n x2 (mirrorTrits x) := rfl
    rw [hrun, mirrorTrits_fieldAdd n x2 (mirrorTrits x) hx2 hxTm, mirrorTrits_invol x hx]
  have hp1 : allTritList (fieldAdd n s2 (onePeg n)) := addT n s2 (onePeg n)
  have hx3p : allTritList (fieldAdd n (fieldAdd n s2 (onePeg n)) x) :=
    addT n (fieldAdd n s2 (onePeg n)) x
  have eA : fieldAdd n (fieldAdd n (fieldAdd n s2 (onePeg n)) x)
        (fieldAdd n (mirrorTrits x2) x) =
      fieldAdd n (fieldAdd n s2 (onePeg n))
        (fieldAdd n x (fieldAdd n (mirrorTrits x2) x)) :=
    fieldAdd_assoc n (fieldAdd n s2 (onePeg n)) x (fieldAdd n (mirrorTrits x2) x)
  have eB : fieldAdd n x (fieldAdd n (mirrorTrits x2) x) =
      fieldAdd n (fieldAdd n x (mirrorTrits x2)) x :=
    (fieldAdd_assoc n x (mirrorTrits x2) x).symm
  have eC : fieldAdd n x (mirrorTrits x2) = fieldAdd n (mirrorTrits x2) x :=
    fieldAdd_comm n x (mirrorTrits x2)
  have eD : fieldAdd n (fieldAdd n (mirrorTrits x2) x) x =
      fieldAdd n (mirrorTrits x2) (fieldAdd n x x) :=
    fieldAdd_assoc n (mirrorTrits x2) x x
  have eE : fieldAdd n x x = mirrorTrits x := fieldAdd_double n x hx hxL
  have eF : fieldAdd n (mirrorTrits x2) (mirrorTrits x) =
      fieldAdd n (mirrorTrits x2) (mirrorTrits x) := rfl
  have hx3eq : x3 = fieldAdd n (fieldAdd n s2 (onePeg n))
      (fieldAdd n (mirrorTrits x2) (mirrorTrits x)) := by
    have hwhite : whiteHole0 n = onePeg n := whiteHole0_eq_onePeg n
    unfold x3
    rw [hwhite, hrunM, eA, eB, eC, eD, eE]
  have eG : fieldAdd n
        (fieldAdd n (fieldAdd n s2 (onePeg n))
          (fieldAdd n (mirrorTrits x2) (mirrorTrits x)))
        (mirrorTrits x2) =
      fieldAdd n (fieldAdd n s2 (onePeg n))
        (fieldAdd n (fieldAdd n (mirrorTrits x2) (mirrorTrits x)) (mirrorTrits x2)) :=
    fieldAdd_assoc n (fieldAdd n s2 (onePeg n))
      (fieldAdd n (mirrorTrits x2) (mirrorTrits x)) (mirrorTrits x2)
  have eH : fieldAdd n (fieldAdd n (mirrorTrits x2) (mirrorTrits x)) (mirrorTrits x2) =
      fieldAdd n (mirrorTrits x2) (fieldAdd n (mirrorTrits x) (mirrorTrits x2)) :=
    fieldAdd_assoc n (mirrorTrits x2) (mirrorTrits x) (mirrorTrits x2)
  have eI : fieldAdd n (mirrorTrits x) (mirrorTrits x2) =
      fieldAdd n (mirrorTrits x2) (mirrorTrits x) :=
    fieldAdd_comm n (mirrorTrits x) (mirrorTrits x2)
  have eJ : fieldAdd n (mirrorTrits x2) (fieldAdd n (mirrorTrits x2) (mirrorTrits x)) =
      fieldAdd n (fieldAdd n (mirrorTrits x2) (mirrorTrits x2)) (mirrorTrits x) :=
    (fieldAdd_assoc n (mirrorTrits x2) (mirrorTrits x2) (mirrorTrits x)).symm
  have eK : fieldAdd n (mirrorTrits x2) (mirrorTrits x2) = x2 := by
    rw [fieldAdd_double n (mirrorTrits x2) hmT hmL, mirrorTrits_invol x2 hx2]
  have eL : fieldAdd n x2 (mirrorTrits x) = run := rfl
  unfold fieldSub
  rw [hx3eq, eG, eH, eI, eJ, eK, eL]

/-- The run's right inverse, carried across `Z`, is a right inverse of `v`. -/
theorem v_right_inv (n k bench : Nat) (run z w g : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hr : allTritList run) (hz : allTritList z) (hw : allTritList w) (hg : allTritList g)
    (hgL : g.length = n) (_hrL : run.length = n)
    (hzw : fieldMul n k bench z w = onePeg n)
    (hgr : fieldMul n k bench g run = onePeg n) :
    fieldMul n k bench (fieldMul n k bench run z) (fieldMul n k bench w g) = onePeg n := by
  have hrzT := mulT n k bench hn hk hb h2 run z hr hz
  have hwgT := mulT n k bench hn hk hb h2 w g hw hg
  have hzwg : fieldMul n k bench z (fieldMul n k bench w g) =
      fieldMul n k bench (fieldMul n k bench z w) g :=
    (fieldMul_assoc n k bench z w g hn hk hb h2 hz hw hg).symm
  have e1 := fieldMul_assoc n k bench run z (fieldMul n k bench w g) hn hk hb h2 hr hz hwgT
  rw [e1, hzwg, hzw, fieldMul_one_left n k bench g hn hk hb h2 hg hgL,
    fieldMul_comm n k bench run g hr hg, hgr]

/-- Cubing the affine point cubes the projective triple, and the new
    denominator stays right-invertible. -/
theorem cube_proj (n k bench : Nat) (px py z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hpx : allTritList px) (hpy : allTritList py) (hz : allTritList z) (hw : allTritList w)
    (hzL : z.length = n) (hwL : w.length = n)
    (hinv : fieldMul n k bench z w = onePeg n) :
    fieldMul n k bench (fieldCube n k bench px) (fieldCube n k bench z) =
        fieldCube n k bench (fieldMul n k bench px z) ∧
      fieldMul n k bench (fieldCube n k bench py) (fieldCube n k bench z) =
        fieldCube n k bench (fieldMul n k bench py z) ∧
      fieldMul n k bench (fieldCube n k bench z) (fieldCube n k bench w) = onePeg n ∧
      fieldCube n k bench z ≠ zeroPeg n := by
  have hpxz := fieldCube_mul n k bench px z hn hk hb h2 h3 hpx hz
  have hpyz := fieldCube_mul n k bench py z hn hk hb h2 h3 hpy hz
  have hinvC := cube_left_inv n k bench z w hn hk hb h2 h3 hz hw hzL hwL hinv
  exact ⟨hpxz.symm, hpyz.symm, hinvC.1, hinvC.2⟩

private theorem oneLen (n : Nat) (hn : 0 < n) : (onePeg n).length = n := by
  unfold onePeg
  simp [List.length_replicate]
  omega

/-- `F = u²Z + v²(v + Z)` is `v²Z · (λ² + 1 + run)` once `u = λv` and `v = run·Z`. -/
theorem gap_expanded (n k bench : Nat) (u v z slope run s2 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hvT : allTritList v) (hzT : allTritList z)
    (hsT : allTritList slope) (hrT : allTritList run) (hs2T : allTritList s2)
    (huEq : u = fieldMul n k bench slope v)
    (hvEq : v = fieldMul n k bench run z)
    (hs2 : s2 = fieldMul n k bench slope slope) :
    fformF n k bench u v z =
      fieldMul n k bench (fieldMul n k bench (fieldMul n k bench v v) z)
        (fieldAdd n (fieldAdd n s2 (onePeg n)) run) := by
  let vv := fieldMul n k bench v v
  have hvvT := mulT n k bench hn hk hb h2 v v hvT hvT
  have haT := mulT n k bench hn hk hb h2 vv z hvvT hzT
  have haL := fieldMul_length n k bench vv z hb
  have huu : fieldMul n k bench u u = fieldMul n k bench s2 vv := by
    rw [huEq, hs2]
    exact sq_mul n k bench slope v hn hk hb h2 hsT hvT
  have huuz : fieldMul n k bench (fieldMul n k bench u u) z =
      fieldMul n k bench s2 (fieldMul n k bench vv z) := by
    rw [huu]
    exact fieldMul_assoc n k bench s2 vv z hn hk hb h2 hs2T hvvT hzT
  have hsplit := fieldMul_right_add n k bench vv v z hvvT hvT hzT hb
  have hv3 : fieldMul n k bench vv v = fieldMul n k bench (fieldMul n k bench vv z) run := by
    have hcong : fieldMul n k bench vv v = fieldMul n k bench vv (fieldMul n k bench run z) :=
      congrArg (fieldMul n k bench vv) hvEq
    have eBack : fieldMul n k bench (fieldMul n k bench vv z) run =
        fieldMul n k bench vv (fieldMul n k bench z run) :=
      fieldMul_assoc n k bench vv z run hn hk hb h2 hvvT hzT hrT
    have eComm : fieldMul n k bench z run = fieldMul n k bench run z :=
      fieldMul_comm n k bench z run hzT hrT
    rw [hcong, eBack, eComm]
  have hone : fieldMul n k bench (fieldMul n k bench vv z) (onePeg n) =
      fieldMul n k bench vv z :=
    fieldMul_one_right n k bench (fieldMul n k bench vv z) hn hk hb h2 haT haL
  have hboth : fieldMul n k bench vv (fieldAdd n v z) =
      fieldMul n k bench (fieldMul n k bench vv z) (fieldAdd n run (onePeg n)) := by
    rw [hsplit, hv3]
    have honly : fieldAdd n (fieldMul n k bench (fieldMul n k bench vv z) run)
          (fieldMul n k bench vv z) =
        fieldAdd n (fieldMul n k bench (fieldMul n k bench vv z) run)
          (fieldMul n k bench (fieldMul n k bench vv z) (onePeg n)) :=
      congrArg (fun t => fieldAdd n (fieldMul n k bench (fieldMul n k bench vv z) run) t) hone.symm
    rw [honly]
    exact (fieldMul_right_add n k bench (fieldMul n k bench vv z) run (onePeg n)
      haT hrT (onePeg_trits n) hb).symm
  have hsum : fieldAdd n (fieldMul n k bench s2 (fieldMul n k bench vv z))
        (fieldMul n k bench (fieldMul n k bench vv z) (fieldAdd n run (onePeg n))) =
      fieldMul n k bench (fieldMul n k bench vv z)
        (fieldAdd n s2 (fieldAdd n run (onePeg n))) := by
    rw [fieldMul_comm n k bench s2 (fieldMul n k bench vv z) hs2T haT]
    exact (fieldMul_right_add n k bench (fieldMul n k bench vv z) s2
      (fieldAdd n run (onePeg n)) haT hs2T (addT n run (onePeg n)) hb).symm
  have hrot : fieldAdd n s2 (fieldAdd n run (onePeg n)) =
      fieldAdd n (fieldAdd n s2 (onePeg n)) run := by
    rw [← fieldAdd_assoc n s2 run (onePeg n)]
    exact add3_rot n s2 run (onePeg n)
  unfold fformF
  dsimp only
  rw [huuz, hboth, hsum, hrot]

/-- `v·F + x₂·Z₃ = x₃·Z₃` when `F = a·(x₃ − x₂)` and `Z₃ = v·a`. -/
theorem across_add (n k bench : Nat) (v a x2 x3 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hv : allTritList v) (ha : allTritList a)     (hx2 : allTritList x2) (hx3 : allTritList x3)
    (_hx2L : x2.length = n) (_hx3L : x3.length = n) :
    fieldAdd n (fieldMul n k bench v (fieldMul n k bench a (fieldSub n x3 x2)))
        (fieldMul n k bench x2 (fieldMul n k bench v a)) =
      fieldMul n k bench x3 (fieldMul n k bench v a) := by
  have hdT : allTritList (fieldSub n x3 x2) := addT n x3 (mirrorTrits x2)
  have hzmT : allTritList (mirrorTrits x2) := mirror_trits x2
  have hZ3T := mulT n k bench hn hk hb h2 v a hv ha
  have hadT := mulT n k bench hn hk hb h2 a (fieldSub n x3 x2) ha hdT
  have hx3mT := mulT n k bench hn hk hb h2 x3 (fieldMul n k bench v a) hx3 hZ3T
  have hx3mL := fieldMul_length n k bench x3 (fieldMul n k bench v a) hb
  have e1 : fieldMul n k bench v (fieldMul n k bench a (fieldSub n x3 x2)) =
      fieldMul n k bench (fieldMul n k bench v a) (fieldSub n x3 x2) :=
    (fieldMul_assoc n k bench v a (fieldSub n x3 x2) hn hk hb h2 hv ha hdT).symm
  have e2 : fieldMul n k bench (fieldMul n k bench v a) (fieldSub n x3 x2) =
      fieldAdd n (fieldMul n k bench (fieldMul n k bench v a) x3)
        (fieldMul n k bench (fieldMul n k bench v a) (mirrorTrits x2)) := by
    unfold fieldSub
    exact fieldMul_right_add n k bench (fieldMul n k bench v a) x3 (mirrorTrits x2)
      hZ3T hx3 hzmT hb
  have e3 : fieldMul n k bench (fieldMul n k bench v a) x3 =
      fieldMul n k bench x3 (fieldMul n k bench v a) :=
    fieldMul_comm n k bench (fieldMul n k bench v a) x3 hZ3T hx3
  have e4 : fieldMul n k bench (fieldMul n k bench v a) (mirrorTrits x2) =
      fieldMul n k bench (mirrorTrits x2) (fieldMul n k bench v a) :=
    fieldMul_comm n k bench (fieldMul n k bench v a) (mirrorTrits x2) hZ3T hzmT
  have e5 : fieldAdd n (fieldMul n k bench (mirrorTrits x2) (fieldMul n k bench v a))
        (fieldMul n k bench x2 (fieldMul n k bench v a)) =
      fieldMul n k bench (fieldAdd n (mirrorTrits x2) x2) (fieldMul n k bench v a) :=
    (fieldMul_left_add n k bench (fieldMul n k bench v a) (mirrorTrits x2) x2
      hZ3T hzmT hx2 hb).symm
  have e6 : fieldAdd n (mirrorTrits x2) x2 = zeroPeg n := by
    rw [fieldAdd_comm]
    exact fieldAdd_mirror n x2 hx2
  have e7 : fieldMul n k bench (zeroPeg n) (fieldMul n k bench v a) = zeroPeg n := by
    rw [fieldMul_comm n k bench (zeroPeg n) (fieldMul n k bench v a)
        (by simpa [zeroPeg] using replicate_trits n) hZ3T]
    exact fieldMul_zero n k bench (fieldMul n k bench v a) hb
  have e8 : fieldAdd n (fieldMul n k bench x3 (fieldMul n k bench v a)) (zeroPeg n) =
      fieldMul n k bench x3 (fieldMul n k bench v a) :=
    fieldAdd_zero_right n (fieldMul n k bench x3 (fieldMul n k bench v a)) hx3mT hx3mL
  have e9 : fieldAdd n
        (fieldAdd n (fieldMul n k bench x3 (fieldMul n k bench v a))
          (fieldMul n k bench (mirrorTrits x2) (fieldMul n k bench v a)))
        (fieldMul n k bench x2 (fieldMul n k bench v a)) =
      fieldAdd n (fieldMul n k bench x3 (fieldMul n k bench v a))
        (fieldAdd n (fieldMul n k bench (mirrorTrits x2) (fieldMul n k bench v a))
          (fieldMul n k bench x2 (fieldMul n k bench v a))) :=
    fieldAdd_assoc n (fieldMul n k bench x3 (fieldMul n k bench v a))
      (fieldMul n k bench (mirrorTrits x2) (fieldMul n k bench v a))
      (fieldMul n k bench x2 (fieldMul n k bench v a))
  rw [e1, e2, e3, e4, e9, e5, e6, e7, e8]

/-- The new across is `x₃` times the new bottom. `x₃` is the chord formula. -/
theorem across_on_x3 (n k bench : Nat) (x y x2 y2 z g : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hx : allTritList x) (hy : allTritList y) (hx2 : allTritList x2) (hy2 : allTritList y2)
    (hz : allTritList z) (hg : allTritList g)
    (hxL : x.length = n) (hyL : y.length = n) (hx2L : x2.length = n) (hy2L : y2.length = n)
    (hzL : z.length = n) (hgL : g.length = n)
    (hinv : fieldMul n k bench g (fieldSub n x2 x) = onePeg n) :
    let run := fieldSub n x2 x
    let rise := fieldSub n y2 y
    let slope := fieldMul n k bench rise g
    let x3 := fieldAdd n (fieldAdd n (fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n)) x)
      (mirrorTrits run)
    let v := fformRun n k bench x2 z (fieldMul n k bench x z)
    fformAcross n k bench x2 (fformRise n k bench y2 z (fieldMul n k bench y z)) v z =
      fieldMul n k bench x3 (fformBottom n k bench v z) := by
  intro run rise slope x3 v
  have hrunT : allTritList run := addT n x2 (mirrorTrits x)
  have hriseT : allTritList rise := addT n y2 (mirrorTrits y)
  have hslopeT := mulT n k bench hn hk hb h2 rise g hriseT hg
  have hs2T := mulT n k bench hn hk hb h2 slope slope hslopeT hslopeT
  have hrunL : run.length = n := subLen n x2 x
  have hriseL : rise.length = n := subLen n y2 y
  have hv : v = fieldMul n k bench run z := run_over_z n k bench x x2 z hb hx hx2 hz
  have hu : fformRise n k bench y2 z (fieldMul n k bench y z) =
      fieldMul n k bench rise z := rise_over_z n k bench y y2 z hb hy hy2 hz
  have huS : fformRise n k bench y2 z (fieldMul n k bench y z) =
      fieldMul n k bench slope v := by
    rw [hu, hv]
    exact (mul_inv_right n k bench rise g run z hn hk hb h2 hriseT hg hrunT hz hriseL hinv).symm
  have hprodT := mulT n k bench hn hk hb h2 run z hrunT hz
  have hvT : allTritList v := by
    rw [hv]
    exact hprodT
  have hs2 : fieldMul n k bench slope slope = fieldMul n k bench slope slope := rfl
  let s2 := fieldMul n k bench slope slope
  have hgap := gap_expanded n k bench (fformRise n k bench y2 z (fieldMul n k bench y z))
    v z slope run s2 hn hk hb h2 hvT hz hslopeT hrunT hs2T huS hv rfl
  have hdiff := x3_minus_x2 n k bench slope x x2 hn hk hb h2 hslopeT hx hx2 hxL hx2L
  have hx3T : allTritList x3 := by
    unfold x3
    exact addT n _ _
  have hx3L : x3.length = n := by
    unfold x3
    exact addLen n _ _
  have haT := mulT n k bench hn hk hb h2 (fieldMul n k bench v v) z
    (mulT n k bench hn hk hb h2 v v hvT hvT) hz
  have hF : fformF n k bench (fformRise n k bench y2 z (fieldMul n k bench y z)) v z =
      fieldMul n k bench (fieldMul n k bench (fieldMul n k bench v v) z) (fieldSub n x3 x2) := by
    rw [hgap]
    have hsub : fieldAdd n (fieldAdd n s2 (onePeg n)) run = fieldSub n x3 x2 := by
      have hwhite : whiteHole0 n = onePeg n := whiteHole0_eq_onePeg n
      simpa [x3, s2, hwhite] using hdiff.symm
    rw [hsub]
  have hbot : fformBottom n k bench v z =
      fieldMul n k bench v (fieldMul n k bench (fieldMul n k bench v v) z) := by
    rw [bottom_as_cube n k bench v z hn hk hb h2 h3 hvT hz,
      cube_as_mul n k bench v hn hk hb h2 h3 hvT]
    exact fieldMul_assoc n k bench v (fieldMul n k bench v v) z hn hk hb h2 hvT
      (mulT n k bench hn hk hb h2 v v hvT hvT) hz
  unfold fformAcross
  rw [hF, hbot]
  exact across_add n k bench v (fieldMul n k bench (fieldMul n k bench v v) z) x2 x3
    hn hk hb h2 hvT haT hx2 hx3T hx2L hx3L

end EcbsLink2.Link2
