/-
  The new up is `y₃` times the new bottom, and that bottom stays
  right-invertible. Irreducibility is not a hypothesis.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformChord

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

/-- `(x − x₃) − (x₂ − x₃) = x − x₂`. -/
theorem sub_slide (n : Nat) (x x2 x3 : List Nat)
    (hx2 : allTritList x2) (hx3 : allTritList x3)
    (hx2L : x2.length = n) :
    fieldSub n (fieldSub n x x3) (fieldSub n x2 x3) = fieldSub n x x2 := by
  have hm2 : mirrorTrits (fieldAdd n x2 (mirrorTrits x3)) =
      fieldAdd n (mirrorTrits x2) x3 := by
    rw [mirrorTrits_fieldAdd n x2 (mirrorTrits x3) hx2 (mirror_trits x3),
      mirrorTrits_invol x3 hx3]
  have hmx2T : allTritList (mirrorTrits x2) := mirror_trits x2
  have eA := fieldAdd_assoc n x (mirrorTrits x3) (fieldAdd n (mirrorTrits x2) x3)
  have eB : fieldAdd n (mirrorTrits x3) (fieldAdd n (mirrorTrits x2) x3) =
      fieldAdd n (fieldAdd n (mirrorTrits x3) (mirrorTrits x2)) x3 :=
    (fieldAdd_assoc n (mirrorTrits x3) (mirrorTrits x2) x3).symm
  have eC : fieldAdd n (mirrorTrits x3) (mirrorTrits x2) =
      fieldAdd n (mirrorTrits x2) (mirrorTrits x3) :=
    fieldAdd_comm n (mirrorTrits x3) (mirrorTrits x2)
  have eD : fieldAdd n (fieldAdd n (mirrorTrits x2) (mirrorTrits x3)) x3 =
      fieldAdd n (mirrorTrits x2) (fieldAdd n (mirrorTrits x3) x3) :=
    fieldAdd_assoc n (mirrorTrits x2) (mirrorTrits x3) x3
  have eE : fieldAdd n (mirrorTrits x3) x3 = zeroPeg n := by
    rw [fieldAdd_comm]
    exact fieldAdd_mirror n x3 hx3
  have eF : fieldAdd n (mirrorTrits x2) (zeroPeg n) = mirrorTrits x2 :=
    fieldAdd_zero_right n (mirrorTrits x2) hmx2T (by rw [mirLen, hx2L])
  unfold fieldSub
  rw [hm2, eA, eB, eC, eD, eE, eF]

theorem mirror_sub (n : Nat) (a b : List Nat)
    (ha : allTritList a) (hb : allTritList b) :
    mirrorTrits (fieldSub n a b) = fieldSub n b a := by
  unfold fieldSub
  rw [mirrorTrits_fieldAdd n a (mirrorTrits b) ha (mirror_trits b),
    mirrorTrits_invol b hb, fieldAdd_comm]

/-- The chord up equals `−(y₂ + λ·(x₃ − x₂))`. -/
theorem y3_on_line (n k bench : Nat) (slope x y x2 y2 x3 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hs : allTritList slope) (hx : allTritList x) (hy : allTritList y)
    (hx2 : allTritList x2) (hy2 : allTritList y2) (hx3 : allTritList x3)
    (hxL : x.length = n) (hyL : y.length = n) (hx2L : x2.length = n)
    (hy2L : y2.length = n) (hx3L : x3.length = n)
    (hlam : fieldMul n k bench slope (fieldSub n x2 x) = fieldSub n y2 y) :
    fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y) =
      mirrorTrits (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2))) := by
  have hd1T : allTritList (fieldSub n x x3) := addT n x (mirrorTrits x3)
  have hd2T : allTritList (fieldSub n x2 x3) := addT n x2 (mirrorTrits x3)
  have hgapT : allTritList (fieldSub n x3 x2) := addT n x3 (mirrorTrits x2)
  have hriseT : allTritList (fieldSub n y2 y) := addT n y2 (mirrorTrits y)
  have hrunT : allTritList (fieldSub n x2 x) := addT n x2 (mirrorTrits x)
  have hs1T := mulT n k bench hn hk hb h2 slope (fieldSub n x x3) hs hd1T
  have hs2T := mulT n k bench hn hk hb h2 slope (fieldSub n x2 x3) hs hd2T
  have hsgT := mulT n k bench hn hk hb h2 slope (fieldSub n x3 x2) hs hgapT
  have hchordT : allTritList
      (fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y)) :=
    addT n _ _
  have haltT : allTritList
      (fieldAdd n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2)) :=
    addT n _ _
  have hchordL := addLen n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y)
  have haltL := addLen n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2)
  have hmyL : (mirrorTrits y2).length = n := by rw [mirLen, hy2L]
  have hslide := sub_slide n x x2 x3 hx2 hx3 hx2L
  have hmirRun := mirror_sub n x2 x hx2 hx
  have hdiff : fieldSub n (fieldSub n x x3) (fieldSub n x2 x3) = mirrorTrits (fieldSub n x2 x) := by
    rw [hslide, ← hmirRun]
  have hfactor : fieldMul n k bench slope
        (fieldSub n (fieldSub n x x3) (fieldSub n x2 x3)) =
      mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x)) := by
    rw [hdiff]
    exact fieldMul_mirror_right n k bench slope (fieldSub n x2 x) hs hrunT
  have hzero : fieldAdd n
        (fieldMul n k bench slope (fieldSub n (fieldSub n x x3) (fieldSub n x2 x3)))
        (fieldSub n y2 y) = zeroPeg n := by
    rw [hfactor, hlam, fieldAdd_comm, fieldAdd_mirror n (fieldSub n y2 y) hriseT]
  have hleft : fieldAdd n (fieldMul n k bench slope (fieldSub n x x3))
        (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) =
      fieldMul n k bench slope
        (fieldSub n (fieldSub n x x3) (fieldSub n x2 x3)) := by
    rw [← fieldMul_mirror_right n k bench slope (fieldSub n x2 x3) hs hd2T]
    exact (fieldMul_right_add n k bench slope (fieldSub n x x3)
      (mirrorTrits (fieldSub n x2 x3)) hs hd1T (mirror_trits _) hb).symm
  let chord := fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y)
  let alt := fieldAdd n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2)
  have hmAlt : mirrorTrits alt =
      fieldAdd n (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) y2 := by
    show mirrorTrits (fieldAdd n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2)) =
      fieldAdd n (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) y2
    rw [mirrorTrits_fieldAdd n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2)
        hs2T (mirror_trits y2), mirrorTrits_invol y2 hy2]
  have hpair : fieldAdd n chord (mirrorTrits alt) = zeroPeg n := by
    show fieldAdd n
        (fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y))
        (mirrorTrits alt) = zeroPeg n
    rw [hmAlt]
    have rearr : fieldAdd n
          (fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y))
          (fieldAdd n (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) y2) =
        fieldAdd n
          (fieldAdd n (fieldMul n k bench slope (fieldSub n x x3))
            (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))))
          (fieldAdd n (mirrorTrits y) y2) := by
      rw [fieldAdd_assoc n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y)
          (fieldAdd n (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) y2)]
      rw [(fieldAdd_assoc n (mirrorTrits y)
          (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3))) y2).symm]
      rw [fieldAdd_comm n (mirrorTrits y)
          (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3)))]
      rw [fieldAdd_assoc n (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3)))
          (mirrorTrits y) y2]
      rw [(fieldAdd_assoc n (fieldMul n k bench slope (fieldSub n x x3))
          (mirrorTrits (fieldMul n k bench slope (fieldSub n x2 x3)))
          (fieldAdd n (mirrorTrits y) y2)).symm]
    rw [rearr, fieldAdd_comm n (mirrorTrits y) y2, hleft]
    unfold fieldSub at hzero
    exact hzero
  have halt0 : fieldAdd n alt (mirrorTrits alt) = zeroPeg n :=
    fieldAdd_mirror n alt haltT
  have hmirAltT : allTritList (mirrorTrits alt) := mirror_trits alt
  have hmirAltL : (mirrorTrits alt).length = n := by rw [mirLen, haltL]
  have hsame : fieldAdd n chord (mirrorTrits alt) = fieldAdd n alt (mirrorTrits alt) := by
    rw [hpair, halt0]
  have hchordAlt : chord = alt :=
    fieldAdd_cancel_right n chord alt (mirrorTrits alt) hchordT haltT hmirAltT
      hchordL haltL hmirAltL hsame
  have htarget : alt =
      mirrorTrits (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2))) := by
    have hmg : mirrorTrits (fieldSub n x3 x2) = fieldSub n x2 x3 :=
      mirror_sub n x3 x2 hx3 hx2
    have hsm : fieldMul n k bench slope (fieldSub n x2 x3) =
        mirrorTrits (fieldMul n k bench slope (fieldSub n x3 x2)) := by
      rw [← hmg]
      exact fieldMul_mirror_right n k bench slope (fieldSub n x3 x2) hs hgapT
    show fieldAdd n (fieldMul n k bench slope (fieldSub n x2 x3)) (mirrorTrits y2) =
      mirrorTrits (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2)))
    rw [hsm, fieldAdd_comm n (mirrorTrits (fieldMul n k bench slope (fieldSub n x3 x2)))
        (mirrorTrits y2),
      ← mirrorTrits_fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2)) hy2 hsgT]
  show chord = mirrorTrits (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2)))
  rw [hchordAlt, htarget]

/-- `−(u·F + y₂·Z₃) = −(y₂ + λ·(x₃ − x₂)) · Z₃` when `u = λv`, `F = a·(x₃ − x₂)`,
    and `Z₃ = v·a`. -/
theorem up_mul (n k bench : Nat) (slope v a y2 x3 x2 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hs : allTritList slope) (hv : allTritList v) (ha : allTritList a)
    (hy2 : allTritList y2) (hx3 : allTritList x3) (hx2 : allTritList x2) :
    mirrorTrits (fieldAdd n
        (fieldMul n k bench (fieldMul n k bench slope v)
          (fieldMul n k bench a (fieldSub n x3 x2)))
        (fieldMul n k bench y2 (fieldMul n k bench v a))) =
      fieldMul n k bench
        (mirrorTrits (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2))))
        (fieldMul n k bench v a) := by
  have hdT : allTritList (fieldSub n x3 x2) := addT n x3 (mirrorTrits x2)
  have huT := mulT n k bench hn hk hb h2 slope v hs hv
  have hadT := mulT n k bench hn hk hb h2 a (fieldSub n x3 x2) ha hdT
  have hZ3T := mulT n k bench hn hk hb h2 v a hv ha
  have hsdT := mulT n k bench hn hk hb h2 slope (fieldSub n x3 x2) hs hdT
  have e1 : fieldMul n k bench (fieldMul n k bench slope v)
        (fieldMul n k bench a (fieldSub n x3 x2)) =
      fieldMul n k bench slope (fieldMul n k bench v
        (fieldMul n k bench a (fieldSub n x3 x2))) :=
    fieldMul_assoc n k bench slope v (fieldMul n k bench a (fieldSub n x3 x2))
      hn hk hb h2 hs hv hadT
  have e2 : fieldMul n k bench v (fieldMul n k bench a (fieldSub n x3 x2)) =
      fieldMul n k bench (fieldMul n k bench v a) (fieldSub n x3 x2) :=
    (fieldMul_assoc n k bench v a (fieldSub n x3 x2) hn hk hb h2 hv ha hdT).symm
  have e3 : fieldMul n k bench slope
        (fieldMul n k bench (fieldMul n k bench v a) (fieldSub n x3 x2)) =
      fieldMul n k bench (fieldMul n k bench slope (fieldMul n k bench v a))
        (fieldSub n x3 x2) :=
    (fieldMul_assoc n k bench slope (fieldMul n k bench v a) (fieldSub n x3 x2)
      hn hk hb h2 hs hZ3T hdT).symm
  have e4 : fieldMul n k bench slope (fieldMul n k bench v a) =
      fieldMul n k bench (fieldMul n k bench v a) slope :=
    fieldMul_comm n k bench slope (fieldMul n k bench v a) hs hZ3T
  have e5 : fieldMul n k bench (fieldMul n k bench (fieldMul n k bench v a) slope)
        (fieldSub n x3 x2) =
      fieldMul n k bench (fieldMul n k bench v a)
        (fieldMul n k bench slope (fieldSub n x3 x2)) :=
    fieldMul_assoc n k bench (fieldMul n k bench v a) slope (fieldSub n x3 x2)
      hn hk hb h2 hZ3T hs hdT
  have e6 : fieldMul n k bench (fieldMul n k bench v a)
        (fieldMul n k bench slope (fieldSub n x3 x2)) =
      fieldMul n k bench (fieldMul n k bench slope (fieldSub n x3 x2))
        (fieldMul n k bench v a) :=
    fieldMul_comm n k bench (fieldMul n k bench v a)
      (fieldMul n k bench slope (fieldSub n x3 x2)) hZ3T hsdT
  have e7 : fieldAdd n
        (fieldMul n k bench (fieldMul n k bench slope (fieldSub n x3 x2))
          (fieldMul n k bench v a))
        (fieldMul n k bench y2 (fieldMul n k bench v a)) =
      fieldMul n k bench
        (fieldAdd n (fieldMul n k bench slope (fieldSub n x3 x2)) y2)
        (fieldMul n k bench v a) :=
    (fieldMul_left_add n k bench (fieldMul n k bench v a)
      (fieldMul n k bench slope (fieldSub n x3 x2)) y2 hZ3T hsdT hy2 hb).symm
  have e8 : fieldAdd n (fieldMul n k bench slope (fieldSub n x3 x2)) y2 =
      fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2)) :=
    fieldAdd_comm n (fieldMul n k bench slope (fieldSub n x3 x2)) y2
  have hsumT : allTritList (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2))) :=
    addT n y2 _
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  exact (fieldMul_mirror_left n k bench
    (fieldAdd n y2 (fieldMul n k bench slope (fieldSub n x3 x2)))
    (fieldMul n k bench v a) hsumT hZ3T).symm

/-- A right inverse of `v³·Z` is the cube of `v`'s inverse, times `Z`'s inverse. -/
theorem denom_inv (n k bench : Nat) (cv z ci w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hcv : allTritList cv) (hz : allTritList z) (hci : allTritList ci) (hw : allTritList w)
    (hzL : z.length = n)
    (hcvz : fieldMul n k bench cv ci = onePeg n)
    (hzw : fieldMul n k bench z w = onePeg n) :
    fieldMul n k bench (fieldMul n k bench cv z) (fieldMul n k bench ci w) = onePeg n := by
  have hzciT := mulT n k bench hn hk hb h2 z ci hz hci
  have hciwT := mulT n k bench hn hk hb h2 ci w hci hw
  have hcvzT := mulT n k bench hn hk hb h2 cv z hcv hz
  have hcizT := mulT n k bench hn hk hb h2 ci z hci hz
  have e1 :=
    (fieldMul_assoc n k bench (fieldMul n k bench cv z) ci w hn hk hb h2 hcvzT hci hw).symm
  have e2 := fieldMul_assoc n k bench cv z ci hn hk hb h2 hcv hz hci
  have e3 := fieldMul_comm n k bench z ci hz hci
  have e4 := (fieldMul_assoc n k bench cv ci z hn hk hb h2 hcv hci hz).symm
  rw [e1, e2, e3, e4, hcvz, fieldMul_one_left n k bench z hn hk hb h2 hz hzL, hzw]

/-- The new up is the chord `y₃` times the new bottom. -/
theorem up_on_parts (n k bench : Nat)
    (slope v a u z y2 x y x2 x3 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hs : allTritList slope) (hv : allTritList v) (ha : allTritList a)
    (hz : allTritList z) (hy2 : allTritList y2) (hx : allTritList x) (hy : allTritList y)
    (hx2 : allTritList x2) (hx3 : allTritList x3)
    (hxL : x.length = n) (hyL : y.length = n) (hx2L : x2.length = n)
    (hy2L : y2.length = n) (hx3L : x3.length = n)
    (hu : u = fieldMul n k bench slope v)
    (hF : fformF n k bench u v z =
      fieldMul n k bench a (fieldSub n x3 x2))
    (hbot : fformBottom n k bench v z = fieldMul n k bench v a)
    (hlam : fieldMul n k bench slope (fieldSub n x2 x) = fieldSub n y2 y) :
    fformUp n k bench y2 u v z =
      fieldMul n k bench
        (fieldAdd n (fieldMul n k bench slope (fieldSub n x x3)) (mirrorTrits y))
        (fformBottom n k bench v z) := by
  unfold fformUp
  rw [hu]
  have hF' := hF
  rw [hu] at hF'
  rw [hF', hbot]
  rw [up_mul n k bench slope v a y2 x3 x2 hn hk hb h2 hs hv ha hy2 hx3 hx2]
  rw [← y3_on_line n k bench slope x y x2 y2 x3 hn hk hb h2 hs hx hy hx2 hy2 hx3
      hxL hyL hx2L hy2L hx3L hlam]

/-- `v³·Z` stays right-invertible when `v = run·Z`, `g·run = 1`, and `Z·w = 1`. -/
theorem bottom_of_run (n k bench : Nat) (run z w g : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hr : allTritList run) (hz : allTritList z) (hw : allTritList w) (hg : allTritList g)
    (hzL : z.length = n) (hwL : w.length = n) (hgL : g.length = n) (hrL : run.length = n)
    (hzw : fieldMul n k bench z w = onePeg n)
    (hgr : fieldMul n k bench g run = onePeg n) :
    fieldMul n k bench (fformBottom n k bench (fieldMul n k bench run z) z)
        (fieldMul n k bench (fieldCube n k bench (fieldMul n k bench w g)) w) =
      onePeg n := by
  have hvT := mulT n k bench hn hk hb h2 run z hr hz
  have hiT := mulT n k bench hn hk hb h2 w g hw hg
  have hvL := fieldMul_length n k bench run z hb
  have hiL := fieldMul_length n k bench w g hb
  have hv1 := v_right_inv n k bench run z w g hn hk hb h2 hr hz hw hg hgL hrL hzw hgr
  have hc := cube_left_inv n k bench (fieldMul n k bench run z) (fieldMul n k bench w g)
    hn hk hb h2 h3 hvT hiT hvL hiL hv1
  have hvC := fieldCube_trits n k bench (fieldMul n k bench run z) hvT h3 (Nat.le_of_lt hk)
  have hiC := fieldCube_trits n k bench (fieldMul n k bench w g) hiT h3 (Nat.le_of_lt hk)
  rw [bottom_as_cube n k bench (fieldMul n k bench run z) z hn hk hb h2 h3 hvT hz]
  exact denom_inv n k bench (fieldCube n k bench (fieldMul n k bench run z)) z
    (fieldCube n k bench (fieldMul n k bench w g)) w hn hk hb h2 hvC hz hiC hw hzL hc.1 hzw

end EcbsLink2.Link2
