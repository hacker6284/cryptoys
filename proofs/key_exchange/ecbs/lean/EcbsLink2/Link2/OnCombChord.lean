/-
  The point `walkStep` returns is `OnComb.x3` and `OnComb.yUp`.
  `walk_chord_coords` cubes the affine point inside the chord.
  `across_is_chord` and `up_is_chord` say the emitted homes are that chord
  times the new bottom. The bottom's right inverse makes the factors unique.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellWalk
import EcbsLink2.Link2.FformChord
import EcbsLink2.Link2.FformLiveAny
import EcbsLink2.Link2.FformProj

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem mulT (n k bench : Nat) (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (x y : List Nat) (hx : allTritList x) (hy : allTritList y) :
    allTritList (fieldMul n k bench x y) := by
  rw [fieldMul_eq_mulVal n k bench x y hn hk hb h2 hx hy]
  exact mulVal_trits n k hn hk x y hx hy

private theorem subLen (n : Nat) (a b : List Nat) : (fieldSub n a b).length = n := by
  simp [fieldSub, fieldAdd, List.length_map, List.length_range]

private theorem addLen (n : Nat) (a b : List Nat) : (fieldAdd n a b).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

/-- A right inverse cancels. -/
private theorem mul_cancel (n k bench : Nat) (a b z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (ha : allTritList a) (hbT : allTritList b) (hz : allTritList z) (hw : allTritList w)
    (haL : a.length = n) (hbL : b.length = n)
    (h : fieldMul n k bench a z = fieldMul n k bench b z)
    (hinv : fieldMul n k bench z w = onePeg n) :
    a = b := by
  have hazT := mulT n k bench hn hk hb h2 a z ha hz
  have hbzT := mulT n k bench hn hk hb h2 b z hbT hz
  have h1 : fieldMul n k bench (fieldMul n k bench a z) w =
      fieldMul n k bench (fieldMul n k bench b z) w :=
    congrArg (fun t => fieldMul n k bench t w) h
  have ha1 : fieldMul n k bench (fieldMul n k bench a z) w = a := by
    rw [fieldMul_assoc n k bench a z w hn hk hb h2 ha hz hw, hinv,
      fieldMul_one_right n k bench a hn hk hb h2 ha haL]
  have hb1 : fieldMul n k bench (fieldMul n k bench b z) w = b := by
    rw [fieldMul_assoc n k bench b z w hn hk hb h2 hbT hz hw, hinv,
      fieldMul_one_right n k bench b hn hk hb h2 hbT hbL]
  exact ha1.symm.trans (h1.trans hb1)

private theorem flag_y (y2 : List Nat) (c : Nat) (red : Bool)
    (hc : c = 1 ∨ c = 2) (hred : red = decide (c = 2)) :
    (if red then mirrorTrits y2 else y2) =
      if c = 2 then mirrorTrits y2 else y2 := by
  rcases hc with rfl | rfl
  · subst hred
    simp
  · subst hred
    simp

/-- The new up is the chord `y₃` times the new bottom, on the same data as
    `across_is_chord`. -/
theorem up_of_chord (n k bench : Nat) (x y x2 y2 z g : List Nat)
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
    let y3 := fieldSub n (fieldMul n k bench slope (fieldSub n x x3)) y
    let v := fformRun n k bench x2 z (fieldMul n k bench x z)
    let u := fformRise n k bench y2 z (fieldMul n k bench y z)
    fformUp n k bench y2 u v z = fieldMul n k bench y3 (fformBottom n k bench v z) := by
  intro run rise slope x3 y3 v u
  have hrunT : allTritList run := fieldAdd_trits n x2 (mirrorTrits x)
  have hriseT : allTritList rise := fieldAdd_trits n y2 (mirrorTrits y)
  have hslopeT := mulT n k bench hn hk hb h2 rise g hriseT hg
  have hs2T := mulT n k bench hn hk hb h2 slope slope hslopeT hslopeT
  have hrunL : run.length = n := subLen n x2 x
  have hriseL : rise.length = n := subLen n y2 y
  have hv : v = fieldMul n k bench run z := run_over_z n k bench x x2 z hb hx hx2 hz
  have hu : u = fieldMul n k bench rise z := rise_over_z n k bench y y2 z hb hy hy2 hz
  have huS : u = fieldMul n k bench slope v := by
    rw [hu, hv]
    exact (mul_inv_right n k bench rise g run z hn hk hb h2 hriseT hg hrunT hz hriseL hinv).symm
  have hprodT := mulT n k bench hn hk hb h2 run z hrunT hz
  have hvT : allTritList v := by
    rw [hv]
    exact hprodT
  let s2 := fieldMul n k bench slope slope
  have hgap := gap_expanded n k bench u v z slope run s2 hn hk hb h2 hvT hz hslopeT hrunT hs2T
    huS hv rfl
  have hdiff := x3_minus_x2 n k bench slope x x2 hn hk hb h2 hslopeT hx hx2 hxL hx2L
  have hx3T : allTritList x3 := fieldAdd_trits n _ _
  have hx3L : x3.length = n := addLen n _ _
  have hvvT := mulT n k bench hn hk hb h2 v v hvT hvT
  have haT := mulT n k bench hn hk hb h2 (fieldMul n k bench v v) z hvvT hz
  have hF : fformF n k bench u v z =
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
    exact fieldMul_assoc n k bench v (fieldMul n k bench v v) z hn hk hb h2 hvT hvvT hz
  have hlam : fieldMul n k bench slope run = rise := by
    have hstep := fieldMul_assoc n k bench rise g run hn hk hb h2 hriseT hg hrunT
    rw [show slope = fieldMul n k bench rise g from rfl, hstep, hinv,
      fieldMul_one_right n k bench rise hn hk hb h2 hriseT hriseL]
  let a := fieldMul n k bench (fieldMul n k bench v v) z
  have hy3 : y3 = fieldSub n (fieldMul n k bench slope (fieldSub n x x3)) y := rfl
  exact up_is_chord n k bench slope v a u z y2 x y x2 x3 y3
    hn hk hb h2 hslopeT hvT haT hz hy2 hx hy hx2 hx3T
    hxL hyL hx2L hy2L hx3L huS hF hbot hlam hy3

/-- `walkStep` on the live affine point cubes that point and adds the base.
    `OnComb.x3` and `OnComb.yUp` are that chord once the comb's `u` and `v`
    are the rise and the run of the cubed homes. -/
theorem oncomb_chord
    (t : Spec.Tier) (bZ : Ecbs.Board) (red : Bool)
    (baseX baseY px py ax' ay' : List Nat)
    (moves' slides' ctrl' cMul c1 c : Nat)
    (o : OnComb t bZ red baseX baseY moves' slides' ctrl' cMul c1)
    (hsh : TierShape t) (sat : TierSat t)
    (hpos : 0 < t.n) (hnb : t.n ≤ t.benchlen)
    (hpxT : allTritList px) (hpyT : allTritList py) (hzT : allTritList o.zP)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hpxL : px.length = t.n) (hpyL : py.length = t.n) (hzL : o.zP.length = t.n)
    (hbxL : baseX.length = t.n) (hbyL : baseY.length = t.n)
    (hXP : o.xP = fieldMul t.n t.k t.benchlen px o.zP)
    (hYP : o.yP = fieldMul t.n t.k t.benchlen py o.zP)
    (hz : o.z = fieldCube t.n t.k t.benchlen o.zP)
    (hc : c = 1 ∨ c = 2) (hred : red = decide (c = 2))
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) c =
      some (true, (ax', ay'))) :
    o.x3 = ax' ∧ o.yUp = ay' := by
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  let xP := o.xP
  let yP := o.yP
  let zP := o.zP
  have hv := o.hv
  have hu := o.hu
  have hk : k < n := by
    have hgap : 0 < n - k := by
      rw [show n - k = t.n - t.k from rfl, hsh.gap]
      exact Nat.mul_pos hsh.w0 hsh.r0
    omega
  have h3span : 3 * (n - 1) < bench := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have h2 : 2 * (n - 1) < bench := by
    have hmul : 2 * (n - 1) ≤ 3 * (n - 1) := Nat.mul_le_mul_right _ (by decide)
    exact Nat.lt_of_le_of_lt hmul h3span
  let x := fieldCube n k bench px
  let y := fieldCube n k bench py
  let z := fieldCube n k bench zP
  let yB := if red then mirrorTrits baseY else baseY
  have hxT := fieldCube_trits n k bench px hpxT h3span hsh.k_le
  have hyT := fieldCube_trits n k bench py hpyT h3span hsh.k_le
  have hzT' := fieldCube_trits n k bench zP hzT h3span hsh.k_le
  have hxL := fieldCube_length n k bench px hnb
  have hyL := fieldCube_length n k bench py hnb
  have hzL' := fieldCube_length n k bench zP hnb
  have hXP' : xP = fieldMul n k bench px zP := hXP
  have hYP' : yP = fieldMul n k bench py zP := hYP
  have hcubeX : fieldCube n k bench xP = fieldMul n k bench x z := by
    rw [hXP', fieldCube_mul n k bench px zP hpos hk hnb h2 h3span hpxT hzT]
  have hcubeY : fieldCube n k bench yP = fieldMul n k bench y z := by
    rw [hYP', fieldCube_mul n k bench py zP hpos hk hnb h2 h3span hpyT hzT]
  have hv' : o.v = fformRun n k bench baseX z (fieldMul n k bench x z) := by
    rw [hv, hcubeX]
  have hu' : o.u = fformRise n k bench yB z (fieldMul n k bench y z) := by
    rw [hu, hcubeY]
  have hflag := flag_y baseY c red hc hred
  obtain ⟨g, hg, hxForm, hyForm⟩ :=
    walk_chord_coords n k bench baseX baseY px py ax' ay' c hc hwalk
  have hxForm' : ax' = fieldAdd n (fieldAdd n (fieldAdd n
      (fieldMul n k bench
        (fieldMul n k bench (fieldSub n yB y) g)
        (fieldMul n k bench (fieldSub n yB y) g))
      (whiteHole0 n)) x) (mirrorTrits (fieldSub n baseX x)) := by
    rw [← hflag, ← show x = fieldCube n k bench px from rfl,
      ← show y = fieldCube n k bench py from rfl] at hxForm
    exact hxForm
  have hyForm' : ay' = fieldSub n
      (fieldMul n k bench (fieldMul n k bench (fieldSub n yB y) g) (fieldSub n x ax')) y := by
    rw [← hflag, ← show x = fieldCube n k bench px from rfl,
      ← show y = fieldCube n k bench py from rfl] at hyForm
    exact hyForm
  have hrunT : allTritList (fieldSub n baseX x) :=
    fieldAdd_trits n baseX (mirrorTrits x)
  have hrunL : (fieldSub n baseX x).length = n := subLen n baseX x
  obtain ⟨hgL, hgT, hginv⟩ :=
    fieldInv_witness t (fieldSub n baseX x) g sat hsh hpos hrunL hrunT hg
  have hyBT : allTritList yB := by
    cases red
    · simpa [yB] using hbyT
    · simpa [yB] using mirror_trits baseY
  have hyBL : yB.length = n := by
    cases red
    · simpa [yB] using hbyL
    · simpa [yB, mirrorTrits, List.length_map] using hbyL
  let run := fieldSub n baseX x
  let rise := fieldSub n yB y
  let slope := fieldMul n k bench rise g
  let chordX := fieldAdd n
    (fieldAdd n (fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n)) x)
    (mirrorTrits run)
  have hchordX : ax' = chordX := by
    simpa [chordX, run, rise, slope] using hxForm'
  have hcross := across_is_chord n k bench x y baseX yB z g chordX
    hpos hk hnb h2 h3span hxT hyT hbxT hyBT hzT' hgT
    hxL hyL hbxL hyBL hzL' hgL hginv
    (by simpa [chordX, run, rise, slope] using hchordX.symm)
  have hvRun : o.v = fformRun n k bench baseX z (fieldMul n k bench x z) := hv'
  have huRise : o.u = fformRise n k bench yB z (fieldMul n k bench y z) := hu'
  have hzZ : o.z = z := hz
  have hL : fformAcross n k bench o.x2 o.u o.v o.z =
      fformAcross n k bench baseX
        (fformRise n k bench yB z (fieldMul n k bench y z))
        (fformRun n k bench baseX z (fieldMul n k bench x z)) z := by
    rw [o.hx2, huRise, hvRun, hzZ]
  have hBot : fformBottom n k bench o.v o.z =
      fformBottom n k bench
        (fformRun n k bench baseX z (fieldMul n k bench x z)) z := by
    rw [hvRun, hzZ]
  have hmulX : fieldMul n k bench o.x3 (fformBottom n k bench o.v o.z) =
      fieldMul n k bench chordX (fformBottom n k bench o.v o.z) := by
    have h1 := o.hx
    rw [hL, hcross, ← hBot] at h1
    exact h1.symm
  rcases o.hinv with ⟨w, hwL, hwT, hw⟩
  have hbotT : allTritList (fformBottom n k bench o.v o.z) := by
    unfold fformBottom
    have hvT := o.s.triV
    have hzT0 := o.s.triZ
    have hvv := mulT n k bench hpos hk hnb h2 o.v o.v hvT hvT
    have hvvz := mulT n k bench hpos hk hnb h2 (fieldMul n k bench o.v o.v) o.z hvv hzT0
    exact mulT n k bench hpos hk hnb h2 o.v _ hvT hvvz
  have hchordT : allTritList chordX := fieldAdd_trits n _ _
  have hchordL : chordX.length = n := addLen n _ _
  have hxId := mul_cancel n k bench o.x3 chordX (fformBottom n k bench o.v o.z) w
    hpos hk hnb h2 o.hpxT hchordT hbotT hwT o.hpx hchordL hmulX hw
  have hxEq : o.x3 = ax' := hxId.trans hchordX.symm
  have hup := up_of_chord n k bench x y baseX yB z g
    hpos hk hnb h2 h3span hxT hyT hbxT hyBT hzT' hgT
    hxL hyL hbxL hyBL hzL' hgL hginv
  have hyChord : ay' = fieldSub n
      (fieldMul n k bench slope (fieldSub n x chordX)) y := by
    rw [hchordX] at hyForm'
    simpa [show slope = fieldMul n k bench (fieldSub n yB y) g from rfl] using hyForm'
  have hup' : fformUp n k bench yB o.u o.v o.z =
      fieldMul n k bench ay' (fformBottom n k bench o.v o.z) := by
    have h := hup
    dsimp only at h
    rw [← huRise, ← hvRun, ← hzZ, ← hyChord] at h
    exact h
  have haddU : addUp n k bench red o.y2 o.u o.v o.z = fformUp n k bench yB o.u o.v o.z := by
    rw [o.hy2]
    cases red with
    | true => simp [addUp, yB]
    | false => simp [addUp, yB]
  have hmulY : fieldMul n k bench o.yUp (fformBottom n k bench o.v o.z) =
      fieldMul n k bench ay' (fformBottom n k bench o.v o.z) := by
    have h1 := o.hy
    rw [haddU, hup'] at h1
    exact h1.symm
  have hyTUp : allTritList ay' := by
    rw [hyChord]
    exact fieldAdd_trits n _ _
  have hyLUp : ay'.length = n := by
    rw [hyChord]
    exact subLen n _ _
  have hyId := mul_cancel n k bench o.yUp ay' (fformBottom n k bench o.v o.z) w
    hpos hk hnb h2 o.hpyT hyTUp hbotT hwT o.hpy hyLUp hmulY hw
  exact ⟨hxEq, hyId⟩

/-- Rewrite the live `FformAt` onto the point `walkStep` returned. -/
theorem oncomb_hAt
    (t : Spec.Tier) (b : Ecbs.Board) (red : Bool)
    (baseX baseY ax' ay' : List Nat) (i moves' slides' ctrl' cMul c1 : Nat)
    (o : OnComb t b red baseX baseY moves' slides' ctrl' cMul c1)
    (hAt : FformAt t b baseX baseY o.x3 o.yUp (i + 1))
    (hx : o.x3 = ax') (hy : o.yUp = ay') :
    FformAt t b baseX baseY ax' ay' (i + 1) := by
  rw [hx, hy] at hAt
  exact hAt

end EcbsLink2.Link2
