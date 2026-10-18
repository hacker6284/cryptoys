/-
  The inverse of the cell's new denominator. `fieldInv` on the run is a
  left factor of one, cubing keeps a right inverse, and `Z₃ = v³·Z` stays
  right-invertible. `ProjOn` asks for that witness. It does not store the
  inverse in a home, and the add tail does not write one.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformLine

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem subLen (n : Nat) (a b : List Nat) : (fieldSub n a b).length = n := by
  simp [fieldSub, fieldAdd, List.length_map, List.length_range]

private theorem mulT (n k bench : Nat) (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (x y : List Nat) (hx : allTritList x) (hy : allTritList y) :
    allTritList (fieldMul n k bench x y) := by
  rw [fieldMul_eq_mulVal n k bench x y hn hk hb h2 hx hy]
  exact mulVal_trits n k hn hk x y hx hy

private theorem zero_trits (n : Nat) : allTritList (List.replicate n 0) := by
  intro x hx
  rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
  exact Nat.zero_le _

private theorem one_ne_zero (n : Nat) (hn : 0 < n) : onePeg n ≠ zeroPeg n := by
  intro heq
  have hn1 : n = (n - 1) + 1 := by omega
  rw [onePeg, zeroPeg, hn1, List.replicate_succ] at heq
  simp at heq

/-- A gap `fieldInv` returns has length `n`, is trits, and left-multiplies to one. -/
theorem fieldInv_witness (t : Spec.Tier) (x g : List Nat)
    (sat : TierSat t) (lay : TierShape t)
    (hpos : 0 < t.n) (hxL : x.length = t.n) (hx : allTritList x)
    (h : fieldInv t.n t.k t.benchlen x = some g) :
    g.length = t.n ∧ allTritList g ∧
      fieldMul t.n t.k t.benchlen g x = onePeg t.n := by
  have hmul := fieldInv_mul t x g sat lay hpos hxL hx h
  rcases fieldInv_some_shape t.n t.k t.benchlen x g h with ⟨_, hg⟩ | ⟨_, hg⟩
  · rw [hg] at hmul ⊢
    exact ⟨invGap_length t x sat hpos, invGap_trits t x sat lay hpos hxL hx, hmul⟩
  · rw [hg] at hmul ⊢
    refine ⟨?_, mirror_trits _, hmul⟩
    simpa [mirrorTrits, List.length_map] using invGap_length t x sat hpos

/-- Cubing the affine point cubes the projective triple, and the cubed
    denominator keeps the cubed right inverse. -/
theorem cube_point_inv (n k bench : Nat) (px py z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hpx : allTritList px) (hpy : allTritList py)
    (hz : allTritList z) (hw : allTritList w)
    (hzL : z.length = n) (hwL : w.length = n)
    (hinv : fieldMul n k bench z w = onePeg n) :
    fieldMul n k bench (fieldCube n k bench px) (fieldCube n k bench z) =
        fieldCube n k bench (fieldMul n k bench px z) ∧
      fieldMul n k bench (fieldCube n k bench py) (fieldCube n k bench z) =
        fieldCube n k bench (fieldMul n k bench py z) ∧
      fieldMul n k bench (fieldCube n k bench z) (fieldCube n k bench w) = onePeg n ∧
      fieldCube n k bench z ≠ List.replicate n 0 ∧
      (fieldCube n k bench w).length = n ∧
      allTritList (fieldCube n k bench w) := by
  obtain ⟨hx, hy, hmul, hne⟩ :=
    cube_proj n k bench px py z w hn hk hb h2 h3 hpx hpy hz hw hzL hwL hinv
  refine ⟨hx, hy, hmul, ?_, fieldCube_length n k bench w hb,
    fieldCube_trits n k bench w hw h3 (Nat.le_of_lt hk)⟩
  simpa [zeroPeg] using hne

/-- `Z₃` after the cubed point is added to the base stays right-invertible.
    `v` is the run over the cubed denominator, and the witness is
    `cube(w³ · g) · w³`. -/
theorem z3_den_inv (t : Spec.Tier) (px py x2 z w g : List Nat)
    (sat : TierSat t) (lay : TierShape t)
    (hn : 0 < t.n) (hk : t.k < t.n) (hb : t.n ≤ t.benchlen)
    (h2 : 2 * (t.n - 1) < t.benchlen) (h3 : 3 * (t.n - 1) < t.benchlen)
    (hpx : allTritList px) (hpy : allTritList py)
    (hx2 : allTritList x2) (hz : allTritList z) (hw : allTritList w)
    (hzL : z.length = t.n) (hwL : w.length = t.n)
    (hinv : fieldMul t.n t.k t.benchlen z w = onePeg t.n)
    (hfi : fieldInv t.n t.k t.benchlen
        (fieldSub t.n x2 (fieldCube t.n t.k t.benchlen px)) = some g) :
    let n := t.n
    let k := t.k
    let bench := t.benchlen
    let zC := fieldCube n k bench z
    let xC := fieldCube n k bench px
    let z3 := fformBottom n k bench
      (fformRun n k bench x2 zC (fieldMul n k bench xC zC)) zC
    ∃ w3, w3.length = n ∧ allTritList w3 ∧ allTritList z3 ∧
      fieldMul n k bench z3 w3 = onePeg n ∧
      z3 ≠ List.replicate n 0 := by
  intro n k bench zC xC z3
  have hcube := cube_point_inv n k bench px py z w hn hk hb h2 h3 hpx hpy hz hw hzL hwL hinv
  have hzC : allTritList zC := fieldCube_trits n k bench z hz h3 (Nat.le_of_lt hk)
  have hzCL : zC.length = n := fieldCube_length n k bench z hb
  have hxC : allTritList xC := fieldCube_trits n k bench px hpx h3 (Nat.le_of_lt hk)
  have hwC : allTritList (fieldCube n k bench w) := hcube.2.2.2.2.2
  have hwCL : (fieldCube n k bench w).length = n := hcube.2.2.2.2.1
  let wC := fieldCube n k bench w
  let run := fieldSub n x2 xC
  have hrunT : allTritList run := fieldAdd_trits n x2 (mirrorTrits xC)
  have hrunL : run.length = n := subLen n x2 xC
  have hgi := fieldInv_witness t run g sat lay hn hrunL hrunT hfi
  have hv : fformRun n k bench x2 zC (fieldMul n k bench xC zC) =
      fieldMul n k bench run zC :=
    run_over_z n k bench xC x2 zC hb hxC hx2 hzC
  have hbot := bottom_of_run n k bench run zC wC g hn hk hb h2 h3 hrunT hzC hwC hgi.2.1
    hzCL hwCL hgi.1 hrunL hcube.2.2.1 hgi.2.2
  let w3 := fieldMul n k bench (fieldCube n k bench (fieldMul n k bench wC g)) wC
  have hwgT : allTritList (fieldMul n k bench wC g) :=
    mulT n k bench hn hk hb h2 wC g hwC hgi.2.1
  have hwgC : allTritList (fieldCube n k bench (fieldMul n k bench wC g)) :=
    fieldCube_trits n k bench _ hwgT h3 (Nat.le_of_lt hk)
  have hw3T : allTritList w3 := mulT n k bench hn hk hb h2 _ wC hwgC hwC
  have hw3L : w3.length = n := fieldMul_length n k bench _ wC hb
  have hvT : allTritList (fformRun n k bench x2 zC (fieldMul n k bench xC zC)) :=
    fieldAdd_trits n _ _
  have hvvT : allTritList (fieldMul n k bench
      (fformRun n k bench x2 zC (fieldMul n k bench xC zC))
      (fformRun n k bench x2 zC (fieldMul n k bench xC zC))) :=
    mulT n k bench hn hk hb h2 _ _ hvT hvT
  have hvvzT : allTritList (fieldMul n k bench
      (fieldMul n k bench
        (fformRun n k bench x2 zC (fieldMul n k bench xC zC))
        (fformRun n k bench x2 zC (fieldMul n k bench xC zC))) zC) :=
    mulT n k bench hn hk hb h2 _ zC hvvT hzC
  have hz3T : allTritList z3 := by
    simpa [z3, fformBottom] using mulT n k bench hn hk hb h2 _ _ hvT hvvzT
  have hmul : fieldMul n k bench z3 w3 = onePeg n := by
    have hcong : fformBottom n k bench (fieldMul n k bench run zC) zC =
        fformBottom n k bench (fformRun n k bench x2 zC (fieldMul n k bench xC zC)) zC :=
      congrArg (fun v => fformBottom n k bench v zC) hv.symm
    simpa [z3, w3, wC] using hcong ▸ hbot
  refine ⟨w3, hw3L, hw3T, hz3T, hmul, ?_⟩
  intro hz0
  have hkill : fieldMul n k bench z3 w3 = zeroPeg n := by
    rw [hz0, show List.replicate n 0 = zeroPeg n from rfl,
      fieldMul_comm n k bench (zeroPeg n) w3 (by simpa [zeroPeg] using zero_trits n) hw3T,
      fieldMul_zero n k bench w3 hb]
  exact one_ne_zero n hn (hmul.symm.trans hkill)

end EcbsLink2.Link2
