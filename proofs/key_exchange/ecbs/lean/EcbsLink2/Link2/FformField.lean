/-
  The gap schedule of `fform_add` is one field value. Each helper below is
  proved equal to the matching formula in SPEC.md §3 R7, so the card order
  is not a second model of the point. Squaring commutes, and `fieldMul`
  distributes over the sum inside `F`. The new up mirrors both products on
  a white cell, and only the gap-times-up product on a red cell.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldComm
import EcbsLink2.Link2.FieldLin
import EcbsLink2.Link2.StripFold
import EcbsLink2.Link2.StripLin
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- `u²`, the copy-square of the rise. -/
def fformU2 (n k bench : Nat) (u : List Nat) : List Nat :=
  fieldMul n k bench u u

/-- `v²`, the copy-square of the run. -/
def fformV2 (n k bench : Nat) (v : List Nat) : List Nat :=
  fieldMul n k bench v v

/-- The bottom times that square of the rise. -/
def fformLeft (n k bench : Nat) (u z : List Nat) : List Nat :=
  fieldMul n k bench z (fformU2 n k bench u)

/-- The run times its own square. -/
def fformCube (n k bench : Nat) (v : List Nat) : List Nat :=
  fieldMul n k bench v (fformV2 n k bench v)

/-- The square of the run times the bottom. -/
def fformRight (n k bench : Nat) (v z : List Nat) : List Nat :=
  fieldMul n k bench (fformV2 n k bench v) z

/-- The gap. Copy-square the up and multiply by the bottom, copy-square the
    across, multiply that square by the bottom, lay the across times the
    square onto the gap, then add the spare-bottom product. -/
def fformGap (n k bench : Nat) (u v z : List Nat) : List Nat :=
  fieldAdd n (fieldAdd n (fformLeft n k bench u z) (fformCube n k bench v))
    (fformRight n k bench v z)

/-- New bottom `Z₃`: the run times the spare-bottom product. -/
def fformZ3 (n k bench : Nat) (v z : List Nat) : List Nat :=
  fieldMul n k bench v (fformRight n k bench v z)

/-- New across `X₃`: the gap times the run, plus base across times `Z₃`. -/
def fformX3 (n k bench : Nat) (x2 u v z : List Nat) : List Nat :=
  fieldAdd n (fieldMul n k bench (fformGap n k bench u v z) v)
    (fieldMul n k bench x2 (fformZ3 n k bench v z))

/-- One mirrored product on a zero strip, before the lane fold's length-`n`
    prefix. This is `mul` with `mirror = true`, `onto = false`. -/
def fformMir (n k bench : Nat) (x y : List Nat) : List Nat :=
  (laneFold n (n - k) (school n x y (List.replicate bench 0) true)).take n

/-- New up on a white cell. The gap-times-up multiply is mirrored, and so is
    base up times `Z₃` (`not red` is true). -/
def fformY3 (n k bench : Nat) (y2 u v z : List Nat) : List Nat :=
  let g := fformGap n k bench u v z
  let z3 := fformZ3 n k bench v z
  fieldAdd n (fformMir n k bench g u) (fformMir n k bench y2 z3)

/-- New up on a red cell. The gap-times-up multiply stays mirrored. Base up
    times `Z₃` uses `not red`, so that mirror flag is false. -/
def fformY3Red (n k bench : Nat) (y2 u v z : List Nat) : List Nat :=
  let g := fformGap n k bench u v z
  let z3 := fformZ3 n k bench v z
  fieldAdd n (fformMir n k bench g u) (fieldMul n k bench y2 z3)

private theorem fieldMul_trits_local (n k bench : Nat) (xs ys : List Nat)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench xs ys) := by
  have hrep : allTritList (List.replicate bench 0) := by
    intro x hx
    simp [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    exact Nat.zero_le _
  have hwide : ∀ i, i < n → i + (n - 1) < (List.replicate bench 0).length := by
    intro i hi
    rw [List.length_replicate]
    have : i + (n - 1) ≤ 2 * (n - 1) := by omega
    omega
  have hsch := school_trits xs ys (List.replicate bench 0) false n hrep hwide
  have hlen : (school n xs ys (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  have hfold := laneFold_trits n (n - k)
    (school n xs ys (List.replicate bench 0) false) hsch (Nat.sub_le _ _) (by rw [hlen]; exact hn)
  simpa [fieldMul, laneFold] using allTritList_take hfold n

private theorem fieldAdd_trits_local (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
  intro x hx
  simp only [fieldAdd, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  simpa [tritAdd] using Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))

/-- The schedule in the card's order equals `u²Z + v³ + v²Z`. -/
theorem fformGap_order (n k bench : Nat) (u v z : List Nat)
    (_hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fformGap n k bench u v z =
      fieldAdd n
        (fieldAdd n
          (fieldMul n k bench (fieldMul n k bench u u) z)
          (fieldMul n k bench (fieldMul n k bench v v) v))
        (fieldMul n k bench (fieldMul n k bench v v) z) := by
  unfold fformGap fformLeft fformCube fformRight fformU2 fformV2
  rw [fieldMul_comm n k bench z (fieldMul n k bench u u) hz
      (fieldMul_trits_local n k bench u u hspan hn)]
  rw [fieldMul_comm n k bench v (fieldMul n k bench v v) hv
      (fieldMul_trits_local n k bench v v hspan hn)]

/-- `X₃ = v F + x₂ Z₃`. The card multiplies the gap by the run, which is the
    same product as the run times the gap. -/
theorem fformX3_order (n k bench : Nat) (x2 u v z : List Nat)
    (hv : allTritList v) :
    fformX3 n k bench x2 u v z =
      fieldAdd n
        (fieldMul n k bench v (fformGap n k bench u v z))
        (fieldMul n k bench x2 (fformZ3 n k bench v z)) := by
  unfold fformX3
  have hg : allTritList (fformGap n k bench u v z) := by
    unfold fformGap
    exact fieldAdd_trits_local _ _ _
  rw [fieldMul_comm n k bench (fformGap n k bench u v z) v hg hv]

/-- The card's new bottom is SPEC.md §3 R7's `v · (v²Z)`. -/
theorem fformZ3_spec (n k bench : Nat) (v z : List Nat) :
    fformZ3 n k bench v z = fformBottom n k bench v z := by
  unfold fformZ3 fformRight fformV2 fformBottom
  rfl

/-- A mirrored multiply on a zero strip is `mirrorTrits` of `fieldMul`. -/
theorem fformMir_mul (n k bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    fformMir n k bench x y = mirrorTrits (fieldMul n k bench x y) := by
  unfold fformMir fieldMul
  rw [laneFold, school_mirror n bench x y hx hy,
    reduceStrip_flip n (n - k)
      (school n x y (List.replicate bench 0) false) (school_zero_trits n bench x y hy),
    ← List.map_take, ← mirrorTrits_map]

/-- The card's gap is SPEC.md §3 R7's `F = u²Z + v²(v + Z)`. -/
theorem fformGap_spec (n k bench : Nat) (u v z : List Nat)
    (hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fformGap n k bench u v z = fformF n k bench u v z := by
  have hv2 : allTritList (fieldMul n k bench v v) := fieldMul_trits_local n k bench v v hspan hn
  rw [fformGap_order n k bench u v z hu hv hz hspan hn]
  dsimp only [fformF]
  rw [fieldMul_right_add n k bench (fieldMul n k bench v v) v z hv2 hv hz hn,
    fieldAdd_assoc]

/-- The card's new across is SPEC.md §3 R7's `v·F + x₂·Z₃`. -/
theorem fformX3_spec (n k bench : Nat) (x2 u v z : List Nat)
    (hu : allTritList u) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fformX3 n k bench x2 u v z = fformAcross n k bench x2 u v z := by
  rw [fformX3_order n k bench x2 u v z hv,
    fformGap_spec n k bench u v z hu hv hz hspan hn,
    fformZ3_spec n k bench v z]
  rfl

/-- The card's white new up is SPEC.md §3 R7's `−(u·F + y₂·Z₃)`. -/
theorem fformY3_spec (n k bench : Nat) (y2 u v z : List Nat)
    (hu : allTritList u) (hy2 : allTritList y2) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fformY3 n k bench y2 u v z = fformUp n k bench y2 u v z := by
  dsimp only [fformY3]
  have hg : allTritList (fformGap n k bench u v z) := by
    unfold fformGap
    exact fieldAdd_trits_local _ _ _
  have hz3 : allTritList (fformZ3 n k bench v z) := by
    unfold fformZ3 fformRight fformV2
    exact fieldMul_trits_local n k bench v _ hspan hn
  rw [fformMir_mul n k bench (fformGap n k bench u v z) u hg hu,
    fformMir_mul n k bench y2 (fformZ3 n k bench v z) hy2 hz3,
    fieldMul_comm n k bench (fformGap n k bench u v z) u hg hu]
  have hmu : allTritList (fieldMul n k bench u (fformGap n k bench u v z)) :=
    fieldMul_trits_local n k bench u _ hspan hn
  have hmy : allTritList (fieldMul n k bench y2 (fformZ3 n k bench v z)) :=
    fieldMul_trits_local n k bench y2 _ hspan hn
  rw [← mirrorTrits_fieldAdd n _ _ hmu hmy,
    fformGap_spec n k bench u v z hu hv hz hspan hn,
    fformZ3_spec n k bench v z]
  rfl

/-- The card's red new up is SPEC.md §3 R7's new up at `−y₂`. -/
theorem fformY3Red_spec (n k bench : Nat) (y2 u v z : List Nat)
    (hu : allTritList u) (hy2 : allTritList y2) (hv : allTritList v) (hz : allTritList z)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    fformY3Red n k bench y2 u v z = fformUp n k bench (mirrorTrits y2) u v z := by
  dsimp only [fformY3Red, fformUp]
  have hg : allTritList (fformGap n k bench u v z) := by
    unfold fformGap
    exact fieldAdd_trits_local _ _ _
  have hz3 : allTritList (fformZ3 n k bench v z) := by
    unfold fformZ3 fformRight fformV2
    exact fieldMul_trits_local n k bench v _ hspan hn
  have hbot : allTritList (fformBottom n k bench v z) := by
    rw [← fformZ3_spec]
    exact hz3
  have hmy : allTritList (fieldMul n k bench y2 (fformZ3 n k bench v z)) :=
    fieldMul_trits_local n k bench y2 _ hspan hn
  rw [fformMir_mul n k bench (fformGap n k bench u v z) u hg hu,
    fieldMul_comm n k bench (fformGap n k bench u v z) u hg hu,
    fformGap_spec n k bench u v z hu hv hz hspan hn,
    fformZ3_spec n k bench v z,
    fieldMul_mirror_left n k bench y2 (fformBottom n k bench v z) hy2 hbot]
  have hmu : allTritList (fieldMul n k bench u (fformF n k bench u v z)) :=
    fieldMul_trits_local n k bench u _ hspan hn
  have hmirP : allTritList (mirrorTrits (fieldMul n k bench y2 (fformBottom n k bench v z))) := by
    rw [mirrorTrits_map]
    intro a ha
    simp only [List.mem_map] at ha
    rcases ha with ⟨_, _, rfl⟩
    exact flipTrit_le _
  rw [fformZ3_spec] at hmy
  rw [mirrorTrits_fieldAdd n _ _ hmu hmirP, mirrorTrits_invol _ hmy]

end EcbsLink2.Link2
