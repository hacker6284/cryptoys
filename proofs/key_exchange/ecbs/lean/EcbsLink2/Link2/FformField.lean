/-
  The gap schedule of `fform_add` is one field value. The new point is the
  three homes that value feeds. Squaring commutes, so the card's order
  `Z · u² + v · v² + v² · Z` is `u² Z + v³ + v² Z`. The new up mirrors both
  products on a white cell, and only the gap-times-up product on a red cell.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldComm
import EcbsLink2.Link2.StripFold

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

private theorem fieldMul_trits (n k bench : Nat) (xs ys : List Nat)
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

private theorem fieldAdd_trits (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
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
      (fieldMul_trits n k bench u u hspan hn)]
  rw [fieldMul_comm n k bench v (fieldMul n k bench v v) hv
      (fieldMul_trits n k bench v v hspan hn)]

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
    exact fieldAdd_trits _ _ _
  rw [fieldMul_comm n k bench (fformGap n k bench u v z) v hg hv]

end EcbsLink2.Link2
