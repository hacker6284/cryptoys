/-
  ECBS Link 2: the bridge from `EcbsLink2.Spec` to the emitted records, and the
  small `SudoRt` lemmas the other files share. Proof-only.
-/
import Ecbs
import EcbsLink2.Spec
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem fits_of {n : Nat} (h : Fits n) : FitsLen n := by
  simpa [FitsLen, i64MaxNat, Fits, i64Bound] using h

/-- `assert` passes. The line is the sudo source line and is not part of the model. -/
theorem sudoAssertEq_of_beq {α : Type} [SudoRt.SEq α] [SudoRt.Canon α] {a b : α}
    (h : SudoRt.SEq.beq a b = true) (line : Nat) : SudoRt.sudoAssertEq a b line = .ok () := by
  unfold SudoRt.sudoAssertEq
  rw [h]
  rfl

theorem sudoAssertEq_int {a b : Int} (h : a = b) (line : Nat) :
    SudoRt.sudoAssertEq a b line = .ok () :=
  sudoAssertEq_of_beq (by rw [sEq_int, h]; exact decide_eq_true rfl) line

theorem sudoAssert_bool (line : Nat) (h : p = true) : SudoRt.sudoAssert p line = .ok () := by
  unfold SudoRt.sudoAssert
  rw [h]
  rfl

/-- The emitted tier of a model tier. -/
def embTier (t : Spec.Tier) : Ecbs.Tier where
  sudo_4Tier_4name := embed t.name
  sudo_4Tier_1n := Int.ofNat t.n
  sudo_4Tier_1k := Int.ofNat t.k
  sudo_4Tier_1w := Int.ofNat t.w
  sudo_4Tier_1h := Int.ofNat t.h
  sudo_4Tier_1r := Int.ofNat t.r
  sudo_4Tier_8benchlen := Int.ofNat t.benchlen
  sudo_4Tier_7combgap := Int.ofNat t.combgap
  sudo_4Tier_7control := Int.ofNat t.control
  sudo_4Tier_6script := Int.ofNat t.script
  sudo_4Tier_4demo := t.demo
  sudo_4Tier_5cells := Int.ofNat t.cells
  sudo_4Tier_7foldsrc := embed t.foldsrc
  sudo_4Tier_7folddst := embed t.folddst
  sudo_4Tier_8keeprows := Int.ofNat t.keeprows
  sudo_4Tier_7georows := Int.ofNat t.georows
  sudo_4Tier_6geoper := Int.ofNat t.geoper
  sudo_4Tier_8geofirst := Int.ofNat t.geofirst
  sudo_4Tier_9geodouble := t.geodouble
  sudo_4Tier_7geowork := Int.ofNat t.geowork
  sudo_4Tier_6geokey := embed t.geokey

def embHole (h : Spec.Hole) : Ecbs.Hole where
  sudo_4Hole_4grid := Int.ofNat h.grid
  sudo_4Hole_3row := Int.ofNat h.row
  sudo_4Hole_3col := Int.ofNat h.col

def embNames (xs : List (List Nat)) : Array (Array Int) :=
  (xs.map embed).toArray

theorem demo_emb : embTier Spec.demo = Ecbs.demo_tier := rfl
theorem toy_emb : embTier Spec.toy = Ecbs.toy_tier := rfl
theorem hobby_emb : embTier Spec.hobby = Ecbs.hobby_tier := rfl
theorem serious_emb : embTier Spec.serious = Ecbs.serious_tier := rfl

/-- What `new_board` and `fold` assume of a tier: the ladder fits the control row, and
    every index the emitted arithmetic builds fits an i64. -/
structure BoardOk (t : Spec.Tier) : Prop where
  n_pos : 0 < t.n
  fits_n : Fits (4 * t.n + 8)
  fits_script : Fits (t.script + 3)
  fits_control : Fits (t.control + 1)
  ladder : t.script + 2 + (rungList (t.n - 1)).length ≤ t.control

/-- What `coordinate` assumes. Demo does not divide by `w` or `geoper`; the other tiers do. -/
structure GridOk (t : Spec.Tier) : Prop where
  fits_n : Fits (t.n + 16)
  w_pos : ¬ t.demo → 0 < t.w
  geoper_pos : ¬ t.demo → 0 < t.geoper
  fits_grid : Fits (8 * t.georows + t.n + t.geofirst + 16)

/-- What `fold` assumes of the row map, on top of `BoardOk`. -/
structure FoldOk (t : Spec.Tier) : Prop where
  w_pos : 0 < t.w
  same : t.foldsrc.length = t.folddst.length
  dst : ∀ d ∈ t.folddst, (d + 1) * t.w ≤ t.n
  keep : t.keeprows * t.w ≤ t.n
  fits_src : ∀ s ∈ t.foldsrc, Fits (s * t.w + t.w)
  fits_dst : ∀ d ∈ t.folddst, Fits (d * t.w + t.w)
  fits_keep : Fits (t.keeprows * t.w + 1)

theorem demo_board : BoardOk Spec.demo := by
  refine ⟨by decide, by decide!, by decide!, by decide!, by decide!⟩

theorem toy_board : BoardOk Spec.toy := by
  refine ⟨by decide, by decide!, by decide!, by decide!, by decide!⟩

theorem hobby_board : BoardOk Spec.hobby := by
  refine ⟨by decide, by decide!, by decide!, by decide!, by decide!⟩

theorem serious_board : BoardOk Spec.serious := by
  refine ⟨by decide, by decide!, by decide!, by decide!, by decide!⟩

theorem demo_grid : GridOk Spec.demo := by
  refine ⟨by decide!, ?_, ?_, by decide!⟩ <;> intro h <;> simp [Spec.demo] at h

theorem toy_grid : GridOk Spec.toy := by
  refine ⟨by decide!, ?_, ?_, by decide!⟩ <;> intro _ <;> decide

theorem hobby_grid : GridOk Spec.hobby := by
  refine ⟨by decide!, ?_, ?_, by decide!⟩ <;> intro _ <;> decide

theorem serious_grid : GridOk Spec.serious := by
  refine ⟨by decide!, ?_, ?_, by decide!⟩ <;> intro _ <;> decide

theorem demo_fold : FoldOk Spec.demo := by
  refine ⟨by decide, by decide, by decide, by decide, by decide!, by decide!, by decide!⟩

theorem toy_fold : FoldOk Spec.toy := by
  refine ⟨by decide, by decide, by decide, by decide, by decide!, by decide!, by decide!⟩

theorem hobby_fold : FoldOk Spec.hobby := by
  refine ⟨by decide, by decide, by decide, by decide, by decide!, by decide!, by decide!⟩

theorem serious_fold : FoldOk Spec.serious := by
  refine ⟨by decide, by decide, by decide, by decide, by decide!, by decide!, by decide!⟩

theorem nnz_length_le (xs : List Int) : Spec.nnz xs ≤ xs.length := by
  induction xs with
  | nil => simp [Spec.nnz]
  | cons x xs ih =>
    simp only [Spec.nnz, List.length_cons]
    split <;> omega

theorem nnz_embed (xs : List Nat) : Spec.nnz (xs.map Int.ofNat) = (xs.filter (· ≠ 0)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, Spec.nnz, List.filter, ih]
    by_cases h : x = 0
    · simp [h, Int.ofNat_eq_zero, ih]
    · have hx0 : (Int.ofNat x) ≠ 0 := by
        intro e
        exact h (Int.ofNat.inj e)
      rw [if_neg hx0]
      simp [h, ih, Int.ofNat_add]
      omega

theorem nnz_nonneg_count (xs : List Nat) :
    (xs.filter (· ≠ 0)).length ≤ xs.length :=
  List.length_filter_le _ _

end EcbsLink2.Link2
