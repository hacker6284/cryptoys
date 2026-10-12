/-
  `curve_test` puts `x` at base across (home 3) and `y` at base up (home 4).
-/
import EcbsLink2.Link2.OneField
import EcbsLink2.Link2.Export

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem n_le_four (n : Nat) : n ≤ 4 * n + 8 := by omega

private theorem two_pegs (n a b : Nat) (ha : a ≤ n) (hb : b ≤ n) : a + b ≤ 4 * n + 8 := by
  omega

private theorem home_lt (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_home_blank]
  simp [Array.size_mkArray, hi]

private theorem held_lt (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held_blank]
  simp [Array.size_mkArray, hi]

private theorem held_false (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    (builtBoard t).sudo_5Board_4held[i]'(held_lt t i hi) = false := by
  simp [built_held_blank, Array.getElem_mkArray]

private theorem count_one (t : Spec.Tier)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    countHeld ((builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true) 7 = 1 := by
  have hclosed :
      countHeld ((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
    decide
  have hs : (builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true =
      (Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true := by
    apply Array.ext
    · simp [built_held_blank, Array.size_set, Array.size_mkArray]
    · intro i hi hi'
      simp [built_held_blank, Array.getElem_set]
  rw [hs, hclosed]

def baseAcrossBoard (t : Spec.Tier) (x : List Nat)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) : Ecbs.Board :=
  { builtBoard t with
    sudo_5Board_4home := (builtBoard t).sudo_5Board_4home.set ⟨3, hH⟩ (embed x)
    sudo_5Board_4held := (builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true
    sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x) } }

private theorem place_across (t : Spec.Tier) (x : List Nat)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    placeBoard (builtBoard t) 3 hH hD x 0 1 = baseAcrossBoard t x hH hD := by
  unfold placeBoard baseAcrossBoard
  simp [count_one t hD, show ¬ ((1 : Nat) < 1) from by decide]

theorem put_base_across (t : Spec.Tier) (hOk : BoardOk t) (x : List Nat)
    (hx : x.length = t.n) :
    Ecbs.put (builtBoard t) Ecbs.base_across (embed x) =
      .ok (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  have hpx : FitsLen (pegCount x) :=
    FitsLen.of_le (by rw [hx]; exact hfn) (pegCount_le x)
  have hput := put_refines (builtBoard t) 3 x 0 1
    (home_lt t 3 (by decide)) (held_lt t 3 (by decide)) (held7_le t)
    (held_false t 3 (by decide))
    (by rw [built_tier, hx]; exact ofNat_eq_natCast _)
    (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl)
    (by rw [built_peak1]; rfl)
    (by simpa using hpx)
  rw [show Ecbs.base_across = ((3 : Nat) : Int) from rfl, hput, place_across]

theorem put_base_up (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    let b := baseAcrossBoard t x hH hD
    ∃ (hH4 : 4 < b.sudo_5Board_4home.size) (hD4 : 4 < b.sudo_5Board_4held.size),
      Ecbs.put b Ecbs.base_up (embed y) =
        .ok (placeBoard b 4 hH4 hD4 y (pegCount x) 1) := by
  intro b
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  have hpy : FitsLen (pegCount x + pegCount y) :=
    FitsLen.of_le (fits_of hOk.fits_n)
      (two_pegs t.n _ _ (by rw [← hx]; exact pegCount_le x) (by rw [← hy]; exact pegCount_le y))
  have hH4 : 4 < b.sudo_5Board_4home.size := by
    simp [b, baseAcrossBoard, built_home_blank, Array.size_set, Array.size_mkArray]
  have hD4 : 4 < b.sudo_5Board_4held.size := by
    simp [b, baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by
    simp [b, baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]
  have hempty : b.sudo_5Board_4held[4] = false := by
    simp [b, baseAcrossBoard, built_held_blank, Array.getElem_set]
  refine ⟨hH4, hD4, ?_⟩
  rw [show Ecbs.base_up = ((4 : Nat) : Int) from rfl]
  exact put_refines b 4 y (pegCount x) 1 hH4 hD4 h7 hempty
    (by simp [b, baseAcrossBoard, built_tier, hy]; exact ofNat_eq_natCast _)
    (by rw [hy]; exact hfn)
    (by simp [b, baseAcrossBoard])
    (by simp [b, baseAcrossBoard, built_peak1])
    hpy

end EcbsLink2.Link2
