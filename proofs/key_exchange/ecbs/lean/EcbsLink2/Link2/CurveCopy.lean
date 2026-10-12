/-
  Field projections of the across copy inside `on_curve`. Each fact is one
  `place` lemma, so the proof that builds the copy does not unfold `placeBoard`
  again. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CurveTest
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A counter under two schoolbooks, on a `FieldLay` tier, still fits an i64. -/
theorem curveLayFit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m := by
  have hbig : 4 * (1000000 * 1000001) + 40 * 1000001 ≤ 9223372036854775807 := by
    decide
  have hp : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hn (by omega)
  have h2 : 2 * (n * (n + 1)) ≤ 2 * (1000000 * 1000001) := Nat.mul_le_mul_left 2 hp
  have h12 : 12 * bench ≤ 12 * 1000001 := Nat.mul_le_mul_left 12 hb
  have h24 : 24 * n ≤ 24 * 1000000 := Nat.mul_le_mul_left 24 hn
  have hsum : 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ≤
      4 * (1000000 * 1000001) + 40 * 1000001 := by omega
  unfold FitsLen i64MaxNat
  omega

/-- Homes and counters on the board `copy_band` writes at the bottom.
    `b1` is the gap multiply. The copy is `placeBoard`, read one field at a time. -/
theorem curve_copy_pack (b1 : Ecbs.Board) (x y : List Nat) (moves peak : Nat)
    (h2H : 2 < b1.sudo_5Board_4home.size) (h2D : 2 < b1.sudo_5Board_4held.size)
    (hhs : b1.sudo_5Board_4home.size = 8) (hds : b1.sudo_5Board_4held.size = 8)
    (h3 : ∀ (h : 3 < b1.sudo_5Board_4home.size), b1.sudo_5Board_4home[3] = embed x)
    (h4 : ∀ (h : 4 < b1.sudo_5Board_4home.size), b1.sudo_5Board_4home[4] = embed y)
    (hh3 : ∀ (h : 3 < b1.sudo_5Board_4held.size), b1.sudo_5Board_4held[3] = true)
    (hh4 : ∀ (h : 4 < b1.sudo_5Board_4held.size), b1.sudo_5Board_4held[4] = true)
    (hh6 : ∀ (h : 6 < b1.sudo_5Board_4held.size), b1.sudo_5Board_4held[6] = false)
    (hop0b : ∀ (h : 0 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      b1.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1) :
    let b := placeBoard b1 2 h2H h2D x moves peak
    b.sudo_5Board_4home.size = 8 ∧
    b.sudo_5Board_4held.size = 8 ∧
    (∀ (h : 2 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[2] = embed x) ∧
    (∀ (h : 2 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[2] = true) ∧
    (∀ (h : 3 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[3] = embed x) ∧
    (∀ (h : 3 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[3] = true) ∧
    (∀ (h : 4 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[4] = embed y) ∧
    (∀ (h : 4 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[4] = true) ∧
    (∀ (h : 6 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[6] = false) ∧
    b.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
    (∀ (h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1) := by
  intro b
  obtain ⟨_, _, _, _, _, _, _, _, hszH0, hszD0⟩ := place_book b1 2 h2H h2D x moves peak
  obtain ⟨_, _, hopsEq, _, _, hstrictEq, hholeEq⟩ := place_idle b1 2 h2H h2D x moves peak
  have hszH : b.sudo_5Board_4home.size = 8 := hszH0.trans hhs
  have hszD : b.sudo_5Board_4held.size = 8 := hszD0.trans hds
  have h3H : 3 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h3D : 3 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h4H : 4 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h4D : 4 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h6D : 6 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  refine ⟨hszH, hszD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstrictEq, hholeEq, ?_⟩
  · intro h2
    exact place_home_here b1 2 h2H h2D x moves peak h2
  · intro h2
    exact place_held_here b1 2 h2H h2D x moves peak h2
  · intro h3c
    exact (place_home_other b1 2 3 h2H h2D x moves peak (by decide) h3H h3c).trans (h3 h3H)
  · intro h3c
    exact (place_held_other b1 2 3 h2H h2D x moves peak (by decide) h3D h3c).trans (hh3 h3D)
  · intro h4c
    exact (place_home_other b1 2 4 h2H h2D x moves peak (by decide) h4H h4c).trans (h4 h4H)
  · intro h4c
    exact (place_held_other b1 2 4 h2H h2D x moves peak (by decide) h4D h4c).trans (hh4 h4D)
  · intro h6c
    exact (place_held_other b1 2 6 h2H h2D x moves peak (by decide) h6D h6c).trans (hh6 h6D)
  · intro h0
    exact (get_eq_of_array hopsEq 0 h0).trans (hop0b (hopsEq ▸ h0))

end EcbsLink2.Link2
