/-
  The search plants `basisPeg` in the base-across home before `curve_side`.
  The board is `PlantAt`: empty base and bottom, natural counters with room
  for the two copies. `builtBoard` is one such board.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchLoop
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.InvertTie
import EcbsLink2.Link2.InvertStep
import EcbsLink2.Link2.WalkCopy
import EcbsLink2.Link2.CurveTest

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- Room for the curve-side cube and the spare square, the same polynomial
    `curveLayFit` uses. -/
def plantRoom (n bench : Nat) : Nat :=
  2 * (n * (n + 1)) + 12 * bench + 24 * n + 8

/-- The board a hole can plant into. The first hole's `builtBoard` is one;
    a miss of an earlier hole is another. -/
structure PlantAt (b : Ecbs.Board) (t : Spec.Tier) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  baseOff : b.sudo_5Board_4held[3]? = some false
  botOff : b.sudo_5Board_4held[2]? = some false
  marker : b.sudo_5Board_6marker = -1
  markerOn : b.sudo_5Board_9marker_on = false
  benchOff : b.sudo_5Board_8bench_on = false
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    FitsLen (mv + plantRoom t.n t.benchlen)
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    FitsLen (sl + plantRoom t.n t.benchlen)
  ctrl : ∃ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN
  mx : ∃ mxN, b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mxN
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∃ (c0 : Nat), (∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (c0 : Int)) ∧
    FitsLen (c0 + 1)
  ops1 : ∃ (c1 : Nat), (∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (c1 : Int)) ∧
    FitsLen (c1 + 1)

private theorem two_n_room (n bench : Nat) : 2 * n ≤ plantRoom n bench := by
  unfold plantRoom
  omega

private theorem some_idx {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : i < a.size := by
  by_cases hlt : i < a.size
  · exact hlt
  · rw [Array.getElem?_ge a (by omega)] at h
    cases h

private theorem some_get {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : a[i]'(some_idx a i v h) = v := by
  rw [Array.getElem?_eq_getElem (some_idx a i v h)] at h
  injection h

private theorem bind_assoc {α β γ : Type}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m <;> simp [ok_bind, error_bind]

private theorem peg_le (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n := by
  have hlen : pegCount xs ≤ xs.length := pegCount_le xs
  rwa [h] at hlen

private theorem two_room (mv peg n : Nat) (hp : peg ≤ n) (h : FitsLen (mv + 2 * n)) :
    FitsLen (mv + peg) := by
  exact FitsLen.of_le h (by omega)

private theorem n_le_add (mv n : Nat) : n ≤ mv + n :=
  Nat.le_add_left n mv

private theorem peg_in (mv peg n : Nat) (hp : peg ≤ n) : mv + peg ≤ mv + n :=
  Nat.add_le_add_left hp mv

private theorem n_le_two (n : Nat) : n ≤ 2 * n :=
  Nat.le_mul_of_pos_left n (by decide : 0 < 2)

private theorem peg_plus (mv peg n : Nat) (hp : peg ≤ n) : mv + peg + n ≤ mv + 2 * n := by
  have h := peg_in mv peg n hp
  have h2 : n + n = 2 * n := (Nat.two_mul n).symm
  omega

private theorem do_copy (b : Ecbs.Board) (n j : Nat) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        let b ← Ecbs.put b Ecbs.base_across x
        Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) =
      ((do
          let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put b Ecbs.base_across x) >>= fun b =>
        Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) :=
  bind_assoc
    (SudoRt.filledL (Int.ofNat n) (0 : Int) >>= fun x => SudoRt.putL x (Int.ofNat j) (1 : Int))
    (fun x => Ecbs.put b Ecbs.base_across x)
    (fun b => Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false)

/-- Plant `basisPeg` into an empty base home. The bottom stays empty. -/
theorem search_plant (b : Ecbs.Board) (t : Spec.Tier) (h : PlantAt b t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put b Ecbs.base_across x) = .ok b' ∧
        b'.sudo_5Board_4home[3]? = some (embed (basisPeg t.n j)) ∧
        b'.sudo_5Board_4held[3]? = some true ∧
        b'.sudo_5Board_4held[2]? = some false ∧
        b'.sudo_5Board_1t = embTier t ∧
        b'.sudo_5Board_4home.size = 8 ∧
        b'.sudo_5Board_4held.size = 8 ∧
        (∃ mv, b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
          FitsLen (mv + t.n)) ∧
        (∃ pk, b'.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) := by
  rcases h.moves with ⟨mv, hmv, hfit⟩
  rcases h.peak with ⟨pk, hpk⟩
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hpeg := peg_le t.n x hx
  have hH : 3 < b.sudo_5Board_4home.size := by rw [h.szH]; decide
  have hD : 3 < b.sudo_5Board_4held.size := by rw [h.szD]; decide
  have hempty : b.sudo_5Board_4held[3] = false := some_get _ _ _ h.baseOff
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [h.szD]; decide
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    rw [h.tier, hx]
    simp [embTier, ofNat_eq_natCast]
  have h2 : FitsLen (mv + 2 * t.n) :=
    FitsLen.of_le hfit (Nat.add_le_add_left (two_n_room t.n t.benchlen) mv)
  have hfn : FitsLen t.n :=
    FitsLen.of_le h2 (Nat.le_trans (n_le_two t.n) (n_le_add mv (2 * t.n)))
  have hput := put_refines b 3 x mv pk hH hD h7 hempty hn (by rw [hx]; exact hfn)
    hmv hpk (two_room mv _ t.n hpeg h2)
  let b' := placeBoard b 3 hH hD x mv pk
  refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bind_assoc, basis_fill t.n j hj, ok_bind, ← searchBase_int]
    exact hput
  · rw [place_home_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set]
  · rw [place_held_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · have hne : (3 : Nat) ≠ 2 := by decide
    rw [place_held_eq, Array.getElem?_set_ne _ ⟨3, hD⟩ true hne]
    exact h.botOff
  · rw [place_tier_eq]; exact h.tier
  · rw [place_home_eq, Array.size_set]; exact h.szH
  · rw [place_held_eq, Array.size_set]; exact h.szD
  · refine ⟨mv + pegCount x, place_moves_eq b 3 hH hD x mv pk, ?_⟩
    exact FitsLen.of_le hfit
      (Nat.le_trans (peg_plus mv (pegCount x) t.n hpeg)
        (Nat.add_le_add_left (two_n_room t.n t.benchlen) mv))
  · exact ⟨_, place_peak_nat b 3 hH hD x mv pk hpk⟩

/-- Copy the planted peg into the empty bottom. -/
theorem search_copy (b : Ecbs.Board) (t : Spec.Tier) (h : PlantAt b t)
    (j : Nat) (hj : j < t.n) :
    ∃ bP bC,
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) = .ok bC ∧
        (do
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            Ecbs.put b Ecbs.base_across x) = .ok bP ∧
        bC.sudo_5Board_4home[2]? = some (embed (basisPeg t.n j)) ∧
        bC.sudo_5Board_4held[2]? = some true ∧
        bC.sudo_5Board_4home[3]? = some (embed (basisPeg t.n j)) ∧
        bC.sudo_5Board_4held[3]? = some true ∧
        bC.sudo_5Board_1t = embTier t ∧
        (∃ mv, bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
          FitsLen mv) ∧
        (∃ pk, bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) := by
  obtain ⟨bP, hplant, hhome, hheld, hbot, htier, hszH, hszD, hmvE, hpkE⟩ :=
    search_plant b t h j hj
  rcases hmvE with ⟨mv, hmv, hfit⟩
  rcases hpkE with ⟨pk, hpk⟩
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hpeg := peg_le t.n x hx
  have hH : 2 < bP.sudo_5Board_4home.size := by rw [hszH]; decide
  have hD : 2 < bP.sudo_5Board_4held.size := by rw [hszD]; decide
  have hHs : 3 < bP.sudo_5Board_4home.size := by rw [hszH]; decide
  have hDs : 3 < bP.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ bP.sudo_5Board_4held.size := by rw [hszD]; decide
  have hempty : bP.sudo_5Board_4held[2] = false := some_get _ _ _ hbot
  have hsrc : bP.sudo_5Board_4held[3] = true := some_get _ _ _ hheld
  have harr : bP.sudo_5Board_4home[3] = embed x := some_get _ _ _ hhome
  have hn : bP.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    rw [htier, hx]
    simp [embTier, ofNat_eq_natCast]
  have hfn : FitsLen t.n := FitsLen.of_le hfit (n_le_add mv t.n)
  have hcopy := copy_band_refines bP 2 3 x mv pk hH hD hHs hDs h7 hsrc harr hempty
    hn (by rw [hx]; exact hfn) hmv hpk (FitsLen.of_le hfit (peg_in mv (pegCount x) t.n hpeg))
  let bC := placeBoard bP 2 hH hD x mv pk
  refine ⟨bP, bC, ?_, hplant, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [do_copy b t.n j, hplant, ok_bind,
      show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
      show Ecbs.base_across = ((3 : Nat) : Int) from rfl]
    exact hcopy
  · rw [place_home_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set]
  · rw [place_held_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · have hne : (2 : Nat) ≠ 3 := by decide
    rw [place_home_eq, Array.getElem?_set_ne _ ⟨2, hH⟩ (embed x) hne]
    exact hhome
  · have hne : (2 : Nat) ≠ 3 := by decide
    rw [place_held_eq, Array.getElem?_set_ne _ ⟨2, hD⟩ true hne]
    exact hheld
  · rw [place_tier_eq]; exact htier
  · refine ⟨mv + pegCount x, place_moves_eq bP 2 hH hD x mv pk, ?_⟩
    exact FitsLen.of_le hfit (peg_in mv (pegCount x) t.n hpeg)
  · exact ⟨_, place_peak_nat bP 2 hH hD x mv pk hpk⟩

end EcbsLink2.Link2
