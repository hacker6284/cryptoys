/-
  A hole may start from any board whose base and bottom are empty and whose
  counters still fit one plant and one copy. `new_board` is that board.
  A miss of the fresh hole is the `searchRoot` step to the next hole.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchSeat
import EcbsLink2.Link2.InvertTie
import EcbsLink2.Link2.CurveCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The board a later hole can plant into: tier seated, base and bottom empty,
    moves and peak natural, and room for two peg copies. -/
structure PlantAt (b : Ecbs.Board) (t : Spec.Tier) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  baseOff : b.sudo_5Board_4held[3]? = some false
  botOff : b.sudo_5Board_4held[2]? = some false
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    FitsLen (mv + 2 * t.n)
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk

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

private theorem peg_plus (mv peg n : Nat) (hp : peg ≤ n) : mv + peg + n ≤ mv + 2 * n := by
  have h := peg_in mv peg n hp
  have h2 : n + n = 2 * n := (Nat.two_mul n).symm
  omega

/-- `builtBoard` can plant the first hole. -/
theorem fresh_plant (t : Spec.Tier) (hsh : TierShape t) : PlantAt (builtBoard t) t where
  tier := built_tier t
  szH := by rw [built_home_blank]; simp [Array.size_mkArray]
  szD := by rw [built_held_blank]; simp [Array.size_mkArray]
  baseOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  botOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  moves := by
    refine ⟨0, by rw [built_moves0]; rfl, ?_⟩
    have hle : 0 + 2 * t.n ≤ 2 * (t.n * (t.n + 1)) + 12 * t.benchlen + 24 * t.n + 8 := by
      omega
    exact curveLayFit t.n t.benchlen (0 + 2 * t.n) hsh.n_small hsh.small.2.2.2 hle
  peak := ⟨1, by rw [built_peak1]; rfl⟩

/-- Plant `basisPeg` into an empty base home. The bottom stays empty. -/
theorem search_plant_on (b : Ecbs.Board) (t : Spec.Tier) (h : PlantAt b t)
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
  have hfn : FitsLen t.n :=
    FitsLen.of_le hfit (Nat.le_trans (n_le_two t.n) (n_le_add mv (2 * t.n)))
  have hput := put_refines b 3 x mv pk hH hD h7 hempty hn (by rw [hx]; exact hfn)
    hmv hpk (two_room mv _ t.n hpeg hfit)
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
    exact FitsLen.of_le hfit (peg_plus mv (pegCount x) t.n hpeg)
  · exact ⟨_, place_peak_nat b 3 hH hD x mv pk hpk⟩

/-- Copy the planted peg into the empty bottom. -/
theorem search_copy_on (b : Ecbs.Board) (t : Spec.Tier) (h : PlantAt b t)
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
  obtain ⟨bP, hplant, hhome, hheld, _hbot, htier, hszH, hszD, hmvE, hpkE⟩ :=
    search_plant_on b t h j hj
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
  have hempty : bP.sudo_5Board_4held[2] = false := some_get _ _ _ _hbot
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

/-- The fresh hole misses. `searchRoot` moves one hole on. -/
theorem search_miss_first (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n)
    (left : Nat) (hleft : 0 < left) (hleftN : left ≤ t.n)
    (hmiss : rootHit t.n t.k t.benchlen (basisPeg t.n j) = false) :
    ∃ b' bC bM,
      (do
          let b ← (do
            let b ← (do
              let b ← (do
                let b ← (do
                  let b ← Ecbs.new_board (embTier t)
                  let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
                  let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
                  let b ← Ecbs.put b Ecbs.base_across x
                  Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
                let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
                Ecbs.settle b)
              Ecbs.white0 b Ecbs.up)
            let strip ← emittedStrip t.n
            let b ← Ecbs.put b Ecbs.across strip
            pure ({ b with sudo_5Board_9marker_on := true }))
          powRun b (rootDigits t.n)) = .ok b' ∧
        searchCheck b' = .ok (false, bC) ∧
        searchMiss bC = .ok bM ∧
        MissAt bM ∧
        searchRoot t.n t.k t.benchlen left j =
          searchRoot t.n t.k t.benchlen (left - 1) (j + 1) := by
  obtain ⟨b', hdo, hOr⟩ := search_plant_step t hOk hsh sat j hj0 hj hn3 left hleft hleftN
  rcases hOr with hL | hR
  · rcases hL with ⟨_, _, _, htrue, _⟩
    rw [hmiss] at htrue
    cases htrue
  · rcases hR with ⟨bC, bM, hck, hm, hMiss, _, hroot⟩
    exact ⟨b', bC, bM, hdo, hck, hm, hMiss, hroot⟩

end EcbsLink2.Link2
