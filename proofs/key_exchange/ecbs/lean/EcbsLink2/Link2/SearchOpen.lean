/-
  `builtBoard` is a `PlantAt`, so the first hole is the same chain as a later
  one. A miss of that hole is the `searchRoot` step to the next hole.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchSeat
import EcbsLink2.Link2.InvertTie
import EcbsLink2.Link2.CurveCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

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
