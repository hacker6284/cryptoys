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

private theorem op_lay (n bench k : Nat) (hk : k ≤ n) :
    perOp n * k ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  unfold perOp
  have hmul : (n + 2) * k ≤ (n + 2) * n := Nat.mul_le_mul_left _ hk
  have hprod : (n + 2) * n = n * n + 2 * n := by rw [Nat.add_mul]
  have hsucc : n * (n + 1) = n * n + n := Nat.mul_succ n n
  have htwo : 2 * (n * (n + 1)) = 2 * (n * n) + 2 * n := by
    rw [hsucc, Nat.mul_add]
  have hsq : n * n ≤ 2 * (n * n) := by
    simpa [Nat.one_mul] using
      Nat.mul_le_mul_right (n * n) (by decide : (1 : Nat) ≤ 2)
  have hmid : n * n + 2 * n ≤ 2 * (n * (n + 1)) := by
    rw [htwo]
    exact Nat.add_le_add_right hsq (2 * n)
  have hleft : (n + 2) * n ≤ 2 * (n * (n + 1)) := by
    rw [hprod]
    exact hmid
  have h1 : 2 * (n * (n + 1)) ≤ 2 * (n * (n + 1)) + 12 * bench :=
    Nat.le_add_right _ _
  have h2 : 2 * (n * (n + 1)) + 12 * bench ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n := Nat.le_add_right _ _
  have h3 : 2 * (n * (n + 1)) + 12 * bench + 24 * n ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := Nat.le_add_right _ _
  exact Nat.le_trans (Nat.le_trans hmul hleft) (Nat.le_trans h1 (Nat.le_trans h2 h3))

/-- `builtBoard` can plant a hole while `holesLeft` holes remain, once those
    budgets fit. The four shipped tiers discharge the budgets below. -/
theorem fresh_plant (t : Spec.Tier) (hsh : TierShape t) (holesLeft : Nat)
    (hpos : 0 < holesLeft)
    (hleft : holesLeft ≤ t.n)
    (hmov : FitsLen (perHole t.n t.benchlen * holesLeft))
    (hslide : FitsLen (perSlide t.n * holesLeft))
    (hctrl : FitsLen (tierR t + perCtrl t.n * holesLeft)) :
    PlantAt (builtBoard t) t holesLeft where
  holesPos := hpos
  tier := built_tier t
  szH := by rw [built_home_blank]; simp [Array.size_mkArray]
  szD := by rw [built_held_blank]; simp [Array.size_mkArray]
  baseOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  botOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  axOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  upOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  gapOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  spareOff := by
    rw [built_held_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  axHome := by
    rw [built_home_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  upHome := by
    rw [built_home_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  gapHome := by
    rw [built_home_blank]
    simp [Array.getElem?_eq_getElem, Array.getElem_mkArray]
  moves := by
    refine ⟨0, by rw [built_moves0]; rfl, ?_⟩
    simpa [Nat.zero_add] using hmov
  slides := by
    refine ⟨0, by rw [built_slides0]; rfl, ?_⟩
    simpa [Nat.zero_add] using hslide
  ctrl := ⟨tierR t, built_ctrl_eq t, hctrl⟩
  peak := ⟨1, by rw [built_peak1]; rfl⟩
  strict := ⟨0, by rw [built_strict]; rfl⟩
  hole := ⟨0, by rw [built_hole]; rfl⟩
  mx := ⟨0, by rw [built_mx0]; rfl⟩
  opsSz := by rw [built_ops_arr]; simp [Array.size_mkArray]
  ops0 := by
    refine ⟨0, ?_, ?_⟩
    · intro h
      have hb : 0 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
      exact cell_eq_of (built_ops_arr t) (hb := hb) (by simp [Array.getElem_mkArray])
    · simpa [Nat.zero_add] using
        curveLayFit t.n t.benchlen (perOp t.n * holesLeft) hsh.n_small hsh.small.2.2.2
          (op_lay t.n t.benchlen holesLeft hleft)
  ops1 := by
    refine ⟨0, ?_, ?_⟩
    · intro h
      have hb : 1 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
      exact cell_eq_of (built_ops_arr t) (hb := hb) (by simp [Array.getElem_mkArray])
    · simpa [Nat.zero_add] using
        curveLayFit t.n t.benchlen (perOp t.n * holesLeft) hsh.n_small hsh.small.2.2.2
          (op_lay t.n t.benchlen holesLeft hleft)
  marker := built_marker_down t
  markerOn := built_flag_off t
  benchOff := built_bench_off t

theorem demo_move_budget : FitsLen (perHole demo.n demo.benchlen * demo.n) := by
  unfold FitsLen perHole plantRoom i64MaxNat demo
  exact Nat.le_of_ble_eq_true rfl

theorem demo_slide_budget : FitsLen (perSlide demo.n * demo.n) := by
  unfold FitsLen perSlide i64MaxNat demo
  exact Nat.le_of_ble_eq_true rfl

private theorem add_cap (c n p : Nat) (hc : c ≤ n - 1) : c + p ≤ (n - 1) + p :=
  Nat.add_le_add_right hc p

theorem demo_ctrl_num : (demo.n - 1) + perCtrl demo.n * demo.n ≤ 9223372036854775807 := by
  unfold perCtrl demo
  exact Nat.le_of_ble_eq_true rfl

theorem demo_ctrl_budget : FitsLen (tierR demo + perCtrl demo.n * demo.n) := by
  have hlen : tierR demo ≤ demo.n - 1 := by
    simpa [tierR] using rungList_length_le (demo.n - 1)
  unfold FitsLen i64MaxNat
  exact Nat.le_trans (add_cap _ demo.n _ hlen) demo_ctrl_num

theorem toy_move_budget : FitsLen (perHole toy.n toy.benchlen * toy.n) := by
  unfold FitsLen perHole plantRoom i64MaxNat toy
  exact Nat.le_of_ble_eq_true rfl

theorem toy_slide_budget : FitsLen (perSlide toy.n * toy.n) := by
  unfold FitsLen perSlide i64MaxNat toy
  exact Nat.le_of_ble_eq_true rfl

theorem toy_ctrl_num : (toy.n - 1) + perCtrl toy.n * toy.n ≤ 9223372036854775807 := by
  unfold perCtrl toy
  exact Nat.le_of_ble_eq_true rfl

theorem toy_ctrl_budget : FitsLen (tierR toy + perCtrl toy.n * toy.n) := by
  have hlen : tierR toy ≤ toy.n - 1 := by
    simpa [tierR] using rungList_length_le (toy.n - 1)
  unfold FitsLen i64MaxNat
  exact Nat.le_trans (add_cap _ toy.n _ hlen) toy_ctrl_num

theorem hobby_move_budget : FitsLen (perHole hobby.n hobby.benchlen * hobby.n) := by
  unfold FitsLen perHole plantRoom i64MaxNat hobby
  exact Nat.le_of_ble_eq_true rfl

theorem hobby_slide_budget : FitsLen (perSlide hobby.n * hobby.n) := by
  unfold FitsLen perSlide i64MaxNat hobby
  exact Nat.le_of_ble_eq_true rfl

theorem hobby_ctrl_num : (hobby.n - 1) + perCtrl hobby.n * hobby.n ≤ 9223372036854775807 := by
  unfold perCtrl hobby
  exact Nat.le_of_ble_eq_true rfl

theorem hobby_ctrl_budget : FitsLen (tierR hobby + perCtrl hobby.n * hobby.n) := by
  have hlen : tierR hobby ≤ hobby.n - 1 := by
    simpa [tierR] using rungList_length_le (hobby.n - 1)
  unfold FitsLen i64MaxNat
  exact Nat.le_trans (add_cap _ hobby.n _ hlen) hobby_ctrl_num

theorem serious_move_budget : FitsLen (perHole serious.n serious.benchlen * serious.n) := by
  unfold FitsLen perHole plantRoom i64MaxNat serious
  exact Nat.le_of_ble_eq_true rfl

theorem serious_slide_budget : FitsLen (perSlide serious.n * serious.n) := by
  unfold FitsLen perSlide i64MaxNat serious
  exact Nat.le_of_ble_eq_true rfl

theorem serious_ctrl_num : (serious.n - 1) + perCtrl serious.n * serious.n ≤ 9223372036854775807 := by
  unfold perCtrl serious
  exact Nat.le_of_ble_eq_true rfl

theorem serious_ctrl_budget : FitsLen (tierR serious + perCtrl serious.n * serious.n) := by
  have hlen : tierR serious ≤ serious.n - 1 := by
    simpa [tierR] using rungList_length_le (serious.n - 1)
  unfold FitsLen i64MaxNat
  exact Nat.le_trans (add_cap _ serious.n _ hlen) serious_ctrl_num

theorem demo_fresh : PlantAt (builtBoard demo) demo demo.n :=
  fresh_plant demo demo_shape demo.n (by decide) (Nat.le_refl _) demo_move_budget demo_slide_budget
    demo_ctrl_budget

theorem toy_fresh : PlantAt (builtBoard toy) toy toy.n :=
  fresh_plant toy toy_shape toy.n (by decide) (Nat.le_refl _) toy_move_budget toy_slide_budget
    toy_ctrl_budget

theorem hobby_fresh : PlantAt (builtBoard hobby) hobby hobby.n :=
  fresh_plant hobby hobby_shape hobby.n (by decide) (Nat.le_refl _) hobby_move_budget
    hobby_slide_budget hobby_ctrl_budget

theorem serious_fresh : PlantAt (builtBoard serious) serious serious.n :=
  fresh_plant serious serious_shape serious.n (by decide) (Nat.le_refl _) serious_move_budget
    serious_slide_budget serious_ctrl_budget

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
