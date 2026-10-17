/-
  The room a live cell spends on top of one charge. Frobenius adds two to the
  ops cap and raises strict and hole through `raisedPeak` and `raisedHole`.
  A chord then adds one `cellOpsCharge`. The shipped-tier lemmas
  `demo_walk_room` and its siblings already fit `(cells + 1)` charges in an
  i64. These lemmas turn that product into the `ops + 2` check and into
  `FitsLen` of the two counters. Neither check is a hypothesis of a tier walk.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `raisedPeak` stays under a cap that already bounds both arguments. -/
theorem raised_keep (cap a b : Nat) (ha : a ≤ cap) (hb : b ≤ cap) :
    raisedPeak a b ≤ cap := by
  unfold raisedPeak
  by_cases h : a < b
  · simpa [h] using hb
  · simpa [h] using ha

/-- `raisedHole` is the same shape as `raisedPeak`. -/
theorem hole_keep (cap a b : Nat) (ha : a ≤ cap) (hb : b ≤ cap) :
    raisedHole a b ≤ cap := by
  unfold raisedHole
  by_cases h : a < b
  · simpa [h] using hb
  · simpa [h] using ha

/-- Two raises, each against a count of at most seven, stay at most seven. -/
theorem strict_out_le (peakS occA occU : Nat) (hst : peakS ≤ 7)
    (ha : occA ≤ 7) (hu : occU ≤ 7) :
    raisedPeak (raisedPeak peakS occA) occU ≤ 7 :=
  raised_keep 7 _ _ (raised_keep 7 peakS occA hst ha) hu

/-- Three raises by counts of at most seven stay at most seven. -/
theorem raised_thrice_le (p a b c : Nat) (hp : p ≤ 7) (ha : a ≤ 7) (hb : b ≤ 7)
    (hc : c ≤ 7) :
    raisedPeak (raisedPeak (raisedPeak p a) b) c ≤ 7 :=
  raised_keep 7 _ c (strict_out_le p a b hp ha hb) hc

/-- Two hole raises stay under the bench when each top does. -/
theorem hole_out_le (hole topA topU bench : Nat) (hh : hole ≤ bench)
    (ha : topA ≤ bench) (hu : topU ≤ bench) :
    raisedHole (raisedHole hole topA) topU ≤ bench :=
  hole_keep bench _ _ (hole_keep bench hole topA hh ha) hu

theorem held_seven (held : Array Bool) : countHeld held 7 ≤ 7 := by
  have : ∀ i, countHeld held i ≤ i := by
    intro i
    induction i with
    | zero => simp [countHeld]
    | succ i ih =>
      unfold countHeld
      have : (if held.getD i false then 1 else 0) ≤ 1 := by split <;> decide
      omega
  exact this 7

/-- The highest-hole scan never returns an index past the strip. -/
theorem topIdx_le (xs : List Nat) : topIdx xs ≤ xs.length := by
  unfold topIdx
  suffices ∀ k t, k ≤ xs.length → t ≤ xs.length →
      (List.range k).foldl (fun t i => if coeff xs i = 0 then t else i) t ≤ xs.length from
    this xs.length 0 (Nat.le_refl _) (Nat.zero_le _)
  intro k
  induction k with
  | zero =>
    intro t _ ht
    simpa using ht
  | succ k ih =>
    intro t hk ht
    rw [List.range_succ, List.foldl_append]
    have hpre := ih t (Nat.le_of_lt (Nat.lt_of_succ_le hk)) ht
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h0 : coeff xs k = 0
    · simpa [h0] using hpre
    · simp only [h0, ite_false]
      exact Nat.le_of_lt (Nat.lt_of_succ_le hk)

theorem cube_over (n bench : Nat) (hn : n ≤ bench) :
    cubeCharge n bench = 6 * bench + 2 * n := by
  unfold cubeCharge
  omega

theorem slide_over_eq (n : Nat) : slideCharge n = 4 * n := rfl

/-- After `done` cells the next `ops + 2`, and the chord's remaining charges
    on that bumped cap, still sit inside `(cells + 1)` op charges. -/
theorem ops_next_fit (cells c done left ops : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hspan : 2 * cells + 2 ≤ c)
    (hops : ops ≤ done * (c + 2))
    (hroom : FitsLen ((cells + 1) * c)) :
    FitsLen (ops + 2) ∧ FitsLen (ops + 2 + left * c) := by
  have hsplit : done * (c + 2) = done * c + 2 * done := by
    rw [Nat.mul_add]
    omega
  have hops' : ops ≤ done * c + 2 * done := by
    rw [← hsplit]
    exact hops
  have hmix : done * c + left * c = cells * c := by
    rw [← Nat.add_mul, hsum]
  have htwo : 2 * done + 2 ≤ 2 * cells := by
    have hd : done ≤ cells - 1 := by omega
    omega
  have hspan' : 2 * cells ≤ c := by omega
  have hsmall : 2 * done + 2 ≤ c := Nat.le_trans htwo hspan'
  have hprod : (cells + 1) * c = cells * c + c := by rw [Nat.succ_mul]
  refine ⟨?_, ?_⟩
  · apply FitsLen.of_le hroom
    have h1 : ops + 2 ≤ cells * c + c := by
      have h0 : ops + 2 ≤ done * c + 2 * done + 2 := by omega
      have hle : done * c + 2 * done + 2 ≤ cells * c + c := by omega
      exact Nat.le_trans h0 hle
    rw [hprod]
    exact h1
  · apply FitsLen.of_le hroom
    have h0 : ops + 2 + left * c ≤ done * c + left * c + 2 * done + 2 := by omega
    have h1 : done * c + left * c + 2 * done + 2 = cells * c + 2 * done + 2 := by
      rw [hmix]
    have h2 : cells * c + 2 * done + 2 ≤ cells * c + c := by omega
    have hbound : ops + 2 + left * c ≤ cells * c + c :=
      Nat.le_trans h0 (h1.symm ▸ h2)
    rw [hprod]
    exact hbound

/-- One cell that adds `c + 2` lands on the next multiple of `c + 2`. -/
theorem ops_succ (c done ops ops' : Nat)
    (hops : ops ≤ done * (c + 2))
    (hstep : ops' ≤ ops + c + 2) :
    ops' ≤ (done + 1) * (c + 2) := by
  have h : (done + 1) * (c + 2) = done * (c + 2) + (c + 2) := by rw [Nat.succ_mul]
  omega

theorem move_succ (walk over done moves moves' : Nat)
    (hm : moves ≤ done * (walk + over))
    (hstep : moves' ≤ moves + walk + over) :
    moves' ≤ (done + 1) * (walk + over) := by
  have h : (done + 1) * (walk + over) = done * (walk + over) + (walk + over) := by
    rw [Nat.succ_mul]
  omega

theorem slide_succ (s extra done slides slides' : Nat)
    (hs : slides ≤ done * (s + extra))
    (hstep : slides' ≤ slides + s + extra) :
    slides' ≤ (done + 1) * (s + extra) := by
  have h : (done + 1) * (s + extra) = done * (s + extra) + (s + extra) := by
    rw [Nat.succ_mul]
  omega

theorem ctrl_succ (c extra done ctrl ctrl' : Nat)
    (hc : ctrl ≤ done * (c + extra))
    (hstep : ctrl' ≤ ctrl + c + extra) :
    ctrl' ≤ (done + 1) * (c + extra) := by
  have h : (done + 1) * (c + extra) = done * (c + extra) + (c + extra) := by
    rw [Nat.succ_mul]
  omega

private theorem move_envelope (cells walk over done left moves : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : over * cells ≤ walk)
    (hm : moves ≤ done * (walk + over)) :
    moves + walk ≤ (cells + 1) * walk := by
  have hsplit : done * (walk + over) = done * walk + done * over := Nat.mul_add _ _ _
  have hm' : moves ≤ done * walk + done * over := by
    rw [← hsplit]
    exact hm
  have hd : done ≤ cells := by omega
  have hmul : over * done ≤ over * cells := Nat.mul_le_mul_left over hd
  have hcap : done * over ≤ walk := by
    rw [Nat.mul_comm done over]
    exact Nat.le_trans hmul hov
  have hsumW : done * walk + walk + walk = (done + 2) * walk := by
    rw [Nat.succ_mul, Nat.succ_mul]
  have henv : (done + 2) * walk ≤ (cells + 1) * walk := by
    apply Nat.mul_le_mul_right
    omega
  have h1 : moves + walk ≤ done * walk + walk + walk := by omega
  have h1' : moves + walk ≤ (done + 2) * walk := by
    rw [← hsumW]
    exact h1
  exact Nat.le_trans h1' henv

theorem move_check_fit (cells walk over done left moves add : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : over * cells ≤ walk)
    (hm : moves ≤ done * (walk + over))
    (hadd : add ≤ walk)
    (hroom : FitsLen ((cells + 1) * walk)) :
    FitsLen (moves + add) := by
  apply FitsLen.of_le hroom
  have henv := move_envelope cells walk over done left moves hsum hleft hov hm
  omega

theorem slide_check_fit (cells n s done left slides : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : 4 * n * cells ≤ s)
    (hs : slides ≤ done * (s + 4 * n))
    (hroom : FitsLen ((cells + 1) * s)) :
    FitsLen (slides + 4 * n) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (s + 4 * n) = done * s + done * (4 * n) := Nat.mul_add _ _ _
  have hs' : slides ≤ done * s + done * (4 * n) := by
    rw [← hsplit]
    exact hs
  have hfac : done * (4 * n) + 4 * n = (done + 1) * (4 * n) := by
    rw [← Nat.succ_mul]
  have hd : done + 1 ≤ cells := by omega
  have hmul : (4 * n) * (done + 1) ≤ (4 * n) * cells := Nat.mul_le_mul_left _ hd
  have hcap : (done + 1) * (4 * n) ≤ s := by
    rw [Nat.mul_comm (done + 1)]
    exact Nat.le_trans hmul hov
  have hprod : (cells + 1) * s = cells * s + s := by rw [Nat.succ_mul]
  have hdoneS : done * s + s ≤ cells * s + s := by
    have : done ≤ cells := by omega
    exact Nat.add_le_add_right (Nat.mul_le_mul_right s this) s
  have h1 : slides + 4 * n ≤ done * s + (done + 1) * (4 * n) := by
    rw [← hfac]
    omega
  have h2 : done * s + (done + 1) * (4 * n) ≤ done * s + s := by omega
  rw [hprod]
  exact Nat.le_trans (Nat.le_trans h1 h2) hdoneS

theorem ctrl_check_fit (cells c done left ctrl : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : 4 * cells ≤ c)
    (hc : ctrl ≤ done * (c + 4))
    (hroom : FitsLen ((cells + 1) * c)) :
    FitsLen (ctrl + 5) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (c + 4) = done * c + 4 * done := by
    rw [Nat.mul_add, Nat.mul_comm 4 done]
  have hc' : ctrl ≤ done * c + 4 * done := by
    rw [← hsplit]
    exact hc
  have hfac : 4 * done + 4 = 4 * (done + 1) := by rw [Nat.mul_succ]
  have hd : done + 1 ≤ cells := by omega
  have hmul : 4 * (done + 1) ≤ 4 * cells := Nat.mul_le_mul_left 4 hd
  have hcap : 4 * (done + 1) ≤ c := Nat.le_trans hmul hov
  have hmix : done * c + left * c = cells * c := by rw [← Nat.add_mul, hsum]
  have hprod : (cells + 1) * c = cells * c + c := by rw [Nat.succ_mul]
  have h1 : ctrl + 5 ≤ done * c + 4 * (done + 1) + 1 := by
    rw [← hfac]
    omega
  have h2 : done * c + 4 * (done + 1) + 1 ≤ done * c + c + 1 := by omega
  have h3 : done * c + c + 1 ≤ cells * c + c := by
    have hleftC : c ≤ left * c := Nat.le_mul_of_pos_left c hleft
    omega
  rw [hprod]
  exact Nat.le_trans (Nat.le_trans h1 h2) h3

/-- The chord's four rooms, charged from the worst counter Frobenius can leave. -/
theorem chord_move_fit (cells walk over cmove done left moves add : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hw : cmove ≤ walk)
    (hov : over * cells ≤ walk)
    (hm : moves ≤ done * (walk + over))
    (hadd : add ≤ over)
    (hroom : FitsLen ((cells + 1) * walk)) :
    FitsLen (moves + add + left * cmove) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (walk + over) = done * walk + done * over := Nat.mul_add _ _ _
  have hm' : moves ≤ done * walk + done * over := by
    rw [← hsplit]
    exact hm
  have hfac : done * over + over = (done + 1) * over := by rw [← Nat.succ_mul]
  have hd : done + 1 ≤ cells := by omega
  have hmul : over * (done + 1) ≤ over * cells := Nat.mul_le_mul_left over hd
  have hcap : (done + 1) * over ≤ walk := by
    rw [Nat.mul_comm (done + 1)]
    exact Nat.le_trans hmul hov
  have hleftM : left * cmove ≤ left * walk := Nat.mul_le_mul_left left hw
  have hsumW : done * walk + walk + left * walk = (done + 1 + left) * walk := by
    have h1 : (done + 1) * walk = done * walk + walk := by rw [Nat.succ_mul]
    have h2 : (done + 1 + left) * walk = (done + 1) * walk + left * walk := by
      rw [Nat.add_mul]
    omega
  have hcells : done + 1 + left = cells + 1 := by omega
  have h1 : moves + add + left * cmove ≤ done * walk + (done + 1) * over + left * walk := by
    rw [← hfac]
    omega
  have h2 : done * walk + (done + 1) * over + left * walk ≤ done * walk + walk + left * walk := by
    omega
  rw [hcells] at hsumW
  have h3 : moves + add + left * cmove ≤ done * walk + walk + left * walk :=
    Nat.le_trans h1 h2
  rw [← hsumW]
  exact h3

theorem chord_slide_fit (cells n s done left slides : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : 4 * n * cells ≤ s)
    (hs : slides ≤ done * (s + 4 * n))
    (hroom : FitsLen ((cells + 1) * s)) :
    FitsLen (slides + 4 * n + left * s) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (s + 4 * n) = done * s + done * (4 * n) := Nat.mul_add _ _ _
  have hs' : slides ≤ done * s + done * (4 * n) := by
    rw [← hsplit]
    exact hs
  have hfac : done * (4 * n) + 4 * n = (done + 1) * (4 * n) := by rw [← Nat.succ_mul]
  have hd : done + 1 ≤ cells := by omega
  have hmul : (4 * n) * (done + 1) ≤ (4 * n) * cells := Nat.mul_le_mul_left _ hd
  have hcap : (done + 1) * (4 * n) ≤ s := by
    rw [Nat.mul_comm (done + 1)]
    exact Nat.le_trans hmul hov
  have hprod : (cells + 1) * s = (done + 1 + left) * s := by
    have : cells + 1 = done + 1 + left := by omega
    rw [this]
  have hsumS : (done + 1 + left) * s = done * s + s + left * s := by
    have h1 : (done + 1) * s = done * s + s := by rw [Nat.succ_mul]
    have h2 : (done + 1 + left) * s = (done + 1) * s + left * s := by rw [Nat.add_mul]
    omega
  have h1 : slides + 4 * n + left * s ≤ done * s + (done + 1) * (4 * n) + left * s := by
    rw [← hfac]
    omega
  have h2 : done * s + (done + 1) * (4 * n) + left * s ≤ done * s + s + left * s := by omega
  rw [hprod, hsumS]
  exact Nat.le_trans h1 h2

theorem chord_ctrl_fit (cells c done left ctrl : Nat)
    (hsum : done + left = cells) (hleft : 0 < left)
    (hov : 4 * cells ≤ c)
    (hc : ctrl ≤ done * (c + 4))
    (hroom : FitsLen ((cells + 1) * c)) :
    FitsLen (ctrl + 4 + left * c) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (c + 4) = done * c + 4 * done := by
    rw [Nat.mul_add, Nat.mul_comm 4 done]
  have hc' : ctrl ≤ done * c + 4 * done := by
    rw [← hsplit]
    exact hc
  have hfac : 4 * done + 4 = 4 * (done + 1) := by rw [Nat.mul_succ]
  have hd : done + 1 ≤ cells := by omega
  have hmul : 4 * (done + 1) ≤ 4 * cells := Nat.mul_le_mul_left 4 hd
  have hcap : 4 * (done + 1) ≤ c := Nat.le_trans hmul hov
  have hprod : (cells + 1) * c = (done + left + 1) * c := by
    have : cells = done + left := by omega
    rw [this]
  have hsumC : (done + left + 1) * c = done * c + left * c + c := by
    have h1 : (done + left) * c = done * c + left * c := by rw [Nat.add_mul]
    have h2 : (done + left + 1) * c = (done + left) * c + c := by rw [Nat.succ_mul]
    omega
  have h1 : ctrl + 4 + left * c ≤ done * c + 4 * (done + 1) + left * c := by
    rw [← hfac]
    omega
  have h2 : done * c + 4 * (done + 1) + left * c ≤ done * c + c + left * c := by omega
  rw [hprod, hsumC]
  omega

theorem counter_fit (k cap : Nat) (hk : k ≤ cap) (h : FitsLen cap) : FitsLen k :=
  FitsLen.of_le h hk

theorem strict_out_fit (peakS occA occU cap : Nat)
    (hst : peakS ≤ 7) (ha : occA ≤ 7) (hu : occU ≤ 7)
    (h7 : 7 ≤ cap) (hroom : FitsLen cap) :
    FitsLen (raisedPeak (raisedPeak peakS occA) occU) := by
  apply counter_fit
  · exact Nat.le_trans (strict_out_le peakS occA occU hst ha hu) h7
  · exact hroom

theorem hole_out_fit (hole topA topU bench cap : Nat)
    (hh : hole ≤ bench) (ha : topA ≤ bench) (hu : topU ≤ bench)
    (hb : bench ≤ cap) (hroom : FitsLen cap) :
    FitsLen (raisedHole (raisedHole hole topA) topU) := by
  apply counter_fit
  · exact Nat.le_trans (hole_out_le hole topA topU bench hh ha hu) hb
  · exact hroom

/-- Frobenius's four checks, the two counters, and the chord's four rooms,
    all `FitsLen.of_le` of the `(cells + 1)` products. -/
theorem frob_fits (t : Spec.Tier) (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = t.cells) (hleft : 0 < left)
    (hn : t.n ≤ t.benchlen)
    (hopsOver : 2 * t.cells + 2 ≤ cellOpsCharge t)
    (hmoveOver : (6 * t.benchlen + 2 * t.n) * t.cells ≤ walkCharge t)
    (hslideOver : 4 * t.n * t.cells ≤ cellSlideCharge t)
    (hctrlOver : 4 * t.cells ≤ cellCtrlCharge t)
    (hseven : 7 ≤ (t.cells + 1) * cellOpsCharge t)
    (hbench : t.benchlen ≤ (t.cells + 1) * cellOpsCharge t)
    (hm : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : slides ≤ done * (cellSlideCharge t + 4 * t.n))
    (hc : ctrl ≤ done * (cellCtrlCharge t + 4))
    (ho : ops ≤ done * (cellOpsCharge t + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ t.benchlen)
    (hRoomM : FitsLen ((t.cells + 1) * walkCharge t))
    (hRoomS : FitsLen ((t.cells + 1) * cellSlideCharge t))
    (hRoomC : FitsLen ((t.cells + 1) * cellCtrlCharge t))
    (hRoomO : FitsLen ((t.cells + 1) * cellOpsCharge t)) :
    FitsLen (moves + cubeCharge t.n t.benchlen + 3 * t.n) ∧
      FitsLen (slides + slideCharge t.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge t) ∧
      FitsLen (moves + cubeCharge t.n t.benchlen + left * cellMoveCharge t) ∧
      FitsLen (slides + slideCharge t.n + left * cellSlideCharge t) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge t) := by
  have hMove := move_check_fit t.cells (walkCharge t) (6 * t.benchlen + 2 * t.n)
    done left moves (cubeCharge t.n t.benchlen + 3 * t.n)
    hsum hleft hmoveOver hm (frob_move_le_walk t) hRoomM
  have hSlide := slide_check_fit t.cells t.n (cellSlideCharge t) done left slides
    hsum hleft hslideOver hs hRoomS
  have hCtrl := ctrl_check_fit t.cells (cellCtrlCharge t) done left ctrl
    hsum hleft hctrlOver hc hRoomC
  have hOps := ops_next_fit t.cells (cellOpsCharge t) done left ops
    hsum hleft hopsOver ho hRoomO
  have hStrict := counter_fit peakS ((t.cells + 1) * cellOpsCharge t)
    (Nat.le_trans hst hseven) hRoomO
  have hHole := counter_fit hole ((t.cells + 1) * cellOpsCharge t)
    (Nat.le_trans hhole hbench) hRoomO
  have hcm : cellMoveCharge t ≤ walkCharge t := by
    rw [← walkCharge_split t]
    omega
  have hadd : cubeCharge t.n t.benchlen ≤ 6 * t.benchlen + 2 * t.n :=
    Nat.le_of_eq (cube_over t.n t.benchlen hn)
  have hChordM := chord_move_fit t.cells (walkCharge t) (6 * t.benchlen + 2 * t.n)
    (cellMoveCharge t) done left moves (cubeCharge t.n t.benchlen)
    hsum hleft hcm hmoveOver hm hadd hRoomM
  have hChordS := chord_slide_fit t.cells t.n (cellSlideCharge t) done left slides
    hsum hleft hslideOver hs hRoomS
  have hChordC := chord_ctrl_fit t.cells (cellCtrlCharge t) done left ctrl
    hsum hleft hctrlOver hc hRoomC
  have hslideEq : slides + 4 * t.n = slides + slideCharge t.n := by rw [slide_over_eq]
  refine ⟨by simpa [Nat.add_assoc] using hMove, by simpa [hslideEq] using hSlide, hCtrl,
    hOps.1, hStrict, hHole, hOps.2, hChordM, by simpa [hslideEq] using hChordS, hChordC⟩

private theorem demo_tierR : tierR Spec.demo = 2 := by
  simp [tierR, demo_rungs]

private theorem toy_tierR : tierR Spec.toy = 4 := by
  simp [tierR, toy_rungs]

private theorem hobby_tierR : tierR Spec.hobby = 5 := by
  simp [tierR, hobby_rungs]

private theorem serious_tierR : tierR Spec.serious = 7 := by
  simp [tierR, serious_rungs]

private theorem demo_row : rowRoom Spec.demo = 6 := by
  rw [rowRoom, tallyOrigin, demo_tierR]
  simp [Spec.demo]

private theorem toy_row : rowRoom Spec.toy = 18 := by
  rw [rowRoom, tallyOrigin, toy_tierR]
  simp [Spec.toy]

private theorem hobby_row : rowRoom Spec.hobby = 57 := by
  rw [rowRoom, tallyOrigin, hobby_tierR]
  simp [Spec.hobby]

private theorem serious_row : rowRoom Spec.serious = 175 := by
  rw [rowRoom, tallyOrigin, serious_tierR]
  simp [Spec.serious]

/-- Demo's extra `+ 2` on ops, the Frobenius move and slide overhead, four
    control steps a cell, and the two counters, all sit inside the proved room. -/
theorem demo_walk_span :
    2 * Spec.demo.cells + 2 ≤ cellOpsCharge Spec.demo ∧
      (6 * Spec.demo.benchlen + 2 * Spec.demo.n) * Spec.demo.cells ≤
        walkCharge Spec.demo ∧
      4 * Spec.demo.n * Spec.demo.cells ≤ cellSlideCharge Spec.demo ∧
      4 * Spec.demo.cells ≤ cellCtrlCharge Spec.demo ∧
      7 ≤ (Spec.demo.cells + 1) * cellOpsCharge Spec.demo ∧
      Spec.demo.benchlen ≤ (Spec.demo.cells + 1) * cellOpsCharge Spec.demo ∧
      Spec.demo.n ≤ Spec.demo.benchlen ∧
      4 < Spec.demo.script := by
  unfold walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap rungCharge mulCharge pegCharge rungSlideCharge
  rw [demo_tierR, demo_row]
  simp only [Spec.demo]
  decide

theorem toy_walk_span :
    2 * Spec.toy.cells + 2 ≤ cellOpsCharge Spec.toy ∧
      (6 * Spec.toy.benchlen + 2 * Spec.toy.n) * Spec.toy.cells ≤ walkCharge Spec.toy ∧
      4 * Spec.toy.n * Spec.toy.cells ≤ cellSlideCharge Spec.toy ∧
      4 * Spec.toy.cells ≤ cellCtrlCharge Spec.toy ∧
      7 ≤ (Spec.toy.cells + 1) * cellOpsCharge Spec.toy ∧
      Spec.toy.benchlen ≤ (Spec.toy.cells + 1) * cellOpsCharge Spec.toy ∧
      Spec.toy.n ≤ Spec.toy.benchlen ∧
      4 < Spec.toy.script := by
  unfold walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap rungCharge mulCharge pegCharge rungSlideCharge
  rw [toy_tierR, toy_row]
  simp only [Spec.toy]
  decide

theorem hobby_walk_span :
    2 * Spec.hobby.cells + 2 ≤ cellOpsCharge Spec.hobby ∧
      (6 * Spec.hobby.benchlen + 2 * Spec.hobby.n) * Spec.hobby.cells ≤
        walkCharge Spec.hobby ∧
      4 * Spec.hobby.n * Spec.hobby.cells ≤ cellSlideCharge Spec.hobby ∧
      4 * Spec.hobby.cells ≤ cellCtrlCharge Spec.hobby ∧
      7 ≤ (Spec.hobby.cells + 1) * cellOpsCharge Spec.hobby ∧
      Spec.hobby.benchlen ≤ (Spec.hobby.cells + 1) * cellOpsCharge Spec.hobby ∧
      Spec.hobby.n ≤ Spec.hobby.benchlen ∧
      4 < Spec.hobby.script := by
  unfold walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap rungCharge mulCharge pegCharge rungSlideCharge
  rw [hobby_tierR, hobby_row]
  simp only [Spec.hobby]
  decide

theorem serious_walk_span :
    2 * Spec.serious.cells + 2 ≤ cellOpsCharge Spec.serious ∧
      (6 * Spec.serious.benchlen + 2 * Spec.serious.n) * Spec.serious.cells ≤
        walkCharge Spec.serious ∧
      4 * Spec.serious.n * Spec.serious.cells ≤ cellSlideCharge Spec.serious ∧
      4 * Spec.serious.cells ≤ cellCtrlCharge Spec.serious ∧
      7 ≤ (Spec.serious.cells + 1) * cellOpsCharge Spec.serious ∧
      Spec.serious.benchlen ≤ (Spec.serious.cells + 1) * cellOpsCharge Spec.serious ∧
      Spec.serious.n ≤ Spec.serious.benchlen ∧
      4 < Spec.serious.script := by
  unfold walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap rungCharge mulCharge pegCharge rungSlideCharge
  rw [serious_tierR, serious_row]
  simp only [Spec.serious]
  decide

/-- The proved span and the proved `(cells + 1)` rooms, as one fact a cell can take. -/
structure TierWalk (t : Spec.Tier) : Prop where
  nLe : t.n ≤ t.benchlen
  opsOver : 2 * t.cells + 2 ≤ cellOpsCharge t
  moveOver : (6 * t.benchlen + 2 * t.n) * t.cells ≤ walkCharge t
  slideOver : 4 * t.n * t.cells ≤ cellSlideCharge t
  ctrlOver : 4 * t.cells ≤ cellCtrlCharge t
  sevenLe : 7 ≤ (t.cells + 1) * cellOpsCharge t
  benchLe : t.benchlen ≤ (t.cells + 1) * cellOpsCharge t
  roomM : FitsLen ((t.cells + 1) * walkCharge t)
  roomS : FitsLen ((t.cells + 1) * cellSlideCharge t)
  roomC : FitsLen ((t.cells + 1) * cellCtrlCharge t)
  roomO : FitsLen ((t.cells + 1) * cellOpsCharge t)
  /-- After Frobenius the marker sits at 1, so the chord's `mark + 3 < script` is `4 < script`. -/
  scriptRoom : 4 < t.script

theorem demo_tier_walk : TierWalk Spec.demo := by
  have s := demo_walk_span
  have r := demo_walk_room
  exact ⟨s.2.2.2.2.2.2.1, s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2.2.2.2⟩

theorem toy_tier_walk : TierWalk Spec.toy := by
  have s := toy_walk_span
  have r := toy_walk_room
  exact ⟨s.2.2.2.2.2.2.1, s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2.2.2.2⟩

theorem hobby_tier_walk : TierWalk Spec.hobby := by
  have s := hobby_walk_span
  have r := hobby_walk_room
  exact ⟨s.2.2.2.2.2.2.1, s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2.2.2.2⟩

theorem serious_tier_walk : TierWalk Spec.serious := by
  have s := serious_walk_span
  have r := serious_walk_room
  exact ⟨s.2.2.2.2.2.2.1, s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2.2.2.2⟩

theorem tier_frob_fits (t : Spec.Tier) (tw : TierWalk t)
    (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = t.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : slides ≤ done * (cellSlideCharge t + 4 * t.n))
    (hc : ctrl ≤ done * (cellCtrlCharge t + 4))
    (ho : ops ≤ done * (cellOpsCharge t + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ t.benchlen) :
    FitsLen (moves + cubeCharge t.n t.benchlen + 3 * t.n) ∧
      FitsLen (slides + slideCharge t.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge t) ∧
      FitsLen (moves + cubeCharge t.n t.benchlen + left * cellMoveCharge t) ∧
      FitsLen (slides + slideCharge t.n + left * cellSlideCharge t) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge t) :=
  frob_fits t done left moves slides ctrl ops peakS hole hsum hleft tw.nLe tw.opsOver
    tw.moveOver tw.slideOver tw.ctrlOver tw.sevenLe tw.benchLe hm hs hc ho hst hhole
    tw.roomM tw.roomS tw.roomC tw.roomO

theorem demo_frob_fits (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = Spec.demo.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge Spec.demo + (6 * Spec.demo.benchlen + 2 * Spec.demo.n)))
    (hs : slides ≤ done * (cellSlideCharge Spec.demo + 4 * Spec.demo.n))
    (hc : ctrl ≤ done * (cellCtrlCharge Spec.demo + 4))
    (ho : ops ≤ done * (cellOpsCharge Spec.demo + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ Spec.demo.benchlen) :
    FitsLen (moves + cubeCharge Spec.demo.n Spec.demo.benchlen + 3 * Spec.demo.n) ∧
      FitsLen (slides + slideCharge Spec.demo.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge Spec.demo) ∧
      FitsLen (moves + cubeCharge Spec.demo.n Spec.demo.benchlen +
        left * cellMoveCharge Spec.demo) ∧
      FitsLen (slides + slideCharge Spec.demo.n + left * cellSlideCharge Spec.demo) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge Spec.demo) := by
  have hspan := demo_walk_span
  have hroom := demo_walk_room
  exact frob_fits Spec.demo done left moves slides ctrl ops peakS hole
    hsum hleft hspan.2.2.2.2.2.2.1 hspan.1 hspan.2.1 hspan.2.2.1 hspan.2.2.2.1
    hspan.2.2.2.2.1 hspan.2.2.2.2.2.1 hm hs hc ho hst hhole
    hroom.1 hroom.2.1 hroom.2.2.1 hroom.2.2.2

theorem toy_frob_fits (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = Spec.toy.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge Spec.toy + (6 * Spec.toy.benchlen + 2 * Spec.toy.n)))
    (hs : slides ≤ done * (cellSlideCharge Spec.toy + 4 * Spec.toy.n))
    (hc : ctrl ≤ done * (cellCtrlCharge Spec.toy + 4))
    (ho : ops ≤ done * (cellOpsCharge Spec.toy + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ Spec.toy.benchlen) :
    FitsLen (moves + cubeCharge Spec.toy.n Spec.toy.benchlen + 3 * Spec.toy.n) ∧
      FitsLen (slides + slideCharge Spec.toy.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge Spec.toy) ∧
      FitsLen (moves + cubeCharge Spec.toy.n Spec.toy.benchlen +
        left * cellMoveCharge Spec.toy) ∧
      FitsLen (slides + slideCharge Spec.toy.n + left * cellSlideCharge Spec.toy) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge Spec.toy) := by
  have hspan := toy_walk_span
  have hroom := toy_walk_room
  exact frob_fits Spec.toy done left moves slides ctrl ops peakS hole
    hsum hleft hspan.2.2.2.2.2.2.1 hspan.1 hspan.2.1 hspan.2.2.1 hspan.2.2.2.1
    hspan.2.2.2.2.1 hspan.2.2.2.2.2.1 hm hs hc ho hst hhole
    hroom.1 hroom.2.1 hroom.2.2.1 hroom.2.2.2

theorem hobby_frob_fits (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = Spec.hobby.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge Spec.hobby +
      (6 * Spec.hobby.benchlen + 2 * Spec.hobby.n)))
    (hs : slides ≤ done * (cellSlideCharge Spec.hobby + 4 * Spec.hobby.n))
    (hc : ctrl ≤ done * (cellCtrlCharge Spec.hobby + 4))
    (ho : ops ≤ done * (cellOpsCharge Spec.hobby + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ Spec.hobby.benchlen) :
    FitsLen (moves + cubeCharge Spec.hobby.n Spec.hobby.benchlen + 3 * Spec.hobby.n) ∧
      FitsLen (slides + slideCharge Spec.hobby.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge Spec.hobby) ∧
      FitsLen (moves + cubeCharge Spec.hobby.n Spec.hobby.benchlen +
        left * cellMoveCharge Spec.hobby) ∧
      FitsLen (slides + slideCharge Spec.hobby.n + left * cellSlideCharge Spec.hobby) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge Spec.hobby) := by
  have hspan := hobby_walk_span
  have hroom := hobby_walk_room
  exact frob_fits Spec.hobby done left moves slides ctrl ops peakS hole
    hsum hleft hspan.2.2.2.2.2.2.1 hspan.1 hspan.2.1 hspan.2.2.1 hspan.2.2.2.1
    hspan.2.2.2.2.1 hspan.2.2.2.2.2.1 hm hs hc ho hst hhole
    hroom.1 hroom.2.1 hroom.2.2.1 hroom.2.2.2

theorem serious_frob_fits (done left moves slides ctrl ops peakS hole : Nat)
    (hsum : done + left = Spec.serious.cells) (hleft : 0 < left)
    (hm : moves ≤ done *
      (walkCharge Spec.serious + (6 * Spec.serious.benchlen + 2 * Spec.serious.n)))
    (hs : slides ≤ done * (cellSlideCharge Spec.serious + 4 * Spec.serious.n))
    (hc : ctrl ≤ done * (cellCtrlCharge Spec.serious + 4))
    (ho : ops ≤ done * (cellOpsCharge Spec.serious + 2))
    (hst : peakS ≤ 7) (hhole : hole ≤ Spec.serious.benchlen) :
    FitsLen (moves + cubeCharge Spec.serious.n Spec.serious.benchlen + 3 * Spec.serious.n) ∧
      FitsLen (slides + slideCharge Spec.serious.n) ∧
      FitsLen (ctrl + 5) ∧
      FitsLen (ops + 2) ∧
      FitsLen peakS ∧
      FitsLen hole ∧
      FitsLen (ops + 2 + left * cellOpsCharge Spec.serious) ∧
      FitsLen (moves + cubeCharge Spec.serious.n Spec.serious.benchlen +
        left * cellMoveCharge Spec.serious) ∧
      FitsLen (slides + slideCharge Spec.serious.n + left * cellSlideCharge Spec.serious) ∧
      FitsLen (ctrl + 4 + left * cellCtrlCharge Spec.serious) := by
  have hspan := serious_walk_span
  have hroom := serious_walk_room
  exact frob_fits Spec.serious done left moves slides ctrl ops peakS hole
    hsum hleft hspan.2.2.2.2.2.2.1 hspan.1 hspan.2.1 hspan.2.2.1 hspan.2.2.2.1
    hspan.2.2.2.2.1 hspan.2.2.2.2.2.1 hm hs hc ho hst hhole
    hroom.1 hroom.2.1 hroom.2.2.1 hroom.2.2.2

end EcbsLink2.Link2
