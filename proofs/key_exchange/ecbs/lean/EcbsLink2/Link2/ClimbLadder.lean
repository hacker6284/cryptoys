/-
  The emitted climb keeps the ladder array. `climbRung_ladder` is one rung.
  `climbEmit_ladder` is the induction. The ladder on the tally board is
  `tierClimb`; this file only carries whatever array the step is given.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ClimbStep
import EcbsLink2.Link2.MulKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem climbStepBoard_ladder (x : Int) (b : Ecbs.Board) (rung : Nat) (last : Bool)
    (b' : Ecbs.Board) (h : climbStepBoard x b rung last = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold climbStepBoard at h
  exact climbRung_ladder b rung last x b.sudo_5Board_9tally_len.toNat b' h

/-- The ladder array is the one the first board stored. A rung does not write it. -/
theorem climbEmit_ladder (x : Int) (b : Ecbs.Board) (rs : List Nat) (b' : Ecbs.Board)
    (h : climbEmit (climbStepBoard x) b rs = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  induction rs generalizing b with
  | nil =>
    simp [climbEmit] at h
    cases h
    rfl
  | cons r rs ih =>
    rw [climbEmit] at h
    cases hs : climbStepBoard x b r rs.isEmpty with
    | error _ =>
      rw [hs] at h
      simp only [error_bind] at h
      cases h
    | ok b1 =>
      rw [hs, ok_bind] at h
      exact (ih b1 h).trans (climbStepBoard_ladder x b r rs.isEmpty b1 hs)

/-- `tally_max` is a natural at least 1. This is the later `hStart` conjunct.
    It is not a closed formula, and it is not an export result. `walk_key`
    returns a point. -/
def TmaxGe (b : Ecbs.Board) : Prop :=
  ∃ n : Nat, b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (n : Int) ∧ 1 ≤ n

theorem TmaxGe.copy {b b' : Ecbs.Board} (h : TmaxGe b)
    (heq : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max) : TmaxGe b' := by
  obtain ⟨n, hn, h1⟩ := h
  exact ⟨n, heq.trans hn, h1⟩

theorem TmaxGe.of_max {b' : Ecbs.Board} {n k : Nat}
    (h1 : 1 ≤ n)
    (heq : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = ((max n k : Nat) : Int)) :
    TmaxGe b' :=
  ⟨max n k, heq, Nat.le_trans h1 (Nat.le_max_left n k)⟩

/-- An idle clear does not write `tally_max`. -/
theorem climbClear_idle_tmax
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hge : TmaxGe b) :
    ∃ b', climbClear b r s.tally = .ok b' ∧ TmaxGe b' := by
  obtain ⟨bClear, hAll⟩ := gap_clear_emit h hM hS hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, _hrowE, _hctrlE, _hfromE, _hridxE, _hlenE, _ht0E, _hparkE,
      _hhighE, _hmarkE, _hbonE, _htoE, _hbenchE, _htierE, _hladE, _hnrE, htmaxE,
      _h5H, _h5D, _h6H, _h6D, _h7E, _h5f, _h6f, _hkeep, _htrits, _hopsE, _hc1E, _hpkSE,
      _hholeE, _hδs, _hctx, _hside, _hquiet⟩
  refine ⟨bClear, ?_, TmaxGe.copy hge htmaxE⟩
  simpa [climbClear] using hrun

/-- Idle final white rung. The nest is the clear, so `tally_max` stays. -/
theorem idle_white_final_ge
    {done : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done [r] b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2) (hge : TmaxGe b) :
    ∃ b', climbRung b r true ((base.xHome : Nat) : Int) s.tally = .ok b' ∧ TmaxGe b' := by
  obtain ⟨b', hclear, hge'⟩ := climbClear_idle_tmax h hM hS hF hm hT hhome hge
  refine ⟨b', ?_, hge'⟩
  rw [dispatch_idle_white_final b r s.tally ((base.xHome : Nat) : Int) s.fromHole true
    hF hwhite rfl]
  simpa [progWhiteFinal] using hclear

/-- Idle non-final red rung. `tally_max` becomes `max` of the old value and
    `2 · tally + 1`, so a maximum of at least 1 stays at least 1. -/
theorem idle_red_open_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rest ≠ [])
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) (hge : TmaxGe b) :
    ∃ b', climbRung b r false ((base.xHome : Nat) : Int) s.tally = .ok b' ∧ TmaxGe b' := by
  obtain ⟨n, hn, h1⟩ := hge
  obtain ⟨bAdd, hpack⟩ := red_open_emit h hM hS hF hm hT hhome hr hrest hxLen hxT
  have hprog := hpack.1
  have htmaxA := hpack.2.2.2.2.2.2.2.1
  have hcho : h.tmaxLt.choose = n := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact h.tmaxLt.choose_spec.symm.trans hn
  refine ⟨bAdd, ?_, ?_⟩
  · rw [dispatch_idle_red_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole false
      hF hr rfl]
    simpa [progRedOpen, climbClear] using hprog
  · have heq : bAdd.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        ((max n (2 * s.tally + 1) : Nat) : Int) := by
      simpa [hcho] using htmaxA
    exact TmaxGe.of_max h1 heq

/-- `tally_note` writes `tally_max` only by copying the length. A length of at
    least 1 leaves a maximum of at least 1. -/
theorem tally_note_ge (b b' : Ecbs.Board) (k : Nat)
    (hlen : b.sudo_5Board_9tally_len = (k : Int)) (hk : 1 ≤ k) (hge : TmaxGe b)
    (h : Ecbs.tally_note b = .ok b') : TmaxGe b' := by
  unfold Ecbs.tally_note at h
  dsimp only at h
  by_cases hc :
      decide (b.sudo_5Board_9tally_len > b.sudo_5Board_4cost.sudo_5Costs_9tally_max) = true
  · rw [if_pos hc, pure_eq_ok] at h
    cases h
    exact ⟨k, by simp [hlen], hk⟩
  · rw [if_neg hc, pure_eq_ok] at h
    cases h
    exact hge

/-- Idle non-final white rung. The clear keeps `tally_max`, then `tally_double`
    records `max` of that value and `2 · tally`. -/
theorem idle_white_open_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2) (hrest : rest ≠ [])
    (hge : TmaxGe b) :
    ∃ b', climbRung b r false ((base.xHome : Nat) : Int) s.tally = .ok b' ∧ TmaxGe b' := by
  obtain ⟨n, hn, h1⟩ := hge
  obtain ⟨bClear, hAll⟩ := gap_clear_emit h hM hS hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, hrowE, hctrlE, _hfromE, _hridxE, hlenE, ht0E, _hparkE,
      hhighE, _hmarkE, _hbonE, _htoE, _hbenchE, htierE, _hladE, _hnrE, htmaxE,
      _h5H, _h5D, _h6H, _h6D, _h7E, _h5f, _h6f, _hkeep, _htrits, _hopsE, _hc1E, _hpkSE,
      _hholeE, _hδs, _hctx, _hside, _hquiet⟩
  have htwo : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom htwo
  have hHighEq : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop]
    exact Nat.le_max_right _ _
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hfitC : FitsLen (s.ctrl + 2 + s.tally + 2 * s.tally) := by
    rw [show s.ctrl + 2 + s.tally + 2 * s.tally = s.ctrl + 2 + 3 * s.tally by omega]
    exact hfits.1
  have hcho : h.tmaxLt.choose = n := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact h.tmaxLt.choose_spec.symm.trans hn
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (n : Int) := by
    simpa [hcho] using htmaxE.trans h.tmaxLt.choose_spec
  let hole := climbAt base.ladder0 base.R s.ridx
  let parked := afterPark s.row (-1) s.parkAt hole r
  let xs := paintRed parked s.t0 s.tally
  have hRow : bClear.sudo_5Board_3row = embed xs := by
    simpa [xs, parked, hole] using hrowE
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, parked, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo parked s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, parked, paintRed_length, afterPark_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [h.shape.rowLen]
      omega
    have hsrc := h.openZero htwo k hk (by simpa [Nat.add_assoc] using hix)
    have hpj : s.parkAt < s.t0 + s.tally + k :=
      Nat.lt_of_lt_of_le h.parkBelow
        (Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k))
    have hhj : hole < s.t0 + s.tally + k :=
      Nat.lt_of_lt_of_le h.holeBelow
        (Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k))
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      rw [h.shape.rowLen]
      exact Nat.lt_of_lt_of_le hlt hRoom
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      hpj hhj (Or.inl (by decide)) hjLen
    have hget := paintRed_get_hi parked s.t0 s.tally (s.t0 + s.tally + k)
      (Nat.le_add_right _ _) (by rw [afterPark_length]; exact hjLen)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    simpa [xs, parked] using hget.trans (hAp.trans hsrc')
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    rw [htierE]
    exact h.shape.tierC
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + 2 + s.tally)
    s.high base.control n hm hlenE ht0E hRow
    (by
      simp [xs, parked, paintRed_length, afterPark_length, h.shape.rowLen]
      exact hRoom)
    hRed hZero hctrlN hhighE hHighEq hctrlE hRoom hFitI hfitC hFitM hmaxC
  let b' :=
    { bClear with
      sudo_5Board_3row :=
        embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
      sudo_5Board_9tally_len := Int.ofNat (2 * s.tally)
      sudo_5Board_4cost := { bClear.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + 2 + s.tally + 2 * s.tally)
        sudo_5Costs_15control_highest :=
          ((max s.high (s.t0 + 2 * s.tally - 1) : Nat) : Int)
        sudo_5Costs_9tally_max := ((max n (2 * s.tally) : Nat) : Int) } }
  have htallyW : Ecbs.tally_double bClear = .ok b' := by
    simpa [b'] using htally
  have hclear : climbClear b r s.tally = .ok bClear := by
    simpa [climbClear] using hrun
  refine ⟨b', ?_, TmaxGe.of_max h1 rfl⟩
  rw [dispatch_idle_white_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole false
    hF hwhite rfl]
  simp [progWhiteOpen, hclear, htallyW, ok_bind]

end EcbsLink2.Link2
