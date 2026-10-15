/-
  `park_rung` and `copy_band` return a board whose tally length is the one
  they were given. Each `.ok` step is a `KeepsLen` fact: unfold the emitted
  body and push the equality through every `set` and field update. The mirror
  arm of `copy_band` flips an array inside `runLoopOn`; the board is the
  `after`, and that `after` is the same home/held/moves/`note_peak` write as
  the other arm.
-/
import EcbsLink2.Link2.LadderKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `f` returns a board with the same tally length, or a trap. -/
def KeepsLen (f : Ecbs.Board → Except SudoRt.Trap Ecbs.Board) : Prop :=
  ∀ b b', f b = .ok b' → b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len

theorem keepsLen_pure : KeepsLen (fun b => pure b) := by
  intro b b' h
  dsimp only at h
  rw [pure_eq_ok] at h
  cases h
  rfl

theorem keepsLen_bind
    (f g : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hf : KeepsLen f) (hg : KeepsLen g) :
    KeepsLen (fun b => f b >>= g) := by
  intro b b' h
  dsimp only at h
  cases hf0 : f b with
  | error _ =>
    rw [hf0, error_bind] at h
    cases h
  | ok b1 =>
    rw [hf0, ok_bind] at h
    exact (hg b1 b' h).trans (hf b b1 hf0)

theorem note_peak_len : KeepsLen Ecbs.note_peak := by
  intro b b' h
  unfold Ecbs.note_peak at h
  dsimp only at h
  cases hv : Ecbs.occupied b with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok v =>
    rw [hv] at h
    simp only [ok_bind] at h
    by_cases hc : decide (v > b.sudo_5Board_4cost.sudo_5Costs_4peak) = true
    · rw [if_pos hc, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hc, pure_eq_ok] at h
      cases h
      rfl

theorem set_control_len (i c : Int) : KeepsLen (fun b => Ecbs.set_control b i c) := by
  intro b b' h
  unfold Ecbs.set_control at h
  dsimp only at h
  by_cases hge : decide (i ≥ (0 : Int)) = true
  · rw [if_pos hge, pure_eq_ok, ok_bind] at h
    cases ha : SudoRt.sudoAssert (decide (i < b.sudo_5Board_1t.sudo_4Tier_7control)) 263 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : SudoRt.putL b.sudo_5Board_3row i c with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hp] at h
        simp only [ok_bind] at h
        by_cases hhi :
            decide (i > b.sudo_5Board_4cost.sudo_5Costs_15control_highest) = true
        · rw [if_pos hhi, pure_eq_ok] at h
          cases h
          rfl
        · rw [if_neg hhi, pure_eq_ok] at h
          cases h
          rfl
  · rw [if_neg hge, pure_eq_ok, ok_bind] at h
    cases ha : SudoRt.sudoAssert false 263 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : SudoRt.putL b.sudo_5Board_3row i c with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hp] at h
        simp only [ok_bind] at h
        by_cases hhi :
            decide (i > b.sudo_5Board_4cost.sudo_5Costs_15control_highest) = true
        · rw [if_pos hhi, pure_eq_ok] at h
          cases h
          rfl
        · rw [if_neg hhi, pure_eq_ok] at h
          cases h
          rfl

/-- After `set_control`, unpark writes the row, `parked_from`, and the
    control counter. The cost projection does not depend on the new row, and
    none of the three writes is the tally length. -/
private theorem unpark_tail_len (b b' : Ecbs.Board)
    (h : (do
        let row ← SudoRt.putL b.sudo_5Board_3row b.sudo_5Board_9park_hole (0 : Int)
        let n ← SudoRt.negI (1 : Int)
        let v ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int)
        pure ({ b with
          sudo_5Board_3row := row
          sudo_5Board_11parked_from := n
          sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  cases hp : SudoRt.putL b.sudo_5Board_3row b.sudo_5Board_9park_hole (0 : Int) with
  | error _ =>
    rw [hp] at h
    simp only [error_bind] at h; cases h
  | ok row =>
    rw [hp] at h
    simp only [ok_bind] at h
    cases hn : SudoRt.negI (1 : Int) with
    | error _ =>
      rw [hn] at h
      simp only [error_bind] at h; cases h
    | ok n =>
      rw [hn] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases h
        rfl

theorem unpark_len : KeepsLen Ecbs.unpark := by
  intro b b' h
  unfold Ecbs.unpark at h
  dsimp only at h
  by_cases hlt : decide (b.sudo_5Board_11parked_from < (0 : Int)) = true
  · rw [if_pos hlt] at h
    exact keepsLen_pure b b' h
  · rw [if_neg hlt] at h
    cases ha : SudoRt.atL b.sudo_5Board_3row b.sudo_5Board_9park_hole with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok c =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hs : Ecbs.set_control b b.sudo_5Board_11parked_from c with
      | error _ =>
        rw [hs] at h
        simp only [error_bind] at h; cases h
      | ok b1 =>
        rw [hs] at h
        simp only [ok_bind] at h
        exact (unpark_tail_len b1 b' h).trans (set_control_len _ c b b1 hs)

/-- After the park assert, `set_control`, the row clear, `parked_from`, and
    the control counter. The counter read is the board `set_control` returned:
    clearing the row does not change the cost. The tally length is that
    board's length. -/
private theorem park_tail_len (b1 : Ecbs.Board) (hole colour c : Int) (b' : Ecbs.Board)
    (h : (do
        let b2 ← Ecbs.set_control b1 b1.sudo_5Board_9park_hole colour
        let row ← SudoRt.putL b2.sudo_5Board_3row hole (0 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int)
        let got ← SudoRt.atL row b2.sudo_5Board_9park_hole
        pure (got, { b2 with
          sudo_5Board_3row := row
          sudo_5Board_11parked_from := hole
          sudo_5Board_4cost :=
            { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } })) = .ok (c, b')) :
    b'.sudo_5Board_9tally_len = b1.sudo_5Board_9tally_len := by
  cases hs : Ecbs.set_control b1 b1.sudo_5Board_9park_hole colour with
  | error _ =>
    rw [hs] at h
    simp only [error_bind] at h; cases h
  | ok b2 =>
    rw [hs] at h
    simp only [ok_bind] at h
    cases hp : SudoRt.putL b2.sudo_5Board_3row hole (0 : Int) with
    | error _ =>
      rw [hp] at h
      simp only [error_bind] at h; cases h
    | ok row =>
      rw [hp] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h; cases h
      | ok v =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases hg : SudoRt.atL row b2.sudo_5Board_9park_hole with
        | error _ =>
          rw [hg] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hg] at h
          simp only [ok_bind] at h
          cases h
          exact set_control_len _ colour b1 b2 hs

theorem park_tally_len (b : Ecbs.Board) (hole c : Int) (b' : Ecbs.Board)
    (h : Ecbs.park b hole = .ok (c, b')) :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  unfold Ecbs.park at h
  dsimp only at h
  cases hu : Ecbs.unpark b with
  | error _ =>
    rw [hu] at h
    simp only [error_bind] at h; cases h
  | ok b1 =>
    rw [hu] at h
    simp only [ok_bind] at h
    have hlen1 : b1.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len :=
      unpark_len b b1 hu
    cases ha : SudoRt.atL b1.sudo_5Board_3row hole with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok colour =>
      rw [ha] at h
      simp only [ok_bind] at h
      by_cases hbeq : SudoRt.SEq.beq colour (0 : Int) = true
      · rw [hbeq] at h
        simp only [Bool.not_true] at h
        rw [if_neg Bool.false_ne_true, pure_eq_ok, ok_bind] at h
        cases hs : SudoRt.sudoAssert false 294 with
        | error _ =>
          rw [hs] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hs] at h
          simp only [ok_bind] at h
          exact (park_tail_len b1 hole colour c b' h).trans hlen1
      · have hbf : SudoRt.SEq.beq colour (0 : Int) = false := Bool.eq_false_iff.mpr hbeq
        rw [hbf] at h
        simp only [Bool.not_false, if_true] at h
        cases hp : SudoRt.atL b1.sudo_5Board_3row b1.sudo_5Board_9park_hole with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok v =>
          rw [hp] at h
          simp only [ok_bind, pure_eq_ok, ok_bind] at h
          cases hs : SudoRt.sudoAssert (SudoRt.SEq.beq v (0 : Int)) 294 with
          | error _ =>
            rw [hs] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hs] at h
            simp only [ok_bind] at h
            exact (park_tail_len b1 hole colour c b' h).trans hlen1

theorem park_rung_tally_len (r : Int) : KeepsLen (fun b => Ecbs.park_rung b r) := by
  intro b b' h
  unfold Ecbs.park_rung at h
  dsimp only at h
  cases hc : Ecbs.climb_holes b with
  | error _ =>
    rw [hc] at h
    simp only [error_bind] at h; cases h
  | ok holes =>
    rw [hc] at h
    simp only [ok_bind] at h
    cases ha : SudoRt.atL holes b.sudo_5Board_8rung_idx with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok hole =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : Ecbs.park b hole with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok p =>
        rw [hp] at h
        simp only [ok_bind] at h
        cases p with
        | mk got b1 =>
          dsimp only at h
          cases he : SudoRt.sudoAssertEq got r 305 with
          | error _ =>
            rw [he] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [he] at h
            simp only [ok_bind] at h
            cases hi : SudoRt.addI b1.sudo_5Board_8rung_idx (1 : Int) with
            | error _ =>
              rw [hi] at h
              simp only [error_bind] at h; cases h
            | ok _ =>
              rw [hi] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              exact park_tally_len b hole got b1 hp

/-- The home write, the held flag, the move counter, and `note_peak`.
    Both arms of `copy_band` end here. The array `s` is not the board. -/
private theorem band_write_len (b : Ecbs.Board) (dst : Int) (s : Array Int) (b' : Ecbs.Board)
    (h : (do
        let ix := dst
        let home ← SudoRt.putL b.sudo_5Board_4home ix s
        let b := ({ b with sudo_5Board_4home := home } : Ecbs.Board)
        let ix := dst
        let held ← SudoRt.putL b.sudo_5Board_4held ix true
        let b := ({ b with sudo_5Board_4held := held } : Ecbs.Board)
        let n ← Ecbs.npeg s
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        let b ← Ecbs.note_peak b
        pure b) = .ok b') :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  dsimp only at h
  cases hh : SudoRt.putL b.sudo_5Board_4home dst s with
  | error _ =>
    rw [hh] at h
    simp only [error_bind] at h; cases h
  | ok home =>
    rw [hh] at h
    simp only [ok_bind] at h
    cases hd : SudoRt.putL
        ({ b with sudo_5Board_4home := home } : Ecbs.Board).sudo_5Board_4held dst true with
    | error _ =>
      rw [hd] at h
      simp only [error_bind] at h; cases h
    | ok held =>
      rw [hd] at h
      simp only [ok_bind] at h
      cases hn : Ecbs.npeg s with
      | error _ =>
        rw [hn] at h
        simp only [error_bind] at h; cases h
      | ok n =>
        rw [hn] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI
            ({ { b with sudo_5Board_4home := home } with
                sudo_5Board_4held := held } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_5moves
            n with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h; cases h
        | ok mv =>
          rw [hm] at h
          simp only [ok_bind] at h
          let bN : Ecbs.Board :=
            { { { b with sudo_5Board_4home := home } with sudo_5Board_4held := held } with
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } }
          cases hk : Ecbs.note_peak bN with
          | error _ =>
            rw [hk] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hk] at h
            simp only [ok_bind, pure_eq_ok] at h
            cases h
            exact (note_peak_len bN b' hk).trans rfl

/-- Flip one coefficient. The block returns `Flow.cont` of the array, so the
    emitted match never takes `.ret`. -/
private theorem flip_step_no_ret (toV : Int) (σ : Int × Array Int) (r : Ecbs.Board) :
    (do
      let i := σ.1
      let s := σ.2
      if i > toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, s))
      else
        match ← (do
          let c ← SudoRt.atL s i
          let f ← Ecbs.flip c
          let s ← SudoRt.putL s i f
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) s)) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
        | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
        | .cont fs => do
            if i == toV then
              pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))) ≠
      .ok (SudoRt.Flow.ret r) := by
  intro h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hc : SudoRt.atL σ.2 σ.1 with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h; cases h
    | ok c =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases hf : Ecbs.flip c with
      | error _ =>
        rw [hf] at h
        simp only [error_bind] at h; cases h
      | ok f =>
        rw [hf] at h
        simp only [ok_bind] at h
        cases hp : SudoRt.putL σ.2 σ.1 f with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok s' =>
          rw [hp] at h
          simp only [ok_bind, pure_eq_ok, map_ok] at h
          by_cases hbeq : (σ.1 == toV) = true
          · rw [if_pos hbeq] at h
            cases h
          · rw [if_neg hbeq] at h
            cases hi : SudoRt.addI σ.1 (1 : Int) with
            | error _ =>
              rw [hi, error_bind] at h
              cases h
            | ok _ =>
              rw [hi, ok_bind] at h
              cases h

theorem copy_band_tally_len (dst src : Int) (mirror : Bool) :
    KeepsLen (fun b => Ecbs.copy_band b dst src mirror) := by
  intro b b' h
  unfold Ecbs.copy_band at h
  dsimp only at h
  cases hv : Ecbs.value b src with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok s =>
    rw [hv] at h
    simp only [ok_bind] at h
    cases he : Ecbs.need_empty b dst with
    | error _ =>
      rw [he] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [he] at h
      simp only [ok_bind] at h
      cases mirror with
      | false =>
        exact band_write_len b dst s b' h
      | true =>
        simp only [if_true] at h
        cases hsub : SudoRt.subI (SudoRt.listLen s) (1 : Int) with
        | error _ =>
          rw [hsub] at h
          simp only [error_bind] at h; cases h
        | ok toV =>
          rw [hsub] at h
          simp only [ok_bind] at h
          rw [except_bind_pure] at h
          apply runLoopOn_ok_inv
            (P := fun _ => True)
            (Q := fun bd : Ecbs.Board => bd.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len)
            (h := h)
          · exact trivial
          · exact fun _ _ _ _ => trivial
          · exact fun _ _ _ _ => trivial
          · intro σ r a _ hstep _
            exact absurd hstep (flip_step_no_ret toV σ r)
          · intro σ a _ ha
            exact band_write_len b dst σ.2 a ha
