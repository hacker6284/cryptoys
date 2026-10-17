/-
  The emitted `walk_fform` loop, restated so the bridge is `rfl`.
  A zero cell while the accumulator is empty only lifts the marker, as in
  `walk_chord`. The F-form cell (`frobenius_point`, `start_walk`, `fform_add`)
  is the body of the other branches. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- One cell of the emitted F-form walk. Line 788 is the trit check. -/
def fformBody (cells : Array Int) (j : Int) (b : Ecbs.Board) (live : Bool) :
    Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Bool) ((Bool × Bool) × Ecbs.Board)) :=
  do
    let c ← SudoRt.atL cells j
    let _rng ← (if (decide (c ≥ (0 : Int))) then (do
      pure (decide (c ≤ (2 : Int)))) else pure false)
    let _as ← SudoRt.sudoAssert _rng 788
    let b ← Ecbs.marker_lift b
    if live then
      do
        let b ← Ecbs.frobenius_point b
        if (!(SudoRt.SEq.beq c (0 : Int))) then
          do
            if (!(live)) then
              do
                let b ← Ecbs.start_walk b (SudoRt.SEq.beq c (2 : Int))
                pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, true))
            else
              do
                let io ← Ecbs.fform_add b (SudoRt.SEq.beq c (2 : Int))
                let ⟨ok, b⟩ := io
                if (!(ok)) then
                  do
                    let b := { b with sudo_5Board_9marker_on := false }
                    pure (SudoRt.Flow.ret (ρ := (Bool × Bool) × Ecbs.Board) ((live, false), b))
                else
                  pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))
        else
          pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))
    else
      do
        if (!(SudoRt.SEq.beq c (0 : Int))) then
          do
            if (!(live)) then
              do
                let b ← Ecbs.start_walk b (SudoRt.SEq.beq c (2 : Int))
                pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, true))
            else
              do
                let io ← Ecbs.fform_add b (SudoRt.SEq.beq c (2 : Int))
                let ⟨ok, b⟩ := io
                if (!(ok)) then
                  do
                    let b := { b with sudo_5Board_9marker_on := false }
                    pure (SudoRt.Flow.ret (ρ := (Bool × Bool) × Ecbs.Board) ((live, false), b))
                else
                  pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))
        else
          pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))

/-- The emitted F-form step: stop past the end, otherwise run one cell. -/
def fformStep (cells : Array Int) (toV : Int)
    (σ : Int × (Ecbs.Board × Bool)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Ecbs.Board × Bool)) ((Bool × Bool) × Ecbs.Board)) :=
  do
    let j := σ.1
    let b := σ.2.1
    let live := σ.2.2
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board) (j, (b, live)))
    else
      match ← fformBody cells j b live with
      | .ret r => pure (SudoRt.Flow.ret (ρ := (Bool × Bool) × Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board) (j, fs))
      | .cont fs =>
        if j == toV then
          pure (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board) (j, fs))
        else
          do
            let i' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (i', fs))

/-- The emitted F-form walk. The closing lift is the chord walk's. -/
def walkFformGo (b : Ecbs.Board) (cells : Array Int) :
    Except SudoRt.Trap ((Bool × Bool) × Ecbs.Board) :=
  do
    let live := false
    let b := chordFlag b
    let toV ← SudoRt.subI (SudoRt.listLen cells) (1 : Int)
    let fromV := (0 : Int)
    let out ← SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board) (fromV, (b, live))
      (fuelRange fromV toV) (fformStep cells toV) chordAfter (fun r => pure r)
    pure out

theorem walk_fform_eq (b : Ecbs.Board) (cells : Array Int) :
    Ecbs.walk_fform b cells = walkFformGo b cells := by
  rfl

private theorem pure_tail {S ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := ρ) (Int.ofNat i, s)) :
          Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (Int.ofNat i) (1 : Int) >>= fun i' =>
        pure (SudoRt.Flow.cont (ρ := ρ) (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s))
      else .ok (.cont (Int.ofNat (i + 1), s)) := by
  simp only [pure_eq_ok]
  exact asc_tail toN i hfit s

/-- A zero cell while the accumulator is not live. Only the marker lifts. -/
theorem fformStep_zero (cells : List Nat) (i toN : Nat) (b b1 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = 0)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hfiti : FitsLen (i + 1)) :
    fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, false)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b1, false)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b1, false))) := by
  unfold fformStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold fformBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind]
  rw [hz]
  have hge : decide (Int.ofNat 0 ≥ (0 : Int)) = true := by decide
  have hle : decide (Int.ofNat 0 ≤ (2 : Int)) = true := by decide
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  dsimp only
  have hff : ((false : Bool) = true) = False := by decide
  simp only [hff, if_false]
  rw [sEq_ofNat_zero 0]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
  exact pure_tail toN i hfiti (b1, false)

/-- A white or red cell while the accumulator is not live. `start_walk` is a
    hypothesis, so the seated marker and an already lifted marker share it. -/
theorem fformStep_fresh (cells : List Nat) (i toN c : Nat) (b b1 b2 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hstart : Ecbs.start_walk b1 (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) = .ok b2)
    (hfiti : FitsLen (i + 1)) :
    fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, false)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b2, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b2, true))) := by
  unfold fformStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold fformBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hz]
  have hge : decide (Int.ofNat c ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg c
  have hle : decide (Int.ofNat c ≤ (2 : Int)) = true := by
    rw [decide_eq_true_eq, show (2 : Int) = Int.ofNat 2 from rfl, ofNat_le_iff]
    exact hc2
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  have hff : ((false : Bool) = true) = False := by decide
  simp only [hff, if_false]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat c 0, decide_eq_false hc0]
  simp only [Bool.not_false, if_true, Bool.not_false, if_true]
  rw [hstart, ok_bind, pure_eq_ok, ok_bind]
  exact pure_tail toN i hfiti (b2, true)

/-- A zero cell while the accumulator is already live. `frobenius_point` is a
    hypothesis so the cubed board stays abstract. -/
theorem fformStep_point (cells : List Nat) (i toN : Nat) (b b1 b2 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = 0)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hfrob : Ecbs.frobenius_point b1 = .ok b2)
    (hfiti : FitsLen (i + 1)) :
    fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b2, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b2, true))) := by
  unfold fformStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold fformBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hz]
  have hge : decide (Int.ofNat 0 ≥ (0 : Int)) = true := by decide
  have hle : decide (Int.ofNat 0 ≤ (2 : Int)) = true := by decide
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  simp only [if_true]
  rw [hfrob, ok_bind]
  rw [sEq_ofNat_zero 0]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
  exact pure_tail toN i hfiti (b2, true)

/-- A live white or red cell whose `fform_add` returns the new point. -/
theorem fformStep_add (cells : List Nat) (i toN c : Nat)
    (b0 b bF bA : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hc : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_point b = .ok bF)
    (hadd : Ecbs.fform_add bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, bA))
    (hfiti : FitsLen (i + 1)) :
    fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bA, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bA, true))) := by
  unfold fformStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold fformBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hc]
  have hge : decide (Int.ofNat c ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg c
  have hle : decide (Int.ofNat c ≤ (2 : Int)) = true := by
    rw [decide_eq_true_eq, show (2 : Int) = Int.ofNat 2 from rfl, ofNat_le_iff]
    exact hc2
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  simp only [if_true]
  rw [hfrob, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat c 0, decide_eq_false hc0]
  simp only [Bool.not_false, if_true, Bool.not_true]
  rw [if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [hadd, ok_bind]
  dsimp only [Prod.fst, Prod.snd]
  simp only [Bool.not_true, if_false, pure_eq_ok, ok_bind]
  exact pure_tail toN i hfiti (bA, true)

/-- A live white or red cell whose `fform_add` returns the reroll flag.
    The step returns `(live, false)` and turns the marker off. -/
theorem fformStep_reroll (cells : List Nat) (i toN c : Nat)
    (b0 b bF bA : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hc : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_point b = .ok bF)
    (hadd : Ecbs.fform_add bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (false, bA)) :
    fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      .ok (SudoRt.Flow.ret ((true, false),
        { bA with sudo_5Board_9marker_on := false })) := by
  unfold fformStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold fformBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hc]
  have hge : decide (Int.ofNat c ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg c
  have hle : decide (Int.ofNat c ≤ (2 : Int)) = true := by
    rw [decide_eq_true_eq, show (2 : Int) = Int.ofNat 2 from rfl, ofNat_le_iff]
    exact hc2
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  simp only [if_true]
  rw [hfrob, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat c 0, decide_eq_false hc0]
  simp only [Bool.not_false, if_true, Bool.not_true]
  rw [if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [hadd, ok_bind]
  dsimp only [Prod.fst, Prod.snd]
  simp only [Bool.not_false, if_true]
  rw [pure_eq_ok, ok_bind]
  dsimp only
  rw [pure_eq_ok]

end EcbsLink2.Link2
