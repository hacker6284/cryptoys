/-
  The emitted `walk_chord` loop, restated so the bridge is `rfl`.
  Empty cells leave the homes alone. One white or red cell after them
  copies the base point. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Cells of one walk, keeping the live bit `walkGo` drops.
    `none` is an exceptional chord. -/
def walkRun (n k bench : Nat) (base : List Nat × List Nat) :
    Bool → List Nat × List Nat → List Nat → Option (Bool × (List Nat × List Nat))
  | live, acc, [] => some (live, acc)
  | live, acc, c :: cs =>
    match walkStep n k bench base live acc c with
    | none => none
    | some (live', acc') => walkRun n k bench base live' acc' cs

theorem walkRun_zeros (n k bench : Nat) (base acc : List Nat × List Nat)
    (cells : List Nat) (hz : ∀ c ∈ cells, c = 0) :
    walkRun n k bench base false acc cells = some (false, acc) := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    have hc : c = 0 := hz c (by simp)
    rw [walkRun, walkStep, hc]
    simp only [ite_false, ite_true]
    exact ih (fun x hx => hz x (List.mem_cons_of_mem _ hx))

/-- One cell of the emitted walk, the inner `do` the loop matches on. -/
def chordBody (cells : Array Int) (j : Int) (b : Ecbs.Board) (live : Bool) :
    Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Bool) ((Bool × Bool) × Ecbs.Board)) :=
  do
    let c ← SudoRt.atL cells j
    let _rng ← (if (decide (c ≥ (0 : Int))) then (do
      pure (decide (c ≤ (2 : Int)))) else pure false)
    let _as ← SudoRt.sudoAssert _rng 869
    let b ← Ecbs.marker_lift b
    if live then
      do
        let b ← Ecbs.frobenius_affine b
        if (!(SudoRt.SEq.beq c (0 : Int))) then
          do
            if (!(live)) then
              do
                let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
                let b ← Ecbs.copy_band b Ecbs.up Ecbs.base_up (SudoRt.SEq.beq c (2 : Int))
                pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, true))
            else
              do
                let io ← Ecbs.chord_add_demo b (SudoRt.SEq.beq c (2 : Int))
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
                let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
                let b ← Ecbs.copy_band b Ecbs.up Ecbs.base_up (SudoRt.SEq.beq c (2 : Int))
                pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, true))
            else
              do
                let io ← Ecbs.chord_add_demo b (SudoRt.SEq.beq c (2 : Int))
                let ⟨ok, b⟩ := io
                if (!(ok)) then
                  do
                    let b := { b with sudo_5Board_9marker_on := false }
                    pure (SudoRt.Flow.ret (ρ := (Bool × Bool) × Ecbs.Board) ((live, false), b))
                else
                  pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))
        else
          pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, live))

/-- The emitted loop step: stop past the end, otherwise run one cell and
    advance the index. -/
def chordStep (cells : Array Int) (toV : Int)
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
      match ← chordBody cells j b live with
      | .ret r => pure (SudoRt.Flow.ret (ρ := (Bool × Bool) × Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board) (j, fs))
      | .cont fs =>
        if j == toV then
          pure (SudoRt.Flow.brk (ρ := (Bool × Bool) × Ecbs.Board) (j, fs))
        else
          do
            let i' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (i', fs))

/-- The board the walk starts from: the same homes, marker flag on. -/
def chordFlag (b : Ecbs.Board) : Ecbs.Board :=
  { b with sudo_5Board_9marker_on := true }

/-- After the first lift: marker up, control advanced, flag still on. -/
def chordLift (b : Ecbs.Board) (ctrl : Nat) : Ecbs.Board :=
  { chordFlag b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { (chordFlag b).sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }

/-- The walk's result on a key that never seats the marker again. -/
def chordDone (b : Ecbs.Board) (ctrl : Nat) : Ecbs.Board :=
  { chordLift b ctrl with sudo_5Board_9marker_on := false }

/-- After the loop: lift the marker and turn it off. The ok bit is true. -/
def chordAfter (σ : Int × (Ecbs.Board × Bool)) :
    Except SudoRt.Trap ((Bool × Bool) × Ecbs.Board) :=
  do
    let b := σ.2.1
    let live := σ.2.2
    let b ← Ecbs.marker_lift b
    let b := { b with sudo_5Board_9marker_on := false }
    pure ((live, true), b)

/-- The emitted walk. The final `pure` is the generated `pure _out`. -/
def walkChordGo (b : Ecbs.Board) (cells : Array Int) :
    Except SudoRt.Trap ((Bool × Bool) × Ecbs.Board) :=
  do
    let live := false
    let b := chordFlag b
    let toV ← SudoRt.subI (SudoRt.listLen cells) (1 : Int)
    let fromV := (0 : Int)
    let out ← SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board) (fromV, (b, live))
      (fuelRange fromV toV) (chordStep cells toV) chordAfter (fun r => pure r)
    pure out

theorem walk_chord_eq (b : Ecbs.Board) (cells : Array Int) :
    Ecbs.walk_chord b cells = walkChordGo b cells := by
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

/-- A zero cell while the accumulator is not live. The lift is a hypothesis,
    so the first cell (marker seated) and a later cell (marker already up)
    share this step. -/
theorem chordStep_zero (cells : List Nat) (i toN : Nat) (b b1 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = 0)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hfiti : FitsLen (i + 1)) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, false)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b1, false)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b1, false))) := by
  unfold chordStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold chordBody
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

private theorem lift_flag (b : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1)) :
    Ecbs.marker_lift (chordFlag b) = .ok (chordLift b ctrl) := by
  have hm' : (chordFlag b).sudo_5Board_6marker = Int.ofNat marker := by
    simp [chordFlag, hm]
  have hc' : (chordFlag b).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simp [chordFlag, hc]
  simpa [chordLift, chordFlag] using marker_lift_refines (chordFlag b) marker ctrl hm' hc' hfitc

private theorem after_done (b : Ecbs.Board) (ctrl : Nat) (j : Int) :
    chordAfter (j, (chordLift b ctrl, false)) =
      .ok ((false, true), chordDone b ctrl) := by
  unfold chordAfter
  dsimp only [Prod.fst, Prod.snd]
  rw [marker_lift_down (chordLift b ctrl) (by simp [chordLift]), ok_bind]
  simp [chordDone, pure_eq_ok]

private theorem after_flag (b : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1)) (j : Int) :
    chordAfter (j, (chordFlag b, false)) =
      .ok ((false, true), chordDone b ctrl) := by
  unfold chordAfter
  dsimp only [Prod.fst, Prod.snd]
  rw [lift_flag b marker ctrl hm hc hfitc, ok_bind]
  simp [chordDone, pure_eq_ok]

/-- Every cell empty. The emitted walk returns not live and ok, the homes stay,
    and `walkRun` keeps the accumulator it was given. -/
theorem walk_chord_zeros (b : Ecbs.Board) (cells : List Nat)
    (n k bench marker ctrl : Nat) (base acc : List Nat × List Nat)
    (hz : ∀ c ∈ cells, c = 0)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (hfit : FitsLen cells.length) :
    Ecbs.walk_chord b (embed cells) =
        .ok ((false, true), chordDone b ctrl) ∧
      (chordDone b ctrl).sudo_5Board_4home = b.sudo_5Board_4home ∧
      (chordDone b ctrl).sudo_5Board_4held = b.sudo_5Board_4held ∧
      (chordDone b ctrl).sudo_5Board_9marker_on = false ∧
      (chordDone b ctrl).sudo_5Board_6marker = -1 ∧
      walkRun n k bench base false acc cells = some (false, acc) := by
  refine ⟨?_, by simp [chordDone, chordLift, chordFlag], by simp [chordDone, chordLift, chordFlag],
    by simp [chordDone], by simp [chordDone, chordLift], walkRun_zeros n k bench base acc cells hz⟩
  rw [walk_chord_eq]
  unfold walkChordGo
  rw [listLen_embed]
  cases cells with
  | nil =>
    rw [show (([] : List Nat).length) = 0 from rfl,
      show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    dsimp only
    rw [except_bind_pure]
    have hgt : (0 : Int) > (-1 : Int) := by decide
    have hstep :
        chordStep (embed ([] : List Nat)) (-1) ((0 : Int), (chordFlag b, false)) =
          .ok (SudoRt.Flow.brk ((0 : Int), (chordFlag b, false))) := by
      unfold chordStep
      dsimp only
      rw [if_pos hgt, pure_eq_ok]
    change SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board)
      ((0 : Int), (chordFlag b, false)) (fuelRange (0 : Int) (-1))
      (chordStep (embed ([] : List Nat)) (-1)) chordAfter (fun r => pure r) = _
    rw [asc_break (0 : Int) (-1) (chordFlag b, false)
      (chordStep (embed ([] : List Nat)) (-1)) chordAfter (fun r => pure r) hgt hstep]
    exact after_flag b marker ctrl hm hc hfitc 0
  | cons c cs =>
    have hpos : 0 < (c :: cs).length := by simp [Nat.succ_pos]
    rw [subI_ofNat_one (c :: cs).length hpos hfit, ok_bind]
    dsimp only
    rw [except_bind_pure]
    have hlen : (c :: cs).length - 1 = cs.length := by simp
    rw [hlen]
    let toN := cs.length
    have hle : 0 ≤ toN := Nat.zero_le _
    change SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat 0, (chordFlag b, false))
      (fuelRange (Int.ofNat 0) (Int.ofNat toN))
      (chordStep (embed (c :: cs)) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
    refine asc_goal (α := Ecbs.Board × Bool)
      (ρ := (Bool × Bool) × Ecbs.Board)
      (β := (Bool × Bool) × Ecbs.Board)
      (Inv := fun i (st : Ecbs.Board × Bool) =>
        st.2 = false ∧
        st.1 = if i = 0 then chordFlag b else chordLift b ctrl)
      (fromN := 0) (toN := toN) (s0 := (chordFlag b, false))
      (goal := .ok ((false, true), chordDone b ctrl))
      hle ⟨rfl, rfl⟩ ?hstep ?hpost
    · intro i st _hi hito hI
      have hlive : st.2 = false := hI.1
      have hbd : st.1 = if i = 0 then chordFlag b else chordLift b ctrl := hI.2
      have hiz : (c :: cs)[i]'(by simp; omega) = 0 :=
        hz _ (List.getElem_mem _)
      have hfiti : FitsLen (i + 1) :=
        FitsLen.of_le hfit (by simp; omega)
      have hlen' : (c :: cs).length = toN + 1 := by simp [toN]
      by_cases h0 : i = 0
      · have hb : st.1 = chordFlag b := by simp [hbd, h0]
        have hml := lift_flag b marker ctrl hm hc hfitc
        have hst := chordStep_zero (c :: cs) i toN st.1 (chordLift b ctrl)
          hito hlen' (by simpa [hb] using hiz) (by rw [hb]; exact hml) hfiti
        refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
        · exact ⟨rfl, by simp⟩
        · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
          rw [hs]
          simpa [h0, hb] using hst
      · have hb : st.1 = chordLift b ctrl := by
          simp [hbd, h0]
        have hml : Ecbs.marker_lift st.1 = .ok (chordLift b ctrl) := by
          rw [hb]
          exact marker_lift_down (chordLift b ctrl) (by simp [chordLift])
        have hst := chordStep_zero (c :: cs) i toN st.1 (chordLift b ctrl)
          hito hlen' (by simpa [hb] using hiz) hml hfiti
        refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
        · exact ⟨rfl, by simp⟩
        · have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
          rw [hs]
          simpa [hb] using hst
    · intro st hI
      have hb : st.1 = chordLift b ctrl := by
        have hne : ¬ (toN + 1) = 0 := by omega
        simpa [hne] using hI.2
      have hlive : st.2 = false := hI.1
      have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
      rw [hs]
      exact after_done b ctrl (Int.ofNat toN)

private theorem bind_copy_cont (m1 : Except SudoRt.Trap Ecbs.Board)
    (m2 : Ecbs.Board → Except SudoRt.Trap Ecbs.Board) (b2 : Ecbs.Board)
    (hm : (m1 >>= m2) = .ok b2) :
    (m1 >>= fun a => m2 a >>= fun b =>
        pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b, true))) =
      (pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b2, true)) :
        Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Bool) ((Bool × Bool) × Ecbs.Board))) := by
  cases m1 with
  | error _ =>
    simp [error_bind] at hm
  | ok a =>
    simp only [ok_bind] at hm ⊢
    cases h2 : m2 a with
    | error _ =>
      simp [h2, error_bind] at hm
    | ok _ =>
      simp [h2, ok_bind, pure_eq_ok] at hm ⊢
      cases hm
      rfl

/-- A white or red cell while the accumulator is not live. The lift and the
    two copies are hypotheses, so a seated marker and an already lifted marker
    share the step. -/
theorem chordStep_fresh (cells : List Nat) (i toN c : Nat) (b b1 b2 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hcopy :
      (do
          let board ← Ecbs.copy_band b1 Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up
            (SudoRt.SEq.beq (Int.ofNat c) (2 : Int))) = .ok b2)
    (hfiti : FitsLen (i + 1)) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, false)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b2, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b2, true))) := by
  unfold chordStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold chordBody
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
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  rw [bind_copy_cont
      (Ecbs.copy_band b1 Ecbs.across Ecbs.base_across false)
      (fun board => Ecbs.copy_band board Ecbs.up Ecbs.base_up
        (SudoRt.SEq.beq (Int.ofNat c) (Int.ofNat 2))) b2 hcopy,
    pure_eq_ok, ok_bind]
  exact pure_tail toN i hfiti (b2, true)

/-- A zero cell while the accumulator is already live. `frobenius_affine` is a
    hypothesis so the cube board stays abstract. -/
theorem chordStep_cube (cells : List Nat) (i toN : Nat) (b b1 b2 : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hz : cells[i]'(by omega) = 0)
    (hml : Ecbs.marker_lift b = .ok b1)
    (hfrob : Ecbs.frobenius_affine b1 = .ok b2)
    (hfiti : FitsLen (i + 1)) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b2, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b2, true))) := by
  unfold chordStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold chordBody
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

/-- Empty cells, then one white cell: the accumulator becomes the base point. -/
theorem walkRun_open_white (n k bench : Nat) (base acc : List Nat × List Nat)
    (zs : List Nat) (hz : ∀ c ∈ zs, c = 0) :
    walkRun n k bench base false acc (zs ++ [1]) = some (true, base) := by
  induction zs generalizing acc with
  | nil =>
    unfold walkRun
    simp [walkStep]
    unfold walkRun
    rfl
  | cons c cs ih =>
    have hc : c = 0 := hz c (by simp)
    unfold walkRun
    simp only [walkStep, hc, ite_false, ite_true]
    exact ih acc (fun x hx => hz x (List.mem_cons_of_mem _ hx))

private theorem lift_held (b : Ecbs.Board) (ctrl : Nat) :
    (chordLift b ctrl).sudo_5Board_4held = b.sudo_5Board_4held := by
  simp [chordLift, chordFlag]

private theorem lift_home (b : Ecbs.Board) (ctrl : Nat) :
    (chordLift b ctrl).sudo_5Board_4home = b.sudo_5Board_4home := by
  simp [chordLift, chordFlag]

private theorem after_live (b : Ecbs.Board) (j : Int)
    (hm : b.sudo_5Board_6marker = -1) :
    chordAfter (j, (b, true)) =
      .ok ((true, true), { b with sudo_5Board_9marker_on := false }) := by
  unfold chordAfter
  dsimp only [Prod.fst, Prod.snd]
  rw [marker_lift_down b hm, ok_bind]
  simp [pure_eq_ok]

/-- Zeros, then one white cell. The emitted walk copies the base point into
    across and up, returns live and ok, and `walkRun` is that base point. -/
theorem walk_chord_white_open (b : Ecbs.Board) (zs : List Nat) (x y : List Nat)
    (n k bench moves peak marker ctrl : Nat) (acc : List Nat × List Nat)
    (hz : ∀ c ∈ zs, c = 0)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (hfit : FitsLen (zs.length + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ (b2 bF : Ecbs.Board),
      Ecbs.walk_chord b (embed (zs ++ [1])) = .ok ((true, true), bF) ∧
      bF = { b2 with sudo_5Board_9marker_on := false } ∧
      (∀ h : 0 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[1] = embed y) ∧
      bF.sudo_5Board_9marker_on = false ∧
      walkRun n k bench (x, y) false acc (zs ++ [1]) = some (true, (x, y)) := by
  have hheldL := lift_held b ctrl
  have hhomeL := lift_home b ctrl
  have hszHL : (chordLift b ctrl).sudo_5Board_4home.size = 8 := by rw [hhomeL, hszH]
  have hszDL : (chordLift b ctrl).sudo_5Board_4held.size = 8 := by rw [hheldL, hszD]
  have hnL : (chordLift b ctrl).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [chordLift, chordFlag, hn]
  have hmovesL : (chordLift b ctrl).sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [chordLift, chordFlag, hmoves]
  have hpeakL : (chordLift b ctrl).sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [chordLift, chordFlag, hpeak]
  have h0L : (chordLift b ctrl).sudo_5Board_4held[0]'(by rw [hszDL]; decide) = false := by
    simpa [hheldL] using h0
  have h1L : (chordLift b ctrl).sudo_5Board_4held[1]'(by rw [hszDL]; decide) = false := by
    simpa [hheldL] using h1
  have h3tL : (chordLift b ctrl).sudo_5Board_4held[3]'(by rw [hszDL]; decide) = true := by
    simpa [hheldL] using h3t
  have h3aL : (chordLift b ctrl).sudo_5Board_4home[3]'(by rw [hszHL]; decide) = embed x := by
    simpa [hhomeL] using h3a
  have h4tL : (chordLift b ctrl).sudo_5Board_4held[4]'(by rw [hszDL]; decide) = true := by
    simpa [hheldL] using h4t
  have h4aL : (chordLift b ctrl).sudo_5Board_4home[4]'(by rw [hszHL]; decide) = embed y := by
    simpa [hhomeL] using h4a
  obtain ⟨b2, _mv2, _pk2, hcopy, _hszH2, _hszD2, hx0, hy1, _, _, _, _, _, _, _, hmarkB⟩ :=
    walk_copy_white (chordLift b ctrl) x y n moves peak hszHL hszDL hx hy hf hfitx hfity
      hnL hmovesL hpeakL h0L h1L h3tL h3aL h4tL h4aL
  have hmark2 : b2.sudo_5Board_6marker = -1 := by
    simpa [chordLift] using hmarkB
  let bF := { b2 with sudo_5Board_9marker_on := false }
  refine ⟨b2, bF, ?_, rfl, ?_, ?_, rfl, walkRun_open_white n k bench (x, y) acc zs hz⟩
  · have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by
      rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 1 2]
      decide
    have hcopyB :
        (do
            let board ← Ecbs.copy_band (chordLift b ctrl) Ecbs.across Ecbs.base_across false
            Ecbs.copy_band board Ecbs.up Ecbs.base_up
              (SudoRt.SEq.beq (Int.ofNat 1) (2 : Int))) = .ok b2 := by
      simpa [hbeq] using hcopy
    rw [walk_chord_eq]
    unfold walkChordGo
    rw [listLen_embed]
    have hpos : 0 < (zs ++ [1]).length := by simp
    have hfitL : FitsLen (zs ++ [1]).length := by simpa [List.length_append] using hfit
    have hsub := subI_ofNat_one (zs ++ [1]).length hpos hfitL
    rw [hsub, ok_bind]
    dsimp only
    rw [except_bind_pure]
    have hlen : (zs ++ [1]).length - 1 = zs.length := by simp
    rw [hlen]
    let toN := zs.length
    change SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat 0, (chordFlag b, false))
      (fuelRange (Int.ofNat 0) (Int.ofNat toN))
      (chordStep (embed (zs ++ [1])) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
    refine asc_goal (α := Ecbs.Board × Bool)
      (ρ := (Bool × Bool) × Ecbs.Board)
      (β := (Bool × Bool) × Ecbs.Board)
      (Inv := fun i (st : Ecbs.Board × Bool) =>
        if i = toN + 1 then st = (b2, true)
        else st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl)
      (fromN := 0) (toN := toN) (s0 := (chordFlag b, false))
      (goal := .ok ((true, true), bF))
      (Nat.zero_le _) (by simp) ?hstep ?hpost
    · intro i st _hi hito hI
      have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by simp [toN]; omega)
      have hlen' : (zs ++ [1]).length = toN + 1 := by simp [toN]
      by_cases hlast : i = toN
      · have hI0 : st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl := by
          have hne : ¬ i = toN + 1 := by omega
          simpa [hne] using hI
        have hcell : (zs ++ [1])[i]'(by simp [toN]; omega) = 1 := by
          have hiL : zs.length ≤ i := by simp [toN, hlast]
          rw [List.getElem_append_right hiL]
          have h0i : i - zs.length = 0 := by simp [toN, hlast]
          simp [h0i]
        by_cases h0i : i = 0
        · have hb : st.1 = chordFlag b := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml := lift_flag b marker ctrl hm hc hfitc
          have hst := chordStep_fresh (zs ++ [1]) i toN 1 st.1 (chordLift b ctrl) b2
            hito hlen' (by simpa [hb] using hcell) (by decide) (by decide)
            (by rw [hb]; exact hml) hcopyB hfiti
          refine ⟨(b2, true), ?_, ?_⟩
          · have hnext : i + 1 = toN + 1 := by omega
            simp [hnext]
          · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hlast, hb] using hst
        · have hb : st.1 = chordLift b ctrl := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml : Ecbs.marker_lift st.1 = .ok (chordLift b ctrl) := by
            rw [hb]
            exact marker_lift_down (chordLift b ctrl) (by simp [chordLift])
          have hst := chordStep_fresh (zs ++ [1]) i toN 1 st.1 (chordLift b ctrl) b2
            hito hlen' (by simpa [hb] using hcell) (by decide) (by decide)
            hml hcopyB hfiti
          refine ⟨(b2, true), ?_, ?_⟩
          · have hnext : i + 1 = toN + 1 := by omega
            simp [hnext]
          · have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hlast, hb] using hst
      · have hI0 : st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl := by
          have hne : ¬ i = toN + 1 := by omega
          simpa [hne] using hI
        have hcell : (zs ++ [1])[i]'(by simp [toN]; omega) = 0 := by
          have hiL : i < zs.length := by
            have hlt : i < toN := Nat.lt_of_le_of_ne hito hlast
            simpa [toN] using hlt
          rw [List.getElem_append_left hiL]
          exact hz _ (List.getElem_mem _)
        by_cases h0i : i = 0
        · have hb : st.1 = chordFlag b := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml := lift_flag b marker ctrl hm hc hfitc
          have hst := chordStep_zero (zs ++ [1]) i toN st.1 (chordLift b ctrl)
            (by omega) hlen' (by simpa [hb] using hcell) (by rw [hb]; exact hml) hfiti
          refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
          · have hneL : ¬ i + 1 = toN + 1 := by omega
            have hne0 : ¬ i + 1 = 0 := by omega
            simp [hneL, hne0]
          · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
            rw [hs]
            simpa [h0i, hb, hlast] using hst
        · have hb : st.1 = chordLift b ctrl := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml : Ecbs.marker_lift st.1 = .ok (chordLift b ctrl) := by
            rw [hb]
            exact marker_lift_down (chordLift b ctrl) (by simp [chordLift])
          have hst := chordStep_zero (zs ++ [1]) i toN st.1 (chordLift b ctrl)
            (by omega) hlen' (by simpa [hb] using hcell) hml hfiti
          refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
          · have hneL : ¬ i + 1 = toN + 1 := by omega
            have hne0 : ¬ i + 1 = 0 := by omega
            simp [hneL, hne0]
          · have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hb, hlast] using hst
    · intro st hI
      have hs : st = (b2, true) := by simpa using hI
      rw [hs]
      simpa [bF] using after_live b2 (Int.ofNat toN) hmark2
  · intro h
    simpa [bF] using hx0 _
  · intro h
    simpa [bF] using hy1 _

/-- Empty cells, then one red cell: the accumulator is the base point with up mirrored. -/
theorem walkRun_open_red (n k bench : Nat) (x y : List Nat) (acc : List Nat × List Nat)
    (zs : List Nat) (hz : ∀ c ∈ zs, c = 0) :
    walkRun n k bench (x, y) false acc (zs ++ [2]) =
      some (true, (x, mirrorTrits y)) := by
  induction zs generalizing acc with
  | nil =>
    unfold walkRun
    simp [walkStep]
    unfold walkRun
    rfl
  | cons c cs ih =>
    have hc : c = 0 := hz c (by simp)
    unfold walkRun
    simp only [walkStep, hc, ite_false, ite_true]
    exact ih acc (fun z hz' => hz z (List.mem_cons_of_mem _ hz'))

/-- Zeros, then one red cell. Across receives the base across and up receives
    the negated base up. `walkRun` is that point. -/
theorem walk_chord_red_open (b : Ecbs.Board) (zs : List Nat) (x y : List Nat)
    (n k bench moves peak marker ctrl : Nat) (acc : List Nat × List Nat)
    (hz : ∀ c ∈ zs, c = 0)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n) (hpos : 0 < n) (hyt : allTritList y)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (hfit : FitsLen (zs.length + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ (b2 bF : Ecbs.Board),
      Ecbs.walk_chord b (embed (zs ++ [2])) = .ok ((true, true), bF) ∧
      bF = { b2 with sudo_5Board_9marker_on := false } ∧
      (∀ h : 0 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      bF.sudo_5Board_9marker_on = false ∧
      walkRun n k bench (x, y) false acc (zs ++ [2]) =
        some (true, (x, mirrorTrits y)) := by
  have hheldL := lift_held b ctrl
  have hhomeL := lift_home b ctrl
  have hszHL : (chordLift b ctrl).sudo_5Board_4home.size = 8 := by rw [hhomeL, hszH]
  have hszDL : (chordLift b ctrl).sudo_5Board_4held.size = 8 := by rw [hheldL, hszD]
  have hnL : (chordLift b ctrl).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [chordLift, chordFlag, hn]
  have hmovesL : (chordLift b ctrl).sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [chordLift, chordFlag, hmoves]
  have hpeakL : (chordLift b ctrl).sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [chordLift, chordFlag, hpeak]
  have h0L : (chordLift b ctrl).sudo_5Board_4held[0]'(by rw [hszDL]; decide) = false := by
    simpa [hheldL] using h0
  have h1L : (chordLift b ctrl).sudo_5Board_4held[1]'(by rw [hszDL]; decide) = false := by
    simpa [hheldL] using h1
  have h3tL : (chordLift b ctrl).sudo_5Board_4held[3]'(by rw [hszDL]; decide) = true := by
    simpa [hheldL] using h3t
  have h3aL : (chordLift b ctrl).sudo_5Board_4home[3]'(by rw [hszHL]; decide) = embed x := by
    simpa [hhomeL] using h3a
  have h4tL : (chordLift b ctrl).sudo_5Board_4held[4]'(by rw [hszDL]; decide) = true := by
    simpa [hheldL] using h4t
  have h4aL : (chordLift b ctrl).sudo_5Board_4home[4]'(by rw [hszHL]; decide) = embed y := by
    simpa [hhomeL] using h4a
  obtain ⟨b2, _mv2, _pk2, hcopy, hx0, hy1, _, _, _, hmarkB⟩ :=
    walk_copy_red (chordLift b ctrl) x y n moves peak hszHL hszDL hx hy hpos hyt hf
      hfitx hfity hnL hmovesL hpeakL h0L h1L h3tL h3aL h4tL h4aL
  have hmark2 : b2.sudo_5Board_6marker = -1 := by
    simpa [chordLift] using hmarkB
  let bF := { b2 with sudo_5Board_9marker_on := false }
  refine ⟨b2, bF, ?_, rfl, ?_, ?_, rfl,
    walkRun_open_red n k bench x y acc zs hz⟩
  · have hbeq : SudoRt.SEq.beq (Int.ofNat 2) (2 : Int) = true := by
      rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 2 2]
      decide
    have hcopyB :
        (do
            let board ← Ecbs.copy_band (chordLift b ctrl) Ecbs.across Ecbs.base_across false
            Ecbs.copy_band board Ecbs.up Ecbs.base_up
              (SudoRt.SEq.beq (Int.ofNat 2) (2 : Int))) = .ok b2 := by
      rw [hbeq]
      exact hcopy
    rw [walk_chord_eq]
    unfold walkChordGo
    rw [listLen_embed]
    have hposL : 0 < (zs ++ [2]).length := by simp
    have hfitL : FitsLen (zs ++ [2]).length := by simpa [List.length_append] using hfit
    have hsub := subI_ofNat_one (zs ++ [2]).length hposL hfitL
    rw [hsub, ok_bind]
    dsimp only
    rw [except_bind_pure]
    have hlen : (zs ++ [2]).length - 1 = zs.length := by simp
    rw [hlen]
    let toN := zs.length
    change SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat 0, (chordFlag b, false))
      (fuelRange (Int.ofNat 0) (Int.ofNat toN))
      (chordStep (embed (zs ++ [2])) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
    refine asc_goal (α := Ecbs.Board × Bool)
      (ρ := (Bool × Bool) × Ecbs.Board)
      (β := (Bool × Bool) × Ecbs.Board)
      (Inv := fun i (st : Ecbs.Board × Bool) =>
        if i = toN + 1 then st = (b2, true)
        else st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl)
      (fromN := 0) (toN := toN) (s0 := (chordFlag b, false))
      (goal := .ok ((true, true), bF))
      (Nat.zero_le _) (by simp) ?hstep ?hpost
    · intro i st _hi hito hI
      have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by simp [toN]; omega)
      have hlen' : (zs ++ [2]).length = toN + 1 := by simp [toN]
      by_cases hlast : i = toN
      · have hI0 : st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl := by
          have hne : ¬ i = toN + 1 := by omega
          simpa [hne] using hI
        have hcell : (zs ++ [2])[i]'(by simp [toN]; omega) = 2 := by
          have hiL : zs.length ≤ i := by simp [toN, hlast]
          rw [List.getElem_append_right hiL]
          have h0i : i - zs.length = 0 := by simp [toN, hlast]
          simp [h0i]
        by_cases h0i : i = 0
        · have hb : st.1 = chordFlag b := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml := lift_flag b marker ctrl hm hc hfitc
          have hst := chordStep_fresh (zs ++ [2]) i toN 2 st.1 (chordLift b ctrl) b2
            hito hlen' (by simpa [hb] using hcell) (by decide) (by decide)
            (by rw [hb]; exact hml) hcopyB hfiti
          refine ⟨(b2, true), ?_, ?_⟩
          · have hnext : i + 1 = toN + 1 := by omega
            simp [hnext]
          · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hlast, hb] using hst
        · have hb : st.1 = chordLift b ctrl := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml : Ecbs.marker_lift st.1 = .ok (chordLift b ctrl) := by
            rw [hb]
            exact marker_lift_down (chordLift b ctrl) (by simp [chordLift])
          have hst := chordStep_fresh (zs ++ [2]) i toN 2 st.1 (chordLift b ctrl) b2
            hito hlen' (by simpa [hb] using hcell) (by decide) (by decide)
            hml hcopyB hfiti
          refine ⟨(b2, true), ?_, ?_⟩
          · have hnext : i + 1 = toN + 1 := by omega
            simp [hnext]
          · have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hlast, hb] using hst
      · have hI0 : st.2 = false ∧ st.1 = if i = 0 then chordFlag b else chordLift b ctrl := by
          have hne : ¬ i = toN + 1 := by omega
          simpa [hne] using hI
        have hcell : (zs ++ [2])[i]'(by simp [toN]; omega) = 0 := by
          have hiL : i < zs.length := by
            have hlt : i < toN := Nat.lt_of_le_of_ne hito hlast
            simpa [toN] using hlt
          rw [List.getElem_append_left hiL]
          exact hz _ (List.getElem_mem _)
        by_cases h0i : i = 0
        · have hb : st.1 = chordFlag b := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml := lift_flag b marker ctrl hm hc hfitc
          have hst := chordStep_zero (zs ++ [2]) i toN st.1 (chordLift b ctrl)
            (by omega) hlen' (by simpa [hb] using hcell) (by rw [hb]; exact hml) hfiti
          refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
          · have hneL : ¬ i + 1 = toN + 1 := by omega
            have hne0 : ¬ i + 1 = 0 := by omega
            simp [hneL, hne0]
          · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
            rw [hs]
            simpa [h0i, hb, hlast] using hst
        · have hb : st.1 = chordLift b ctrl := by simp [hI0.2, h0i]
          have hlive : st.2 = false := hI0.1
          have hml : Ecbs.marker_lift st.1 = .ok (chordLift b ctrl) := by
            rw [hb]
            exact marker_lift_down (chordLift b ctrl) (by simp [chordLift])
          have hst := chordStep_zero (zs ++ [2]) i toN st.1 (chordLift b ctrl)
            (by omega) hlen' (by simpa [hb] using hcell) hml hfiti
          refine ⟨(chordLift b ctrl, false), ?_, ?_⟩
          · have hneL : ¬ i + 1 = toN + 1 := by omega
            have hne0 : ¬ i + 1 = 0 := by omega
            simp [hneL, hne0]
          · have hs : st = (chordLift b ctrl, false) := Prod.ext hb hlive
            rw [hs]
            simpa [hb, hlast] using hst
    · intro st hI
      have hs : st = (b2, true) := by simpa using hI
      rw [hs]
      simpa [bF] using after_live b2 (Int.ofNat toN) hmark2
  · intro h
    simpa [bF] using hx0 _
  · intro h
    simpa [bF] using hy1 _

end EcbsLink2.Link2
