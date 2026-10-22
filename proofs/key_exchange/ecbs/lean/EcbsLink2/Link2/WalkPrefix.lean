/-
  The part of `walk_chord` before the first live cell, when the marker is
  already `-1`. Empty cells leave the flagged board alone. The first nonzero
  cell copies the base point and does not move control. A later live cell is
  what seats the marker. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkInd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Run the ascending loop from `fromN` up to, but not through, index `k`.
    Every one of those steps continues. The loop from `fromN` is the loop from `k`. -/
theorem asc_resume {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (Inv : Nat → α → Prop)
    (fromN k toN : Nat) (s0 : α)
    (hfrom : fromN ≤ k) (hk : k ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i < k → Inv i s →
      ∃ s', Inv (i + 1) s' ∧
        step (Int.ofNat i, s) =
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s'))) :
    ∃ sK, Inv k sK ∧
      SudoRt.runLoopOn (Int.ofNat fromN, s0)
          (fuelRange (Int.ofNat fromN) (Int.ofNat toN)) step after onRet =
        SudoRt.runLoopOn (Int.ofNat k, sK)
          (fuelRange (Int.ofNat k) (Int.ofNat toN)) step after onRet := by
  obtain ⟨d, hd⟩ : ∃ d, k - fromN = d := ⟨_, rfl⟩
  induction d generalizing fromN s0 with
  | zero =>
    have heq : fromN = k := by omega
    subst heq
    exact ⟨s0, h0, rfl⟩
  | succ d ih =>
    have hlt : fromN < k := by omega
    have hleN : fromN ≤ toN := by omega
    have hle1 : fromN + 1 ≤ toN := by omega
    obtain ⟨s', hs', hst⟩ := hstep fromN s0 (Nat.le_refl _) hlt h0
    have hfuel :
        fuelRange (Int.ofNat fromN) (Int.ofNat toN) =
          fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le hleN, fuelRange_le hle1]
      omega
    rw [hfuel, runLoopOn_succ, hst]
    exact ih (fromN + 1) s' (by omega) hs'
      (fun i s hi1 hi2 hI => hstep i s (Nat.le_trans (Nat.le_succ fromN) hi1) hi2 hI)
      (by omega)

private theorem after_down (b : Ecbs.Board) (j : Int)
    (hm : b.sudo_5Board_6marker = -1) :
    chordAfter (j, (chordFlag b, false)) =
      .ok ((false, true), { b with sudo_5Board_9marker_on := false }) := by
  unfold chordAfter
  dsimp only
  have hm' : (chordFlag b).sudo_5Board_6marker = -1 := by simp [chordFlag, hm]
  rw [marker_lift_down (chordFlag b) hm', ok_bind]
  simp [pure_eq_ok, chordFlag]

private theorem flag_marker (b : Ecbs.Board) (hm : b.sudo_5Board_6marker = -1) :
    Ecbs.marker_lift (chordFlag b) = .ok (chordFlag b) :=
  marker_lift_down (chordFlag b) (by simp [chordFlag, hm])

/-- Every cell empty, marker already `-1`. The lift is the board itself, so
    control does not move. The homes stay, the result is not live, and `walkRun`
    keeps the accumulator. -/
theorem walk_chord_zeros_down (b : Ecbs.Board) (cells : List Nat)
    (n k bench : Nat) (base acc : List Nat × List Nat)
    (hz : ∀ c ∈ cells, c = 0)
    (hm : b.sudo_5Board_6marker = -1)
    (hfit : FitsLen cells.length) :
    Ecbs.walk_chord b (embed cells) =
        .ok ((false, true), { b with sudo_5Board_9marker_on := false }) ∧
      walkRun n k bench base false acc cells = some (false, acc) ∧
      walkGo n k bench base false acc cells = some acc := by
  refine ⟨?_, walkRun_zeros n k bench base acc cells hz,
    walkRun_walkGo n k bench base false acc cells false acc
      (walkRun_zeros n k bench base acc cells hz)⟩
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
    exact after_down b 0 hm
  | cons c cs =>
    have hpos : 0 < (c :: cs).length := by simp
    rw [subI_ofNat_one (c :: cs).length hpos hfit, ok_bind]
    dsimp only
    rw [except_bind_pure]
    have hlen : (c :: cs).length - 1 = cs.length := by simp
    rw [hlen]
    let toN := cs.length
    change SudoRt.runLoopOn (ρ := (Bool × Bool) × Ecbs.Board)
      (Int.ofNat 0, (chordFlag b, false))
      (fuelRange (Int.ofNat 0) (Int.ofNat toN))
      (chordStep (embed (c :: cs)) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
    refine asc_goal (α := Ecbs.Board × Bool)
      (ρ := (Bool × Bool) × Ecbs.Board)
      (β := (Bool × Bool) × Ecbs.Board)
      (Inv := fun _ (st : Ecbs.Board × Bool) =>
        st.2 = false ∧ st.1 = chordFlag b)
      (fromN := 0) (toN := toN) (s0 := (chordFlag b, false))
      (goal := .ok ((false, true), { b with sudo_5Board_9marker_on := false }))
      (Nat.zero_le _) ⟨rfl, rfl⟩ ?hstep ?hpost
    · intro i st _hi hito hI
      have hlive : st.2 = false := hI.1
      have hb : st.1 = chordFlag b := hI.2
      have hiz : (c :: cs)[i]'(by simp; omega) = 0 := hz _ (List.getElem_mem _)
      have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by simp; omega)
      have hlen' : (c :: cs).length = toN + 1 := by simp [toN]
      have hml := flag_marker b hm
      have hst := chordStep_zero (c :: cs) i toN st.1 (chordFlag b)
        hito hlen' (by simpa [hb] using hiz) (by rw [hb]; exact hml) hfiti
      refine ⟨(chordFlag b, false), ?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · have hs : st = (chordFlag b, false) := Prod.ext hb hlive
        rw [hs]
        simpa [hb] using hst
    · intro st hI
      have hs : st = (chordFlag b, false) := Prod.ext hI.2 hI.1
      rw [hs]
      exact after_down b (Int.ofNat toN) hm

/-- A cell `c ≤ 2` that is not zero is white or red. -/
theorem colour_of_cell (c : Nat) (hc0 : c ≠ 0) (hc2 : c ≤ 2) : c = 1 ∨ c = 2 := by
  omega

/-- Once the accumulator is live, a successful cell leaves it live. -/
theorem walkStep_stays_live (n k bench : Nat) (base acc q : List Nat × List Nat)
    (c : Nat) (live : Bool)
    (h : walkStep n k bench base true acc c = some (live, q)) : live = true := by
  unfold walkStep at h
  simp only [if_true] at h
  by_cases hz : c = 0
  · rw [if_pos hz] at h
    cases h
    rfl
  · rw [if_neg hz] at h
    by_cases hbad : c ≠ 1 ∧ c ≠ 2
    · rw [if_pos hbad] at h
      cases h
    · rw [if_neg hbad] at h
      split at h
      · cases h
      · cases h
        rfl

/-- A live run that returns stays live. -/
theorem walkRun_stays_live (n k bench : Nat) (base acc p : List Nat × List Nat)
    (cells : List Nat) (live : Bool)
    (h : walkRun n k bench base true acc cells = some (live, p)) : live = true := by
  induction cells generalizing acc with
  | nil =>
    simp only [walkRun] at h
    cases h
    rfl
  | cons c cs ih =>
    simp only [walkRun] at h
    cases hstep : walkStep n k bench base true acc c with
    | none => simp [hstep] at h
    | some q =>
      simp only [hstep] at h
      have hlive := walkStep_stays_live n k bench base acc q.2 c q.1 hstep
      rw [hlive] at h
      exact ih q.2 h

/-- `walkRun` stayed not live only if every cell was empty, and the accumulator
    is the one the walk started with. -/
theorem walkRun_false_zeros (n k bench : Nat) (base acc p : List Nat × List Nat)
    (cells : List Nat)
    (h : walkRun n k bench base false acc cells = some (false, p))
    (hc : ∀ c ∈ cells, c ≤ 2) :
    (∀ c ∈ cells, c = 0) ∧ p = acc := by
  induction cells generalizing acc with
  | nil =>
    simp only [walkRun] at h
    cases h
    exact ⟨fun _ hmem => by simp at hmem, rfl⟩
  | cons c cs ih =>
    simp only [walkRun] at h
    cases hstep : walkStep n k bench base false acc c with
    | none => simp [hstep] at h
    | some q =>
      simp only [hstep] at h
      have hc2 : c ≤ 2 := hc c (List.mem_cons_self _ _)
      by_cases hhead : c = 0
      · have hzero : walkStep n k bench base false acc 0 = some (false, acc) := by
          unfold walkStep
          simp
        rw [hhead] at hstep
        have hq : q = (false, acc) :=
          Option.some.inj (hstep.symm.trans hzero)
        rw [hq] at h
        have htail := ih acc h (fun x hx => hc x (List.mem_cons_of_mem _ hx))
        exact ⟨fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hhead
          · exact htail.1 x hx, htail.2⟩
      · have hcol : c = 1 ∨ c = 2 := colour_of_cell c hhead hc2
        rcases hcol with rfl | rfl
        · rw [walkStep_fresh_white] at hstep
          cases hstep
          have hbad := walkRun_stays_live n k bench base base p cs false h
          cases hbad
        · rw [walkStep_fresh_red] at hstep
          cases hstep
          have hbad := walkRun_stays_live n k bench base (base.1, mirrorTrits base.2) p cs false h
          cases hbad

private theorem after_live_down (b : Ecbs.Board) (j : Int)
    (hm : b.sudo_5Board_6marker = -1) :
    chordAfter (j, (b, true)) =
      .ok ((true, true), { b with sudo_5Board_9marker_on := false }) := by
  unfold chordAfter
  dsimp only
  rw [marker_lift_down b hm, ok_bind]
  simp [pure_eq_ok]

/-- Empty cells, then one white cell, marker already `-1`. The lift does not
    move control. Across and up become the base point, and `walkRun` is that point. -/
theorem walk_chord_white_down (b : Ecbs.Board) (zs : List Nat) (x y : List Nat)
    (n k bench moves peak : Nat) (acc : List Nat × List Nat)
    (hz : ∀ c ∈ zs, c = 0)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = -1)
    (hfit : FitsLen (zs.length + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 : Ecbs.Board,
      Ecbs.walk_chord b (embed (zs ++ [1])) =
        .ok ((true, true), { b2 with sudo_5Board_9marker_on := false }) ∧
      (∀ h : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[1] = embed y) ∧
      b2.sudo_5Board_6marker = -1 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      walkRun n k bench (x, y) false acc (zs ++ [1]) = some (true, (x, y)) ∧
      walkGo n k bench (x, y) false acc (zs ++ [1]) = some (x, y) := by
  let bf := chordFlag b
  have hszHF : bf.sudo_5Board_4home.size = 8 := by simp [bf, chordFlag, hszH]
  have hszDF : bf.sudo_5Board_4held.size = 8 := by simp [bf, chordFlag, hszD]
  have hnF : bf.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [bf, chordFlag, hn]
  have hmovesF : bf.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [bf, chordFlag, hmoves]
  have hpeakF : bf.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bf, chordFlag, hpeak]
  have h0F : bf.sudo_5Board_4held[0]'(by rw [hszDF]; decide) = false := by
    simpa [bf, chordFlag] using h0
  have h1F : bf.sudo_5Board_4held[1]'(by rw [hszDF]; decide) = false := by
    simpa [bf, chordFlag] using h1
  have h3tF : bf.sudo_5Board_4held[3]'(by rw [hszDF]; decide) = true := by
    simpa [bf, chordFlag] using h3t
  have h3aF : bf.sudo_5Board_4home[3]'(by rw [hszHF]; decide) = embed x := by
    simpa [bf, chordFlag] using h3a
  have h4tF : bf.sudo_5Board_4held[4]'(by rw [hszDF]; decide) = true := by
    simpa [bf, chordFlag] using h4t
  have h4aF : bf.sudo_5Board_4home[4]'(by rw [hszHF]; decide) = embed y := by
    simpa [bf, chordFlag] using h4a
  obtain ⟨b2, _mv, _pk, hcopy, _, _, hx0, hy1, _, _, _, _, _, _, _, hmark,
      hst, hho, hctrl, hsl, _, _⟩ :=
    walk_copy_white bf x y n moves peak hszHF hszDF hx hy hf hfitx hfity
      hnF hmovesF hpeakF h0F h1F h3tF h3aF h4tF h4aF
  have hmark2 : b2.sudo_5Board_6marker = -1 := by simpa [bf, chordFlag, hm] using hmark
  have hst2 : b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by simpa [bf, chordFlag] using hst
  have hho2 : b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by simpa [bf, chordFlag] using hho
  have hctrl2 : b2.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by simpa [bf, chordFlag] using hctrl
  have hsl2 : b2.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by simpa [bf, chordFlag] using hsl
  refine ⟨b2, ?_, hx0, hy1, hmark2, hst2, hho2, hctrl2, hsl2,
    walkRun_open_white n k bench (x, y) acc zs hz,
    walkRun_walkGo n k bench (x, y) false acc (zs ++ [1]) true (x, y)
      (walkRun_open_white n k bench (x, y) acc zs hz)⟩
  have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 1 2]
    decide
  have hcopyB :
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
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
    (Int.ofNat 0, (bf, false))
    (fuelRange (Int.ofNat 0) (Int.ofNat toN))
    (chordStep (embed (zs ++ [1])) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
  refine asc_goal (α := Ecbs.Board × Bool)
    (ρ := (Bool × Bool) × Ecbs.Board)
    (β := (Bool × Bool) × Ecbs.Board)
    (Inv := fun i (st : Ecbs.Board × Bool) =>
      if i = toN + 1 then st = (b2, true)
      else st.2 = false ∧ st.1 = bf)
    (fromN := 0) (toN := toN) (s0 := (bf, false))
    (goal := .ok ((true, true), { b2 with sudo_5Board_9marker_on := false }))
    (Nat.zero_le _) (by simp [toN]) ?hstep ?hpost
  · intro i st _hi hito hI
    have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by simp [toN]; omega)
    have hlen' : (zs ++ [1]).length = toN + 1 := by simp [toN]
    by_cases hlast : i = toN
    · have hI0 : st.2 = false ∧ st.1 = bf := by
        have hne : ¬ i = toN + 1 := by omega
        simpa [hne] using hI
      have hcell : (zs ++ [1])[i]'(by simp [toN]; omega) = 1 := by
        have hiL : zs.length ≤ i := by simp [toN, hlast]
        rw [List.getElem_append_right hiL]
        simp [toN, hlast]
      have hml := flag_marker b hm
      have hst := chordStep_fresh (zs ++ [1]) i toN 1 bf bf b2
        hito hlen' hcell (by decide) (by decide) hml hcopyB hfiti
      refine ⟨(b2, true), ?_, ?_⟩
      · simp [show i + 1 = toN + 1 from by omega]
      · have hs : st = (bf, false) := Prod.ext hI0.2 hI0.1
        rw [hs]
        simpa [hlast] using hst
    · have hI0 : st.2 = false ∧ st.1 = bf := by
        have hne : ¬ i = toN + 1 := by omega
        simpa [hne] using hI
      have hcell : (zs ++ [1])[i]'(by simp [toN]; omega) = 0 := by
        have hiL : i < zs.length := by
          have hlt : i < toN := Nat.lt_of_le_of_ne hito hlast
          simpa [toN] using hlt
        rw [List.getElem_append_left hiL]
        exact hz _ (List.getElem_mem _)
      have hml := flag_marker b hm
      have hst := chordStep_zero (zs ++ [1]) i toN bf bf
        (by omega) hlen' hcell hml hfiti
      refine ⟨(bf, false), ?_, ?_⟩
      · have hneL : ¬ i + 1 = toN + 1 := by omega
        simp [hneL]
      · have hs : st = (bf, false) := Prod.ext hI0.2 hI0.1
        rw [hs]
        simpa [hlast] using hst
  · intro st hI
    have hs : st = (b2, true) := by simpa using hI
    rw [hs]
    exact after_live_down b2 (Int.ofNat toN) hmark2

/-- Empty cells, then one red cell, marker already `-1`. Up receives the
    negated base up. Control does not move. -/
theorem walk_chord_red_down (b : Ecbs.Board) (zs : List Nat) (x y : List Nat)
    (n k bench moves peak : Nat) (acc : List Nat × List Nat)
    (hz : ∀ c ∈ zs, c = 0)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n) (hpos : 0 < n)
    (hyt : allTritList y) (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = -1)
    (hfit : FitsLen (zs.length + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 : Ecbs.Board,
      Ecbs.walk_chord b (embed (zs ++ [2])) =
        .ok ((true, true), { b2 with sudo_5Board_9marker_on := false }) ∧
      (∀ h : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b2.sudo_5Board_4home.size,
        b2.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      b2.sudo_5Board_6marker = -1 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      walkRun n k bench (x, y) false acc (zs ++ [2]) =
        some (true, (x, mirrorTrits y)) ∧
      walkGo n k bench (x, y) false acc (zs ++ [2]) =
        some (x, mirrorTrits y) := by
  let bf := chordFlag b
  have hszHF : bf.sudo_5Board_4home.size = 8 := by simp [bf, chordFlag, hszH]
  have hszDF : bf.sudo_5Board_4held.size = 8 := by simp [bf, chordFlag, hszD]
  have hnF : bf.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [bf, chordFlag, hn]
  have hmovesF : bf.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [bf, chordFlag, hmoves]
  have hpeakF : bf.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bf, chordFlag, hpeak]
  have h0F : bf.sudo_5Board_4held[0]'(by rw [hszDF]; decide) = false := by
    simpa [bf, chordFlag] using h0
  have h1F : bf.sudo_5Board_4held[1]'(by rw [hszDF]; decide) = false := by
    simpa [bf, chordFlag] using h1
  have h3tF : bf.sudo_5Board_4held[3]'(by rw [hszDF]; decide) = true := by
    simpa [bf, chordFlag] using h3t
  have h3aF : bf.sudo_5Board_4home[3]'(by rw [hszHF]; decide) = embed x := by
    simpa [bf, chordFlag] using h3a
  have h4tF : bf.sudo_5Board_4held[4]'(by rw [hszDF]; decide) = true := by
    simpa [bf, chordFlag] using h4t
  have h4aF : bf.sudo_5Board_4home[4]'(by rw [hszHF]; decide) = embed y := by
    simpa [bf, chordFlag] using h4a
  obtain ⟨b2, _mv, _pk, hcopy, hx0, hy1, _, _, _, hmark, hst, hho, hctrl, hsl⟩ :=
    walk_copy_red bf x y n moves peak hszHF hszDF hx hy hpos hyt hf hfitx hfity
      hnF hmovesF hpeakF h0F h1F h3tF h3aF h4tF h4aF
  have hmark2 : b2.sudo_5Board_6marker = -1 := by simpa [bf, chordFlag, hm] using hmark
  have hst2 : b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by simpa [bf, chordFlag] using hst
  have hho2 : b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by simpa [bf, chordFlag] using hho
  have hctrl2 : b2.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by simpa [bf, chordFlag] using hctrl
  have hsl2 : b2.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by simpa [bf, chordFlag] using hsl
  refine ⟨b2, ?_, hx0, hy1, hmark2, hst2, hho2, hctrl2, hsl2,
    walkRun_open_red n k bench x y acc zs hz,
    walkRun_walkGo n k bench (x, y) false acc (zs ++ [2]) true (x, mirrorTrits y)
      (walkRun_open_red n k bench x y acc zs hz)⟩
  have hbeq : SudoRt.SEq.beq (Int.ofNat 2) (2 : Int) = true := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 2 2]
    decide
  have hcopyB :
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
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
    (Int.ofNat 0, (bf, false))
    (fuelRange (Int.ofNat 0) (Int.ofNat toN))
    (chordStep (embed (zs ++ [2])) (Int.ofNat toN)) chordAfter (fun r => pure r) = _
  refine asc_goal (α := Ecbs.Board × Bool)
    (ρ := (Bool × Bool) × Ecbs.Board)
    (β := (Bool × Bool) × Ecbs.Board)
    (Inv := fun i (st : Ecbs.Board × Bool) =>
      if i = toN + 1 then st = (b2, true)
      else st.2 = false ∧ st.1 = bf)
    (fromN := 0) (toN := toN) (s0 := (bf, false))
    (goal := .ok ((true, true), { b2 with sudo_5Board_9marker_on := false }))
    (Nat.zero_le _) (by simp [toN]) ?hstep ?hpost
  · intro i st _hi hito hI
    have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by simp [toN]; omega)
    have hlen' : (zs ++ [2]).length = toN + 1 := by simp [toN]
    by_cases hlast : i = toN
    · have hI0 : st.2 = false ∧ st.1 = bf := by
        have hne : ¬ i = toN + 1 := by omega
        simpa [hne] using hI
      have hcell : (zs ++ [2])[i]'(by simp [toN]; omega) = 2 := by
        have hiL : zs.length ≤ i := by simp [toN, hlast]
        rw [List.getElem_append_right hiL]
        simp [toN, hlast]
      have hml := flag_marker b hm
      have hst := chordStep_fresh (zs ++ [2]) i toN 2 bf bf b2
        hito hlen' hcell (by decide) (by decide) hml hcopyB hfiti
      refine ⟨(b2, true), ?_, ?_⟩
      · simp [show i + 1 = toN + 1 from by omega]
      · have hs : st = (bf, false) := Prod.ext hI0.2 hI0.1
        rw [hs]
        simpa [hlast] using hst
    · have hI0 : st.2 = false ∧ st.1 = bf := by
        have hne : ¬ i = toN + 1 := by omega
        simpa [hne] using hI
      have hcell : (zs ++ [2])[i]'(by simp [toN]; omega) = 0 := by
        have hiL : i < zs.length := by
          have hlt : i < toN := Nat.lt_of_le_of_ne hito hlast
          simpa [toN] using hlt
        rw [List.getElem_append_left hiL]
        exact hz _ (List.getElem_mem _)
      have hml := flag_marker b hm
      have hst := chordStep_zero (zs ++ [2]) i toN bf bf
        (by omega) hlen' hcell hml hfiti
      refine ⟨(bf, false), ?_, ?_⟩
      · have hneL : ¬ i + 1 = toN + 1 := by omega
        simp [hneL]
      · have hs : st = (bf, false) := Prod.ext hI0.2 hI0.1
        rw [hs]
        simpa [hlast] using hst
  · intro st hI
    have hs : st = (b2, true) := by simpa using hI
    rw [hs]
    exact after_live_down b2 (Int.ofNat toN) hmark2

end EcbsLink2.Link2
