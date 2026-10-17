/-
  The first live cell after the opening copy, then the live suffix.
  A successful `walkRun` is `.ok ((true, true), b')` and the homes are that
  point. The inverse is read off the run. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkJoin
import EcbsLink2.Link2.WalkReach
import EcbsLink2.Link2.WalkRunInv

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A cell that `walkStep` accepts is `0`, `1`, or `2`. -/
theorem walkStep_le2 (n k bench : Nat) (base acc : List Nat × List Nat)
    (live : Bool) (c : Nat) (q : Bool × (List Nat × List Nat))
    (h : walkStep n k bench base live acc c = some q) : c ≤ 2 := by
  by_cases h0 : c = 0
  · omega
  · by_cases h1 : c = 1
    · omega
    · by_cases h2 : c = 2
      · omega
      · exfalso
        unfold walkStep at h
        simp [h0, h1, h2] at h

/-- Every cell of a successful run is `0`, `1`, or `2`. -/
theorem walkRun_cells_le (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (cells : List Nat)
    (q : Bool × (List Nat × List Nat))
    (h : walkRun n k bench base live acc cells = some q) :
    ∀ i (hi : i < cells.length), cells[i] ≤ 2 := by
  intro i hi
  obtain ⟨_, _, step, _, hcell, _⟩ :=
    walkRun_at n k bench base live acc cells i q hi h
  exact walkStep_le2 n k bench base _ _ _ step hcell

/-- A run that ends live has a first white or red cell, after zeros. -/
theorem walk_split_live (n k bench : Nat) (base acc p : List Nat × List Nat)
    (cells : List Nat)
    (h : walkRun n k bench base false acc cells = some (true, p)) :
    ∃ zs c rest, cells = zs ++ (c :: rest) ∧ (∀ z ∈ zs, z = 0) ∧
      (c = 1 ∨ c = 2) := by
  induction cells generalizing acc with
  | nil =>
    simp [walkRun] at h
  | cons c cs ih =>
    obtain ⟨step, hstep, htail⟩ :=
      walkRun_cons_some n k bench base false acc c cs (true, p) h
    by_cases h0 : c = 0
    · have hskip : step = (false, acc) := by
        have hs := walkStep_skip n k bench base acc
        rw [h0] at hstep
        exact Option.some.inj (hstep.symm.trans hs)
      rw [hskip] at htail
      obtain ⟨zs, c', rest, heq, hz, hc⟩ := ih acc htail
      refine ⟨c :: zs, c', rest, ?_, ?_, hc⟩
      · simp [heq]
      · intro z hz'
        simp at hz'
        rcases hz' with rfl | hz'
        · exact h0
        · exact hz z hz'
    · have hc : c = 1 ∨ c = 2 := by
        have hle := walkStep_le2 n k bench base acc false c step hstep
        omega
      refine ⟨[], c, cs, by simp, by simp, hc⟩

/-- The closing lift. The marker is a natural and one more control step fits,
    so the walk is `.ok` and the homes stay. -/
theorem chord_after_nat (b : Ecbs.Board) (j : Int) (live : Bool) (m ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1)) :
    chordAfter (j, (b, live)) =
      .ok ((live, true),
        { b with
          sudo_5Board_6marker := -1
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) }
          sudo_5Board_9marker_on := false }) := by
  unfold chordAfter
  dsimp only
  rw [marker_lift_refines b m ctrl hm hc hfit, ok_bind]
  simp [pure_eq_ok]

private theorem one_to_done (done cap a : Nat) (hge : 1 ≤ done) (ha : a ≤ cap) :
    a ≤ done * cap := by
  have h1 : a ≤ 1 * cap := by
    rw [Nat.one_mul]
    exact ha
  exact Nat.le_trans h1 (Nat.mul_le_mul_right cap hge)

private theorem opening_ctrl_one (t : Spec.Tier) :
    tierR t + 3 ≤ cellCtrlCharge t + 4 := by
  have h5 : 5 ≤ 3 * rowRoom t + 5 := by omega
  have hmul : (tierR t + 1) * 5 ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
    Nat.mul_le_mul_left _ h5
  have hchg : cellCtrlCharge t = 1 + (tierR t + 1) * (3 * rowRoom t + 5) + 6 := by
    unfold cellCtrlCharge
    rfl
  rw [hchg]
  omega

private theorem take_succ_cell (cells : List Nat) (i : Nat) (hi : i < cells.length) :
    cells.take (i + 1) = cells.take i ++ [cells[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp

private theorem walkRun_snoc (n k bench : Nat) (base acc p p' : List Nat × List Nat)
    (cells : List Nat) (c : Nat) (live : Bool)
    (h : walkRun n k bench base live acc cells = some (true, p))
    (hstep : walkStep n k bench base true p c = some (true, p')) :
    walkRun n k bench base live acc (cells ++ [c]) = some (true, p') := by
  induction cells generalizing live acc with
  | nil =>
    simp only [walkRun] at h
    cases h
    simp [walkRun, hstep]
  | cons d ds ih =>
    simp only [walkRun] at h
    cases hgo : walkStep n k bench base live acc d with
    | none => simp [hgo] at h
    | some q =>
      simp only [hgo] at h
      have hrec := ih q.2 q.1 h
      simp [walkRun, hgo, hrec]

private theorem cells_fit (t : Spec.Tier) (tw : TierWalk t) : FitsLen t.cells := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  calc
    t.cells ≤ t.cells * cellOpsCharge t := Nat.le_mul_of_pos_right t.cells hpos
    _ ≤ t.cells * cellOpsCharge t + cellOpsCharge t := Nat.le_add_right _ _
    _ = (t.cells + 1) * cellOpsCharge t := by rw [Nat.succ_mul]

private theorem step_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    have h := tw.opsOver
    omega
  exact Nat.le_trans (by omega : i + 1 ≤ t.cells + 1)
    (Nat.le_mul_of_pos_right (t.cells + 1) hpos)

/-- The emitted walk, for a nonempty key, is the loop from index 0. -/
theorem walk_chord_loop (b : Ecbs.Board) (cells : List Nat)
    (hpos : 0 < cells.length) (hfit : FitsLen cells.length) :
    Ecbs.walk_chord b (embed cells) =
      SudoRt.runLoopOn (Int.ofNat 0, (chordFlag b, false))
        (fuelRange (Int.ofNat 0) (Int.ofNat (cells.length - 1)))
        (chordStep (embed cells) (Int.ofNat (cells.length - 1)))
        chordAfter (fun r => pure r) := by
  rw [walk_chord_eq]
  unfold walkChordGo
  rw [listLen_embed, subI_ofNat_one cells.length hpos hfit, ok_bind]
  dsimp only
  rw [except_bind_pure]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]

private theorem cont_from (k toN : Nat) (b b' : Ecbs.Board) (cells : List Nat)
    (hlt : k < toN)
    (hstep : chordStep (embed cells) (Int.ofNat toN) (Int.ofNat k, (b, true)) =
      .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), (b', true)))) :
    SudoRt.runLoopOn (Int.ofNat k, (b, true))
        (fuelRange (Int.ofNat k) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat (k + 1), (b', true))
        (fuelRange (Int.ofNat (k + 1)) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  have hfuel : fuelRange (Int.ofNat k) (Int.ofNat toN) =
      fuelRange (Int.ofNat (k + 1)) (Int.ofNat toN) + 1 := by
    rw [fuelRange_le (by omega : k ≤ toN), fuelRange_le (by omega : k + 1 ≤ toN)]
    omega
  rw [hfuel, runLoopOn_succ, hstep]

private theorem brk_from (k : Nat) (b b' : Ecbs.Board) (cells : List Nat)
    (hstep : chordStep (embed cells) (Int.ofNat k) (Int.ofNat k, (b, true)) =
      .ok (SudoRt.Flow.brk (Int.ofNat k, (b', true)))) :
    SudoRt.runLoopOn (Int.ofNat k, (b, true))
        (fuelRange (Int.ofNat k) (Int.ofNat k))
        (chordStep (embed cells) (Int.ofNat k)) chordAfter (fun r => pure r) =
      chordAfter (Int.ofNat k, (b', true)) := by
  rw [fuelRange_le (Nat.le_refl k), Nat.sub_self, Nat.zero_add, runLoopOn_succ, hstep]

private theorem flag_beq (c : Nat) (hc : c = 1 ∨ c = 2) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rcases hc with rfl | rfl <;> decide

private theorem ready_of_run (t : Spec.Tier) (x y : List Nat)
    (acc : List Nat × List Nat) (cells : List Nat) (start : Nat)
    (px py : List Nat)
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells = some (true, (px, py))) :
    ∀ i (hi : i < cells.length), start ≤ i → cells[i] ≠ 0 →
      ∀ ax ay, walkRun t.n t.k t.benchlen (x, y) false acc (cells.take i) =
        some (true, (ax, ay)) →
        ∃ inv, fieldInv t.n t.k t.benchlen
          (fieldSub t.n x (fieldCube t.n t.k t.benchlen ax)) = some inv := by
  intro i hi _hge hnz ax ay hpre
  have hle := walkRun_cells_le t.n t.k t.benchlen (x, y) false acc cells
    (true, (px, py)) h i hi
  have hc : cells[i]'hi = 1 ∨ cells[i]'hi = 2 := by omega
  exact walkRun_live_inv t.n t.k t.benchlen (x, y) acc (ax, ay) cells i
    (true, (px, py)) hi hc hpre h

/-- The cubed opening, as a `LiveAt` at any later index. `1 ≤ done`. -/
private theorem cubed_live (t : Spec.Tier) (b : Ecbs.Board)
    (x y up : List Nat) (mv : Nat)
    (fr : RunFrame b t x (fieldCube t.n t.k t.benchlen x))
    (done : Nat) (tw : TierWalk t) (sat : TierSat t) (hsh : TierShape t)
    (hR : 0 < tierR t)
    (_hx : x.length = t.n) (hy : y.length = t.n)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = y) (hA : fr.y1 = fieldCube t.n t.k t.benchlen up)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hmv : fr.moves ≤ mv + cubeCharge t.n t.benchlen)
    (hsl : fr.slides ≤ 4 * t.n)
    (hctrl : fr.ctrl = tierR t - 1 + 4)
    (hops : fr.opsCap = 3)
    (hst : fr.peakS ≤ 7) (hho : fr.hole ≤ t.benchlen)
    (htriY : allTritList y) (htriUp : allTritList up)
    (hmvN : mv ≤ 4 * t.n) (hge : 1 ≤ done) :
    LiveAt t b x y (fieldCube t.n t.k t.benchlen x)
      (fieldCube t.n t.k t.benchlen up) done := by
  have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
    cube_over t.n t.benchlen tw.nLe
  refine ⟨fr, hmk, hY, hA, hf4, hf1, hst, hho, ?_, ?_, ?_, ?_, hy, htriY, ?_, ?_⟩
  · apply one_to_done done _ _ hge
    have hpeg : mv ≤ walkCharge t := by
      have h4 : 4 * t.n ≤ walkCharge t := by
        unfold walkCharge cellMoveCharge
        omega
      exact Nat.le_trans hmvN h4
    calc
      fr.moves ≤ mv + cubeCharge t.n t.benchlen := hmv
      _ ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) := by
        rw [hcube]
        omega
  · apply one_to_done done _ _ hge
    calc
      fr.slides ≤ 4 * t.n := hsl
      _ = slideCharge t.n := by rw [slideCharge]
      _ ≤ cellSlideCharge t + slideCharge t.n := Nat.le_add_left _ _
  · have hctrl' : fr.ctrl = tierR t + 3 := by
      rw [hctrl]
      omega
    rw [hctrl']
    exact one_to_done done _ _ hge (opening_ctrl_one t)
  · rw [hops]
    apply one_to_done done _ _ hge
    unfold cellOpsCharge
    omega
  · exact fieldCube_length t.n t.k t.benchlen up tw.nLe
  · apply fieldCube_trits t.n t.k t.benchlen up htriUp
    · have h := sat.cube_span
      omega
    · exact hsh.k_le

private theorem take_open (zs rest : List Nat) (c : Nat) :
    (zs ++ (c :: rest)).take (zs.length + 1) = zs ++ [c] := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp [List.take_succ_cons, ih]

private theorem point_eq (ax ay px py : List Nat)
    (h : (true, (ax, ay)) = (true, (px, py))) : ax = px ∧ ay = py := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem homes_of_after (b : Ecbs.Board) (px py : List Nat) (m ctrl : Nat)
    (j : Int)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1))
    (hx : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = embed px)
    (hy : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = embed py) :
    ∃ b',
      chordAfter (j, (b, true)) = .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  refine ⟨_, chord_after_nat b j true m ctrl hm hc hfit, ?_, ?_⟩
  · intro h
    simpa using hx (by simpa using h)
  · intro h
    simpa using hy (by simpa using h)

/-- The loop at the copied board. One seat cell, then `walk_chord_from` when
    another cell remains. The result is the spec point. -/
private theorem seat_suffix (t : Spec.Tier) (b2 : Ecbs.Board)
    (x y up px py : List Nat) (mv pk : Nat)
    (acc : List Nat × List Nat) (cells : List Nat) (k : Nat)
    (out : OutLay t b2 x up y mv pk)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (htriUp : allTritList up)
    (hup : up.length = t.n)
    (hmvEq : mv = pegCount x + pegCount y + pegCount x + pegCount y)
    (hmvN : mv ≤ 4 * t.n)
    (hlen : cells.length = t.cells) (hk : k ≤ t.cells - 1) (hk1 : 1 ≤ k)
    (hpre : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
      some (true, (x, up)))
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells =
      some (true, (px, py))) :
    ∃ b',
      SudoRt.runLoopOn (Int.ofNat k, (b2, true))
          (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
          (chordStep (embed cells) (Int.ofNat (t.cells - 1)))
          chordAfter (fun r => pure r) =
        .ok ((true, true), b') ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  let toN := t.cells - 1
  have hto : toN = t.cells - 1 := rfl
  have hkTo : k ≤ toN := hk
  have hlenC : cells.length = toN + 1 := by
    have hpos : 0 < t.cells := by omega
    omega
  have hiK : k < cells.length := by omega
  have hfitk := step_fit t tw k (by omega)
  obtain ⟨bF, fr, hml, hfrob, hmk, hy1, hy4, hmark, hctrl, hst, hho, hmv, hsl, hops,
      hf1, hf4⟩ :=
    seat_out t b2 x up y mv pk out tw hOk sat hsh hR hx hup htriX htriUp hmvN
      (by omega : 0 < t.cells)
  have hc2all := walkRun_cells_le t.n t.k t.benchlen (x, y) false acc cells
    (true, (px, py)) h
  by_cases hzero : cells[k] = 0
  · have hwalk := walkStep_cube t.n t.k t.benchlen (x, y) (x, up)
    have hstep0 := chordStep_cube cells k toN b2 b2 bF hkTo hlenC
      hzero hml hfrob hfitk
    have hsnoc := walkRun_snoc t.n t.k t.benchlen (x, y) acc (x, up)
      (fieldCube t.n t.k t.benchlen x, fieldCube t.n t.k t.benchlen up)
      (cells.take k) 0 false hpre hwalk
    have htake := take_succ_cell cells k hiK
    have hrun1 : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take (k + 1)) =
        some (true, (fieldCube t.n t.k t.benchlen x,
          fieldCube t.n t.k t.benchlen up)) := by
      simpa [htake, hzero] using hsnoc
    by_cases hlast : k = toN
    · have hbr : chordStep (embed cells) (Int.ofNat k) (Int.ofNat k, (b2, true)) =
          .ok (SudoRt.Flow.brk (Int.ofNat k, (bF, true))) := by
        simpa [hlast] using hstep0
      have hloop := brk_from k b2 bF cells hbr
      have hfull : cells.take (k + 1) = cells := by
        have hlen1 : k + 1 = cells.length := by omega
        simp [hlen1]
      rw [hfull] at hrun1
      have hp := point_eq _ _ px py (Option.some.inj (hrun1.symm.trans h))
      obtain ⟨b', hch, hx0, hy0⟩ := homes_of_after bF px py fr.mark fr.ctrl
        (Int.ofNat k) fr.hmark fr.hctrl fr.fitCtrl
        (by
          intro h0
          simpa [hp.1] using fr.home0)
        (by
          intro h1
          simpa [hp.2, hy1] using fr.home1)
      refine ⟨b', ?_, hx0, hy0⟩
      simpa [hto, hlast] using hloop.trans hch
    · have hlt : k < toN := by omega
      have hcont : chordStep (embed cells) (Int.ofNat toN)
          (Int.ofNat k, (b2, true)) =
          .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), (bF, true))) := by
        simpa [hlast] using hstep0
      have hAt := cubed_live t bF x y up mv fr (k + 1) tw sat hsh hR hx hy hmk hy4 hy1
        hf4 hf1 hmv hsl hctrl hops hst hho htriY htriUp hmvN (by omega)
      obtain ⟨st, hI, heq⟩ := walk_chord_from t tw bF x y
        (fieldCube t.n t.k t.benchlen x) (fieldCube t.n t.k t.benchlen up)
        false acc (k + 1) cells hOk sat hR hsh hAt hlen (by omega) (by omega)
        hrun1 hc2all (ready_of_run t x y acc cells (k + 1) px py h)
      have hjoin := (cont_from k toN b2 bF cells hlt hcont).trans heq
      obtain ⟨hlive, ax, ay, hrunF, _, hlast⟩ := hI
      have hgt : toN < t.cells := by omega
      obtain ⟨hxF, hyF, m, c, hm, hc, hfit⟩ := hlast hgt
      have htakeF : cells.take t.cells = cells := by
        rw [show t.cells = cells.length from hlen.symm, List.take_length]
      have hrunP : walkRun t.n t.k t.benchlen (x, y) false acc cells =
          some (true, (ax, ay)) := by
        simpa [htakeF] using hrunF
      have hp := point_eq ax ay px py (Option.some.inj (hrunP.symm.trans h))
      have hslive : st.2 = true := hlive
      cases st with
      | mk sb sl =>
        have hsl' : sl = true := hslive
        subst hsl'
        obtain ⟨b', hch, hx0, hy0⟩ := homes_of_after sb px py m c
          (Int.ofNat toN) hm hc hfit
          (by intro h0; simpa [hp.1] using hxF h0)
          (by intro h1; simpa [hp.2] using hyF h1)
        refine ⟨b', hjoin.trans hch, hx0, hy0⟩
  · have hcS : cells[k]'hiK = 1 ∨ cells[k]'hiK = 2 := by
      have hle := hc2all k hiK
      omega
    obtain ⟨inv, hinv⟩ := walkRun_live_inv t.n t.k t.benchlen (x, y) acc (x, up)
      cells k (true, (px, py)) hiK hcS hpre h
    by_cases hlast : k = toN
    · have hleft : t.cells - k = 1 := by omega
      have hmvP : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
          cubeCharge t.n t.benchlen := by
        simpa [hmvEq] using hmv
      obtain ⟨b', x3, y3, hdemo, hwalk, hx3, hy3, m, c, hm, hc, hfit⟩ :=
        seat_cell_last t bF x y up (cells[k]) k 1 inv fr tw hOk sat hR hsh
          hmk hy4 hy1 hf4 hf1 hy htriY htriUp hmvP hsl hctrl hops hmark hho
          hcS hinv hk1 rfl (by omega)
      have hadd : Ecbs.chord_add_demo bF
          (SudoRt.SEq.beq (Int.ofNat (cells[k]'hiK)) (2 : Int)) = .ok (true, b') := by
        rw [flag_beq _ hcS]
        exact hdemo
      have hstep := chordStep_open cells k k (cells[k]) b2 b2 bF b' (Nat.le_refl _)
        (by omega) rfl (by omega) (by omega) hml hfrob hadd hfitk
      have hbr : chordStep (embed cells) (Int.ofNat k) (Int.ofNat k, (b2, true)) =
          .ok (SudoRt.Flow.brk (Int.ofNat k, (b', true))) := by
        simpa [hlast] using hstep
      have hloop := brk_from k b2 b' cells hbr
      have hsnoc := walkRun_snoc t.n t.k t.benchlen (x, y) acc (x, up) (x3, y3)
        (cells.take k) (cells[k]) false hpre hwalk
      have htake := take_succ_cell cells k hiK
      have hfull : cells.take (k + 1) = cells := by
        rw [show k + 1 = cells.length by omega, List.take_length]
      have hrun1 : walkRun t.n t.k t.benchlen (x, y) false acc cells =
          some (true, (x3, y3)) := by
        rw [← hfull, htake]
        exact hsnoc
      have hp := point_eq x3 y3 px py (Option.some.inj (hrun1.symm.trans h))
      obtain ⟨bA, hch, hx0, hy0⟩ := homes_of_after b' px py m c (Int.ofNat k)
        hm hc hfit
        (by intro h0; simpa [hp.1] using hx3 h0)
        (by intro h1; simpa [hp.2] using hy3 h1)
      refine ⟨bA, ?_, hx0, hy0⟩
      simpa [hto, hlast] using hloop.trans hch
    · have hlt : k < toN := by omega
      let left := t.cells - k
      let fuel := left - 1
      have hfuel : 1 ≤ fuel := by
        have h := hlt
        omega
      have hleftEq : fuel + 1 = left := by omega
      have hsum : k + left = t.cells := by omega
      have hmvP : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
          cubeCharge t.n t.benchlen := by
        simpa [hmvEq] using hmv
      obtain ⟨b', x3, y3, hdemo, hwalk, hAt⟩ :=
        seat_cell_chord t bF x y up (cells[k]) k left fuel inv fr tw hOk sat hR hsh
          hmk hy4 hy1 hf4 hf1 hy htriY htriUp hmvP hsl hctrl hops hmark hst hho
          hcS hinv hk1 hfuel hleftEq hsum
      have hadd : Ecbs.chord_add_demo bF
          (SudoRt.SEq.beq (Int.ofNat (cells[k]'hiK)) (2 : Int)) = .ok (true, b') := by
        rw [flag_beq _ hcS]
        exact hdemo
      have hstep := chordStep_open cells k toN (cells[k]) b2 b2 bF b' hkTo hlenC
        rfl (by omega) (by omega) hml hfrob hadd hfitk
      have hcont : chordStep (embed cells) (Int.ofNat toN)
          (Int.ofNat k, (b2, true)) =
          .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), (b', true))) := by
        simpa [hlast] using hstep
      have hsnoc := walkRun_snoc t.n t.k t.benchlen (x, y) acc (x, up) (x3, y3)
        (cells.take k) (cells[k]) false hpre hwalk
      have htake := take_succ_cell cells k hiK
      have hrun1 : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take (k + 1)) =
          some (true, (x3, y3)) := by
        simpa [htake] using hsnoc
      obtain ⟨st, hI, heq⟩ := walk_chord_from t tw b' x y x3 y3 false acc (k + 1)
        cells hOk sat hR hsh hAt hlen (by omega) (by omega) hrun1 hc2all
        (ready_of_run t x y acc cells (k + 1) px py h)
      have hjoin := (cont_from k toN b2 b' cells hlt hcont).trans heq
      obtain ⟨hlive, ax, ay, hrunF, _, hend⟩ := hI
      obtain ⟨hxF, hyF, m, c, hm, hc, hfit⟩ := hend (by omega : toN < t.cells)
      have htakeF : cells.take t.cells = cells := by
        rw [show t.cells = cells.length from hlen.symm, List.take_length]
      have hrunP : walkRun t.n t.k t.benchlen (x, y) false acc cells =
          some (true, (ax, ay)) := by
        simpa [htakeF] using hrunF
      have hp := point_eq ax ay px py (Option.some.inj (hrunP.symm.trans h))
      cases st with
      | mk sb sl =>
        have hsl' : sl = true := hlive
        subst hsl'
        obtain ⟨bA, hch, hx0, hy0⟩ := homes_of_after sb px py m c
          (Int.ofNat toN) hm hc hfit
          (by intro h0; simpa [hp.1] using hxF h0)
          (by intro h1; simpa [hp.2] using hyF h1)
        refine ⟨bA, hjoin.trans hch, hx0, hy0⟩

/-- A successful spec walk is the emitted walk. The homes are that point. -/
theorem walk_chord_success (t : Spec.Tier) (x y px py : List Nat)
    (acc : List Nat × List Nat) (cells : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hlen : cells.length = t.cells)
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells = some (true, (px, py))) :
    ∃ b',
      Ecbs.walk_chord (baseBoard t x y) (embed cells) = .ok ((true, true), b') ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  obtain ⟨zs, c, rest, heq, hz, hc⟩ :=
    walk_split_live t.n t.k t.benchlen (x, y) acc (px, py) cells h
  have hfit : FitsLen t.cells := cells_fit t tw
  by_cases hrest : rest = []
  · have hnil : cells = zs ++ [c] := by simp [heq, hrest]
    rcases hc with rfl | rfl
    · rw [hnil] at hlen h
      obtain ⟨b', hch, hx0, hy1, hrun⟩ :=
        walk_chord_base_white t x y zs tw hsh acc hx hy hz hlen
      have hp := point_eq x y px py (Option.some.inj (hrun.symm.trans h))
      refine ⟨b', by simpa [hnil] using hch, ?_, ?_⟩
      · intro h0
        simpa [hp.1] using hx0 h0
      · intro h1
        simpa [hp.2] using hy1 h1
    · rw [hnil] at hlen h
      obtain ⟨b', hch, hx0, hy1, hrun⟩ :=
        walk_chord_base_red t x y zs tw hOk hsh acc hx hy htriY hz hlen
      have hp := point_eq x (mirrorTrits y) px py (Option.some.inj (hrun.symm.trans h))
      refine ⟨b', by simpa [hnil] using hch, ?_, ?_⟩
      · intro h0
        simpa [hp.1] using hx0 h0
      · intro h1
        simpa [hp.2] using hy1 h1
  · have hposR : 0 < rest.length := by
      cases rest with
      | nil => simp at hrest
      | cons _ _ => simp
    have hpos : 0 < t.cells := by
      have hlen' := hlen
      rw [heq] at hlen'
      simp at hlen'
      omega
    let k := zs.length + 1
    have hk : k ≤ t.cells - 1 := by
      have hlen' := hlen
      rw [heq] at hlen'
      simp [List.length_append] at hlen'
      omega
    have hk1 : 1 ≤ k := by omega
    have hpreTake : cells.take k = zs ++ [c] := by
      simpa [heq, k] using take_open zs rest c
    rcases hc with rfl | rfl
    · obtain ⟨b2, pk, out, _hcopy, hloop⟩ :=
        walk_reach_white t x y zs rest tw hsh hR hx hy hz (by simpa [heq] using hlen) hposR
      have hpre : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
          some (true, (x, y)) := by
        simpa [hpreTake] using walkRun_open_white t.n t.k t.benchlen (x, y) acc zs hz
      have hmvN : pegCount x + pegCount y + pegCount x + pegCount y ≤ 4 * t.n := by
        have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
        have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
        omega
      obtain ⟨b', hrun, hx0, hy0⟩ :=
        seat_suffix t b2 x y y px py
          (pegCount x + pegCount y + pegCount x + pegCount y) pk acc cells k out
          tw hOk sat hR hsh hx hy htriX htriY htriY hy rfl hmvN hlen hk hk1 hpre h
      refine ⟨b', ?_, hx0, hy0⟩
      have hloop' :
          Ecbs.walk_chord (baseBoard t x y) (embed cells) =
            SudoRt.runLoopOn (Int.ofNat k, (b2, true))
              (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
              (chordStep (embed cells) (Int.ofNat (t.cells - 1)))
              chordAfter (fun r => pure r) := by
        rw [walk_chord_loop (baseBoard t x y) cells (by rw [hlen]; exact hpos)
          (by simpa [hlen] using hfit)]
        rw [show cells.length - 1 = t.cells - 1 by rw [hlen]]
        rw [heq]
        simp only [k]
        exact hloop
      exact hloop'.trans hrun
    · obtain ⟨b2, pk, out, _hcopy, hloop⟩ :=
        walk_reach_red t x y zs rest tw hOk hsh hR hx hy htriY hz
          (by simpa [heq] using hlen) hposR
      have hpre : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
          some (true, (x, mirrorTrits y)) := by
        simpa [hpreTake] using walkRun_open_red t.n t.k t.benchlen x y acc zs hz
      have hmvN : pegCount x + pegCount y + pegCount x + pegCount y ≤ 4 * t.n := by
        have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
        have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
        omega
      obtain ⟨b', hrun, hx0, hy0⟩ :=
        seat_suffix t b2 x y (mirrorTrits y) px py
          (pegCount x + pegCount y + pegCount x + pegCount y) pk acc cells k out
          tw hOk sat hR hsh hx hy htriX htriY (mirrorTrits_allTrit htriY)
          (by rw [mirror_length, hy]) rfl hmvN hlen hk hk1 hpre h
      refine ⟨b', ?_, hx0, hy0⟩
      have hloop' :
          Ecbs.walk_chord (baseBoard t x y) (embed cells) =
            SudoRt.runLoopOn (Int.ofNat k, (b2, true))
              (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
              (chordStep (embed cells) (Int.ofNat (t.cells - 1)))
              chordAfter (fun r => pure r) := by
        rw [walk_chord_loop (baseBoard t x y) cells (by rw [hlen]; exact hpos)
          (by simpa [hlen] using hfit)]
        rw [show cells.length - 1 = t.cells - 1 by rw [hlen]]
        rw [heq]
        simp only [k]
        exact hloop
      exact hloop'.trans hrun

end EcbsLink2.Link2
