/-
  The live suffix of `walk_fform` on a spec walk that returns a point.
  Each cell is `fform_frame`: colour 0 cubes, and white or red adds.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFformFrame

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

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

/-- The live loop from index `start`, on a spec walk that returns a point.
    `hfull` is that success. Each cell is `fform_frame`. -/
theorem walk_fform_from (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py pxF pyF : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (start : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py start)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hstart : start ≤ t.cells - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (px, py)))
    (hfull : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxF, pyF)))
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t) (tw : TierWalk t)
    (h8 : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hfitY : ∀ (sb : Ecbs.Board) (ys : List Nat),
      sb.sudo_5Board_5bench = embed ys → FitsLen ys.length)
    (run : ∀ (i : Nat) (sb : Ecbs.Board) (ax ay : List Nat),
      FformAt t sb baseX baseY ax ay i →
      ∀ (red : Bool) (bZ : Ecbs.Board) (xP yP zP : List Nat)
        (moves slides ctrl c0 moves' slides' c1 : Nat) (lane : List Nat),
        FrameAt bZ t baseX baseY →
        bZ.sudo_5Board_9marker_on = true →
        bZ.sudo_5Board_6marker = Int.ofNat 2 →
        bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) →
        bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' →
        bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' →
        bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
        sb.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) →
        moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
          3 * (t.benchlen - t.n) →
        slides' ≤ slides + 6 * t.n →
        bZ.sudo_5Board_8bench_on = true →
        bZ.sudo_5Board_8bench_to = (2 : Int) →
        bZ.sudo_5Board_5bench = embed lane →
        lane.take t.n = fieldCube t.n t.k t.benchlen zP →
        (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) →
        bZ.sudo_5Board_4home[0]? =
          some (embed (fieldCube t.n t.k t.benchlen xP)) →
        bZ.sudo_5Board_4home[1]? =
          some (embed (fieldCube t.n t.k t.benchlen yP)) →
        ∃ o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1,
          o.xP = xP ∧ o.yP = yP ∧ o.zP = zP ∧
            o.z = fieldCube t.n t.k t.benchlen zP ∧
              sb.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat o.c4)) :
    ∃ st : Ecbs.Board × Bool,
      FformInv t baseX baseY live0 acc0 cells t.cells st ∧
      FformAt t st.1 baseX baseY pxF pyF t.cells ∧
      walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
        some (true, (pxF, pyF)) ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
        (fformStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (t.cells - 1), st) := by
  let toN := t.cells - 1
  have hto : toN + 1 = t.cells := by omega
  have h0 : FformInv t baseX baseY live0 acc0 cells start (b, true) :=
    ⟨rfl, px, py, hspec, hAt⟩
  have hstep : ∀ i s, start ≤ i → i ≤ toN →
      FformInv t baseX baseY live0 acc0 cells i s →
      ∃ s', FformInv t baseX baseY live0 acc0 cells (i + 1) s' ∧
        fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st hi hito hI
    cases st with
    | mk sb slive =>
    obtain ⟨hlive, ax, ay, hrunP, hAtI⟩ := hI
    have hslive : slive = true := hlive
    subst hslive
    have hiLen : i < cells.length := by omega
    obtain ⟨ax', ay', hwalk⟩ :=
      walkRun_step_of_full t.n t.k t.benchlen (baseX, baseY) live0 acc0
        (pxF, pyF) cells i ax ay hiLen hfull hrunP
    have hiTo : i ≤ t.cells - 1 := hito
    obtain ⟨sb', hst, hAt'⟩ :=
      fform_frame t sb baseX baseY ax ay ax' ay' i cells hAtI hsh hOk sat tw
        h8 h12 hwide h32 h46 (fun ys hys => hfitY sb ys hys) hpos hiTo hlen hwalk
        (fun red bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane =>
          run i sb ax ay hAtI red bZ xP yP zP moves slides ctrl c0 moves' slides'
            c1 lane)
    have htake := take_succ_cell cells i hiLen
    have hrun' := walkRun_snoc t.n t.k t.benchlen (baseX, baseY) acc0
      (ax, ay) (ax', ay') (cells.take i) (cells[i]'hiLen) live0 hrunP hwalk
    refine ⟨(sb', true), ?_, ?_⟩
    · refine ⟨rfl, ax', ay', ?_, ?_⟩
      · simpa [htake, hto] using hrun'
      · simpa [hto] using hAt'
    · simpa [hto] using hst
  rcases asc_inv (fformStep (embed cells) (Int.ofNat toN)) chordAfter
      (fun r => pure r) (FformInv t baseX baseY live0 acc0 cells) start toN
      hstart hstep (b, true) h0 with ⟨st, hInv, heq⟩
  have hInvC : FformInv t baseX baseY live0 acc0 cells t.cells st := by
    rw [hto] at hInv
    exact hInv
  have hcopy := hInvC
  rcases hcopy with ⟨_hlive, pxOut, pyOut, hrun0, hAtF⟩
  have htakeAll : cells.take t.cells = cells := by
    rw [← hlen]
    exact List.take_length cells
  have hrunOut : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxOut, pyOut)) := by
    simpa [htakeAll] using hrun0
  have heqP := Option.some.inj (hrunOut.symm.trans hfull)
  have hpt : (pxOut, pyOut) = (pxF, pyF) := congrArg Prod.snd heqP
  have hpx : pxOut = pxF := congrArg Prod.fst hpt
  have hpy : pyOut = pyF := congrArg Prod.snd hpt
  have hAtF' : FformAt t st.1 baseX baseY pxF pyF t.cells := by
    rw [← hpx, ← hpy]
    exact hAtF
  exact ⟨st, hInvC, hAtF', hfull, heq⟩

/-- Closing the live loop. The frame's marker is a natural and one more
    control step fits, so the suffix is `.ok ((true, true), …)`. -/
theorem walk_fform_close (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py pxF pyF : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (start : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py start)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hstart : start ≤ t.cells - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (px, py)))
    (hfull : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxF, pyF)))
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t) (tw : TierWalk t)
    (h8 : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hfitY : ∀ (sb : Ecbs.Board) (ys : List Nat),
      sb.sudo_5Board_5bench = embed ys → FitsLen ys.length)
    (run : ∀ (i : Nat) (sb : Ecbs.Board) (ax ay : List Nat),
      FformAt t sb baseX baseY ax ay i →
      ∀ (red : Bool) (bZ : Ecbs.Board) (xP yP zP : List Nat)
        (moves slides ctrl c0 moves' slides' c1 : Nat) (lane : List Nat),
        FrameAt bZ t baseX baseY →
        bZ.sudo_5Board_9marker_on = true →
        bZ.sudo_5Board_6marker = Int.ofNat 2 →
        bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) →
        bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' →
        bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' →
        bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
        sb.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) →
        moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
          3 * (t.benchlen - t.n) →
        slides' ≤ slides + 6 * t.n →
        bZ.sudo_5Board_8bench_on = true →
        bZ.sudo_5Board_8bench_to = (2 : Int) →
        bZ.sudo_5Board_5bench = embed lane →
        lane.take t.n = fieldCube t.n t.k t.benchlen zP →
        (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) →
        bZ.sudo_5Board_4home[0]? =
          some (embed (fieldCube t.n t.k t.benchlen xP)) →
        bZ.sudo_5Board_4home[1]? =
          some (embed (fieldCube t.n t.k t.benchlen yP)) →
        ∃ o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1,
          o.xP = xP ∧ o.yP = yP ∧ o.zP = zP ∧
            o.z = fieldCube t.n t.k t.benchlen zP ∧
              sb.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat o.c4)) :
    ∃ bF pxF pyF xP yP zP, ∃ lay : ProjLay, ∃ ctrl,
      FformAt t bF baseX baseY pxF pyF t.cells ∧
      bF.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
        some (true, (pxF, pyF)) ∧
      xP.length = t.n ∧ yP.length = t.n ∧ zP.length = t.n ∧
      allTritList xP ∧ allTritList yP ∧ allTritList zP ∧
      xP = fieldMul t.n t.k t.benchlen pxF zP ∧
      yP = fieldMul t.n t.k t.benchlen pyF zP ∧
      zP ≠ List.replicate t.n 0 ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
        (fformStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .ok ((true, true),
          { bF with
            sudo_5Board_6marker := -1
            sudo_5Board_4cost := { bF.sudo_5Board_4cost with
              sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) }
            sudo_5Board_9marker_on := false }) ∧
      (∀ h : 0 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[0] = embed xP) ∧
      (match lay with
        | .homes =>
            bF.sudo_5Board_8bench_on = false ∧
            (∀ h : 1 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[1] = embed yP) ∧
            (∀ h : 2 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[2] = embed zP) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = true) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = true)
        | .yBench =>
            bF.sudo_5Board_8bench_on = true ∧
            bF.sudo_5Board_8bench_to = (1 : Int) ∧
            (∃ lane, bF.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
              lane.take t.n = yP ∧
              ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = false) ∧
            (∀ h : 2 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[2] = embed zP) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = true)
        | .zBench =>
            bF.sudo_5Board_8bench_on = true ∧
            bF.sudo_5Board_8bench_to = (2 : Int) ∧
            (∃ lane, bF.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
              lane.take t.n = zP ∧
              ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
            (∀ h : 1 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[1] = embed yP) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = true) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = false)) := by
  obtain ⟨st, hI, hAtF, hrun, hloop⟩ :=
    walk_fform_from t b baseX baseY px py pxF pyF live0 acc0 start cells
      hAt hlen hpos hstart hspec hfull hsh hOk sat tw h8 h12 hwide h32 h46
      hfitY run
  have hlive : st.2 = true := hI.1
  cases st with
  | mk bF slive =>
  have hslive : slive = true := hlive
  subst hslive
  have hpack := hAtF
  rcases hpack with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hproj, ⟨_moves, _slides, ctrl, mark, _mx, _pk, _ps, _hole, _cOps, _c0,
      _, _, hctrl, hmark, _, _, _, _, _, _, _, hfit6, _, _, _, _, _, _, _⟩⟩
  rcases hproj with ⟨xP, yP, zP, lay, hxL, hyL, hzL, hxt, hyt, hzt, hx, hy, hz, h0, hlay, _hw⟩
  have hfit : FitsLen (ctrl + 1) := FitsLen.of_le hfit6 (by omega)
  have hclose := chord_after_nat bF (Int.ofNat (t.cells - 1)) true
    mark ctrl hmark hctrl hfit
  refine ⟨bF, pxF, pyF, xP, yP, zP, lay, ctrl, hAtF, hctrl, hrun,
    hxL, hyL, hzL, hxt, hyt, hzt, hx, hy, hz, ?_, h0, hlay⟩
  rw [hloop, hclose]

end EcbsLink2.Link2
