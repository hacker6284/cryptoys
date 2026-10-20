/-
  The live suffix of any length. Each cell is `suffix_chord_add`: the cube,
  then the chord when the cell is live. The room is `(len + 1)` charges on top
  of the counters the suffix started from, and one `walkCharge` covers every
  cube. `cells.length = t.cells` is the fresh key. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SuffixAt
import EcbsLink2.Link2.CopyKeep
import EcbsLink2.Link2.WalkInd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The board after `done` cells, once the marker is a natural. The cubes are
    charged on top of `mv0`. -/
def SpanFrame (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (done mv0 sl0 ct0 op0 : Nat) : Prop :=
  ∃ fr : RunFrame b t baseX accX,
    b.sudo_5Board_9marker_on = true ∧
    fr.y4 = baseY ∧
    fr.y1 = accY ∧
    fr.flag4 = true ∧
    fr.flag1 = true ∧
    fr.peakS ≤ 7 ∧
    fr.hole ≤ t.benchlen ∧
    fr.moves ≤ mv0 + done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
    fr.slides ≤ sl0 + done * (cellSlideCharge t + 4 * t.n) ∧
    fr.ctrl ≤ ct0 + done * (cellCtrlCharge t + 4) ∧
    fr.opsCap ≤ op0 + done * (cellOpsCharge t + 2) ∧
    baseY.length = t.n ∧
    allTritList baseY ∧
    accY.length = t.n ∧
    allTritList accY

/-- The board `chord_fresh_white_down` leaves. The marker is still `-1`, homes
    0 and 1 hold the copied point, and `done` charges of cube overhead sit on
    top of `mv0`. -/
def SpanDown (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (done mv0 sl0 ct0 op0 : Nat) : Prop :=
  ∃ (mv pk : Nat) (out : OutLay t b accX accY baseY mv pk),
    mv ≤ mv0 + done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
    out.sl0 ≤ sl0 + done * (cellSlideCharge t + 4 * t.n) ∧
    out.ctrl0 ≤ ct0 + done * (cellCtrlCharge t + 4) ∧
    out.ops0 ≤ op0 + done * (cellOpsCharge t + 2) ∧
    out.strict0 ≤ 7 ∧
    out.hole0 ≤ t.benchlen ∧
    0 < out.ctrl0 ∧
    baseX.length = t.n ∧
    allTritList baseX ∧
    baseY.length = t.n ∧
    allTritList baseY ∧
    accY.length = t.n ∧
    allTritList accY

/-- A suffix cell. The live frames are `SpanFrame`. The opening copy, marker
    still `-1`, is `SpanDown`. -/
def SpanAt (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (done mv0 sl0 ct0 op0 : Nat) : Prop :=
  SpanFrame t b baseX baseY accX accY done mv0 sl0 ct0 op0 ∨
    SpanDown t b baseX baseY accX accY done mv0 sl0 ct0 op0

def SuffixInv (t : Spec.Tier) (baseX baseY : List Nat) (live0 : Bool)
    (acc0 : List Nat × List Nat) (cells : List Nat) (toN mv0 sl0 ct0 op0 : Nat)
    (i : Nat) (st : Ecbs.Board × Bool) : Prop :=
  st.2 = true ∧
  ∃ ax ay,
    walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take i) =
      some (true, (ax, ay)) ∧
    (i ≤ toN → SpanFrame t st.1 baseX baseY ax ay i mv0 sl0 ct0 op0) ∧
    (toN < i →
      (∀ h : 0 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[0] = embed ax) ∧
      (∀ h : 1 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[1] = embed ay) ∧
      ∃ m ctrl,
        st.1.sudo_5Board_6marker = Int.ofNat m ∧
        st.1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
        FitsLen (ctrl + 1) ∧
        LastLay st.1 baseX baseY (suffixMoveCap t mv0 toN)
          (suffixSlideCap t sl0 toN))

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

private theorem ops_pos (len c : Nat) (h : 2 * len + 2 ≤ c) : 0 < c :=
  Nat.lt_of_lt_of_le (Nat.succ_pos (2 * len + 1)) h

private theorem index_fit (len i c : Nat) (hi : i + 1 ≤ len + 1) (hc : 0 < c)
    (hroom : FitsLen ((len + 1) * c)) : FitsLen (i + 1) :=
  FitsLen.of_le hroom (Nat.le_trans hi (Nat.le_mul_of_pos_right (len + 1) hc))

/-- One cell of a suffix of length `len`, from the span at that index. -/
private theorem suffix_span_step (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (cells : List Nat)
    (len toN i mv0 sl0 ct0 op0 : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : SpanFrame t b baseX baseY accX accY i mv0 sl0 ct0 op0)
    (hn : t.n ≤ t.benchlen)
    (hmoveOver : (6 * t.benchlen + 2 * t.n) * len ≤ walkCharge t)
    (hslideOver : 4 * t.n * len ≤ cellSlideCharge t)
    (hctrlOver : 4 * len ≤ cellCtrlCharge t)
    (hopsOver : 2 * len + 2 ≤ cellOpsCharge t)
    (hRoomM : FitsLen (mv0 + (len + 1) * walkCharge t))
    (hRoomS : FitsLen (sl0 + (len + 1) * cellSlideCharge t))
    (hRoomC : FitsLen (ct0 + (len + 1) * cellCtrlCharge t))
    (hRoomO : FitsLen (op0 + (len + 1) * cellOpsCharge t))
    (hscript : 4 < t.script)
    (hto : toN + 1 = len) (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hiLen : i < cells.length) (hcLe : cells[i]'hiLen ≤ 2)
    (hinv : cells[i]'hiLen ≠ 0 →
      ∃ inv, fieldInv t.n t.k t.benchlen
        (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX)) = some inv) :
    ∃ b' ax' ay',
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b', true)))) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (accX, accY) (cells[i]'hiLen) =
        some (true, (ax', ay')) ∧
      (i < toN → SpanFrame t b' baseX baseY ax' ay' (i + 1) mv0 sl0 ct0 op0) ∧
      (i = toN →
        (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed ax') ∧
        (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed ay') ∧
        ∃ m ctrl,
          b'.sudo_5Board_6marker = Int.ofNat m ∧
          b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
          FitsLen (ctrl + 1) ∧
          LastLay b' baseX baseY (suffixMoveCap t mv0 toN)
            (suffixSlideCap t sl0 toN)) := by
  obtain ⟨fr, hmk, hY, hA, hf4, hf1, hst, hho, hm, hs, hc0, ho, hyB, htriB, hyA, htriA⟩ := hAt
  have hleft : 0 < toN - i + 1 := Nat.succ_pos (toN - i)
  have hsum : i + (toN - i + 1) = toN + 1 := by
    rw [← Nat.add_assoc, Nat.add_sub_of_le hi]
  have hpureO : FitsLen ((len + 1) * cellOpsCharge t) :=
    FitsLen.of_le hRoomO (Nat.le_add_left ((len + 1) * cellOpsCharge t) op0)
  have hfiti : FitsLen (i + 1) :=
    index_fit len i (cellOpsCharge t)
      (Nat.le_trans (Nat.le_trans (Nat.succ_le_succ hi) (Nat.le_of_eq hto)) (Nat.le_succ len))
      (ops_pos len _ hopsOver) hpureO
  obtain ⟨b', ax', ay', hstep, hwalk, hnext, hlast⟩ :=
    suffix_chord_add t b baseX accX baseY accY fr len i (toN - i + 1) mv0 sl0 ct0 op0
      (cells[i]'hiLen) cells i toN hOk sat hR hsh hmk hY hA hf4 hf1 hyB htriB hyA htriA
      (hsum.trans hto) hleft hn hmoveOver hslideOver hctrlOver hopsOver hm hs hc0 ho
      hRoomM hRoomS hRoomC hRoomO hst hho hscript rfl hto hi hlen hiLen rfl hcLe hfiti hinv
  refine ⟨b', ax', ay', hstep, hwalk, ?_, hlast⟩
  intro hlt
  obtain ⟨fr', hmk', hy4', hy1', hf4', hf1', hst', hho', hm', hs', hc', ho', hlenY, htriY⟩ :=
    hnext hlt
  exact ⟨fr', hmk', hy4', hy1', hf4', hf1', hst', hho', hm', hs', hc', ho', hyB, htriB,
    hlenY, htriY⟩

/-- The live loop from `start` through a list of length `len`. -/
theorem suffix_walk (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (cells : List Nat) (len start mv0 sl0 ct0 op0 : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : SpanFrame t b baseX baseY accX accY start mv0 sl0 ct0 op0)
    (hn : t.n ≤ t.benchlen)
    (hmoveOver : (6 * t.benchlen + 2 * t.n) * len ≤ walkCharge t)
    (hslideOver : 4 * t.n * len ≤ cellSlideCharge t)
    (hctrlOver : 4 * len ≤ cellCtrlCharge t)
    (hopsOver : 2 * len + 2 ≤ cellOpsCharge t)
    (hRoomM : FitsLen (mv0 + (len + 1) * walkCharge t))
    (hRoomS : FitsLen (sl0 + (len + 1) * cellSlideCharge t))
    (hRoomC : FitsLen (ct0 + (len + 1) * cellCtrlCharge t))
    (hRoomO : FitsLen (op0 + (len + 1) * cellOpsCharge t))
    (hscript : 4 < t.script)
    (hlen : cells.length = len) (hpos : 0 < len) (hstart : start ≤ len - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (accX, accY)))
    (hc2 : ∀ i (hi : i < cells.length), cells[i] ≤ 2)
    (hready : ∀ i (hi : i < cells.length), start ≤ i → cells[i] ≠ 0 →
      ∀ ax ay, walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take i) =
        some (true, (ax, ay)) →
        ∃ inv, fieldInv t.n t.k t.benchlen
          (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen ax)) = some inv) :
    ∃ st : Ecbs.Board × Bool,
      SuffixInv t baseX baseY live0 acc0 cells (len - 1) mv0 sl0 ct0 op0 len st ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (len - 1)))
        (chordStep (embed cells) (Int.ofNat (len - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (len - 1), st) := by
  let toN := len - 1
  have hto : toN + 1 = len := Nat.succ_pred_eq_of_pos hpos
  have h0 : SuffixInv t baseX baseY live0 acc0 cells toN mv0 sl0 ct0 op0 start (b, true) := by
    refine ⟨rfl, accX, accY, hspec, fun _ => hAt, fun h => absurd h (Nat.not_lt.mpr hstart)⟩
  have hstep : ∀ i s, start ≤ i → i ≤ toN →
      SuffixInv t baseX baseY live0 acc0 cells toN mv0 sl0 ct0 op0 i s →
      ∃ s', SuffixInv t baseX baseY live0 acc0 cells toN mv0 sl0 ct0 op0 (i + 1) s' ∧
        chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st hfrom hito hI
    obtain ⟨hlive, ax, ay, hrun, hspan, _hhome⟩ := hI
    have hslive : st.2 = true := hlive
    cases st with
    | mk sb slive =>
      cases hslive
      have hiLen : i < cells.length := by
        rw [hlen]
        exact Nat.lt_of_lt_of_eq (Nat.lt_succ_of_le hito) hto
      have hlenT : cells.length = toN + 1 := hlen.trans hto.symm
      obtain ⟨b', ax', ay', hstep, hwalk, hnext, hlast⟩ :=
        suffix_span_step t sb baseX baseY ax ay cells len toN i mv0 sl0 ct0 op0
          hOk sat hR hsh (hspan hito) hn hmoveOver hslideOver hctrlOver hopsOver
          hRoomM hRoomS hRoomC hRoomO hscript hto hito hlenT hiLen (hc2 i hiLen)
          (fun hnz => hready i hiLen hfrom hnz ax ay hrun)
      have htake := take_succ_cell cells i hiLen
      have hrun' := walkRun_snoc t.n t.k t.benchlen (baseX, baseY) acc0 (ax, ay) (ax', ay')
        (cells.take i) (cells[i]'hiLen) live0 hrun hwalk
      refine ⟨(b', true), ?_, hstep⟩
      refine ⟨rfl, ax', ay', ?_, ?_, ?_⟩
      · simpa [htake] using hrun'
      · intro hle
        have hne : i ≠ toN := by
          intro heq
          rw [heq] at hle
          exact Nat.not_succ_le_self toN hle
        exact hnext (Nat.lt_of_le_of_ne hito hne)
      · intro hgt
        have heq : i + 1 = toN + 1 :=
          Nat.le_antisymm (Nat.succ_le_succ hito) (Nat.succ_le_of_lt hgt)
        exact hlast (Nat.succ.inj heq)
  obtain ⟨st, hI, heq⟩ := asc_inv (chordStep (embed cells) (Int.ofNat toN)) chordAfter
    (fun r => pure r) (SuffixInv t baseX baseY live0 acc0 cells toN mv0 sl0 ct0 op0)
    start toN hstart hstep (b, true) h0
  refine ⟨st, ?_, heq⟩
  simpa [hto] using hI

private theorem fresh_span (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (fr : RunFrame b t baseX accX)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hst : fr.peakS ≤ 7) (hho : fr.hole ≤ t.benchlen)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0) (ho0 : fr.opsCap = 0)
    (hyB : baseY.length = t.n) (htriY : allTritList baseY)
    (hyA : accY.length = t.n) (htriA : allTritList accY) :
    SpanFrame t b baseX baseY accX accY 0 0 0 0 0 := by
  refine ⟨fr, hmk, hY, hA, hf4, hf1, hst, hho, ?_, ?_, ?_, ?_, hyB, htriY, hyA, htriA⟩
  · simp [hm0]
  · simp [hs0]
  · simp [hc0]
  · simp [ho0]

/-- The fresh key. `cells.length = t.cells`, counters at zero, room from `TierWalk`. -/
theorem suffix_fresh (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (fr : RunFrame b t baseX accX) (cells : List Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hst : fr.peakS ≤ 7) (hho : fr.hole ≤ t.benchlen)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0) (ho0 : fr.opsCap = 0)
    (hyB : baseY.length = t.n) (htriY : allTritList baseY)
    (hyA : accY.length = t.n) (htriA : allTritList accY)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hc2 : ∀ i (hi : i < cells.length), cells[i] ≤ 2)
    (hready : ∀ i (hi : i < cells.length), cells[i] ≠ 0 →
      ∀ ax ay, walkRun t.n t.k t.benchlen (baseX, baseY) true (accX, accY) (cells.take i) =
        some (true, (ax, ay)) →
        ∃ inv, fieldInv t.n t.k t.benchlen
          (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen ax)) = some inv) :
    ∃ st : Ecbs.Board × Bool,
      WalkInv t baseX baseY true (accX, accY) cells (t.cells - 1) t.cells st ∧
      SudoRt.runLoopOn (Int.ofNat 0, (b, true))
        (fuelRange (Int.ofNat 0) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (t.cells - 1), st) := by
  have hAt := fresh_span t b baseX baseY accX accY fr hmk hY hA hf4 hf1 hst hho
    hm0 hs0 hc0 ho0 hyB htriY hyA htriA
  have hRoomM : FitsLen (0 + (t.cells + 1) * walkCharge t) := by
    simpa [Nat.zero_add] using tw.roomM
  have hRoomS : FitsLen (0 + (t.cells + 1) * cellSlideCharge t) := by
    simpa [Nat.zero_add] using tw.roomS
  have hRoomC : FitsLen (0 + (t.cells + 1) * cellCtrlCharge t) := by
    simpa [Nat.zero_add] using tw.roomC
  have hRoomO : FitsLen (0 + (t.cells + 1) * cellOpsCharge t) := by
    simpa [Nat.zero_add] using tw.roomO
  obtain ⟨st, hI, heq⟩ := suffix_walk t b baseX baseY accX accY true (accX, accY) cells
    t.cells 0 0 0 0 0 hOk sat hR hsh hAt tw.nLe tw.moveOver tw.slideOver tw.ctrlOver
    tw.opsOver hRoomM hRoomS hRoomC hRoomO tw.scriptRoom hlen hpos (Nat.zero_le _)
    (by simp [walkRun]) hc2 (fun i hi _ hnz ax ay hrun => hready i hi hnz ax ay hrun)
  refine ⟨st, ?_, heq⟩
  obtain ⟨hlive, ax, ay, hrun, _hspan, hhome⟩ := hI
  have hhome' : t.cells - 1 < t.cells →
      (∀ h : 0 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[0] = embed ax) ∧
      (∀ h : 1 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[1] = embed ay) ∧
      ∃ m ctrl,
        st.1.sudo_5Board_6marker = Int.ofNat m ∧
        st.1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
        FitsLen (ctrl + 1) := by
    intro hgt
    obtain ⟨hx, hy, ⟨m, c, hm, hc, hfit, _⟩⟩ := hhome hgt
    exact ⟨hx, hy, ⟨m, c, hm, hc, hfit⟩⟩
  refine ⟨hlive, ax, ay, hrun, ?_, hhome'⟩
  intro hle
  exact absurd hle (Nat.not_le.mpr (Nat.pred_lt (Nat.ne_of_gt hpos)))

end EcbsLink2.Link2
