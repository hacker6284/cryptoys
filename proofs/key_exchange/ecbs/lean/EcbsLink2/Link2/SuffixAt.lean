/-
  One live cell's Frobenius, paid from the counters already on the board.
  `cellsLeft` is how many cells of this suffix remain, including this one.
  The fresh key spends `t.cells + 1` at the opening seat and `t.cells - i`
  here. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellRun
import EcbsLink2.Link2.WalkCharge
import EcbsLink2.Link2.ChordFrame
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.BenchAdd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem room_one (a c k : Nat) (hk : 0 < k) (h : FitsLen (a + c * k)) :
    FitsLen (a + c) := by
  apply FitsLen.of_le h
  have hc : c * 1 ≤ c * k := Nat.mul_le_mul_left c hk
  simpa using hc

private theorem cube_in_walk (t : Spec.Tier) :
    cubeCharge t.n t.benchlen + 3 * t.n ≤ walkCharge t := by
  unfold walkCharge cellMoveCharge cubeCharge pegCharge
  omega

private theorem slide_in_cell (t : Spec.Tier) : slideCharge t.n ≤ cellSlideCharge t := by
  unfold slideCharge cellSlideCharge tailSlideCap
  omega

private theorem ctrl_in_cell (t : Spec.Tier) : 5 ≤ cellCtrlCharge t := by
  unfold cellCtrlCharge
  omega

private theorem ops_in_cell (t : Spec.Tier) : 2 ≤ cellOpsCharge t := by
  unfold cellOpsCharge
  omega

private theorem spend_mul (moves moves' c rem : Nat) (hrem : 0 < rem)
    (hm : moves' ≤ moves + c) (h : FitsLen (moves + c * rem)) :
    FitsLen (moves' + c * (rem - 1)) := by
  have hcomm : FitsLen (moves + rem * c) := by simpa [Nat.mul_comm] using h
  have hsucc := ctrl_room_succ moves moves' rem c hrem hm hcomm
  simpa [Nat.mul_comm] using hsucc

/-- Frobenius of one live cell. The four rooms shrink by one charge. -/
theorem suffix_frob (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (cellsLeft : Nat) (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hleft : 0 < cellsLeft)
    (hst : fr.peakS ≤ 7) (hhole : fr.hole ≤ t.benchlen)
    (hM : FitsLen (fr.moves + walkCharge t * cellsLeft))
    (hS : FitsLen (fr.slides + cellSlideCharge t * cellsLeft))
    (hO : FitsLen (fr.opsCap + cellOpsCharge t * cellsLeft))
    (hC : FitsLen (fr.ctrl + cellCtrlCharge t * cellsLeft)) :
    ∃ bL bF, ∃ fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen accY ∧
      fr'.y4 = baseY ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true ∧
      fr'.mark = 1 ∧
      fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ fr.slides + slideCharge t.n ∧
      fr'.ctrl = fr.ctrl + 4 ∧
      fr'.opsCap = fr.opsCap + 2 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      FitsLen (fr'.moves + walkCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.slides + cellSlideCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.opsCap + cellOpsCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.ctrl + cellCtrlCharge t * (cellsLeft - 1)) := by
  have hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n) := by
    have h1 := room_one fr.moves (walkCharge t) cellsLeft hleft hM
    apply FitsLen.of_le h1
    have hcu := cube_in_walk t
    omega
  have hSlide : FitsLen (fr.slides + slideCharge t.n) := by
    have h1 := room_one fr.slides (cellSlideCharge t) cellsLeft hleft hS
    apply FitsLen.of_le h1
    have hslC := slide_in_cell t
    omega
  have hCtrl : FitsLen (fr.ctrl + 5) := by
    have h1 := room_one fr.ctrl (cellCtrlCharge t) cellsLeft hleft hC
    apply FitsLen.of_le h1
    have hc5 := ctrl_in_cell t
    omega
  have hOps : FitsLen (fr.opsCap + 2) := by
    have h1 := room_one fr.opsCap (cellOpsCharge t) cellsLeft hleft hO
    apply FitsLen.of_le h1
    have hop := ops_in_cell t
    omega
  obtain ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hctrl, hmark,
      _hcOps, _hchord, hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hholeEq,
      htopX, htopY⟩ :=
    cell_run_frame b t baseX accX baseY accY fr hOk sat hsh hmk hY hA hf4 hf1
      hyA htriY hMove hSlide hCtrl hOps
  have hst' : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld b.sudo_5Board_4held 7) occU hst hheld hocc
  have hho' : fr'.hole ≤ t.benchlen := by
    rw [hholeEq]
    exact hole_out_le fr.hole (topIdx (combStrip t.n t.benchlen accX))
      (topIdx (combStrip t.n t.benchlen accY)) t.benchlen hhole htopX htopY
  refine ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hmark, hmv, hsl, hctrl, hops,
    hst', hho', ?_, ?_, ?_, ?_⟩
  · have hspend : fr'.moves ≤ fr.moves + walkCharge t := by
      calc
        fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen := hmv
        _ ≤ fr.moves + walkCharge t := by
          have hcu := cube_in_walk t
          omega
    exact spend_mul fr.moves fr'.moves (walkCharge t) cellsLeft hleft hspend hM
  · have hspend : fr'.slides ≤ fr.slides + cellSlideCharge t := by
      calc
        fr'.slides ≤ fr.slides + slideCharge t.n := hsl
        _ ≤ fr.slides + cellSlideCharge t := by
          have hslC := slide_in_cell t
          omega
    exact spend_mul fr.slides fr'.slides (cellSlideCharge t) cellsLeft hleft hspend hS
  · have hspend : fr'.opsCap ≤ fr.opsCap + cellOpsCharge t := by
      have hop := ops_in_cell t
      calc
        fr'.opsCap = fr.opsCap + 2 := hops
        _ ≤ fr.opsCap + cellOpsCharge t := by omega
    exact spend_mul fr.opsCap fr'.opsCap (cellOpsCharge t) cellsLeft hleft hspend hO
  · have hspend : fr'.ctrl ≤ fr.ctrl + cellCtrlCharge t := by
      rw [hctrl]
      have hc5 := ctrl_in_cell t
      omega
    exact spend_mul fr.ctrl fr'.ctrl (cellCtrlCharge t) cellsLeft hleft hspend hC

/-- The cells still to run keep one charge each, and the cubes already counted
    sit in the spare charge. `base` is the counter the suffix started from. -/
private theorem budget_mul (len done left base now walk over : Nat)
    (hsum : done + left = len) (hov : over * len ≤ walk)
    (hm : now ≤ base + done * (walk + over))
    (hroom : FitsLen (base + (len + 1) * walk)) :
    FitsLen (now + left * walk) := by
  apply FitsLen.of_le hroom
  have hsplit : done * (walk + over) = done * walk + done * over := Nat.mul_add _ _ _
  have hm' : now ≤ base + (done * walk + done * over) := by
    rw [hsplit] at hm
    exact hm
  have hd : done ≤ len := by omega
  have hmul : over * done ≤ over * len := Nat.mul_le_mul_left over hd
  have hcap : done * over ≤ walk := by
    rw [Nat.mul_comm done over]
    exact Nat.le_trans hmul hov
  have hmix : done * walk + left * walk = len * walk := by
    rw [← Nat.add_mul, hsum]
  have hprod : (len + 1) * walk = len * walk + walk := by rw [Nat.succ_mul]
  omega

/-- Worst-case counter, plus one cube and the chords still left, inside the
    spare room `(len + 1) · walk`. -/
private theorem move_pot_le (len done left walk over cmove add moves : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hw : cmove ≤ walk) (hov : over * len ≤ walk)
    (hm : moves ≤ done * (walk + over)) (hadd : add ≤ over) :
    moves + add + left * cmove ≤ (len + 1) * walk := by
  have hsplit : done * (walk + over) = done * walk + done * over := Nat.mul_add _ _ _
  have hm' : moves ≤ done * walk + done * over := by
    rw [← hsplit]
    exact hm
  have hfac : done * over + over = (done + 1) * over := by rw [← Nat.succ_mul]
  have hd : done + 1 ≤ len := by omega
  have hmul : over * (done + 1) ≤ over * len := Nat.mul_le_mul_left over hd
  have hcap : (done + 1) * over ≤ walk := by
    rw [Nat.mul_comm (done + 1)]
    exact Nat.le_trans hmul hov
  have hleftM : left * cmove ≤ left * walk := Nat.mul_le_mul_left left hw
  have hsumW : done * walk + walk + left * walk = (done + 1 + left) * walk := by
    have h1 : (done + 1) * walk = done * walk + walk := by rw [Nat.succ_mul]
    have h2 : (done + 1 + left) * walk = (done + 1) * walk + left * walk := by
      rw [Nat.add_mul]
    omega
  have hlen : done + 1 + left = len + 1 := by omega
  have h1 : moves + add + left * cmove ≤ done * walk + (done + 1) * over + left * walk := by
    rw [← hfac]
    omega
  have h2 : done * walk + (done + 1) * over + left * walk ≤
      done * walk + walk + left * walk := by omega
  rw [hlen] at hsumW
  have h3 : moves + add + left * cmove ≤ done * walk + walk + left * walk :=
    Nat.le_trans h1 h2
  rw [← hsumW]
  exact h3

private theorem slide_pot_le (len n s done left slides : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 4 * n * len ≤ s) (hs : slides ≤ done * (s + 4 * n)) :
    slides + 4 * n + left * s ≤ (len + 1) * s := by
  have hsplit : done * (s + 4 * n) = done * s + done * (4 * n) := Nat.mul_add _ _ _
  have hs' : slides ≤ done * s + done * (4 * n) := by
    rw [← hsplit]
    exact hs
  have hfac : done * (4 * n) + 4 * n = (done + 1) * (4 * n) := by rw [← Nat.succ_mul]
  have hd : done + 1 ≤ len := by omega
  have hmul : (4 * n) * (done + 1) ≤ (4 * n) * len := Nat.mul_le_mul_left _ hd
  have hcap : (done + 1) * (4 * n) ≤ s := by
    rw [Nat.mul_comm (done + 1)]
    exact Nat.le_trans hmul hov
  have hprod : (len + 1) * s = (done + 1 + left) * s := by
    have : len + 1 = done + 1 + left := by omega
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

private theorem ctrl_pot_le (len c done left ctrl : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 4 * len ≤ c) (hc : ctrl ≤ done * (c + 4)) :
    ctrl + 4 + left * c ≤ (len + 1) * c := by
  have hsplit : done * (c + 4) = done * c + 4 * done := by
    rw [Nat.mul_add, Nat.mul_comm 4 done]
  have hc' : ctrl ≤ done * c + 4 * done := by
    rw [← hsplit]
    exact hc
  have hfac : 4 * done + 4 = 4 * (done + 1) := by rw [Nat.mul_succ]
  have hd : done + 1 ≤ len := by omega
  have hmul : 4 * (done + 1) ≤ 4 * len := Nat.mul_le_mul_left 4 hd
  have hcap : 4 * (done + 1) ≤ c := Nat.le_trans hmul hov
  have hprod : (len + 1) * c = (done + left + 1) * c := by
    have : len = done + left := by omega
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

private theorem ops_pot_le (len c done left ops : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 2 * len + 2 ≤ c) (ho : ops ≤ done * (c + 2)) :
    ops + 2 + left * c ≤ (len + 1) * c := by
  have hsplit : done * (c + 2) = done * c + 2 * done := by
    rw [Nat.mul_add]
    omega
  have hops' : ops ≤ done * c + 2 * done := by
    rw [← hsplit]
    exact ho
  have hmix : done * c + left * c = len * c := by
    rw [← Nat.add_mul, hsum]
  have htwo : 2 * done + 2 ≤ 2 * len := by
    have hd : done ≤ len - 1 := by omega
    omega
  have hspan' : 2 * len ≤ c := by omega
  have hsmall : 2 * done + 2 ≤ c := Nat.le_trans htwo hspan'
  have hprod : (len + 1) * c = len * c + c := by rw [Nat.succ_mul]
  have h0 : ops + 2 + left * c ≤ done * c + left * c + 2 * done + 2 := by omega
  have h1 : done * c + left * c + 2 * done + 2 = len * c + 2 * done + 2 := by
    rw [hmix]
  have h2 : len * c + 2 * done + 2 ≤ len * c + c := by omega
  have hbound : ops + 2 + left * c ≤ len * c + c :=
    Nat.le_trans h0 (h1.symm ▸ h2)
  rw [hprod]
  exact hbound

private theorem post_move (t : Spec.Tier) (len done left mv0 moves moves' : Nat)
    (hsum : done + left = len) (hleft : 0 < left) (hn : t.n ≤ t.benchlen)
    (hov : (6 * t.benchlen + 2 * t.n) * len ≤ walkCharge t)
    (hm : moves ≤ mv0 + done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hmv : moves' ≤ moves + cubeCharge t.n t.benchlen)
    (hroom : FitsLen (mv0 + (len + 1) * walkCharge t)) :
    FitsLen (moves' + left * cellMoveCharge t) := by
  have hcm : cellMoveCharge t ≤ walkCharge t := cellMove_le_walk t
  have hadd : cubeCharge t.n t.benchlen ≤ 6 * t.benchlen + 2 * t.n :=
    Nat.le_of_eq (cube_over t.n t.benchlen hn)
  have hworst := move_pot_le len done left (walkCharge t) (6 * t.benchlen + 2 * t.n)
    (cellMoveCharge t) (cubeCharge t.n t.benchlen)
    (done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    hsum hleft hcm hov (Nat.le_refl _) hadd
  apply FitsLen.of_le hroom
  have hstep : moves' + left * cellMoveCharge t ≤
      moves + cubeCharge t.n t.benchlen + left * cellMoveCharge t := by omega
  have hpre : moves + cubeCharge t.n t.benchlen + left * cellMoveCharge t ≤
      mv0 + (done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) +
        cubeCharge t.n t.benchlen + left * cellMoveCharge t) := by omega
  exact Nat.le_trans hstep (Nat.le_trans hpre (Nat.add_le_add_left hworst mv0))

private theorem post_slide (len done left n sl0 slides slides' s : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 4 * n * len ≤ s)
    (hs : slides ≤ sl0 + done * (s + 4 * n))
    (hsl : slides' ≤ slides + 4 * n)
    (hroom : FitsLen (sl0 + (len + 1) * s)) :
    FitsLen (slides' + left * s) := by
  have hworst := slide_pot_le len n s done left (done * (s + 4 * n))
    hsum hleft hov (Nat.le_refl _)
  apply FitsLen.of_le hroom
  have hpre : slides + 4 * n + left * s ≤
      sl0 + (done * (s + 4 * n) + 4 * n + left * s) := by omega
  exact Nat.le_trans (by omega) (Nat.le_trans hpre (Nat.add_le_add_left hworst sl0))

private theorem post_ctrl (len done left ct0 ctrl ctrl' c : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 4 * len ≤ c)
    (hc : ctrl ≤ ct0 + done * (c + 4))
    (hctrl : ctrl' ≤ ctrl + 4)
    (hroom : FitsLen (ct0 + (len + 1) * c)) :
    FitsLen (ctrl' + left * c) := by
  have hworst := ctrl_pot_le len c done left (done * (c + 4)) hsum hleft hov (Nat.le_refl _)
  apply FitsLen.of_le hroom
  have hpre : ctrl + 4 + left * c ≤ ct0 + (done * (c + 4) + 4 + left * c) := by omega
  exact Nat.le_trans (by omega) (Nat.le_trans hpre (Nat.add_le_add_left hworst ct0))

private theorem post_ops (len done left op0 ops ops' c : Nat)
    (hsum : done + left = len) (hleft : 0 < left)
    (hov : 2 * len + 2 ≤ c)
    (ho : ops ≤ op0 + done * (c + 2))
    (hops : ops' ≤ ops + 2)
    (hroom : FitsLen (op0 + (len + 1) * c)) :
    FitsLen (ops' + left * c) := by
  have hworst := ops_pot_le len c done left (done * (c + 2)) hsum hleft hov (Nat.le_refl _)
  apply FitsLen.of_le hroom
  have hpre : ops + 2 + left * c ≤ op0 + (done * (c + 2) + 2 + left * c) := by omega
  exact Nat.le_trans (by omega) (Nat.le_trans hpre (Nat.add_le_add_left hworst op0))

private theorem base_next (base done cap spent now next : Nat)
    (hnow : now ≤ base + done * cap) (hstep : next ≤ now + spent) (hspent : spent ≤ cap) :
    next ≤ base + (done + 1) * cap := by
  have h : (done + 1) * cap = done * cap + cap := by rw [Nat.succ_mul]
  omega

/-- Moves through cell `done`, charged as `(done + 1)` suffix steps above `mv0`. -/
def suffixMoveCap (t : Spec.Tier) (mv0 done : Nat) : Nat :=
  mv0 + (done + 1) * (walkCharge t + (6 * t.benchlen + 2 * t.n))

/-- Slides through cell `done`, charged the same way. -/
def suffixSlideCap (t : Spec.Tier) (sl0 done : Nat) : Nat :=
  sl0 + (done + 1) * (cellSlideCharge t + 4 * t.n)

/-- The cubed frame plus one chord is one suffix step. -/
private theorem move_cap_le (t : Spec.Tier) (mv0 done toN mv mvF : Nat)
    (hn : t.n ≤ t.benchlen)
    (hm : mv ≤ mv0 + done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hmvF : mvF ≤ mv + cubeCharge t.n t.benchlen)
    (hdone : done = toN) :
    mvF + walkCharge t ≤ suffixMoveCap t mv0 toN := by
  have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ hn
  have hmvF' : mvF ≤ mv + (6 * t.benchlen + 2 * t.n) := by
    rw [← hcube]
    exact hmvF
  have hstep : mvF + walkCharge t ≤
      mv + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
    generalize wEq : walkCharge t = w
    generalize oEq : 6 * t.benchlen + 2 * t.n = o
    have hmv : mvF ≤ mv + o := by
      rw [← oEq]
      exact hmvF'
    clear wEq oEq
    calc
      mvF + w ≤ (mv + o) + w := Nat.add_le_add_right hmv _
      _ = mv + (w + o) := by rw [Nat.add_assoc, Nat.add_comm o w]
  have hbase := base_next mv0 done (walkCharge t + (6 * t.benchlen + 2 * t.n))
    (walkCharge t + (6 * t.benchlen + 2 * t.n)) mv (mvF + walkCharge t)
    hm hstep (Nat.le_refl _)
  rw [hdone] at hbase
  rw [suffixMoveCap]
  exact hbase

/-- The cube's slides plus one chord slide charge are one suffix step. -/
private theorem slide_cap_le (t : Spec.Tier) (sl0 done toN sl slF : Nat)
    (hs : sl ≤ sl0 + done * (cellSlideCharge t + 4 * t.n))
    (hslF : slF ≤ sl + 4 * t.n)
    (hdone : done = toN) :
    slF + cellSlideCharge t ≤ suffixSlideCap t sl0 toN := by
  have hstep : slF + cellSlideCharge t ≤ sl + (cellSlideCharge t + 4 * t.n) := by
    generalize cEq : cellSlideCharge t = c
    generalize oEq : 4 * t.n = o
    have hsl : slF ≤ sl + o := by
      rw [← oEq]
      exact hslF
    clear cEq oEq
    calc
      slF + c ≤ (sl + o) + c := Nat.add_le_add_right hsl _
      _ = sl + (c + o) := by rw [Nat.add_assoc, Nat.add_comm o c]
  have hbase := base_next sl0 done (cellSlideCharge t + 4 * t.n)
    (cellSlideCharge t + 4 * t.n) sl (slF + cellSlideCharge t)
    hs hstep (Nat.le_refl _)
  rw [hdone] at hbase
  rw [suffixSlideCap]
  exact hbase

private theorem cell_eq (cells : List Nat) (i : Nat) (h1 h2 : i < cells.length) :
    cells[i]'h1 = cells[i]'h2 := rfl

private theorem suffix_zero_step (cells : List Nat) (i toN : Nat) (b bL bF : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1) (hiLen : i < cells.length)
    (hz : cells[i]'hiLen = 0)
    (hml : Ecbs.marker_lift b = .ok bL)
    (hfrob : Ecbs.frobenius_affine bL = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
      (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bF, true)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bF, true)))) := by
  have hzO : cells[i]'(by omega) = 0 := (cell_eq cells i hiLen (by omega)).trans hz
  exact chordStep_cube cells i toN b bL bF hi hlen hzO hml hfrob hfiti

private theorem walk_step_cube (n k bench : Nat) (base acc : List Nat × List Nat) :
    walkStep n k bench base true acc 0 =
      some (true, (fieldCube n k bench acc.1, fieldCube n k bench acc.2)) := by
  unfold walkStep pointCube
  simp

private theorem colour_beq (c : Nat) (hc : c = 1 ∨ c = 2) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rcases hc with rfl | rfl <;> decide

private theorem cube_trits (t : Spec.Tier) (sat : TierSat t) (hsh : TierShape t)
    (xs : List Nat) (hxs : allTritList xs) :
    allTritList (fieldCube t.n t.k t.benchlen xs) := by
  apply fieldCube_trits t.n t.k t.benchlen xs hxs
  · have h := sat.cube_span
    omega
  · exact hsh.k_le

private theorem chord_y_trits (n k bench : Nat) (slope dx y : List Nat) :
    allTritList (chordY3 n k bench slope dx y) := by
  simpa [chordY3, fieldSub] using
    fieldAdd_span_trits n (fieldMul n k bench slope dx) (mirrorTrits y)

private theorem chord_y_len (n k bench : Nat) (slope dx y : List Nat) :
    (chordY3 n k bench slope dx y).length = n := by
  simpa [chordY3] using fieldSub_length n (fieldMul n k bench slope dx) y

/-- What the last cell leaves besides the new point: the bench is off, the base
    homes are still seated, and the counters are naturals under the suffix
    budget `moveCap` and `slideCap`. -/
structure LastLay (b : Ecbs.Board) (baseX baseY : List Nat)
    (moveCap slideCap : Nat) : Prop where
  bench : b.sudo_5Board_8bench_on = false
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  held0 : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = true
  held1 : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true
  home3 : ∀ h : 3 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[3] = embed baseX
  held3 : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
  home4 : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4] = embed baseY
  held4 : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4] = true
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧ mv ≤ moveCap
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    sl ≤ slideCap
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk

/-- A larger budget still covers the same counters. -/
theorem LastLay.mono {b : Ecbs.Board} {baseX baseY : List Nat}
    {capM capS capM' capS' : Nat}
    (hM : capM ≤ capM') (hS : capS ≤ capS')
    (lay : LastLay b baseX baseY capM capS) :
    LastLay b baseX baseY capM' capS' where
  bench := lay.bench
  szH := lay.szH
  szD := lay.szD
  held0 := lay.held0
  held1 := lay.held1
  home3 := lay.home3
  held3 := lay.held3
  home4 := lay.home4
  held4 := lay.held4
  moves := (by
    obtain ⟨mv, hmv, hle⟩ := lay.moves
    exact ⟨mv, hmv, Nat.le_trans hle hM⟩)
  slides := (by
    obtain ⟨sl, hsl, hle⟩ := lay.slides
    exact ⟨sl, hsl, Nat.le_trans hle hS⟩)
  peak := lay.peak

/-- The last live cell. The chord rooms are one charge on the cubed frame. -/
private theorem suffix_live_last (cells : List Nat) (i toN c : Nat)
    (b0 b bF : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat)
    (fr : RunFrame bF t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : bF.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hMove : FitsLen (fr.moves + cellMoveCharge t))
    (hSlide : FitsLen (fr.slides + cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + cellOpsCharge t))
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hholeFr : fr.hole ≤ t.benchlen)
    (hi : i = toN) (hlen : cells.length = toN + 1)
    (hiLen : i < cells.length)
    (hcAt : cells[i]'hiLen = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ b' ax ay,
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
        .ok (SudoRt.Flow.brk (Int.ofNat i, (b', true))) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY)
        (cells[i]'hiLen) = some (true, (ax, ay)) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed ax) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed ay) ∧
      ∃ m ctrl,
        b'.sudo_5Board_6marker = Int.ofNat m ∧
        b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
        FitsLen (ctrl + 1) ∧
      LastLay b' baseX baseY (fr.moves + walkCharge t)
        (fr.slides + cellSlideCharge t) := by
  have hMoveR : FitsLen (liveMoveRoom t fr.moves baseX accX) := by
    apply FitsLen.of_le hMove
    exact live_move_le t fr.moves baseX accX fr.lenX fr.lenA
  have hSlideR : FitsLen (liveSlideRoom t fr.slides) := by
    rw [live_slide_eq]
    exact hSlide
  have hCtrlR : FitsLen (liveCtrlRoom t fr.ctrl) := by
    rw [live_ctrl_eq]
    exact hCtrl
  have hOpsR : FitsLen (liveOpsRoom t fr.opsCap) := by
    rw [live_ops_eq]
    exact hOps
  obtain ⟨b', hdemo, hx0, hy1, hwalk, _hhigh, _hbud, _bI, _mv0, _pack, _cap,
      _sl, _ho, _flag, hlift⟩ :=
    chord_add_live bF t baseX accX baseY accY preX preY inv c fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hMoveR hSlideR hCtrlR hOpsR hMark hMarkF hholeFr
  have hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, b') := by
    rw [colour_beq c hc]
    exact hdemo
  have hcOpen : cells[i]'(by omega) = c := (cell_eq cells i hiLen (by omega)).trans hcAt
  have hstep := chordStep_open cells i toN c b0 b bF b' (Nat.le_of_eq hi) hlen hcOpen hc0 hc2
    hml hfrob hadd hfiti
  obtain ⟨bud, hL, _, hmoveEq, _, _⟩ := _hbud
  obtain ⟨mvL, hmvL, hmvLe⟩ := hL.movesLe
  obtain ⟨slL, hslL, hslLe⟩ := _sl
  obtain ⟨pkL, hpkL⟩ := _pack.peak
  have hlive := live_move_le t fr.moves baseX accX fr.lenX fr.lenA
  have hmvCap : mvL ≤ fr.moves + walkCharge t := by
    have hcomm : checkMoveCap bud + 2 * t.n + tailMoveCap t.n t.benchlen =
        checkMoveCap bud + tailMoveCap t.n t.benchlen + 2 * t.n := by
      rw [Nat.add_right_comm]
    have hroom : checkMoveCap bud + tailMoveCap t.n t.benchlen + 2 * t.n =
        liveMoveRoom t fr.moves baseX accX + 2 * t.n := by
      rw [hmoveEq]
    calc
      mvL ≤ checkMoveCap bud + 2 * t.n + tailMoveCap t.n t.benchlen := hmvLe
      _ = liveMoveRoom t fr.moves baseX accX + 2 * t.n := by rw [hcomm, hroom]
      _ ≤ fr.moves + cellMoveCharge t + 2 * t.n := Nat.add_le_add_right hlive _
      _ = fr.moves + walkCharge t := by rw [Nat.add_assoc, walkCharge_split]
  have hslCap : slL ≤ fr.slides + cellSlideCharge t := by
    rw [live_slide_eq] at hslLe
    exact hslLe
  have hlay : LastLay b' baseX baseY (fr.moves + walkCharge t)
      (fr.slides + cellSlideCharge t) :=
    { bench := _pack.benchOff
      szH := _pack.szH
      szD := _pack.szD
      held0 := _pack.held0
      held1 := _pack.held1
      home3 := hL.home3
      held3 := hL.held3
      home4 := hL.home4
      held4 := hL.held4
      moves := ⟨mvL, hmvL, hmvCap⟩
      slides := ⟨slL, hslL, hslCap⟩
      peak := ⟨pkL, hpkL⟩ }
  obtain ⟨m, c, hm, hc, hfit⟩ := hlift
  exact ⟨b', _, _, by simpa [hi] using hstep, by simpa [← hcAt] using hwalk, hx0, hy1,
    ⟨m, c, hm, hc, hfit, hlay⟩⟩

/-- A live cell with another cell after it. `fuel + 1` charges are the cells
    still left, including this one. -/
private theorem suffix_live_next (cells : List Nat) (i toN c fuel : Nat)
    (b0 b bF : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat)
    (fr : RunFrame bF t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : bF.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hFuel : 1 ≤ fuel)
    (hMove : FitsLen (fr.moves + (fuel + 1) * cellMoveCharge t))
    (hSlide : FitsLen (fr.slides + (fuel + 1) * cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + (fuel + 1) * cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + (fuel + 1) * cellOpsCharge t))
    (hst7 : fr.peakS ≤ 7) (hholeFr : fr.hole ≤ t.benchlen)
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hi : i < toN) (hlen : cells.length = toN + 1)
    (hiLen : i < cells.length)
    (hcAt : cells[i]'hiLen = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ b' x3 y3, ∃ fr' : RunFrame b' t baseX x3,
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b', true)))) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY)
        (cells[i]'hiLen) = some (true, (x3, y3)) ∧
      b'.sudo_5Board_9marker_on = true ∧
      fr'.y4 = baseY ∧ fr'.y1 = y3 ∧
      fr'.flag4 = true ∧ fr'.flag1 = true ∧
      fr'.peakS ≤ 7 ∧ fr'.hole ≤ t.benchlen ∧
      fr'.moves ≤ fr.moves + walkCharge t ∧
      fr'.slides ≤ fr.slides + cellSlideCharge t ∧
      fr'.ctrl ≤ fr.ctrl + cellCtrlCharge t ∧
      fr'.opsCap = fr.opsCap + cellOpsCharge t ∧
      y3.length = t.n ∧ allTritList y3 := by
  obtain ⟨b', x3, y3, hdemo, _hx3, hy3, hwalk, fr', hops', hmv', hctrl', hsl',
      hst', hho', hy1', hy4', hf1', hf4', hmk'⟩ :=
    chord_add_live_frame bF t baseX accX baseY accY preX preY inv c fuel fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hFuel hMove hSlide hCtrl hOps hst7 hholeFr hMark hMarkF
  have hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, b') := by
    rw [colour_beq c hc]
    exact hdemo
  have hcOpen : cells[i]'(by omega) = c := (cell_eq cells i hiLen (by omega)).trans hcAt
  have hstep := chordStep_open cells i toN c b0 b bF b' (Nat.le_of_lt hi) hlen hcOpen hc0 hc2
    hml hfrob hadd hfiti
  have htriY3 : allTritList y3 := by
    rw [hy3]
    exact chord_y_trits _ _ _ _ _ _
  have hlenY3 : y3.length = t.n := by
    rw [hy3]
    exact chord_y_len _ _ _ _ _ _
  exact ⟨b', x3, y3, fr', hstep, by simpa [← hcAt] using hwalk, hmk', hy4', hy1',
    hf4', hf1', hst', hho', hmv', hsl', hctrl', hops', hlenY3, htriY3⟩

/-- One cell after `suffix_frob`. A zero cell is the cubed frame. A live cell
    is that frame plus the chord. The room is `(len + 1)` charges on top of the
    counters the suffix started from, and one `walkCharge` covers every cube
    (`over · len ≤ walkCharge`). `left = 1` is the last cell. Proof-only. -/
theorem suffix_chord_add (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (len done left mv0 sl0 ct0 op0 c : Nat) (cells : List Nat) (i toN : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (htriB : allTritList baseY)
    (hyA : accY.length = t.n) (htriA : allTritList accY)
    (hsum : done + left = len) (hleft : 0 < left)
    (hn : t.n ≤ t.benchlen)
    (hmoveOver : (6 * t.benchlen + 2 * t.n) * len ≤ walkCharge t)
    (hslideOver : 4 * t.n * len ≤ cellSlideCharge t)
    (hctrlOver : 4 * len ≤ cellCtrlCharge t)
    (hopsOver : 2 * len + 2 ≤ cellOpsCharge t)
    (hm : fr.moves ≤ mv0 + done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : fr.slides ≤ sl0 + done * (cellSlideCharge t + 4 * t.n))
    (hc0 : fr.ctrl ≤ ct0 + done * (cellCtrlCharge t + 4))
    (ho : fr.opsCap ≤ op0 + done * (cellOpsCharge t + 2))
    (hRoomM : FitsLen (mv0 + (len + 1) * walkCharge t))
    (hRoomS : FitsLen (sl0 + (len + 1) * cellSlideCharge t))
    (hRoomC : FitsLen (ct0 + (len + 1) * cellCtrlCharge t))
    (hRoomO : FitsLen (op0 + (len + 1) * cellOpsCharge t))
    (hst : fr.peakS ≤ 7) (hhole : fr.hole ≤ t.benchlen)
    (hscript : 4 < t.script)
    (hdone : done = i) (hto : toN + 1 = len)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hiLen : i < cells.length)
    (hcAt : cells[i]'hiLen = c) (hcLe : c ≤ 2)
    (hfiti : FitsLen (i + 1))
    (hinv : c ≠ 0 →
      ∃ inv, fieldInv t.n t.k t.benchlen
        (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX)) = some inv) :
    ∃ b' ax' ay',
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b', true)))) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (accX, accY)
        (cells[i]'hiLen) = some (true, (ax', ay')) ∧
      (i < toN →
        ∃ fr' : RunFrame b' t baseX ax',
          b'.sudo_5Board_9marker_on = true ∧
          fr'.y4 = baseY ∧ fr'.y1 = ay' ∧
          fr'.flag4 = true ∧ fr'.flag1 = true ∧
          fr'.peakS ≤ 7 ∧ fr'.hole ≤ t.benchlen ∧
          fr'.moves ≤ mv0 + (done + 1) * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
          fr'.slides ≤ sl0 + (done + 1) * (cellSlideCharge t + 4 * t.n) ∧
          fr'.ctrl ≤ ct0 + (done + 1) * (cellCtrlCharge t + 4) ∧
          fr'.opsCap ≤ op0 + (done + 1) * (cellOpsCharge t + 2) ∧
          ay'.length = t.n ∧ allTritList ay') ∧
      (i = toN →
        (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed ax') ∧
        (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed ay') ∧
        ∃ m ctrl,
          b'.sudo_5Board_6marker = Int.ofNat m ∧
          b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
          FitsLen (ctrl + 1) ∧
          LastLay b' baseX baseY (suffixMoveCap t mv0 toN)
            (suffixSlideCap t sl0 toN)) := by
  have hMrel : FitsLen (fr.moves + walkCharge t * left) := by
    simpa [Nat.mul_comm] using
      budget_mul len done left mv0 fr.moves (walkCharge t) (6 * t.benchlen + 2 * t.n)
        hsum hmoveOver hm hRoomM
  have hSrel : FitsLen (fr.slides + cellSlideCharge t * left) := by
    simpa [Nat.mul_comm] using
      budget_mul len done left sl0 fr.slides (cellSlideCharge t) (4 * t.n) hsum hslideOver hs hRoomS
  have hCrel : FitsLen (fr.ctrl + cellCtrlCharge t * left) := by
    simpa [Nat.mul_comm] using
      budget_mul len done left ct0 fr.ctrl (cellCtrlCharge t) 4 hsum hctrlOver hc0 hRoomC
  have hOrel : FitsLen (fr.opsCap + cellOpsCharge t * left) := by
    have hov : 2 * len ≤ cellOpsCharge t := by omega
    simpa [Nat.mul_comm] using
      budget_mul len done left op0 fr.opsCap (cellOpsCharge t) 2 hsum hov ho hRoomO
  obtain ⟨bL, bF, frF, hml, hfrob, hmkF, hy1F, hy4F, hf1F, hf4F, hmarkF, hmvF, hslF,
      hctrlF, hopsF, hstF, hhoF, _hMf, _hSf, _hOf, _hCf⟩ :=
    suffix_frob t b baseX accX baseY accY fr left hOk sat hsh hmk hY hA hf4 hf1
      hyA htriA hleft hst hhole hMrel hSrel hOrel hCrel
  have hMoveF : FitsLen (frF.moves + left * cellMoveCharge t) :=
    post_move t len done left mv0 fr.moves frF.moves hsum hleft hn hmoveOver hm hmvF hRoomM
  have hSlideF : FitsLen (frF.slides + left * cellSlideCharge t) := by
    have hsl4 : frF.slides ≤ fr.slides + 4 * t.n := by
      rw [slide_over_eq] at hslF
      exact hslF
    exact post_slide len done left t.n sl0 fr.slides frF.slides (cellSlideCharge t)
      hsum hleft hslideOver hs hsl4 hRoomS
  have hCtrlF : FitsLen (frF.ctrl + left * cellCtrlCharge t) :=
    post_ctrl len done left ct0 fr.ctrl frF.ctrl (cellCtrlCharge t)
      hsum hleft hctrlOver hc0 (Nat.le_of_eq hctrlF) hRoomC
  have hOpsF : FitsLen (frF.opsCap + left * cellOpsCharge t) :=
    post_ops len done left op0 fr.opsCap frF.opsCap (cellOpsCharge t)
      hsum hleft hopsOver ho (Nat.le_of_eq hopsF) hRoomO
  by_cases hz : c = 0
  · have hzAt : cells[i]'hiLen = 0 := by
      rw [hcAt]
      exact hz
    have hstep := suffix_zero_step cells i toN b bL bF hi hlen hiLen hzAt hml hfrob hfiti
    have hwalk := walk_step_cube t.n t.k t.benchlen (baseX, baseY) (accX, accY)
    let ax' := fieldCube t.n t.k t.benchlen accX
    let ay' := fieldCube t.n t.k t.benchlen accY
    refine ⟨bF, ax', ay', by simpa [hzAt] using hstep, by simpa [hzAt] using hwalk, ?_, ?_⟩
    · intro _hlt
      have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
        cube_over _ _ hn
      have hstepM : frF.moves ≤ fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
        calc
          frF.moves ≤ fr.moves + cubeCharge t.n t.benchlen := hmvF
          _ = fr.moves + (6 * t.benchlen + 2 * t.n) := by rw [hcube]
          _ ≤ fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by omega
      have hstepS : frF.slides ≤ fr.slides + (cellSlideCharge t + 4 * t.n) := by
        rw [slide_over_eq] at hslF
        omega
      have hstepC : frF.ctrl ≤ fr.ctrl + (cellCtrlCharge t + 4) := by
        rw [hctrlF]
        omega
      have hstepO : frF.opsCap ≤ fr.opsCap + (cellOpsCharge t + 2) := by
        rw [hopsF]
        omega
      refine ⟨frF, hmkF, hy4F, hy1F, hf4F, hf1F, hstF, hhoF,
        base_next mv0 done _ _ fr.moves frF.moves hm hstepM (Nat.le_refl _),
        base_next sl0 done _ _ fr.slides frF.slides hs hstepS (Nat.le_refl _),
        base_next ct0 done _ _ fr.ctrl frF.ctrl hc0 hstepC (Nat.le_refl _),
        base_next op0 done _ _ fr.opsCap frF.opsCap ho hstepO (Nat.le_refl _),
        fieldCube_length t.n t.k t.benchlen accY hn,
        cube_trits t sat hsh accY htriA⟩
    · intro hlastZ
      have hdoneT : done = toN := hdone.trans hlastZ
      have hmoveCap := move_cap_le t mv0 done toN fr.moves frF.moves hn hm hmvF hdoneT
      have hleM : frF.moves ≤ suffixMoveCap t mv0 toN :=
        Nat.le_trans (Nat.le_add_right frF.moves (walkCharge t)) hmoveCap
      have hsl4 : frF.slides ≤ fr.slides + 4 * t.n := by
        rw [slide_over_eq] at hslF
        exact hslF
      have hslideCap := slide_cap_le t sl0 done toN fr.slides frF.slides hs hsl4 hdoneT
      have hleS : frF.slides ≤ suffixSlideCap t sl0 toN :=
        Nat.le_trans (Nat.le_add_right frF.slides (cellSlideCharge t)) hslideCap
      refine ⟨?_, ?_, ?_⟩
      · intro _h0
        exact frF.home0
      · intro _h1
        simpa [hy1F] using frF.home1
      · exact ⟨frF.mark, frF.ctrl, frF.hmark, frF.hctrl, frF.fitCtrl,
          { bench := frF.bench
            szH := frF.szH
            szD := frF.szD
            held0 := fun _ => frF.held0
            held1 := fun _ => by simpa [hf1F] using frF.held1
            home3 := fun _ => frF.home3
            held3 := fun _ => frF.held3
            home4 := fun _ => by simpa [hy4F] using frF.home4
            held4 := fun _ => by simpa [hf4F] using frF.held4
            moves := ⟨frF.moves, frF.hmoves, hleM⟩
            slides := ⟨frF.slides, frF.hslides, hleS⟩
            peak := ⟨frF.peak, frF.hpeak⟩ }⟩
  · have hcLive : c = 1 ∨ c = 2 := by
      have hle := hcLe
      omega
    obtain ⟨inv, hacc⟩ := hinv hz
    have hyCube : (fieldCube t.n t.k t.benchlen accY).length = t.n :=
      fieldCube_length t.n t.k t.benchlen accY hn
    have htriCube : allTritList (fieldCube t.n t.k t.benchlen accY) :=
      cube_trits t sat hsh accY htriA
    have hMark : frF.mark + 3 < t.script := by
      rw [hmarkF]
      omega
    have hMarkFit : FitsLen (frF.mark + 4) := by
      rw [hmarkF]
      unfold FitsLen i64MaxNat
      decide
    by_cases hlast : i = toN
    · have hleft1 : left = 1 := by omega
      have hMove1 : FitsLen (frF.moves + cellMoveCharge t) := by
        rw [hleft1, Nat.one_mul] at hMoveF
        exact hMoveF
      have hSlide1 : FitsLen (frF.slides + cellSlideCharge t) := by
        rw [hleft1, Nat.one_mul] at hSlideF
        exact hSlideF
      have hCtrl1 : FitsLen (frF.ctrl + cellCtrlCharge t) := by
        rw [hleft1, Nat.one_mul] at hCtrlF
        exact hCtrlF
      have hOps1 : FitsLen (frF.opsCap + cellOpsCharge t) := by
        rw [hleft1, Nat.one_mul] at hOpsF
        exact hOpsF
      clear hMoveF hSlideF hCtrlF hOpsF hMrel hSrel hCrel hOrel
      obtain ⟨b', ax', ay', hstep, hwalk, hx0, hy1, hlift⟩ :=
        suffix_live_last cells i toN c b bL bF t baseX
          (fieldCube t.n t.k t.benchlen accX) baseY (fieldCube t.n t.k t.benchlen accY)
          accX accY inv frF hOk sat hR hsh hmkF hcLive hy4F hy1F hf4F hf1F
          hyB hyCube htriB htriCube rfl rfl hacc hMove1 hSlide1 hCtrl1 hOps1
          hMark hMarkFit hhoF hlast hlen hiLen hcAt hz hcLe hml hfrob hfiti
      have hdoneT : done = toN := hdone.trans hlast
      have hmoveCap := move_cap_le t mv0 done toN fr.moves frF.moves hn hm hmvF hdoneT
      have hsl4 : frF.slides ≤ fr.slides + 4 * t.n := by
        rw [slide_over_eq] at hslF
        exact hslF
      have hslideCap := slide_cap_le t sl0 done toN fr.slides frF.slides hs hsl4 hdoneT
      obtain ⟨m, cctrl, hm, hc, hfit, hlay⟩ := hlift
      refine ⟨b', ax', ay', by simpa [hlast] using hstep, hwalk,
        fun hlt => absurd hlast (by omega),
        fun _ => ⟨hx0, hy1, ⟨m, cctrl, hm, hc, hfit, hlay.mono hmoveCap hslideCap⟩⟩⟩
    · have hlt : i < toN := by omega
      have hge : 2 ≤ left := by omega
      have hfuel : 1 ≤ left - 1 := by
        have h := hge
        omega
      have hleftEq : left - 1 + 1 = left := by omega
      have hMove : FitsLen (frF.moves + (left - 1 + 1) * cellMoveCharge t) := by
        rw [hleftEq]
        exact hMoveF
      have hSlide : FitsLen (frF.slides + (left - 1 + 1) * cellSlideCharge t) := by
        rw [hleftEq]
        exact hSlideF
      have hCtrl : FitsLen (frF.ctrl + (left - 1 + 1) * cellCtrlCharge t) := by
        rw [hleftEq]
        exact hCtrlF
      have hOps : FitsLen (frF.opsCap + (left - 1 + 1) * cellOpsCharge t) := by
        rw [hleftEq]
        exact hOpsF
      obtain ⟨b', x3, y3, fr', hstep, hwalk, hmk', hy4', hy1', hf4', hf1', hst', hho',
          hmv', hsl', hctrl', hops', hlenY3, htriY3⟩ :=
        suffix_live_next cells i toN c (left - 1) b bL bF t baseX
          (fieldCube t.n t.k t.benchlen accX) baseY (fieldCube t.n t.k t.benchlen accY)
          accX accY inv frF hOk sat hR hsh hmkF hcLive hy4F hy1F hf4F hf1F
          hyB hyCube htriB htriCube rfl rfl hacc hfuel hMove hSlide hCtrl hOps
          hstF hhoF hMark hMarkFit hlt hlen hiLen hcAt hz hcLe hml hfrob hfiti
      have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
        cube_over _ _ hn
      have hstepM : fr'.moves ≤ fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
        calc
          fr'.moves ≤ frF.moves + walkCharge t := hmv'
          _ ≤ fr.moves + cubeCharge t.n t.benchlen + walkCharge t :=
            Nat.add_le_add_right hmvF _
          _ = fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
            rw [hcube]; omega
      have hstepS : fr'.slides ≤ fr.slides + (cellSlideCharge t + 4 * t.n) := by
        have hsl4 : frF.slides ≤ fr.slides + 4 * t.n := by
          rw [slide_over_eq] at hslF
          exact hslF
        calc
          fr'.slides ≤ frF.slides + cellSlideCharge t := hsl'
          _ ≤ fr.slides + 4 * t.n + cellSlideCharge t := Nat.add_le_add_right hsl4 _
          _ = fr.slides + (cellSlideCharge t + 4 * t.n) := by omega
      have hstepC : fr'.ctrl ≤ fr.ctrl + (cellCtrlCharge t + 4) := by
        have hctrl4 : frF.ctrl = fr.ctrl + 4 := hctrlF
        omega
      have hstepO : fr'.opsCap ≤ fr.opsCap + (cellOpsCharge t + 2) := by
        have hops2 : frF.opsCap = fr.opsCap + 2 := hopsF
        rw [hops', hops2]
        omega
      refine ⟨b', x3, y3, hstep, hwalk, ?_, fun h => absurd h (by omega)⟩
      intro _
      refine ⟨fr', hmk', hy4', hy1', hf4', hf1', hst', hho',
        base_next mv0 done _ _ fr.moves fr'.moves hm hstepM (Nat.le_refl _),
        base_next sl0 done _ _ fr.slides fr'.slides hs hstepS (Nat.le_refl _),
        base_next ct0 done _ _ fr.ctrl fr'.ctrl hc0 hstepC (Nat.le_refl _),
        base_next op0 done _ _ fr.opsCap fr'.opsCap ho hstepO (Nat.le_refl _),
        hlenY3, htriY3⟩

end EcbsLink2.Link2
