/-
  A nonzero cell, packed as the next `FformAt`. The cube counter steps by 3
  and the multiply counter steps by 12, which is inside the 13-cell slack.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAddCell
import EcbsLink2.Link2.FformAtPack
import EcbsLink2.Link2.FformCellStep
import EcbsLink2.Link2.FformSumRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- `CellAt` is the frame once homes 3 and 4 are the base point. -/
theorem frame_of_cell (t : Spec.Tier) (b : Ecbs.Board) (lane : List Nat)
    (v z x2 y2 x3 yUp : List Nat) (tier : Ecbs.Tier) (szH szD : Nat)
    (baseX baseY : List Nat)
    (c : CellAt b lane t.n t.k t.benchlen v z x2 y2 x3 yUp tier szH szD)
    (hx2 : x2 = baseX) (hy2 : y2 = baseY)
    (ht : tier = embTier t) (hszH : szH = 8) (hszD : szD = 8) :
    FrameAt b t baseX baseY := {
  tier := c.tierEq.trans ht
  szH := c.szH.trans hszH
  szD := c.szD.trans hszD
  home3 := fun h => (c.home3 h).trans (congrArg embed hx2)
  held3 := c.held3
  home4 := fun h => (c.home4 h).trans (congrArg embed hy2)
  held4 := c.held4
}

theorem sum_ops_seven (c : Nat) : ((c + 1) + 5) + 1 = c + 7 := by omega

theorem tail_ops_five (c : Nat) : (c + 7) + 5 = c + 12 := by omega

private theorem twelve_le : (12 : Nat) ≤ 13 := by omega

private theorem six_le_cube (n : Nat) : 6 * n ≤ 8 * n * (n + 1) := by
  have h : 6 ≤ 8 * (n + 1) := by omega
  calc
    6 * n = n * 6 := Nat.mul_comm _ _
    _ ≤ n * (8 * (n + 1)) := Nat.mul_le_mul_left n h
    _ = 8 * n * (n + 1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm n 8, Nat.mul_assoc]

/-- Two cube spends and one more `2 * n` sit inside eight steps. -/
private theorem two_spend_le (n bench : Nat) :
    2 * (cubeCharge n bench + 2 * n + 3 * (bench - n)) + 2 * n ≤
      8 * stepBudget n bench := by
  unfold cubeCharge stepBudget
  generalize hd : bench - n = d
  have h6 : 6 * n ≤ 8 * (n * (n + 1)) := by
    simpa [Nat.mul_assoc] using six_le_cube n
  have hmain : 22 * n + 18 * d ≤ 16 * n + 8 * (n * (n + 1)) + 24 * d := by
    omega
  have hL : 2 * (8 * n + 6 * d + 2 * n + 3 * d) + 2 * n = 22 * n + 18 * d := by omega
  have hR : 8 * (2 * n + n * (n + 1) + 3 * d) =
      16 * n + 8 * (n * (n + 1)) + 24 * d := by omega
  rw [hL, hR]
  exact hmain

private theorem cube_room_le (n bench : Nat) :
    cubeCharge n bench + 2 * n + 3 * (bench - n) + 2 * n ≤
      8 * stepBudget n bench := by
  unfold cubeCharge stepBudget
  generalize hd : bench - n = d
  have h6 : 6 * n ≤ 8 * (n * (n + 1)) := by
    simpa [Nat.mul_assoc] using six_le_cube n
  omega

private theorem spend_of_room (spend extra room : Nat)
    (h : spend + extra ≤ room) : spend ≤ room := by omega

private theorem group_in (moves pre c n d : Nat)
    (h : moves ≤ pre + c + 2 * n + 3 * d) :
    moves ≤ pre + (c + 2 * n + 3 * d) := by omega

private theorem wide_n (n bench tn tb B : Nat) (hn : n = tn) (hb : bench = tb)
    (h : 32 * stepBudget tn tb ≤ B) : 32 * stepBudget n bench ≤ B := by
  subst hn hb
  exact h

private theorem unit_le (spend step B : Nat)
    (h8 : spend ≤ 8 * step) (h32 : 32 * step ≤ B) :
    spend + 24 * step ≤ B := by omega

private theorem live_spend (moves' moves pre spend step : Nat)
    (h1 : moves' ≤ moves + 24 * step) (h2 : moves ≤ pre + spend) :
    moves' ≤ pre + spend + 24 * step := by omega

private theorem live_next (moves' pre spend extra step : Nat)
    (hm : moves' ≤ pre + spend + 24 * step)
    (h2 : 2 * spend + extra ≤ 8 * step) :
    moves' + spend + extra ≤ pre + 32 * step := by omega

private theorem move_shape (moves' n c d pre budget : Nat)
    (h : moves' + (c + 2 * n + 3 * d) + 2 * n ≤ pre + budget) :
    moves' + 2 * n + c + 2 * n + 3 * d ≤ pre + budget := by omega

private theorem move_step (moves' pre i spend step B : Nat)
    (hm : moves' ≤ pre + spend + 24 * step)
    (hprev : pre ≤ i * B) (hunit : spend + 24 * step ≤ B) :
    moves' ≤ (i + 1) * B := by
  have hsum := ledger_next i B (spend + 24 * step) pre hprev hunit
  omega

private theorem fit_move (a pre n bench tn tb : Nat) (hn : n = tn) (hb : bench = tb)
    (hroom : FitsLen (pre + 32 * stepBudget tn tb))
    (hle : a ≤ pre + 32 * stepBudget n bench) :
    FitsLen a := by
  subst hn hb
  exact FitsLen.of_le hroom hle

private theorem fit_move_tier (moves' n bench tn tb : Nat) (hn : n = tn) (hb : bench = tb)
    (h : FitsLen (moves' + 2 * n + cubeCharge n bench + 2 * n + 3 * (bench - n))) :
    FitsLen (moves' + 2 * tn + cubeCharge tn tb + 2 * tn + 3 * (tb - tn)) := by
  subst hn hb
  exact h

private theorem fit_slide_tier (slides' n tn : Nat) (hn : n = tn)
    (h : FitsLen (slides' + 2 * n + slideCharge n)) :
    FitsLen (slides' + 2 * tn + slideCharge tn) := by
  subst hn
  exact h

private theorem ops_fin (cOps cMul cOps' : Nat)
    (hc : cOps = cMul + 7) (h5 : cOps' = cOps + 5) : cOps' = cMul + 12 := by
  omega

private theorem live_ctrl (ctrl' ctrl pre : Nat)
    (h1 : ctrl' = ctrl + 10) (h2 : ctrl = pre + 6) : ctrl' = pre + 16 := by omega

private theorem ctrl_pad (ctrl' pre : Nat) (h : ctrl' = pre + 16) :
    ctrl' + 6 ≤ (pre + 6) + 40 := by omega

private theorem sixteen_le (S : Nat) (h : 46 ≤ S) : 16 ≤ S := by omega

private theorem ctrl_step (ctrl' pre i S : Nat)
    (heq : ctrl' = pre + 16) (hprev : pre ≤ i * S) (h16 : 16 ≤ S) :
    ctrl' ≤ (i + 1) * S := by
  have hsum := ledger_next i S 16 pre hprev h16
  omega

private theorem live_slides (slides' slides pre n : Nat)
    (h1 : slides' ≤ slides + 16 * n) (h2 : slides ≤ pre + 4 * n) :
    slides' ≤ pre + 20 * n := by omega

private theorem slides_tn (slides' pre n tn : Nat) (heq : n = tn)
    (h : slides' ≤ pre + 20 * n) : slides' ≤ pre + 20 * tn := by
  subst heq
  exact h

private theorem twenty_le (n S : Nat) (h : 32 * n ≤ S) : 20 * n ≤ S := by omega

private theorem slide_step (slides' pre i n S : Nat)
    (hs : slides' ≤ pre + 20 * n) (hprev : pre ≤ i * S) (h20 : 20 * n ≤ S) :
    slides' ≤ (i + 1) * S := by
  have hsum := ledger_next i S (20 * n) pre hprev h20
  omega

private theorem slide_pad (slides' pre n : Nat) (h : slides' ≤ pre + 20 * n) :
    slides' + 6 * n ≤ pre + 32 * n := by omega

private theorem slide_shape (slides' n pre wide : Nat)
    (h : slides' + 6 * n ≤ pre + wide) :
    slides' + 2 * n + 4 * n ≤ pre + wide := by omega

private theorem fit_slide (a pre n tn : Nat) (heq : n = tn)
    (hroom : FitsLen (pre + 32 * tn))
    (hle : a ≤ pre + 32 * n) : FitsLen a := by
  subst heq
  exact FitsLen.of_le hroom hle

private theorem cell_room32 (t : Spec.Tier) (moves done : Nat) (tw : TierWalk t)
    (hmoves : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hpos : done < t.cells)
    (hstep : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n)) :
    FitsLen (moves + 32 * stepBudget t.n t.benchlen) := by
  let W := walkCharge t
  let E := 6 * t.benchlen + 2 * t.n
  let B := W + E
  have hle : moves + 32 * stepBudget t.n t.benchlen ≤ (done + 1) * B := by
    have hsum : moves + 32 * stepBudget t.n t.benchlen ≤ done * B + B :=
      Nat.add_le_add hmoves hstep
    rw [← Nat.succ_mul] at hsum
    simpa [Nat.succ_eq_add_one] using hsum
  have hDE : (done + 1) * E ≤ t.cells * E :=
    Nat.mul_le_mul_right E (by omega : done + 1 ≤ t.cells)
  have hEW : t.cells * E ≤ W := by
    rw [Nat.mul_comm]
    simpa [E, W] using tw.moveOver
  have hE1 : (done + 1) * E ≤ W := Nat.le_trans hDE hEW
  have hgap : 1 ≤ t.cells - done := by omega
  have hWgap : W ≤ (t.cells - done) * W := by
    have hmul : 1 * W ≤ (t.cells - done) * W := Nat.mul_le_mul_right W hgap
    simpa using hmul
  have hEg : (done + 1) * E ≤ (t.cells - done) * W := Nat.le_trans hE1 hWgap
  have hcap : (done + 1) * B ≤ (t.cells + 1) * W := by
    have hleft : (done + 1) * B = (done + 1) * W + (done + 1) * E := by
      simp [B, Nat.mul_add]
    have hjoin : (done + 1) * W + (t.cells - done) * W =
        ((done + 1) + (t.cells - done)) * W := by
      rw [← Nat.add_mul]
    have hidx : (done + 1) + (t.cells - done) = t.cells + 1 := by omega
    calc
      (done + 1) * B = (done + 1) * W + (done + 1) * E := hleft
      _ ≤ (done + 1) * W + (t.cells - done) * W := Nat.add_le_add_left hEg _
      _ = ((done + 1) + (t.cells - done)) * W := hjoin
      _ = (t.cells + 1) * W := by rw [hidx]
  exact FitsLen.of_le tw.roomM (Nat.le_trans hle hcap)

private theorem slide_room32 (t : Spec.Tier) (slides done : Nat) (tw : TierWalk t)
    (hslides : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hpos : done < t.cells)
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n) :
    FitsLen (slides + 32 * t.n) := by
  let S := cellSlideCharge t + slideCharge t.n
  have hle : slides + 32 * t.n ≤ (done + 1) * S := by
    have hsum : slides + 32 * t.n ≤ done * S + S := Nat.add_le_add hslides h32
    rw [← Nat.succ_mul] at hsum
    simpa [Nat.succ_eq_add_one] using hsum
  have h4 : slideCharge t.n * t.cells ≤ cellSlideCharge t := by
    simpa [slideCharge] using tw.slideOver
  let C := cellSlideCharge t
  let F := slideCharge t.n
  have hcap : (done + 1) * S ≤ (t.cells + 1) * C := by
    have hDE : (done + 1) * F ≤ t.cells * F :=
      Nat.mul_le_mul_right F (by omega : done + 1 ≤ t.cells)
    have hEW : t.cells * F ≤ C := by
      rw [Nat.mul_comm]
      simpa [F, C] using h4
    have hE1 : (done + 1) * F ≤ C := Nat.le_trans hDE hEW
    have hgap : 1 ≤ t.cells - done := by omega
    have hWgap : C ≤ (t.cells - done) * C := by
      have hmul : 1 * C ≤ (t.cells - done) * C := Nat.mul_le_mul_right C hgap
      simpa using hmul
    have hEg : (done + 1) * F ≤ (t.cells - done) * C := Nat.le_trans hE1 hWgap
    have hleft : (done + 1) * S = (done + 1) * C + (done + 1) * F := by
      simp [S, Nat.mul_add]
    have hjoin : (done + 1) * C + (t.cells - done) * C =
        ((done + 1) + (t.cells - done)) * C := by
      rw [← Nat.add_mul]
    have hidx : (done + 1) + (t.cells - done) = t.cells + 1 := by omega
    calc
      (done + 1) * S = (done + 1) * C + (done + 1) * F := hleft
      _ ≤ (done + 1) * C + (t.cells - done) * C := Nat.add_le_add_left hEg _
      _ = ((done + 1) + (t.cells - done)) * C := hjoin
      _ = (t.cells + 1) * C := by rw [hidx]
  exact FitsLen.of_le tw.roomS (Nat.le_trans hle hcap)

private theorem cell_at_tier (b : Ecbs.Board) (lane : List Nat)
    (n k bench tn tk tb : Nat) (v z x2 y2 x3 yUp : List Nat)
    (tier : Ecbs.Tier) (szH szD : Nat)
    (hn : tn = n) (hk : tk = k) (hb : tb = bench)
    (c : CellAt b lane n k bench v z x2 y2 x3 yUp tier szH szD) :
    CellAt b lane tn tk tb v z x2 y2 x3 yUp tier szH szD := by
  subst hn hk hb
  exact c

private theorem idx_lt_of_some {α : Type} (a : Array α) (v : α)
    (h : a[1]? = some v) : 1 < a.size := by
  have hnot : ¬ a.size ≤ 1 := by
    intro hle
    have hn : a[1]? = none := Array.getElem?_eq_none_iff.mpr hle
    rw [h] at hn
    cases hn
  omega

/-- Homes layout, white or red. `fform_add_cell` is `CellAt`, the frame and
    `ProjOn` are that cell, and the two op slots step into the next `FformAt`. -/
theorem live_cell_at
    (t : Spec.Tier) (b : Ecbs.Board) (red : Bool)
    (t0 t1 : Int) (ops : Array Int)
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Ecbs.Board)
    (hAtL : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok false)
    (hMirU : mirror b3 up = .ok b4)
    (hRise : mul b4 up base_up bottom true true red = .ok b5)
    (hU : mul b5 gap up up true false false = .ok b6)
    (hUZ : mul b6 gap bottom gap false false false = .ok b7)
    (hV : mul b7 spare across across true false false = .ok b8)
    (hVZ : mul b8 bottom spare bottom false false false = .ok b9)
    (hSum : mul b9 gap across spare false true false = .ok b10)
    (hAdd : add b10 gap bottom false = .ok b11)
    (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat)
    (x3 yUp : List Nat)
    (s : AddAt b11 lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z))
    (baseX baseY : List Nat) (i cMul c1 preMoves preSlides preCtrl : Nat)
    (tw : TierWalk t)
    (hpos : i < t.cells)
    (hscript : 2 < t.script)
    (hpx : x3.length = t.n) (hpy : yUp.length = t.n)
    (hpxT : allTritList x3) (hpyT : allTritList yUp)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hx2 : x2 = baseX) (hy2 : y2 = baseY)
    (htier : b11.sudo_5Board_1t = embTier t)
    (hszH : b11.sudo_5Board_4home.size = 8) (hszD : b11.sudo_5Board_4held.size = 8)
    (hnk : t.n = n) (hkk : t.k = k) (hbb : t.benchlen = bench)
    (hopIn : 1 < b11.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b11.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((c1 + 3 : Nat) : Int))
    (hcOps : cOps = cMul + 7)
    (hmvB : moves ≤ preMoves + cubeCharge n bench + 2 * n + 3 * (bench - n))
    (hslB : slides ≤ preSlides + 4 * n)
    (hctrlB : ctrl = preCtrl + 6)
    (hfitC1 : FitsLen (c1 + 3 * (t.cells - i)))
    (hfitMul : FitsLen (cMul + 13 * (t.cells - i)))
    (hmvLe : preMoves ≤ i * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hslLe : preSlides ≤ i * (cellSlideCharge t + slideCharge t.n))
    (hcLe : preCtrl ≤ i * (cellCtrlCharge t + 4))
    (hwide : 32 * stepBudget t.n t.benchlen ≤
        walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hspan : 2 * (t.n - 1) < t.benchlen) (hnb : t.n ≤ t.benchlen)
    (hne : fformBottom t.n t.k t.benchlen v z ≠ List.replicate t.n 0)
    (hinv : ∃ w, w.length = t.n ∧ allTritList w ∧
      fieldMul t.n t.k t.benchlen (fformBottom t.n t.k t.benchlen v z) w = onePeg t.n) :
    ∃ b',
      Ecbs.fform_add b red = .ok (true, b') ∧
      FformAt t b' baseX baseY x3 yUp (i + 1) := by
  obtain ⟨b', lane', hadd, hC, hmon, hH0, hcount, hslot⟩ :=
    fform_add_cell b red t0 t1 ops b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
      hAtL hInc hPut hMir hRun hZ hMirU hRise hU hUZ hV hVZ hSum hAdd
      lane n k bench u v z x2 y2 script w h r m ctrl mx cOps moves slides hole
      peak peakS x3 yUp s hbound hfitM6 hfitC6 hfops6 hf hBig hSlide
      hw0 hh0 hrR hrP hnE hkLe hgapN hsm hnsm hfitB hx hy
  have hCt := cell_at_tier b' lane' n k bench t.n t.k t.benchlen v z x2 y2 x3 yUp
    b11.sudo_5Board_1t b11.sudo_5Board_4home.size b11.sudo_5Board_4held.size
    hnk hkk hbb hC
  have hfr := frame_of_cell t b' lane' v z x2 y2 x3 yUp b11.sudo_5Board_1t
    b11.sudo_5Board_4home.size b11.sudo_5Board_4held.size baseX baseY
    hCt hx2 hy2 htier hszH hszD
  have hp := cell_proj t b' lane' v z x2 y2 x3 yUp b11.sudo_5Board_1t
    b11.sudo_5Board_4home.size b11.sudo_5Board_4held.size
    hCt hspan hnb hne hinv
  obtain ⟨moves', slides', ctrl', mark', mx', pk', ps', hole', cOps', ch, hopEq,
      hctrlEq, hmvLeT, hslLeT⟩ := hcount
  have hcFin := ops_fin cOps cMul cOps' hcOps hopEq
  have hc1' : FitsLen ((c1 + 3) + 3 * (t.cells - (i + 1))) :=
    cube_slack_next c1 t.cells i hfitC1 hpos
  have hc0' : FitsLen (cOps' + 13 * (t.cells - (i + 1))) := by
    have hnext := mul_slack_next cMul 12 t.cells i hfitMul twelve_le hpos
    rw [← hcFin] at hnext
    exact hnext
  have hop1' : b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some ((c1 + 3 : Nat) : Int) := (hslot hopIn).trans hop1
  have hops1' : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    idx_lt_of_some _ _ hop1'
  let spend := cubeCharge n bench + 2 * n + 3 * (bench - n)
  let step := stepBudget n bench
  let B := walkCharge t + (6 * t.benchlen + 2 * t.n)
  have hgroup := group_in moves preMoves (cubeCharge n bench) n (bench - n) hmvB
  have hspent := live_spend moves' moves preMoves spend step hmvLeT hgroup
  have h2 := two_spend_le n bench
  have hnextM := live_next moves' preMoves spend (2 * n) step hspent h2
  have hshape := move_shape moves' n (cubeCharge n bench) (bench - n) preMoves
    (32 * step) hnextM
  have hroom := cell_room32 t preMoves i tw hmvLe hpos hwide
  have hfitM : FitsLen (moves' + 2 * n + cubeCharge n bench + 2 * n +
      3 * (bench - n)) :=
    fit_move _ preMoves n bench t.n t.benchlen hnk.symm hbb.symm hroom hshape
  have hslideR := slide_room32 t preSlides i tw hslLe hpos h32
  have hslN := live_slides slides' slides preSlides n hslLeT hslB
  have hpad := slide_pad slides' preSlides n hslN
  have hshS := slide_shape slides' n preSlides (32 * n) hpad
  have hfitS : FitsLen (slides' + 2 * n + slideCharge n) := by
    rw [slideCharge]
    exact fit_slide _ preSlides n t.n hnk.symm hslideR hshS
  have h8 := spend_of_room spend (2 * n) (8 * step) (cube_room_le n bench)
  have h32s := wide_n n bench t.n t.benchlen B hnk.symm hbb.symm hwide
  have hunit := unit_le spend step B h8 h32s
  have hmvLe' := move_step moves' preMoves i spend step B hspent hmvLe hunit
  have h20 := twenty_le t.n (cellSlideCharge t + slideCharge t.n) h32
  have hslTn := slides_tn slides' preSlides n t.n hnk.symm hslN
  have hslLe' := slide_step slides' preSlides i t.n
    (cellSlideCharge t + slideCharge t.n) hslTn hslLe h20
  have hctrlFin := live_ctrl ctrl' ctrl preCtrl hctrlEq hctrlB
  have hfitC : FitsLen (ctrl' + 6) :=
    FitsLen.of_le (comb_ctrl_fit t preCtrl i (preCtrl + 6) tw hcLe hpos rfl h46)
      (ctrl_pad ctrl' preCtrl hctrlFin)
  have hcLe' := ctrl_step ctrl' preCtrl i (cellCtrlCharge t + 4) hctrlFin hcLe
    (sixteen_le _ h46)
  have ch' : TailCharge b' moves' slides' ctrl' mark' mx' pk' ps' hole' cOps' := ch
  exact ⟨b', hadd, fform_at_pack t b' baseX baseY x3 yUp (i + 1)
    hmon hpx hpy hpxT hpyT hbx hby hbxT hbyT hH0 hscript hfr hp
    moves' slides' ctrl' mark' mx' pk' ps' hole' (c1 + 3) cOps' ch' hops1' hop1'
    hfitC hc1' hc0'
    (fit_move_tier moves' n bench t.n t.benchlen hnk.symm hbb.symm hfitM)
    (fit_slide_tier slides' n t.n hnk.symm hfitS)
    hmvLe' hslLe' hcLe'⟩

end EcbsLink2.Link2
