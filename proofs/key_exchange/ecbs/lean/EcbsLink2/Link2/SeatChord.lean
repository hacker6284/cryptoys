/-
  The chord of the first live cell. Frobenius has already seated the marker
  on the opening board. A white or red cell then runs `chord_add_demo`.
  The opening counters sit under one charge, so a later index only widens
  the `LiveAt` bound. The early-marker board is not part of these statements.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SeatDown

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem succ_sum (done a : Nat) :
    (done + 1) * a = done * a + a := by
  rw [Nat.succ_mul]

private theorem next_le (done cap spent now next : Nat)
    (hnow : now ≤ done * cap) (hstep : next ≤ now + spent) (hspent : spent ≤ cap) :
    next ≤ (done + 1) * cap := by
  rw [succ_sum]
  exact Nat.le_trans hstep (Nat.add_le_add hnow hspent)

private theorem one_to_done (done cap a : Nat) (hge : 1 ≤ done) (ha : a ≤ cap) :
    a ≤ done * cap := by
  have h1 : a ≤ 1 * cap := by
    rw [Nat.one_mul]
    exact ha
  exact Nat.le_trans h1 (Nat.mul_le_mul_right cap hge)

/-- One control step before the seat is still inside a cell's control charge. -/
private theorem tier_ctrl_room (t : Spec.Tier) :
    tierR t - 1 ≤ cellCtrlCharge t + 4 := by
  have h5 : 5 ≤ 3 * rowRoom t + 5 := by omega
  have hmul : (tierR t + 1) * 5 ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
    Nat.mul_le_mul_left _ h5
  have hbase : tierR t - 1 ≤ (tierR t + 1) * 5 := by
    have hmul1 : tierR t + 1 ≤ (tierR t + 1) * 5 :=
      Nat.le_mul_of_pos_right (tierR t + 1) (by decide : 0 < 5)
    omega
  have hchg : cellCtrlCharge t = 1 + (tierR t + 1) * (3 * rowRoom t + 5) + 6 := by
    unfold cellCtrlCharge
    rfl
  calc
    tierR t - 1 ≤ (tierR t + 1) * 5 := hbase
    _ ≤ (tierR t + 1) * (3 * rowRoom t + 5) := hmul
    _ ≤ cellCtrlCharge t + 4 := by rw [hchg]; omega

private theorem opening_ops_one (t : Spec.Tier) : 1 ≤ cellOpsCharge t + 2 := by
  unfold cellOpsCharge
  have h5 : (1 : Nat) ≤ 5 := by decide
  exact Nat.le_trans h5 (Nat.le_add_left 5 (tierR t * (rowRoom t + 3)))

private theorem opening_moves_le (t : Spec.Tier) (x y : List Nat) (done : Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) (hge : 1 ≤ done) :
    pegCount x + pegCount y + pegCount x + pegCount y ≤
      done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  have hpeg : pegCount x + pegCount y + pegCount x + pegCount y ≤ walkCharge t := by
    unfold walkCharge cellMoveCharge
    omega
  have hcap : walkCharge t ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) :=
    Nat.le_add_right _ _
  exact one_to_done done _ _ hge (Nat.le_trans hpeg hcap)

private theorem seat_counters (t : Spec.Tier) (x y : List Nat) (done : Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) (hge : 1 ≤ done) :
    pegCount x + pegCount y + pegCount x + pegCount y ≤
        done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
      (0 : Nat) ≤ done * (cellSlideCharge t + 4 * t.n) ∧
      tierR t - 1 ≤ done * (cellCtrlCharge t + 4) ∧
      1 ≤ done * (cellOpsCharge t + 2) :=
  ⟨opening_moves_le t x y done hx hy hge, Nat.zero_le _,
    one_to_done done _ _ hge (tier_ctrl_room t),
    one_to_done done _ _ hge (opening_ops_one t)⟩

private theorem seat_mark (t : Spec.Tier) (tw : TierWalk t) (mark : Nat) (hmark : mark = 1) :
    mark + 3 < t.script ∧ FitsLen (mark + 4) := by
  rw [hmark]
  refine ⟨tw.scriptRoom, ?_⟩
  unfold FitsLen i64MaxNat
  decide

private theorem chord_y_trits (n k bench : Nat) (slope dx y : List Nat) :
    allTritList (chordY3 n k bench slope dx y) := by
  simpa [chordY3, fieldSub] using
    fieldAdd_span_trits n (fieldMul n k bench slope dx) (mirrorTrits y)

private theorem chord_y_len (n k bench : Nat) (slope dx y : List Nat) :
    (chordY3 n k bench slope dx y).length = n := by
  simpa [chordY3] using fieldSub_length n (fieldMul n k bench slope dx) y

private theorem cube_up_trits (t : Spec.Tier) (sat : TierSat t) (hsh : TierShape t)
    (up : List Nat) (hup : allTritList up) :
    allTritList (fieldCube t.n t.k t.benchlen up) := by
  apply fieldCube_trits t.n t.k t.benchlen up hup
  · have h := sat.cube_span
    omega
  · exact hsh.k_le

/-- A non-final seat cell. `fuel + 1 = left`, and `done` is that cell's index.
    `up` is the opening's up home: the base up, or its negation. -/
theorem seat_cell_chord (t : Spec.Tier) (b : Ecbs.Board)
    (x y up : List Nat) (c done left fuel : Nat) (inv : List Nat)
    (fr : RunFrame b t x (fieldCube t.n t.k t.benchlen x))
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = y) (hA : fr.y1 = fieldCube t.n t.k t.benchlen up)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hy : y.length = t.n) (htriY : allTritList y) (htriUp : allTritList up)
    (hmv : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
      cubeCharge t.n t.benchlen)
    (hsl : fr.slides ≤ 4 * t.n)
    (hctrl : fr.ctrl = tierR t - 1 + 4)
    (hops : fr.opsCap = 3)
    (hmark : fr.mark = 1)
    (hst : fr.peakS ≤ 7)
    (hhole : fr.hole ≤ t.benchlen)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = t.cells) :
    ∃ b' x3 y3,
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, up) c = some (true, (x3, y3)) ∧
      LiveAt t b' x y x3 y3 (done + 1) := by
  obtain ⟨hm0, hs0, hc0, ho0⟩ := seat_counters t x y done fr.lenX hy hge
  have hsl0 : fr.slides ≤ 0 + slideCharge t.n := by
    rw [Nat.zero_add, slideCharge]
    exact hsl
  have hctrl0 : fr.ctrl = (tierR t - 1) + 4 := by rw [hctrl]
  have hops0 : fr.opsCap = 1 + 2 := by rw [hops]
  obtain ⟨hmarkLt, hmarkFit⟩ := seat_mark t tw fr.mark hmark
  have htriCube : allTritList (fieldCube t.n t.k t.benchlen up) :=
    cube_up_trits t sat hsh up htriUp
  have hlenCube : (fieldCube t.n t.k t.benchlen up).length = t.n :=
    fieldCube_length t.n t.k t.benchlen up tw.nLe
  have hleft : 0 < left := by omega
  obtain ⟨b', x3, y3, fr', hdemo, hwalk, _hops', hmv', hctrl', hsl', hst', hho',
      hy1', hy4', hf1', hf4', hmk', hopsB⟩ :=
    tier_cell_chord t b x (fieldCube t.n t.k t.benchlen x) y
      (fieldCube t.n t.k t.benchlen up) x up inv c fuel fr
      (pegCount x + pegCount y + pegCount x + pegCount y) 0 (tierR t - 1) 1
      done left tw hOk sat hR hsh hmk hc hY hA hf4 hf1 hy hlenCube htriY htriCube
      rfl rfl hacc hFuel hleftEq hsum hleft hm0 hs0 hc0 ho0 hmv hsl0
      (Nat.le_of_eq hctrl0) (Nat.le_of_eq hops0) hst hhole hmarkLt hmarkFit
  have hform := walkStep_live_chord t.n t.k t.benchlen x y x up c inv hc
    (by rw [specInv_eq]; exact hacc)
  have hsome := Option.some.inj (hwalk.symm.trans hform)
  have hy3 : y3 = chordY3 t.n t.k t.benchlen
      (fieldMul t.n t.k t.benchlen
        (fieldSub t.n (if c = 2 then mirrorTrits y else y)
          (fieldCube t.n t.k t.benchlen up)) inv)
      (fieldSub t.n (fieldCube t.n t.k t.benchlen x)
        (chordX3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if c = 2 then mirrorTrits y else y)
              (fieldCube t.n t.k t.benchlen up)) inv)
          (fieldCube t.n t.k t.benchlen x)
          (fieldSub t.n x (fieldCube t.n t.k t.benchlen x))))
      (fieldCube t.n t.k t.benchlen up) :=
    congrArg Prod.snd (congrArg Prod.snd hsome)
  have htriY3 : allTritList y3 := by
    rw [hy3]
    exact chord_y_trits _ _ _ _ _ _
  have hlenY3 : y3.length = t.n := by
    rw [hy3]
    exact chord_y_len _ _ _ _ _ _
  refine ⟨b', x3, y3, hdemo, hwalk, fr', hmk', hy4', hy1', hf4', hf1', hst', hho',
    ?_, ?_, ?_, hopsB, hy, htriY, hlenY3, htriY3⟩
  · have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
      cube_over _ _ tw.nLe
    have hstepM : fr'.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
        (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
      calc
        fr'.moves ≤ fr.moves + walkCharge t := hmv'
        _ ≤ pegCount x + pegCount y + pegCount x + pegCount y +
            cubeCharge t.n t.benchlen + walkCharge t := Nat.add_le_add_right hmv _
        _ = pegCount x + pegCount y + pegCount x + pegCount y +
            (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by rw [hcube]; omega
    exact next_le done _ _ _ fr'.moves hm0 hstepM (Nat.le_refl _)
  · have hstepS : fr'.slides ≤ 0 + (cellSlideCharge t + slideCharge t.n) := by
      calc
        fr'.slides ≤ fr.slides + cellSlideCharge t := hsl'
        _ ≤ 0 + slideCharge t.n + cellSlideCharge t := Nat.add_le_add_right hsl0 _
        _ = 0 + (cellSlideCharge t + slideCharge t.n) := by omega
    exact next_le done _ _ 0 fr'.slides (Nat.zero_le _) hstepS (Nat.le_refl _)
  · have hstepC : fr'.ctrl ≤ (tierR t - 1) + (cellCtrlCharge t + 4) := by
      rw [hctrl0] at hctrl'
      omega
    exact next_le done _ _ (tierR t - 1) fr'.ctrl hc0 hstepC (Nat.le_refl _)

/-- The seat cell is the last cell. One charge, and the homes are the new point. -/
theorem seat_cell_last (t : Spec.Tier) (b : Ecbs.Board)
    (x y up : List Nat) (c done left : Nat) (inv : List Nat)
    (fr : RunFrame b t x (fieldCube t.n t.k t.benchlen x))
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = y) (hA : fr.y1 = fieldCube t.n t.k t.benchlen up)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hy : y.length = t.n) (htriY : allTritList y) (htriUp : allTritList up)
    (hmv : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
      cubeCharge t.n t.benchlen)
    (hsl : fr.slides ≤ 4 * t.n)
    (hctrl : fr.ctrl = tierR t - 1 + 4)
    (hops : fr.opsCap = 3)
    (hmark : fr.mark = 1)
    (hhole : fr.hole ≤ t.benchlen)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hleft : left = 1) (hsum : done + left = t.cells) :
    ∃ b' x3 y3,
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, up) c = some (true, (x3, y3)) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) := by
  obtain ⟨hm0, hs0, hc0, ho0⟩ := seat_counters t x y done fr.lenX hy hge
  have hsl0 : fr.slides ≤ 0 + slideCharge t.n := by
    rw [Nat.zero_add, slideCharge]
    exact hsl
  have hctrl0 : fr.ctrl = (tierR t - 1) + 4 := by rw [hctrl]
  have hops0 : fr.opsCap = 1 + 2 := by rw [hops]
  obtain ⟨hmarkLt, hmarkFit⟩ := seat_mark t tw fr.mark hmark
  have htriCube : allTritList (fieldCube t.n t.k t.benchlen up) :=
    cube_up_trits t sat hsh up htriUp
  have hlenCube : (fieldCube t.n t.k t.benchlen up).length = t.n :=
    fieldCube_length t.n t.k t.benchlen up tw.nLe
  have hrooms := chord_rooms t tw
    (pegCount x + pegCount y + pegCount x + pegCount y) 0 (tierR t - 1) 1
    fr.moves fr.slides fr.ctrl fr.opsCap done left hsum (by omega) hm0 hs0 hc0 ho0
    hmv hsl0 (Nat.le_of_eq hctrl0) (Nat.le_of_eq hops0)
  have hMove : FitsLen (liveMoveRoom t fr.moves x (fieldCube t.n t.k t.benchlen x)) := by
    apply FitsLen.of_le (by simpa [hleft] using hrooms.1)
    exact live_move_le t fr.moves x (fieldCube t.n t.k t.benchlen x) fr.lenX
      (fieldCube_length t.n t.k t.benchlen x tw.nLe)
  have hSlide : FitsLen (liveSlideRoom t fr.slides) :=
    live_slide_of_cell t fr.slides (by simpa [hleft] using hrooms.2.1)
  have hCtrl : FitsLen (liveCtrlRoom t fr.ctrl) :=
    live_ctrl_of_cell t fr.ctrl (by simpa [hleft] using hrooms.2.2.1)
  have hOps : FitsLen (liveOpsRoom t fr.opsCap) :=
    live_ops_of_cell t fr.opsCap (by simpa [hleft] using hrooms.2.2.2)
  obtain ⟨b', hdemo, hx0, hy1h, hwalk, _hhigh, _hbud, _hpack⟩ :=
    chord_add_live b t x (fieldCube t.n t.k t.benchlen x) y
      (fieldCube t.n t.k t.benchlen up) x up inv c fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hy hlenCube htriY htriCube
      rfl rfl hacc hMove hSlide hCtrl hOps hmarkLt hmarkFit hhole
  exact ⟨b', _, _, hdemo, hwalk, hx0, hy1h⟩

/-- The white seat cell is not last. Frobenius, then the chord, is `walkStep`
    on the copied point, and the board it leaves is `LiveAt` at the next index. -/
theorem seat_white_chord (t : Spec.Tier) (x y : List Nat) (c done left fuel : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = t.cells) :
    ∃ bF b' x3 y3,
      Ecbs.frobenius_affine (whiteRec t x y) = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, y) c = some (true, (x3, y3)) ∧
      LiveAt t b' x y x3 y3 (done + 1) := by
  have hcells : 0 < t.cells := by omega
  obtain ⟨_bL, bF, fr, _hlift, hfrob, _hbL, hmk, hy1, hy4, hmark, hctrl, hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_white t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  obtain ⟨b', x3, y3, hdemo, hwalk, hAt⟩ :=
    seat_cell_chord t bF x y y c done left fuel inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY htriY hmv hsl hctrl hops hmark hst hho
      hc hacc hge hFuel hleftEq hsum
  exact ⟨bF, b', x3, y3, hfrob, hdemo, hwalk, hAt⟩

/-- The white seat cell is the last cell. The homes are the point `walkStep` names. -/
theorem seat_white_last (t : Spec.Tier) (x y : List Nat) (c done left : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hleft : left = 1) (hsum : done + left = t.cells) :
    ∃ bF b' x3 y3,
      Ecbs.frobenius_affine (whiteRec t x y) = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, y) c = some (true, (x3, y3)) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) := by
  have hcells : 0 < t.cells := by omega
  obtain ⟨_bL, bF, fr, _hlift, hfrob, _hbL, hmk, hy1, hy4, hmark, hctrl, _hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_white t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  obtain ⟨b', x3, y3, hdemo, hwalk, hx0, hy1h⟩ :=
    seat_cell_last t bF x y y c done left inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY htriY hmv hsl hctrl hops hmark hho
      hc hacc hge hleft hsum
  exact ⟨bF, b', x3, y3, hfrob, hdemo, hwalk, hx0, hy1h⟩

/-- The red seat cell is not last. The opening up is the negated base up. -/
theorem seat_red_chord (t : Spec.Tier) (x y : List Nat) (c done left fuel : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = t.cells) :
    ∃ bF b' x3 y3,
      Ecbs.frobenius_affine (redRec t x y) = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, mirrorTrits y) c =
        some (true, (x3, y3)) ∧
      LiveAt t b' x y x3 y3 (done + 1) := by
  have hcells : 0 < t.cells := by omega
  obtain ⟨_bL, bF, fr, _hlift, hfrob, _hbL, hmk, hy1, hy4, hmark, hctrl, hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_red t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  have hmirr : pegCount (mirrorTrits y) = pegCount y := pegCount_mirror y htriY
  rw [hmirr] at hmv
  obtain ⟨b', x3, y3, hdemo, hwalk, hAt⟩ :=
    seat_cell_chord t bF x y (mirrorTrits y) c done left fuel inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY (mirrorTrits_allTrit htriY) hmv hsl hctrl hops
      hmark hst hho hc hacc hge hFuel hleftEq hsum
  exact ⟨bF, b', x3, y3, hfrob, hdemo, hwalk, hAt⟩

/-- The red seat cell is the last cell. The opening up is the negated base up. -/
theorem seat_red_last (t : Spec.Tier) (x y : List Nat) (c done left : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hleft : left = 1) (hsum : done + left = t.cells) :
    ∃ bF b' x3 y3,
      Ecbs.frobenius_affine (redRec t x y) = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, mirrorTrits y) c =
        some (true, (x3, y3)) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) := by
  have hcells : 0 < t.cells := by omega
  obtain ⟨_bL, bF, fr, _hlift, hfrob, _hbL, hmk, hy1, hy4, hmark, hctrl, _hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_red t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  have hmirr : pegCount (mirrorTrits y) = pegCount y := pegCount_mirror y htriY
  rw [hmirr] at hmv
  obtain ⟨b', x3, y3, hdemo, hwalk, hx0, hy1h⟩ :=
    seat_cell_last t bF x y (mirrorTrits y) c done left inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY (mirrorTrits_allTrit htriY) hmv hsl hctrl hops
      hmark hho hc hacc hge hleft hsum
  exact ⟨bF, b', x3, y3, hfrob, hdemo, hwalk, hx0, hy1h⟩

end EcbsLink2.Link2
