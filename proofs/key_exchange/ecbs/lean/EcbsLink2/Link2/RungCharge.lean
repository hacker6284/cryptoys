/-
  Rung charges, the climb budget, and the invariant a rung preserves.
  Split out of `Invert` so that file stays under the per-file memory line.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves one live nocopy mul can add: the settle into the spare, the schoolbook,
    and the lane fold. -/
def mulCharge (n bench : Nat) : Nat :=
  2 * n + n * (n + 1) + 3 * (bench - n)

/-- Moves of the heaviest rung: a non-final red rung that unparks first.
    Unpark and park add none. The copy and the clear add at most `n` each.
    The `m` cube-pegs add at most `pegCharge` each, which also covers a settle
    into a different home before the first cube. One live mul adds at most
    `mulCharge`. The red cube and the red mul add one more of each. Doubling
    and the extra white peg add no moves. -/
def rungCharge (n bench m : Nat) : Nat :=
  2 * n + (m + 1) * pegCharge n bench + 2 * mulCharge n bench

/-- Slides of that rung: `2 · n` for each of the `m` pegs, the gap mul, the red
    cube, and the red mul. -/
def rungSlideCharge (n m : Nat) : Nat :=
  (m + 3) * (2 * n)

/-- Ops of that rung. The cube slot grows by `m + 1` and the mul slot by `2`,
    so every slot grows by at most `m + 3`. -/
def rungOpCharge (m : Nat) : Nat :=
  m + 3

theorem mulCharge_ge (n bench : Nat) (moves : Nat) (_xs ys : List Nat) (_k : Nat)
    (_hn : n ≤ bench) (hp : pegCount (ys.take n) ≤ n) :
    moves + 2 * pegCount (ys.take n) + n * (n + 1) + 3 * (bench - n) ≤
      moves + mulCharge n bench := by
  unfold mulCharge
  omega

theorem charge_final_white (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n ≤ rungCharge n bench m := by
  unfold rungCharge
  have hp : m * pegCharge n bench ≤ (m + 1) * pegCharge n bench :=
    Nat.mul_le_mul_right _ (Nat.le_succ m)
  have hc : mulCharge n bench ≤ mulCharge n bench + mulCharge n bench :=
    Nat.le_add_right _ _
  have h2 : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
    rw [Nat.two_mul]
  have hsum : n + n = 2 * n := by rw [Nat.two_mul]
  omega

theorem charge_open_white (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n ≤ rungCharge n bench m :=
  charge_final_white n bench m

theorem charge_final_red (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
        mulCharge n bench ≤
      rungCharge n bench m := by
  unfold rungCharge
  have hsum : n + n = 2 * n := by rw [Nat.two_mul]
  have hpeg : m * pegCharge n bench + pegCharge n bench = (m + 1) * pegCharge n bench := by
    rw [Nat.succ_mul]
  have hmul : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
    rw [Nat.two_mul]
  omega

theorem charge_open_red (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
        mulCharge n bench ≤
      rungCharge n bench m :=
  charge_final_red n bench m

theorem slide_open_red (n m : Nat) :
    m * (2 * n) + 2 * n + 2 * n + 2 * n ≤ rungSlideCharge n m := by
  unfold rungSlideCharge
  have h : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by rw [Nat.add_mul]
  have h3 : 3 * (2 * n) = 2 * n + 2 * n + 2 * n := by omega
  omega

theorem op_open_red (m : Nat) : m + 1 + 2 ≤ rungOpCharge m := by
  unfold rungOpCharge
  omega

/-- With `n > 0`, one `rungCharge` dominates one `rungCtrl` step. -/
theorem rungCharge_ge_ctrl (n bench m : Nat) (hn : 0 < n) :
    3 * m + 5 ≤ rungCharge n bench m := by
  have h4n : 4 ≤ 4 * n := by
    have : 1 ≤ n := hn
    omega
  have hpeg : 4 ≤ 4 * n + 3 * (bench - n) := Nat.le_trans h4n (Nat.le_add_right _ _)
  have hmul : (m + 1) * 4 ≤ (m + 1) * (4 * n + 3 * (bench - n)) :=
    Nat.mul_le_mul_left _ hpeg
  have h2 : 2 ≤ 2 * n := by omega
  unfold rungCharge pegCharge
  have hlow : 2 * n + (m + 1) * 4 ≤
      2 * n + (m + 1) * (4 * n + 3 * (bench - n)) :=
    Nat.add_le_add_left hmul _
  have hrest : 2 * n + (m + 1) * (4 * n + 3 * (bench - n)) ≤
      2 * n + (m + 1) * (4 * n + 3 * (bench - n)) +
        2 * mulCharge n bench :=
    Nat.le_add_right _ _
  have hnum : 3 * m + 5 ≤ 2 + (m + 1) * 4 := by omega
  have h2n : 2 + (m + 1) * 4 ≤ 2 * n + (m + 1) * 4 := Nat.add_le_add_right h2 _
  exact Nat.le_trans hnum (Nat.le_trans h2n (Nat.le_trans hlow hrest))

/-- `2 · tally + 1` fits an i64 because it is at most one `rungCharge`, and the
    budget fits `R` of those. -/
theorem double_len_fit {moves0 R n bench m tally : Nat}
    (hn : 0 < n) (hR : 0 < R) (ht : tally ≤ m)
    (hf : FitsLen (moves0 + R * rungCharge n bench m)) :
    FitsLen (2 * tally + 1) := by
  have hstep := rungCharge_ge_ctrl n bench m hn
  have h1 : 2 * tally + 1 ≤ 3 * m + 5 := by omega
  have h2 : rungCharge n bench m ≤ R * rungCharge n bench m :=
    Nat.le_mul_of_pos_left (rungCharge n bench m) hR
  exact FitsLen.of_le hf (by omega)

/-- An index strictly below the control row fits an i64 when `control + 1` does.
    That is the tier's `fits_control`. -/
theorem double_index_fit {t0 m control : Nat}
    (h : t0 + 2 * m < control) (hc : FitsLen (control + 1)) :
    FitsLen (t0 + 2 * m) ∧ FitsLen (2 * m) ∧ FitsLen (2 * m + 1) := by
  refine ⟨FitsLen.of_le hc (by omega), FitsLen.of_le hc (by omega),
    FitsLen.of_le hc (by omega)⟩

/-- The same fits when the doubled index only reaches the end of the row.
    A final white double uses the whole remaining tail, so the bound is `≤`. -/
theorem double_index_fit_le {t0 m control : Nat}
    (h : t0 + 2 * m ≤ control) (hc : FitsLen (control + 1)) :
    FitsLen (t0 + 2 * m) ∧ FitsLen (2 * m) ∧ FitsLen (2 * m + 1) := by
  refine ⟨FitsLen.of_le hc (by omega), FitsLen.of_le hc (by omega),
    FitsLen.of_le hc (by omega)⟩

/-- The running counter plus one extra peg fits when the budget's `fitCtrl` does. -/
theorem double_ctrl_fit {ctrl tally ctrl0 done R mMax : Nat}
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 3 * tally) ∧
      FitsLen (ctrl + tally + 2 * tally + 1) := by
  have hS : 3 * tally + 1 ≤ 3 * mMax + 5 := by omega
  have hbody : ctrl + 3 * tally + 1 ≤
      ctrl0 + (done + 1) * (3 * mMax + 5) := by
    have hmul : (done + 1) * (3 * mMax + 5) =
        done * (3 * mMax + 5) + (3 * mMax + 5) := by
      rw [Nat.succ_mul]
    omega
  have hdone : ctrl0 + (done + 1) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) := by
    have hle : done + 1 ≤ R + 1 := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) _
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega)⟩

theorem rungCharge_mono (n bench m mMax : Nat) (h : m ≤ mMax) :
    rungCharge n bench m ≤ rungCharge n bench mMax := by
  unfold rungCharge
  have h1 : (m + 1) * pegCharge n bench ≤ (mMax + 1) * pegCharge n bench :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)
  omega

theorem rungSlideCharge_mono (n m mMax : Nat) (h : m ≤ mMax) :
    rungSlideCharge n m ≤ rungSlideCharge n mMax := by
  unfold rungSlideCharge
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h 3)

theorem rungOpCharge_mono (m mMax : Nat) (h : m ≤ mMax) :
    rungOpCharge m ≤ rungOpCharge mMax := by
  unfold rungOpCharge
  omega

/-- After `k` rungs, `k ≤ R`, a counter that stayed under `k` charges still fits
    the `R`-charge budget. This is the moves, slides, and ops fit in the domain
    of `invert_number_refines`. -/
theorem rung_budget_fit (base k R charge value : Nat)
    (hk : k ≤ R) (hval : value ≤ base + k * charge)
    (hFit : FitsLen (base + R * charge)) : FitsLen value := by
  apply FitsLen.of_le hFit
  have hk' : k * charge ≤ R * charge := Nat.mul_le_mul_right _ hk
  omega

/-- Park, copy, the white scan, the cube-peg loop, the live nocopy mul, and
    clear. `hPark` is either the idle keep-park or the unpark-then-park. -/
theorem rung_prefix_refines (b bPark : Ecbs.Board) (rung : Nat)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (g : List Nat) (moves peak : Nat)
    (hHs : 6 < bPark.sudo_5Board_4home.size)
    (hDs : 6 < bPark.sudo_5Board_4held.size)
    (hH5s : 5 < bPark.sudo_5Board_4home.size)
    (hD5s : 5 < bPark.sudo_5Board_4held.size)
    (h7 : 7 ≤ bPark.sudo_5Board_4held.size)
    (hsrc : bPark.sudo_5Board_4held[5] = true)
    (harr : bPark.sudo_5Board_4home[5] = embed g)
    (hempty : bPark.sudo_5Board_4held[6] = false)
    (hn : bPark.sudo_5Board_1t.sudo_4Tier_1n = (g.length : Int))
    (hf : FitsLen g.length)
    (hmoves : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount g))
    (c : PegCtx)
    (hCopy : c.b0 = placeBoard bPark 6 hHs hDs g moves peak)
    (rowXs : List Nat)
    (hT0 : c.b0.sudo_5Board_6tally0 = (c.t0 : Int))
    (hRow : c.b0.sudo_5Board_3row = embed rowXs)
    (hRoom : c.t0 + c.m ≤ rowXs.length)
    (hWhite : ∀ j (hj : j < c.m), rowXs[c.t0 + j]'(by omega) = 1)
    (hfitW : FitsLen (c.t0 + c.m))
    (xs ys : List Nat)
    (n k mvs slides holeM bench pk pkS cOps : Nat)
    (hH6 : 6 < (pegBoard c c.m).sudo_5Board_4home.size)
    (hD6 : 6 < (pegBoard c c.m).sudo_5Board_4held.size)
    (hops0 : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (mulHyps : Ecbs.mul (pegBoard c c.m) (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩))
    (hH5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩).sudo_5Board_4home.size)
    (hD5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩).sudo_5Board_4held.size)
    (movesC : Nat)
    (hClear : Ecbs.clear (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩) (5 : Int) =
      .ok (clearHeldBoard (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩) 5 xs movesC hH5 hD5)) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (whiteStep b (Int.ofNat (c.m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (cubePegStep c.src (Int.ofNat (c.m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) =
      .ok (clearHeldBoard (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys ⟨n, k, mvs, slides, holeM, bench, pk, pkS, cOps, hops0⟩ ⟨hH6, hD6⟩) 5 xs movesC hH5 hD5) := by
  rw [hPark, ok_bind]
  rw [copy_band_refines bPark 6 5 g moves peak hHs hDs hH5s hD5s h7 hsrc harr hempty
      hn hf hmoves hpeak hfit, ok_bind]
  rw [← hCopy]
  rw [white_scan_loop_refines c.b0 rowXs c.t0 c.m c.hm hT0 hRow hRoom hWhite hfitW c.hfitM,
    ok_bind]
  rw [cube_peg_loop_refines c, ok_bind]
  dsimp only
  rw [mulHyps, ok_bind, hClear]

/-- The board after the clear, once the final/non-final and white/red branches
    have run. `bD` is the doubled board, `bMulF` the final red product, `bAdd`
    the non-final red board after the extra white peg. -/
def rungStepBoard (bC bD bMulF bAdd : Ecbs.Board) (last : Bool) (rung : Nat) : Ecbs.Board :=
  if last then
    if rung = 2 then bMulF else bC
  else
    if rung = 2 then bAdd else bD

private theorem beq_rung_two (rung : Nat) (h : rung = 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = true := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl, h]
  exact decide_eq_true rfl

private theorem beq_rung_not_two (rung : Nat) (h : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

/-- One emitted rung after the park-through-clear prefix, for every
    final/non-final and white/red combination. `pre` is that prefix, so the
    park is the idle keep or the unpark-then-park, whichever proved `pre`.
    A non-final rung doubles. A red rung cubes the gap and multiplies by `x`.
    A non-final red rung then lays one white peg. -/
theorem rung_step_refines (pre : Except SudoRt.Trap Ecbs.Board) (bC bD bCubeF bMulF
    bCubeO bMulO bAdd : Ecbs.Board) (last : Bool) (rung : Nat) (x : Int)
    (hPre : pre = .ok bC)
    (hDouble : Ecbs.tally_double bC = .ok bD)
    (hCubeF : Ecbs.cube bC (6 : Int) (5 : Int) = .ok bCubeF)
    (hMulF : Ecbs.mul bCubeF (5 : Int) x (6 : Int) false false false = .ok bMulF)
    (hCubeO : Ecbs.cube bD (6 : Int) (5 : Int) = .ok bCubeO)
    (hMulO : Ecbs.mul bCubeO (5 : Int) x (6 : Int) false false false = .ok bMulO)
    (hAdd : Ecbs.tally_add_one bMulO = .ok bAdd) :
    (do
        let b ← pre
        if !last then
          do
            let b ← Ecbs.tally_double b
            if SudoRt.SEq.beq (rung : Int) (2 : Int) then
              do
                let b ← Ecbs.cube b (6 : Int) (5 : Int)
                let b ← Ecbs.mul b (5 : Int) x (6 : Int) false false false
                if !last then Ecbs.tally_add_one b else pure b
            else pure b
        else if SudoRt.SEq.beq (rung : Int) (2 : Int) then
          do
            let b ← Ecbs.cube b (6 : Int) (5 : Int)
            let b ← Ecbs.mul b (5 : Int) x (6 : Int) false false false
            if !last then Ecbs.tally_add_one b else pure b
        else pure b) =
      .ok (rungStepBoard bC bD bMulF bAdd last rung) := by
  rw [hPre, ok_bind]
  by_cases hL : last
  · rw [hL]
    simp only [Bool.not_true, if_false]
    by_cases hR : rung = 2
    · rw [beq_rung_two rung hR]
      simp only [if_true]
      rw [hCubeF, ok_bind, hMulF, ok_bind]
      simp only [Bool.not_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hL, hR]
    · rw [beq_rung_not_two rung hR]
      simp only [Bool.false_eq_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hL, hR]
  · have hLf : last = false := by simpa using hL
    rw [hLf]
    simp only [Bool.not_false, if_true]
    rw [hDouble, ok_bind]
    by_cases hR : rung = 2
    · rw [beq_rung_two rung hR]
      simp only [if_true]
      rw [hCubeO, ok_bind, hMulO, ok_bind, hAdd]
      simp [rungStepBoard, hLf, hR]
    · rw [beq_rung_not_two rung hR]
      simp only [Bool.false_eq_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hLf, hR]

/-- Tally length `invRung` leaves. A final rung keeps it. A non-final rung doubles
    it, and a non-final red rung adds one. -/
def tallyAfter (tally rung : Nat) (last : Bool) : Nat :=
  let tally1 := if last then tally else 2 * tally
  if rung = 2 then (if last then tally1 else tally1 + 1) else tally1

theorem invRung_tally (n k bench : Nat) (x g : List Nat) (tally rung : Nat) (last : Bool) :
    (invRung n k bench x g tally rung last).2 = tallyAfter tally rung last := by
  unfold invRung tallyAfter
  by_cases hL : last <;> by_cases hR : rung = 2 <;> simp [hL, hR]

theorem modelRung_tally (s : ClimbModel) (x : List Nat) (rung hole : Nat) (last : Bool) :
    (modelRung s x rung hole last).tally = tallyAfter s.tally rung last := by
  simp [modelRung, invRung_tally]

theorem tallyAfter_le (tally rung : Nat) (last : Bool) :
    tallyAfter tally rung last ≤ 2 * tally + 1 := by
  unfold tallyAfter
  by_cases hL : last <;> by_cases hR : rung = 2 <;> simp [hL, hR] <;> omega

theorem tallyAfter_ge (tally rung : Nat) (last : Bool) :
    tally ≤ tallyAfter tally rung last := by
  unfold tallyAfter
  by_cases hL : last <;> by_cases hR : rung = 2 <;> simp [hL, hR] <;> omega

theorem paintOnes_get_before (xs : List Nat) (start k j : Nat)
    (hj : j < start) (hlen : j < xs.length) :
    (paintOnes xs start k)[j]'(by rw [paintOnes_length]; exact hlen) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := Nat.ne_of_gt (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
    simp [paintOnes, List.getElem_set, hne, ih]

/-- A non-final white rung doubles the tally: both halves are white, and holes
    past `2 · tally` stay empty. -/
theorem openWhite_seg (row : List Nat) (t0 tally : Nat)
    (hroom : t0 + 2 * tally ≤ row.length)
    (htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < row.length), row[t0 + j]'h = 0) :
    RowSeg (paintOnes (paintOnes (paintRed row t0 tally) t0 tally) (t0 + tally) tally)
      t0 (2 * tally) false := by
  let reds := paintRed row t0 tally
  let back := paintOnes reds t0 tally
  let wide := paintOnes back (t0 + tally) tally
  have htwo : 2 * tally = tally + tally := Nat.two_mul tally
  have hroom' : t0 + tally + tally ≤ row.length := by
    simpa [htwo, Nat.add_assoc] using hroom
  have hhalf : t0 + tally ≤ row.length := Nat.le_trans (Nat.le_add_right _ _) hroom'
  have hlenW : t0 + 2 * tally ≤ wide.length := by
    simpa [wide, back, reds, paintOnes_length, paintRed_length] using hroom
  refine ⟨hlenW, ?_, ?_⟩
  · intro j hj
    by_cases hfst : j < tally
    · have hback := paintOnes_get_lo reds t0 tally j hfst
        (by simpa [reds, paintRed_length] using hhalf)
      have hpre : t0 + j < t0 + tally := Nat.add_lt_add_left hfst t0
      have hlenB : t0 + j < back.length := by
        simpa [back, reds, paintOnes_length, paintRed_length] using
          (Nat.lt_of_lt_of_le hpre hhalf)
      have hbefore := paintOnes_get_before back (t0 + tally) tally (t0 + j) hpre hlenB
      have : wide[t0 + j]'(by
          simpa [wide, back, reds, paintOnes_length, paintRed_length] using
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hroom)) = 1 := by
        simpa [wide, hbefore] using hback
      simpa [wide] using this
    · have hsec : j - tally < tally := by omega
      have hidx : (t0 + tally) + (j - tally) = t0 + j := by omega
      have hlo := paintOnes_get_lo back (t0 + tally) tally (j - tally) hsec
        (by simpa [back, reds, paintOnes_length, paintRed_length] using hroom')
      have : wide[(t0 + tally) + (j - tally)] = 1 := hlo
      simpa [wide, hidx] using this
  · intro _ j hj h
    have hrow : t0 + j < row.length := by
      simpa [wide, back, reds, paintOnes_length, paintRed_length] using h
    have h0 := htail j (by omega) hrow
    have hr := paintRed_get_hi row t0 tally (t0 + j) (by omega) hrow
    have hb := paintOnes_get_hi reds t0 tally (t0 + j) (by omega)
      (by simpa [reds, paintRed_length] using hrow)
    have hw := paintOnes_get_hi back (t0 + tally) tally (t0 + j) (by omega)
      (by simpa [back, reds, paintOnes_length, paintRed_length] using hrow)
    simpa [wide, hw, hb, hr] using h0

theorem afterPark_seg (row : List Nat) (fromHole : Int) (park hole colour t0 tally : Nat)
    (hseg : RowSeg row t0 tally false) (hp : park < t0) (hh : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0) :
    RowSeg (afterPark row fromHole park hole colour) t0 tally false := by
  have hlen : t0 + tally ≤ (afterPark row fromHole park hole colour).length := by
    rw [afterPark_length]; exact hseg.room
  refine ⟨hlen, ?_, ?_⟩
  · intro j hj
    have hget := afterPark_get row fromHole park hole colour (t0 + j)
      (Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le hh (Nat.le_add_right _ _))
      (by
        cases hfrom with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hseg.room)
    simpa [hget] using hseg.colour j hj
  · intro _ j hj h
    have hrow : t0 + j < row.length := by rw [afterPark_length] at h; exact h
    have hget := afterPark_get row fromHole park hole colour (t0 + j)
      (by omega) (by omega)
      (by
        cases hfrom with
        | inl hf => exact Or.inl hf
        | inr hf => exact Or.inr (by omega))
      hrow
    have hz := hseg.beyond rfl j hj hrow
    rw [hget, hz]

/-- One model rung, park writes before `t0`. A final rung turns the white segment
    red. A non-final white rung doubles it. The empty tail past the new length
    stays empty when the row has room for that write. -/
theorem rungRow_final_seg (row : List Nat) (fromHole : Int) (park hole t0 tally colour : Nat)
    (hseg : RowSeg row t0 tally false) (hp : park < t0) (hh : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0) :
    RowSeg (rungRow row fromHole park hole t0 tally colour true) t0 tally true := by
  have hpark := afterPark_seg row fromHole park hole colour t0 tally hseg hp hh hfrom
  have hred := paintRed_seg (afterPark row fromHole park hole colour) t0 tally hpark.room
    (by
      intro j hj
      simpa using hpark.colour j hj)
    (by
      intro j hj h
      exact hpark.beyond rfl j hj h)
  simpa [rungRow, afterTally] using hred

theorem rungRow_open_white_seg (row : List Nat) (fromHole : Int)
    (park hole t0 tally colour : Nat) (hseg : RowSeg row t0 tally false)
    (hp : park < t0) (hh : hole < t0) (hfrom : fromHole < 0 ∨ fromHole.toNat < t0)
    (hroom : t0 + 2 * tally ≤ row.length) (hcolour : colour ≠ 2) :
    RowSeg (rungRow row fromHole park hole t0 tally colour false) t0 (2 * tally) false := by
  have hpark := afterPark_seg row fromHole park hole colour t0 tally hseg hp hh hfrom
  have htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < (afterPark row fromHole park hole colour).length),
      (afterPark row fromHole park hole colour)[t0 + j]'h = 0 := by
    intro j hj h
    exact hpark.beyond rfl j hj h
  have hwhite := openWhite_seg (afterPark row fromHole park hole colour) t0 tally
    (by rw [afterPark_length]; exact hroom) htail
  have hne : (colour = 2) = False := by simpa using hcolour
  simpa [rungRow, afterTally, hne] using hwhite

/-- A non-final red rung doubles the tally and lays one more white peg.
    Holes past that peg stay empty. The extra peg needs one hole beyond the double. -/
theorem openRed_seg (row : List Nat) (t0 tally : Nat)
    (hroom : t0 + 2 * tally < row.length)
    (htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < row.length), row[t0 + j]'h = 0) :
    let wide := paintOnes (paintOnes (paintRed row t0 tally) t0 tally) (t0 + tally) tally
    RowSeg (wide.set (t0 + 2 * tally) 1) t0 (2 * tally + 1) false := by
  intro wide
  have hroomD : t0 + 2 * tally ≤ row.length := Nat.le_of_lt hroom
  have hwhite := openWhite_seg row t0 tally hroomD htail
  have hlenW : wide.length = row.length := by
    simp [wide, paintOnes_length, paintRed_length]
  have hset : t0 + 2 * tally < wide.length := by rw [hlenW]; exact hroom
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_set, hlenW]
    omega
  · intro j hj
    by_cases hlast : j = 2 * tally
    · subst hlast
      simp [List.getElem_set]
    · have hlt : j < 2 * tally := by omega
      have hne : t0 + 2 * tally ≠ t0 + j := by omega
      have hwhiteJ := hwhite.colour j hlt
      have hlenJ : t0 + j < wide.length := by
        rw [hlenW]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt t0) hroomD
      have hback : (wide.set (t0 + 2 * tally) 1)[t0 + j]'(by
          rw [List.length_set]; exact hlenJ) = wide[t0 + j]'hlenJ := by
        simp [List.getElem_set, hne]
      exact hback.trans hwhiteJ
  · intro _ j hj h
    have hlenS : (wide.set (t0 + 2 * tally) 1).length = row.length := by
      rw [List.length_set, hlenW]
    have hrow : t0 + j < row.length := by rw [← hlenS]; exact h
    have hne : t0 + 2 * tally ≠ t0 + j := by omega
    have hlenJ : t0 + j < wide.length := by rw [hlenW]; exact hrow
    have hback : (wide.set (t0 + 2 * tally) 1)[t0 + j]'(by
        rw [List.length_set]; exact hlenJ) = wide[t0 + j]'hlenJ := by
      simp [List.getElem_set, hne]
    have h0 := hwhite.beyond rfl j (by omega) hlenJ
    exact hback.trans h0

/-- Non-final red model row: the parked tally, doubled, plus one white peg. -/
theorem rungRow_open_red_seg (row : List Nat) (fromHole : Int)
    (park hole t0 tally : Nat) (hseg : RowSeg row t0 tally false)
    (hp : park < t0) (hh : hole < t0) (hfrom : fromHole < 0 ∨ fromHole.toNat < t0)
    (hroom : t0 + 2 * tally < row.length) :
    RowSeg (rungRow row fromHole park hole t0 tally 2 false) t0 (2 * tally + 1) false := by
  have hpark := afterPark_seg row fromHole park hole 2 t0 tally hseg hp hh hfrom
  have htail : ∀ j, tally ≤ j →
      ∀ (h : t0 + j < (afterPark row fromHole park hole 2).length),
      (afterPark row fromHole park hole 2)[t0 + j]'h = 0 := by
    intro j hj h
    exact hpark.beyond rfl j hj h
  have hred := openRed_seg (afterPark row fromHole park hole 2) t0 tally
    (by rw [afterPark_length]; exact hroom) htail
  have hR : ((2 : Nat) = 2) = True := by decide
  have hL : (false = true) = False := by decide
  simpa [rungRow, afterTally, hR, hL] using hred

/-- Tally length along a rung list. The head is the next rung; `last` is the
    empty tail, so the final element of the list is the final rung. -/
def climbTally (tally : Nat) : List Nat → Nat
  | [] => tally
  | r :: rs => climbTally (tallyAfter tally r rs.isEmpty) rs

/-- Tally length after the prefix `done`, with `rest` still to come, so a rung
    in `done` is final only when nothing remains after it in `done ++ rest`. -/
def climbTallyPrefix (tally : Nat) : List Nat → List Nat → Nat
  | [], _ => tally
  | r :: done, rest =>
    climbTallyPrefix (tallyAfter tally r ((done ++ rest).isEmpty)) done rest

theorem climbTallyPrefix_nil (tally : Nat) (rest : List Nat) :
    climbTallyPrefix tally [] rest = tally := rfl

theorem climbTallyPrefix_snoc (tally : Nat) (done rest : List Nat) (r : Nat) :
    climbTallyPrefix tally (done ++ [r]) rest =
      tallyAfter (climbTallyPrefix tally done (r :: rest)) r rest.isEmpty := by
  induction done generalizing tally with
  | nil =>
    simp [climbTallyPrefix]
  | cons h done ih =>
    simp [climbTallyPrefix, List.cons_append, ih]

theorem climbTallyPrefix_full (tally : Nat) (rs : List Nat) :
    climbTallyPrefix tally rs [] = climbTally tally rs := by
  induction rs generalizing tally with
  | nil => rfl
  | cons r rs ih =>
    simp [climbTally, climbTallyPrefix, ih]

theorem climbTally_ge (tally : Nat) (rs : List Nat) : tally ≤ climbTally tally rs := by
  induction rs generalizing tally with
  | nil => simp [climbTally]
  | cons r rs ih =>
    simp [climbTally]
    exact Nat.le_trans (tallyAfter_ge tally r rs.isEmpty) (ih _)

/-- The tally after the prefix `done`, then the tally of what remains, is the
    tally of the whole list. It does not depend on how the list is split. -/
theorem climbTally_prefix_rest (tally : Nat) (done rest : List Nat) :
    climbTally (climbTallyPrefix tally done rest) rest =
      climbTally tally (done ++ rest) := by
  induction done generalizing tally rest with
  | nil => simp [climbTallyPrefix]
  | cons r done ih =>
    simp [climbTallyPrefix, climbTally, List.cons_append, ih]

/-- Every prefix tally is at most the tally of the whole list. -/
theorem climbTallyPrefix_le_final (tally : Nat) (done rest : List Nat) :
    climbTallyPrefix tally done rest ≤ climbTally tally (done ++ rest) := by
  rw [← climbTally_prefix_rest]
  exact climbTally_ge _ _

/-- Two rungs still to run means the tally at least doubles before the end. -/
theorem double_le_final (tally : Nat) (rs : List Nat) (h : 2 ≤ rs.length) :
    2 * tally ≤ climbTally tally rs := by
  cases rs with
  | nil => simp at h
  | cons r rs =>
    cases rs with
    | nil => simp at h
    | cons r2 rs =>
      have hstep : 2 * tally ≤ tallyAfter tally r false := by
        unfold tallyAfter
        simp
        by_cases hr : r = 2 <;> simp [hr] <;> omega
      exact Nat.le_trans hstep (climbTally_ge (tallyAfter tally r false) (r2 :: rs))

/-- A non-final red rung pushes the final tally strictly past `2 · tally`. -/
theorem red_final_gt (tally r : Nat) (rest : List Nat) (hr : r = 2) (hrest : rest ≠ []) :
    2 * tally < climbTally tally (r :: rest) := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons r2 rs =>
    have hstep : 2 * tally + 1 ≤ tallyAfter tally r false := by
      unfold tallyAfter
      simp [hr]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (2 * tally))
      (Nat.le_trans hstep (climbTally_ge (tallyAfter tally r false) (r2 :: rs)))

theorem climbTallyPrefix_le (tally : Nat) (done rest : List Nat) :
    climbTallyPrefix tally done rest ≤ (tally + 1) * 2 ^ done.length := by
  induction done generalizing tally rest with
  | nil =>
    simp [climbTallyPrefix]
  | cons r done ih =>
    simp [climbTallyPrefix]
    have hAfter := tallyAfter_le tally r ((done ++ rest).isEmpty)
    have hih := ih (tallyAfter tally r ((done ++ rest).isEmpty)) rest
    have hstep : tallyAfter tally r ((done ++ rest).isEmpty) + 1 ≤ 2 * (tally + 1) := by
      omega
    calc
      climbTallyPrefix (tallyAfter tally r ((done ++ rest).isEmpty)) done rest
          ≤ (tallyAfter tally r ((done ++ rest).isEmpty) + 1) * 2 ^ done.length := hih
      _ ≤ (2 * (tally + 1)) * 2 ^ done.length :=
          Nat.mul_le_mul_right _ hstep
      _ = (tally + 1) * 2 ^ (done.length + 1) := by
          rw [Nat.mul_comm 2 (tally + 1), Nat.mul_assoc, Nat.pow_succ,
            Nat.mul_comm (2 ^ done.length) 2]

theorem invClimb_tally (n k bench : Nat) (x g : List Nat) (tally : Nat) (rs : List Nat) :
    (invClimb n k bench x (g, tally) rs).2 = climbTally tally rs := by
  induction rs generalizing g tally with
  | nil => simp [invClimb, climbTally]
  | cons r rs ih =>
    have h2 := invRung_tally n k bench x g tally r rs.isEmpty
    simp [invClimb, climbTally, h2, ih]

/-- Fold `modelRung`. The hole does not affect the gap or the tally. -/
def modelClimb (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) : List Nat → ClimbModel
  | [] => s
  | r :: rs =>
    modelClimb (modelRung s x r (hole s r rs.isEmpty) rs.isEmpty) x hole rs

theorem modelClimb_spec (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (rs : List Nat) :
    ((modelClimb s x hole rs).gap, (modelClimb s x hole rs).tally) =
      invClimb s.n s.k s.benchlen x (s.gap, s.tally) rs := by
  induction rs generalizing s with
  | nil => simp [modelClimb, invClimb]
  | cons r rs ih =>
    rw [modelClimb]
    have ih' := ih (modelRung s x r (hole s r rs.isEmpty) rs.isEmpty)
    rw [ih']
    simp [modelRung, invClimb, modelRung_value]

theorem modelClimb_tally (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (rs : List Nat) :
    (modelClimb s x hole rs).tally = climbTally s.tally rs := by
  rw [← invClimb_tally, ← modelClimb_spec]

/-- Budgets for one climb. `mMax` bounds the tally. It is at most the geometric
    envelope `(tally0 + 1) · 2 ^ R`, which `climbTallyPrefix_le` always gives.
    A shipped tier uses a smaller cap, the holes left in the control row after
    the tally origin: that envelope does not fit the control row of Demo, Toy,
    Hobby, or Serious. The three `FitsLen` facts are the moves, slides, and ops
    fit in the domain of `invert_number_refines`, taken at this cap. `fitTailM`
    and `fitTailS` are headroom for the unpark, final cube, outer settle, and
    `tally_clear` that follow the ladder. They do not change the rung charge. -/
structure ClimbBudget where
  n : Nat
  bench : Nat
  moves0 : Nat
  slides0 : Nat
  ops0 : Nat
  peak0 : Nat
  tally0 : Nat
  R : Nat
  mMax : Nat
  mMax_le : mMax ≤ (tally0 + 1) * 2 ^ R
  fitM : FitsLen (moves0 + R * rungCharge n bench mMax)
  fitS : FitsLen (slides0 + R * rungSlideCharge n mMax)
  fitO : FitsLen (ops0 + R * (mMax + 3))
  /-- Comb, fold, and the outer settle, past the settle the climb already reserved. -/
  fitTailM : FitsLen (moves0 + R * rungCharge n bench mMax + pegCharge n bench)
  /-- The outer settle's `2 · n` slides, past the settle reserved in `fitS`. -/
  fitTailS : FitsLen (slides0 + R * rungSlideCharge n mMax + 2 * n)
  /-- One more copy, schoolbook, and fold after that tail: the check multiply.
      `n` bounds the copied pegs. The schoolbook is at most `n · (n + 1)` and
      the fold is at most three moves on each hole past `n`. -/
  fitCheckM : FitsLen (moves0 + R * rungCharge n bench mMax + pegCharge n bench +
    n + n * (n + 1) + 3 * (bench - n) + 2 * n)
  /-- Counter at the start of the climb. One `rungCtrl` step is at most
      `3 · mMax + 5`, so the counter after every rung still fits an i64. -/
  ctrl0 : Nat
  fitCtrl : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))
  x : List Nat
  xHome : Nat
  w : Nat
  h : Nat
  r : Nat
  cg : Nat
  control : Nat
  /-- Control-row length plus one fits an i64. This is `BoardOk.fits_control`
      for each shipped tier. -/
  fitControl : FitsLen (control + 1)
  ladder0 : Nat
  /-- Homes 0, 1, and 4. The climb writes the gap and the spare; these three
      stay the lists the walk had when the climb started. -/
  side0 : List Nat
  side1 : List Nat
  side4 : List Nat
  held0 : Bool
  held1 : Bool
  held4 : Bool

/-- One rung's counter growth: at most one `rungCharge` of the current tally,
    one slide charge, `mMax + 3` on every ops slot, and a peak that is
    `raisedPeak` against at most seven homes. -/
structure RungDelta (b b' : Ecbs.Board) (base : ClimbBudget) (m : Nat) : Prop where
  moves : ∃ (mv mv' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
    mv' ≤ mv + rungCharge base.n base.bench m
  slides : ∃ (sl sl' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
    sl' ≤ sl + rungSlideCharge base.n m
  opsSize : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
    b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c c' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(opsSize ▸ hi) = (c' : Int) ∧
      c' ≤ c + (base.mMax + 3)
  peak : ∃ (pk pk' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_4peak = (pk' : Int) ∧
    pk' ≤ max pk 7

/-- `RungDelta` plus the tight conjuncts `mv' + 2 · n ≤ mv + rungCharge` and
    the same for slides. The loose fields are unchanged. Bench composition
    spends the settle inside that `2 · n`. -/
structure RungDeltaTight (b b' : Ecbs.Board) (base : ClimbBudget) (m : Nat) : Prop where
  delta : RungDelta b b' base m
  moveTight : ∃ (mv mv' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
    mv' + 2 * base.n ≤ mv + rungCharge base.n base.bench m
  slideTight : ∃ (sl sl' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
    sl' + 2 * base.n ≤ sl + rungSlideCharge base.n m
  /-- One under `mMax + 3`. Slot 1 grows by at most the tally plus one cube,
      and the mul slot by at most two. -/
  opsTight : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c c' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(delta.opsSize ▸ hi) = (c' : Int) ∧
      c' ≤ c + (base.mMax + 2)

/-- The climb hole `park_rung` reads, and the colour sitting there.
    `climb_holes` walks `ladder0 + R - 1` down to `ladder0`. The hole for
    rung index `ridx` is that list at `ridx`. -/
def climbAt (ladder0 len i : Nat) : Nat := ladder0 + len - 1 - i

theorem climbAt_ge (L R i : Nat) (hi : i < R) : L ≤ climbAt L R i := by
  unfold climbAt
  omega

theorem climbAt_pred (L R i : Nat) (_hi : i + 1 < R) :
    climbAt L R (i + 1) = climbAt L R i - 1 := by
  unfold climbAt
  omega

theorem climbAt_end (L R i : Nat) (hL : 0 < L) (hi : i + 1 = R) :
    climbAt L R (i + 1) = L - 1 := by
  unfold climbAt
  omega

theorem climbAt_ne_sum (L R i park : Nat) (hL : 0 < L) (_hi : i ≤ R) (hp : park = L + R) :
    climbAt L R i ≠ park := by
  intro h
  unfold climbAt at h
  omega

/-- The next climb hole is still before the tally. Indices only walk down
    the ladder, and the last hole is `ladder0 - 1`. -/
theorem climb_hole_next (L R i t0 : Nat) (hL : 0 < L) (hi : i + 1 ≤ R)
    (hold : climbAt L R i < t0) : climbAt L R (i + 1) < t0 := by
  by_cases hlt : i + 1 < R
  · rw [climbAt_pred L R i hlt]
    omega
  · have heq : i + 1 = R := by omega
    rw [climbAt_end L R i hL heq]
    have hcur : climbAt L R i = L := by
      unfold climbAt
      omega
    omega

/-- Later climb holes stay before the tally once the current one does. -/
theorem climb_below (L R i k t0 : Nat) (hL : 0 < L) (hk : i + k ≤ R)
    (hold : climbAt L R i < t0) : climbAt L R (i + k) < t0 := by
  induction k with
  | zero => simpa using hold
  | succ k ih =>
    exact climb_hole_next L R (i + k) t0 hL (by omega) (ih (by omega))

structure ParkRead (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) : Prop where
  ladder0B : b.sudo_5Board_7ladder0 = (base.ladder0 : Int)
  nrungsB : b.sudo_5Board_6nrungs = (base.R : Int)
  climbH : Ecbs.climb_holes b =
    .ok (embed (downFrom (base.ladder0 + base.R - 1) base.R))
  holeLt : climbAt base.ladder0 base.R s.ridx < s.row.length
  parkLt : s.parkAt < s.row.length
  parkNe : climbAt base.ladder0 base.R s.ridx ≠ s.parkAt
  parkLe : s.parkAt ≤ s.high
  parkIn : s.parkAt < base.control
  parkCell : s.fromHole < 0 → s.row[s.parkAt]'(parkLt) = 0
  fromIdle : s.fromHole < 0 → s.fromHole = -1
  fromNat : 0 ≤ s.fromHole → s.fromHole = ((s.fromHole.toNat : Nat) : Int)
  srcOk : 0 ≤ s.fromHole →
    s.fromHole.toNat < s.row.length ∧ s.fromHole.toNat < base.control ∧
      s.fromHole.toNat ≤ s.high ∧
      s.fromHole.toNat ≠ climbAt base.ladder0 base.R s.ridx
  parkHeld : 0 ≤ s.fromHole → ∃ prev, s.row[s.parkAt]'(parkLt) = prev
  nextRung : ∀ r rs, rest = r :: rs →
    s.row[climbAt base.ladder0 base.R s.ridx]'(holeLt) = r ∧ r ≠ 0
  /-- Every still-pending rung, not only the head, sits on its climb hole.
      A successor reads the tail after the hole just consumed. -/
  ladderTail : ∀ k (hk : k < rest.length)
      (hlt : climbAt base.ladder0 base.R (s.ridx + k) < s.row.length),
    s.row[climbAt base.ladder0 base.R (s.ridx + k)]'hlt = rest[k]'(hk) ∧
      rest[k]'(hk) ≠ 0
  fit2 : FitsLen (s.ctrl + 2)
  fit4 : FitsLen ((s.ctrl + 2) + 2)
  fitI : FitsLen (s.ridx + 1)
  l0pos : 0 < base.ladder0
  fitL0 : FitsLen base.ladder0
  fitLR : FitsLen (base.ladder0 + base.R)

/-- Naturals the cube-peg loop reads: ops slot 1, the strict peak, the recorded
    bench hole, the trit gap, and the i64 room for one loop. -/
structure PegRead (b : Ecbs.Board) (s : ClimbModel) (base : ClimbBudget) : Prop where
  opsGt : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  cOps : ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(opsGt) = (c : Int)
  peakS : ∃ (p : Nat), b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  holeM : ∃ (h : Nat), b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (h : Int)
  trits : allTritList s.gap
  top : 0 < s.tally → s.t0 + s.tally - 1 ≤ s.high
  fitRow : FitsLen (s.t0 + s.tally)
  fitTall : FitsLen s.tally
  fitCtrl : FitsLen (s.ctrl + s.tally)
  n_pos : 0 < s.n
  span : 3 * (s.n - 1) + base.cg < s.benchlen
  small : base.w ≤ 1000000 ∧ base.h ≤ 1000000 ∧ base.r ≤ 1000000 ∧
    s.benchlen ≤ 1000001
  n_small : s.n ≤ 1000000
  fitN : FitsLen s.n
  fitBn : FitsLen s.benchlen
  fit3 : FitsLen (3 * (s.n - 1))

/-- Homes 0, 1, and 4, which a climb does not write. -/
structure SideKeep (b : Ecbs.Board) (base : ClimbBudget) : Prop where
  h0H : 0 < b.sudo_5Board_4home.size
  h0D : 0 < b.sudo_5Board_4held.size
  h1H : 1 < b.sudo_5Board_4home.size
  h1D : 1 < b.sudo_5Board_4held.size
  h4H : 4 < b.sudo_5Board_4home.size
  h4D : 4 < b.sudo_5Board_4held.size
  home0 : b.sudo_5Board_4home[0]'h0H = embed base.side0
  held0 : b.sudo_5Board_4held[0]'h0D = base.held0
  home1 : b.sudo_5Board_4home[1]'h1H = embed base.side1
  held1 : b.sudo_5Board_4held[1]'h1D = base.held1
  home4 : b.sudo_5Board_4home[4]'h4H = embed base.side4
  held4 : b.sudo_5Board_4held[4]'h4D = base.held4

private theorem side_cell {α : Type} {a b : Array α} (h : a = b) {i : Nat}
    {ha : i < a.size} {hb : i < b.size} {v : α}
    (hv : b[i]'hb = v) : a[i]'ha = v := by
  subst h
  have : (⟨i, ha⟩ : Fin a.size) = ⟨i, hb⟩ := Fin.ext rfl
  simpa [this] using hv

/-- Same home array and held array, so homes 0, 1, and 4 stay. -/
theorem side_arrays {b b' : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base)
    (hH : b'.sudo_5Board_4home = b.sudo_5Board_4home)
    (hD : b'.sudo_5Board_4held = b.sudo_5Board_4held) :
    SideKeep b' base := by
  refine
    { h0H := by rw [hH]; exact h.h0H
      h0D := by rw [hD]; exact h.h0D
      h1H := by rw [hH]; exact h.h1H
      h1D := by rw [hD]; exact h.h1D
      h4H := by rw [hH]; exact h.h4H
      h4D := by rw [hD]; exact h.h4D
      home0 := side_cell hH h.home0
      held0 := side_cell hD h.held0
      home1 := side_cell hH h.home1
      held1 := side_cell hD h.held1
      home4 := side_cell hH h.home4
      held4 := side_cell hD h.held4 }

/-- The three side cells of `b'` are the three side cells of `b`. -/
theorem side_copy {b b' : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base)
    (h0H : 0 < b'.sudo_5Board_4home.size)
    (h0D : 0 < b'.sudo_5Board_4held.size)
    (h1H : 1 < b'.sudo_5Board_4home.size)
    (h1D : 1 < b'.sudo_5Board_4held.size)
    (h4H : 4 < b'.sudo_5Board_4home.size)
    (h4D : 4 < b'.sudo_5Board_4held.size)
    (e0 : b'.sudo_5Board_4home[0]'h0H = b.sudo_5Board_4home[0]'h.h0H)
    (d0 : b'.sudo_5Board_4held[0]'h0D = b.sudo_5Board_4held[0]'h.h0D)
    (e1 : b'.sudo_5Board_4home[1]'h1H = b.sudo_5Board_4home[1]'h.h1H)
    (d1 : b'.sudo_5Board_4held[1]'h1D = b.sudo_5Board_4held[1]'h.h1D)
    (e4 : b'.sudo_5Board_4home[4]'h4H = b.sudo_5Board_4home[4]'h.h4H)
    (d4 : b'.sudo_5Board_4held[4]'h4D = b.sudo_5Board_4held[4]'h.h4D) :
    SideKeep b' base :=
  { h0H := h0H
    h0D := h0D
    h1H := h1H
    h1D := h1D
    h4H := h4H
    h4D := h4D
    home0 := e0.trans h.home0
    held0 := d0.trans h.held0
    home1 := e1.trans h.home1
    held1 := d1.trans h.held1
    home4 := e4.trans h.home4
    held4 := d4.trans h.held4 }

/-- Writing one home other than 0, 1, or 4 leaves those three cells. -/
theorem side_set {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (i : Nat)
    (hiH : i < b.sudo_5Board_4home.size) (hiD : i < b.sudo_5Board_4held.size)
    (hne0 : i ≠ 0) (hne1 : i ≠ 1) (hne4 : i ≠ 4)
    (arr : Array Int) (flag : Bool) :
    SideKeep
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨i, hiH⟩ arr
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨i, hiD⟩ flag }
      base := by
  let b' := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨i, hiH⟩ arr
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨i, hiD⟩ flag }
  have h0H : 0 < b'.sudo_5Board_4home.size := by
    simp [b', Array.size_set]; exact h.h0H
  have h0D : 0 < b'.sudo_5Board_4held.size := by
    simp [b', Array.size_set]; exact h.h0D
  have h1H : 1 < b'.sudo_5Board_4home.size := by
    simp [b', Array.size_set]; exact h.h1H
  have h1D : 1 < b'.sudo_5Board_4held.size := by
    simp [b', Array.size_set]; exact h.h1D
  have h4H : 4 < b'.sudo_5Board_4home.size := by
    simp [b', Array.size_set]; exact h.h4H
  have h4D : 4 < b'.sudo_5Board_4held.size := by
    simp [b', Array.size_set]; exact h.h4D
  refine
    { h0H := h0H
      h0D := h0D
      h1H := h1H
      h1D := h1D
      h4H := h4H
      h4D := h4D
      home0 := by
        have hne : (⟨i, hiH⟩ : Fin _).1 ≠ 0 := hne0
        have hget := Array.getElem_set_ne b.sudo_5Board_4home ⟨i, hiH⟩ arr
          (by simp [b', Array.size_set]; exact h.h0H) hne
        simpa [b'] using hget.trans h.home0
      held0 := by
        have hne : (⟨i, hiD⟩ : Fin _).1 ≠ 0 := hne0
        have hget := Array.getElem_set_ne b.sudo_5Board_4held ⟨i, hiD⟩ flag
          (by simp [b', Array.size_set]; exact h.h0D) hne
        simpa [b'] using hget.trans h.held0
      home1 := by
        have hne : (⟨i, hiH⟩ : Fin _).1 ≠ 1 := hne1
        have hget := Array.getElem_set_ne b.sudo_5Board_4home ⟨i, hiH⟩ arr
          (by simp [b', Array.size_set]; exact h.h1H) hne
        simpa [b'] using hget.trans h.home1
      held1 := by
        have hne : (⟨i, hiD⟩ : Fin _).1 ≠ 1 := hne1
        have hget := Array.getElem_set_ne b.sudo_5Board_4held ⟨i, hiD⟩ flag
          (by simp [b', Array.size_set]; exact h.h1D) hne
        simpa [b'] using hget.trans h.held1
      home4 := by
        have hne : (⟨i, hiH⟩ : Fin _).1 ≠ 4 := hne4
        have hget := Array.getElem_set_ne b.sudo_5Board_4home ⟨i, hiH⟩ arr
          (by simp [b', Array.size_set]; exact h.h4H) hne
        simpa [b'] using hget.trans h.home4
      held4 := by
        have hne : (⟨i, hiD⟩ : Fin _).1 ≠ 4 := hne4
        have hget := Array.getElem_set_ne b.sudo_5Board_4held ⟨i, hiD⟩ flag
          (by simp [b', Array.size_set]; exact h.h4D) hne
        simpa [b'] using hget.trans h.held4 }

theorem side_withTally {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (row : Array Int) (len ctrl high tmax : Int) :
    SideKeep (withTally b row len ctrl high tmax) base :=
  side_arrays h (withTally_home b row len ctrl high tmax)
    (withTally_held b row len ctrl high tmax)

theorem side_withPark {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (row : Array Int) (ctrl fromHole ridx : Int) :
    SideKeep (withPark b row ctrl fromHole ridx) base :=
  side_arrays h (withPark_home b row ctrl fromHole ridx)
    (withPark_held b row ctrl fromHole ridx)

theorem side_clear {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (home : Nat) (xs : List Nat) (moves : Nat)
    (hin : HomeIn b home)
    (hne0 : home ≠ 0) (hne1 : home ≠ 1) (hne4 : home ≠ 4) :
    SideKeep (clearHeldBoard b home xs moves hin.hH hin.hD) base := by
  have hH : (clearHeldBoard b home xs moves hin.hH hin.hD).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hin.hH⟩ #[] := by
    simp [clearHeldBoard]
  have hD : (clearHeldBoard b home xs moves hin.hH hin.hD).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hin.hD⟩ false := by
    simp [clearHeldBoard]
  exact side_arrays (side_set h home hin.hH hin.hD hne0 hne1 hne4 #[] false) hH hD

theorem side_place {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (home : Nat)
    (hin : HomeIn b home) (xs : List Nat) (moves peak : Nat)
    (hne0 : home ≠ 0) (hne1 : home ≠ 1) (hne4 : home ≠ 4) :
    SideKeep (placeBoard b home hin.hH hin.hD xs moves peak) base := by
  have hH : (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed xs) := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  have hD : (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  exact side_arrays (side_set h home hin.hH hin.hD hne0 hne1 hne4 (embed xs) true) hH hD

theorem side_settle {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (home : Nat)
    (hin : HomeIn b home) (xs : List Nat) (n moves slides peak : Nat)
    (hne0 : home ≠ 0) (hne1 : home ≠ 1) (hne4 : home ≠ 4) :
    SideKeep (settleBoard b home hin.hH hin.hD xs n moves slides peak) base := by
  have hH := settle_home_eq b home hin xs n moves slides peak
  have hD := settle_held_eq b home hin xs n moves slides peak
  exact side_arrays
    (side_set h home hin.hH hin.hD hne0 hne1 hne4 (embed (xs.take n)) true) hH hD

/-- What one rung reads off the board, beyond the gap polynomial and the counters.
    The spare (home 6) is empty. When the gap sits on the bench, home 5 is clear.
    When it sits in the home, the bench is off. The input home stays held. The
    tier layout is the board's. `seg` is the white tally and the empty holes
    past it, or the red segment once the final rung has run. -/
structure ClimbShape (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) : Prop where
  spareH : 6 < b.sudo_5Board_4home.size
  spareD : 6 < b.sudo_5Board_4held.size
  spareE : b.sudo_5Board_4held[6] = false
  h7 : 7 ≤ b.sudo_5Board_4held.size
  gapClear : s.onBench = true →
    b.sudo_5Board_4held[5]'(Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h7) = false
  offWhenHome : s.onBench = false → b.sudo_5Board_8bench_on = false
  xD : base.xHome < b.sudo_5Board_4held.size
  xH : base.xHome < b.sudo_5Board_4home.size
  xHeld : b.sudo_5Board_4held[base.xHome] = true
  xArr : b.sudo_5Board_4home[base.xHome] = embed base.x
  xNe5 : base.xHome ≠ 5
  xNe6 : base.xHome ≠ 6
  gapLen : s.gap.length = s.n
  seg : RowSeg s.row s.t0 s.tally rest.isEmpty
  tierN : b.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int)
  tierK : b.sudo_5Board_1t.sudo_4Tier_1k = (s.k : Int)
  tierB : b.sudo_5Board_1t.sudo_4Tier_8benchlen = (s.benchlen : Int)
  tierW : b.sudo_5Board_1t.sudo_4Tier_1w = (base.w : Int)
  tierH : b.sudo_5Board_1t.sudo_4Tier_1h = (base.h : Int)
  tierR : b.sudo_5Board_1t.sudo_4Tier_1r = (base.r : Int)
  tierCg : b.sudo_5Board_1t.sudo_4Tier_7combgap = (base.cg : Int)
  tierC : b.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int)
  rowLen : s.row.length = base.control
  w0 : 0 < base.w
  h0 : 0 < base.h
  r0 : 0 < base.r
  rlt : base.r < base.h
  n_eq : s.n = base.w * base.h - 1
  k_le : s.k ≤ s.n
  gap_eq : s.n - s.k = base.w * base.r
  side : SideKeep b base
  park : ParkRead b s rest base
  peg : PegRead b s base

/-- Induction hypothesis after the prefix `done`, with `rest` still to run.
    The tally length is `climbTallyPrefix`, proved from the rung list. The
    counters are at most `done.length` charges, and while the gap sits on the
    bench the bound also reserves the pending slide of `2 · n` and one pending
    op. `shape` is the
    spare, the gap home, the tally segment past the current length, the held
    input, and the tier layout. -/
structure ClimbInvK (done rest : List Nat) (b : Ecbs.Board) (s : ClimbModel)
    (base : ClimbBudget) : Prop where
  inv : ClimbInv b s
  idx : s.ridx = done.length
  hn : s.n = base.n
  hbench : s.benchlen = base.bench
  htally0 : s.tally = climbTallyPrefix base.tally0 done rest
  kLe : (done ++ rest).length ≤ base.R
  shape : ClimbShape b s rest base
  moves : ∃ (mv : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    mv + (if s.onBench then 2 * base.n else 0) ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax
  slides : ∃ (sl : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    sl + (if s.onBench then 2 * base.n else 0) ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax
  ops : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      c + (if s.onBench then 1 else 0) ≤
        base.ops0 + done.length * (base.mMax + 3)
  peak : ∃ (pk : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
    pk ≤ max base.peak0 7
  /-- The recorded high is the last peg of the current tally. -/
  highTop : 0 < s.tally → s.high = s.t0 + s.tally - 1
  /-- Park and the climb hole sit strictly before the tally. A rung's writes
      there do not reach the empty tail. -/
  parkBelow : s.parkAt < s.t0
  holeBelow : climbAt base.ladder0 base.R s.ridx < s.t0
  fromBelow : 0 ≤ s.fromHole → s.fromHole.toNat < s.t0
  /-- `climbTally` of the whole rung list. It does not change as rungs finish. -/
  finalLe : s.tally ≤ climbTally base.tally0 (done ++ rest)
  /-- Every hole from the current tally through that final tally is on the row. -/
  tailFit : s.t0 + climbTally base.tally0 (done ++ rest) ≤ s.row.length
  /-- And those holes are empty. A rung only shortens this segment from the left. -/
  tailZero : ∀ k, s.tally ≤ k → k < climbTally base.tally0 (done ++ rest) →
    ∀ (hix : s.t0 + k < s.row.length), s.row[s.t0 + k]'hix = 0
  /-- One double still fits when two rungs remain. Follows from `tailFit`. -/
  openRoom : 2 ≤ rest.length → s.t0 + 2 * s.tally ≤ base.control
  /-- The holes a double reads, up to but not including the end of the tail
      when the final tally is exactly `2 · tally`. -/
  openZero : 2 ≤ rest.length → ∀ k, k < s.tally →
    ∀ (hix : s.t0 + s.tally + k < s.row.length),
      s.row[s.t0 + s.tally + k]'hix = 0
  /-- `tally_max` is a natural below twice the current length. -/
  tmaxLt : ∃ tmax : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
      (0 < s.tally → tmax < 2 * s.tally)
  /-- The control counter stays within `ctrl0` plus one `rungCtrl` step per
      finished rung. -/
  ctrlLe : s.ctrl ≤ base.ctrl0 + done.length * (3 * base.mMax + 5)
  /-- A parked source sits strictly above the climb hole about to be read.
      Nothing is parked at entry, so the implication is vacuous there. A
      successor parks the hole it just read, and the ladder steps down. -/
  srcAbove : 0 ≤ s.fromHole →
    climbAt base.ladder0 base.R s.ridx < s.fromHole.toNat

/-- `ClimbInvK` without the absolute move and slide bounds. A bench-start rung
    slides `2 · pegs` onto the counter before the home program, so those two
    inequalities need not hold. Everything else is unchanged. The i64 fits use
    a headroom hypothesis on the actual counter instead. -/
structure ClimbInvKCore (done rest : List Nat) (b : Ecbs.Board) (s : ClimbModel)
    (base : ClimbBudget) : Prop where
  inv : ClimbInv b s
  idx : s.ridx = done.length
  hn : s.n = base.n
  hbench : s.benchlen = base.bench
  htally0 : s.tally = climbTallyPrefix base.tally0 done rest
  kLe : (done ++ rest).length ≤ base.R
  shape : ClimbShape b s rest base
  ops : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      c ≤ base.ops0 + done.length * (base.mMax + 3)
  peak : ∃ (pk : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
    pk ≤ max base.peak0 7
  highTop : 0 < s.tally → s.high = s.t0 + s.tally - 1
  parkBelow : s.parkAt < s.t0
  holeBelow : climbAt base.ladder0 base.R s.ridx < s.t0
  fromBelow : 0 ≤ s.fromHole → s.fromHole.toNat < s.t0
  finalLe : s.tally ≤ climbTally base.tally0 (done ++ rest)
  tailFit : s.t0 + climbTally base.tally0 (done ++ rest) ≤ s.row.length
  tailZero : ∀ k, s.tally ≤ k → k < climbTally base.tally0 (done ++ rest) →
    ∀ (hix : s.t0 + k < s.row.length), s.row[s.t0 + k]'hix = 0
  openRoom : 2 ≤ rest.length → s.t0 + 2 * s.tally ≤ base.control
  openZero : 2 ≤ rest.length → ∀ k, k < s.tally →
    ∀ (hix : s.t0 + s.tally + k < s.row.length),
      s.row[s.t0 + s.tally + k]'hix = 0
  tmaxLt : ∃ tmax : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
      (0 < s.tally → tmax < 2 * s.tally)
  ctrlLe : s.ctrl ≤ base.ctrl0 + done.length * (3 * base.mMax + 5)
  srcAbove : 0 ≤ s.fromHole →
    climbAt base.ladder0 base.R s.ridx < s.fromHole.toNat

theorem ClimbInvK.toCore {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ClimbInvKCore done rest b s base :=
  { inv := h.inv
    idx := h.idx
    hn := h.hn
    hbench := h.hbench
    htally0 := h.htally0
    kLe := h.kLe
    shape := h.shape
    ops := by
      intro i hi
      obtain ⟨c, hc, hle⟩ := h.ops i hi
      refine ⟨c, hc, ?_⟩
      cases hs : s.onBench <;> simp [hs] at hle <;> omega
    peak := h.peak
    highTop := h.highTop
    parkBelow := h.parkBelow
    holeBelow := h.holeBelow
    fromBelow := h.fromBelow
    finalLe := h.finalLe
    tailFit := h.tailFit
    tailZero := h.tailZero
    openRoom := h.openRoom
    openZero := h.openZero
    tmaxLt := h.tmaxLt
    ctrlLe := h.ctrlLe
    srcAbove := h.srcAbove }

theorem ClimbInvKCore.tally_le {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvKCore done rest b s base)
    (hCap : climbTallyPrefix base.tally0 done rest ≤ base.mMax) :
    s.tally ≤ base.mMax := by
  rw [h.htally0]
  exact hCap

/-- Headroom on the move counter actually stored on the board: one tight
    remainder `rungCharge − 2 · n` still fits an i64. -/
structure MoveHeadroom (b : Ecbs.Board) (n bench mMax : Nat) where
  mv : Nat
  eq : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)
  room : FitsLen (mv + (rungCharge n bench mMax - 2 * n))

/-- Headroom on the slide counter: one tight remainder of the slide charge. -/
structure SlideHeadroom (b : Ecbs.Board) (n mMax : Nat) where
  sl : Nat
  eq : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int)
  room : FitsLen (sl + (rungSlideCharge n mMax - 2 * n))

/-- The same tight remainder, read off a counter that equals the stored one. -/
theorem MoveHeadroom.at {b : Ecbs.Board} {n bench mMax mv : Nat}
    (hM : MoveHeadroom b n bench mMax)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)) :
    FitsLen (mv + (rungCharge n bench mMax - 2 * n)) := by
  have hm : mv = hM.mv := ofNat_inj_nat (hmv.symm.trans hM.eq)
  rw [hm]
  exact hM.room

/-- The same tight slide remainder, read off a counter that equals the stored one. -/
theorem SlideHeadroom.at {b : Ecbs.Board} {n mMax sl : Nat}
    (hS : SlideHeadroom b n mMax)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int)) :
    FitsLen (sl + (rungSlideCharge n mMax - 2 * n)) := by
  have hs : sl = hS.sl := ofNat_inj_nat (hsl.symm.trans hS.eq)
  rw [hs]
  exact hS.room

/-- At entry nothing is parked, so the source-above-hole fact holds outright. -/
theorem srcAbove_of_idle {s : ClimbModel} {L R : Nat} (hF : s.fromHole < 0) :
    0 ≤ s.fromHole → climbAt L R s.ridx < s.fromHole.toNat := by
  intro hge
  omega

/-- The geometric envelope is a legal cap for whatever list is being climbed. -/
theorem climbCap_geom (tally0 R mMax : Nat) (rs done rest : List Nat)
    (hm : mMax = (tally0 + 1) * 2 ^ R)
    (hR : rs.length = R)
    (hrs : rs = done ++ rest) :
    climbTallyPrefix tally0 done rest ≤ mMax := by
  rw [hm]
  have hpre := climbTallyPrefix_le tally0 done rest
  have hlen : done.length ≤ R := by
    have hlenr : (done ++ rest).length = rs.length := by rw [hrs]
    simp at hlenr
    omega
  have hpow : 2 ^ done.length ≤ 2 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hlen
  exact Nat.le_trans hpre (Nat.mul_le_mul_left _ hpow)

theorem ClimbInvK.tally_le {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base)
    (hCap : climbTallyPrefix base.tally0 done rest ≤ base.mMax) :
    s.tally ≤ base.mMax := by
  rw [h.htally0]
  exact hCap

/-- The reserved slide is nonnegative, so the strengthened bound implies the
    old one. -/
theorem ClimbInvK.moves_loose {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ∃ (mv : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
  obtain ⟨mv, heq, hle⟩ := h.moves
  refine ⟨mv, heq, ?_⟩
  cases hs : s.onBench <;> simp [hs] at hle <;> omega

theorem ClimbInvK.slides_loose {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ∃ (sl : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
  obtain ⟨sl, heq, hle⟩ := h.slides
  refine ⟨sl, heq, ?_⟩
  cases hs : s.onBench <;> simp [hs] at hle <;> omega

/-- At entry the bench is off and the counter has not started, so the
    reservation is zero and the strengthened field is `mv ≤ moves0`. -/
theorem moves_reserve_entry (n mv moves0 rc : Nat) (onBench : Bool)
    (hon : onBench = false) (hle : mv ≤ moves0) :
    mv + (if onBench then 2 * n else 0) ≤ moves0 + 0 * rc := by
  simp [hon, Nat.zero_mul, Nat.add_zero]
  exact hle

theorem slides_reserve_entry (n sl slides0 rc : Nat) (onBench : Bool)
    (hon : onBench = false) (hle : sl ≤ slides0) :
    sl + (if onBench then 2 * n else 0) ≤ slides0 + 0 * rc := by
  simp [hon, Nat.zero_mul, Nat.add_zero]
  exact hle

/-- The reserved op is nonnegative, so the strengthened bound implies the old one. -/
theorem ClimbInvK.ops_loose {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        c ≤ base.ops0 + done.length * (base.mMax + 3) := by
  intro i hi
  obtain ⟨c, hc, hle⟩ := h.ops i hi
  refine ⟨c, hc, ?_⟩
  cases hs : s.onBench <;> simp [hs] at hle <;> omega

/-- At entry the bench is off, so the reservation is zero and the field is `c ≤ ops0`. -/
theorem ops_reserve_entry (c ops0 charge : Nat) (onBench : Bool)
    (hon : onBench = false) (hle : c ≤ ops0) :
    c + (if onBench then 1 else 0) ≤ ops0 + 0 * charge := by
  simp [hon, Nat.zero_mul, Nat.add_zero]
  exact hle

theorem ClimbInvK.moves_fit {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ∃ (mv : Nat), b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧ FitsLen mv := by
  obtain ⟨mv, heq, hle⟩ := h.moves_loose
  have hk : done.length ≤ base.R := by
    have := h.kLe
    simp at this
    omega
  exact ⟨mv, heq, rung_budget_fit base.moves0 done.length base.R
    (rungCharge base.n base.bench base.mMax) mv hk hle base.fitM⟩

/-- `rungHigh` keeps "high = last peg of the tally" as the length grows. -/
private theorem modelRung_highTop (s : ClimbModel) (x : List Nat) (rung hole : Nat)
    (last : Bool) (hTop : 0 < s.tally → s.high = s.t0 + s.tally - 1) :
    0 < (modelRung s x rung hole last).tally →
      (modelRung s x rung hole last).high =
        (modelRung s x rung hole last).t0 +
          (modelRung s x rung hole last).tally - 1 := by
  intro hpos
  have ht : (modelRung s x rung hole last).tally = tallyAfter s.tally rung last :=
    modelRung_tally s x rung hole last
  have hh : (modelRung s x rung hole last).high =
      rungHigh s.high s.t0 s.tally rung last := by
    simp [modelRung]
  have h0 : (modelRung s x rung hole last).t0 = s.t0 := by
    simp [modelRung]
  rw [ht] at hpos
  rw [hh, h0, ht]
  by_cases hL : last
  · have hta : tallyAfter s.tally rung last = s.tally := by
      simp [tallyAfter, hL]
    have hhi : rungHigh s.high s.t0 s.tally rung last = s.high := by
      simp [rungHigh, hL]
    rw [hta] at hpos
    rw [hhi, hta]
    exact hTop hpos
  · by_cases hR : rung = 2
    · have hta : tallyAfter s.tally rung last = 2 * s.tally + 1 := by
        simp [tallyAfter, hL, hR]
      have hhi : rungHigh s.high s.t0 s.tally rung last = s.t0 + 2 * s.tally := by
        simp [rungHigh, hL, hR]
      rw [hhi, hta]
      omega
    · have hta : tallyAfter s.tally rung last = 2 * s.tally := by
        simp [tallyAfter, hL, hR]
      have hhi : rungHigh s.high s.t0 s.tally rung last =
          s.t0 + 2 * s.tally - 1 := by
        simp [rungHigh, hL, hR]
      rw [hhi, hta]

/-- Holes at or past the new tally are not written by the rung. Park, the climb
    hole, and an unpark source all sit before `t0`. -/
theorem rungRow_past
    (row : List Nat) (fromHole : Int) (park hole t0 tally colour j : Nat)
    (last : Bool)
    (hp : park < t0) (hh : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0)
    (hnew : t0 + tallyAfter tally colour last ≤ j)
    (hj : j < row.length) :
    (rungRow row fromHole park hole t0 tally colour last)[j]'(by
      rw [rungRow_length]; exact hj) = row[j] := by
  have hjp : park < j := by omega
  have hjh : hole < j := by omega
  have hfromj : fromHole < 0 ∨ fromHole.toNat < j := by
    cases hfrom with
    | inl h => exact Or.inl h
    | inr h =>
      have ht0j : t0 ≤ j := by
        have hge := tallyAfter_ge tally colour last
        omega
      exact Or.inr (Nat.lt_of_lt_of_le h ht0j)
  have hAp := afterPark_get row fromHole park hole colour j hjp hjh hfromj hj
  have hlenA : j < (afterPark row fromHole park hole colour).length := by
    rw [afterPark_length]; exact hj
  unfold rungRow afterTally
  cases last with
  | true =>
    have hcut : t0 + tally ≤ j := by
      unfold tallyAfter at hnew
      simp at hnew
      exact hnew
    have hred := paintRed_get_hi (afterPark row fromHole park hole colour) t0 tally j hcut hlenA
    exact hred.trans hAp
  | false =>
    have hspan : t0 + tally + tally ≤ j := by
      unfold tallyAfter at hnew
      simp at hnew
      by_cases hr : colour = 2
      · simp [hr] at hnew
        omega
      · simp [hr] at hnew
        omega
    have hhalf : t0 + tally ≤ j := by omega
    have hred := paintRed_get_hi (afterPark row fromHole park hole colour) t0 tally j hhalf hlenA
    let reds := paintRed (afterPark row fromHole park hole colour) t0 tally
    have hlenR : j < reds.length := by
      simpa [reds, paintRed_length, afterPark_length] using hj
    have hback := paintOnes_get_hi reds t0 tally j hhalf hlenR
    let back := paintOnes reds t0 tally
    have hlenB : j < back.length := by
      simpa [back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
    have hone := paintOnes_get_hi back (t0 + tally) tally j hspan hlenB
    by_cases hr : colour = 2
    · subst hr
      have hlt : t0 + 2 * tally < j := by
        unfold tallyAfter at hnew
        simp at hnew
        omega
      have hne : t0 + 2 * tally ≠ j := Nat.ne_of_lt hlt
      have hL : (false = true) = False := by decide
      have hR : ((2 : Nat) = 2) = True := by decide
      simp only [hL, hR, ite_false, ite_true, List.getElem_set, hne]
      exact hone.trans (hback.trans (hred.trans hAp))
    · simp only [hr, ↓reduceIte]
      exact hone.trans (hback.trans (hred.trans hAp))

/-- A non-final white rung's paints start at `t0`, so a cell before the tally
    that is neither the park nor the climb hole is unchanged. -/
theorem rungRow_white_below_ge
    (row : List Nat) (fromHole : Int) (park hole t0 tally colour j : Nat)
    (hwhite : colour ≠ 2) (hp : park ≠ j) (hh : hole ≠ j)
    (hfrom : fromHole < 0 ∨ fromHole.toNat ≠ j)
    (hj0 : j < t0) (hj : j < row.length) :
    (rungRow row fromHole park hole t0 tally colour false)[j]'(by
      rw [rungRow_length]; exact hj) = row[j] := by
  have hAp := afterPark_other row fromHole park hole colour j hp hh hfrom hj
  unfold rungRow afterTally
  have hC : (colour = 2) = False := by simpa using hwhite
  have hL : (false = true) = False := by decide
  simp only [hL, hC, ite_false]
  have hlenA : j < (afterPark row fromHole park hole colour).length := by
    rw [afterPark_length]; exact hj
  have hred := paintRed_get_before (afterPark row fromHole park hole colour) t0 tally j hj0 hlenA
  let reds := paintRed (afterPark row fromHole park hole colour) t0 tally
  have hlenR : j < reds.length := by
    simpa [reds, paintRed_length, afterPark_length] using hj
  have hback := paintOnes_get_before reds t0 tally j hj0 hlenR
  let back := paintOnes reds t0 tally
  have hpre : j < t0 + tally := Nat.lt_of_lt_of_le hj0 (Nat.le_add_right _ _)
  have hlenB : j < back.length := by
    simpa [back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hone := paintOnes_get_before back (t0 + tally) tally j hpre hlenB
  exact hone.trans (hback.trans (hred.trans hAp))

theorem rungRow_white_below
    (row : List Nat) (fromHole : Int) (park hole t0 tally colour j : Nat)
    (hF : fromHole < 0) (hwhite : colour ≠ 2)
    (hp : park ≠ j) (hh : hole ≠ j)
    (hj0 : j < t0) (hj : j < row.length) :
    (rungRow row fromHole park hole t0 tally colour false)[j]'(by
      rw [rungRow_length]; exact hj) = row[j] := by
  have hAp := afterPark_off row fromHole park hole colour j hF hp hh hj
  unfold rungRow afterTally
  have hC : (colour = 2) = False := by simpa using hwhite
  have hL : (false = true) = False := by decide
  simp only [hL, hC, ite_false]
  have hlenA : j < (afterPark row fromHole park hole colour).length := by
    rw [afterPark_length]; exact hj
  have hred := paintRed_get_before (afterPark row fromHole park hole colour) t0 tally j hj0 hlenA
  let reds := paintRed (afterPark row fromHole park hole colour) t0 tally
  have hlenR : j < reds.length := by
    simpa [reds, paintRed_length, afterPark_length] using hj
  have hback := paintOnes_get_before reds t0 tally j hj0 hlenR
  let back := paintOnes reds t0 tally
  have hpre : j < t0 + tally := Nat.lt_of_lt_of_le hj0 (Nat.le_add_right _ _)
  have hlenB : j < back.length := by
    simpa [back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hone := paintOnes_get_before back (t0 + tally) tally j hpre hlenB
  exact hone.trans (hback.trans (hred.trans hAp))

/-- An idle non-final red rung writes the extra peg at `t0 + 2 · tally`.
    Climb holes strictly before the tally are neither that peg nor the park write. -/
theorem rungRow_red_below
    (row : List Nat) (fromHole : Int) (park hole t0 tally j : Nat)
    (hF : fromHole < 0) (hp : park ≠ j) (hh : hole ≠ j)
    (hj0 : j < t0) (hj : j < row.length) :
    (rungRow row fromHole park hole t0 tally 2 false)[j]'(by
      rw [rungRow_length]; exact hj) = row[j] := by
  have hAp := afterPark_off row fromHole park hole 2 j hF hp hh hj
  unfold rungRow afterTally
  have hR : ((2 : Nat) = 2) = True := by decide
  have hL : (false = true) = False := by decide
  simp only [hL, hR, ite_false, ite_true]
  have hlenA : j < (afterPark row fromHole park hole 2).length := by
    rw [afterPark_length]; exact hj
  have hred := paintRed_get_before (afterPark row fromHole park hole 2) t0 tally j hj0 hlenA
  let reds := paintRed (afterPark row fromHole park hole 2) t0 tally
  have hlenR : j < reds.length := by
    simpa [reds, paintRed_length, afterPark_length] using hj
  have hback := paintOnes_get_before reds t0 tally j hj0 hlenR
  let back := paintOnes reds t0 tally
  have hpre : j < t0 + tally := Nat.lt_of_lt_of_le hj0 (Nat.le_add_right _ _)
  have hlenB : j < back.length := by
    simpa [back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hone := paintOnes_get_before back (t0 + tally) tally j hpre hlenB
  let wide := paintOnes back (t0 + tally) tally
  have hlenW : j < wide.length := by
    simpa [wide, back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hne : t0 + 2 * tally ≠ j := by omega
  have hset : (wide.set (t0 + 2 * tally) 1)[j]'(by
      rw [List.length_set]; exact hlenW) = wide[j] := by
    simp [List.getElem_set, hne]
  exact hset.trans (hone.trans (hback.trans (hred.trans hAp)))

/-- A parked non-final red rung's extra peg sits at `t0 + 2 · tally`. A climb
    hole before the tally is neither that peg, the park, the source, nor the
    hole just read. -/
theorem rungRow_red_below_ge
    (row : List Nat) (fromHole : Int) (park hole t0 tally j : Nat)
    (hp : park ≠ j) (hh : hole ≠ j)
    (hfrom : fromHole < 0 ∨ fromHole.toNat ≠ j)
    (hj0 : j < t0) (hj : j < row.length) :
    (rungRow row fromHole park hole t0 tally 2 false)[j]'(by
      rw [rungRow_length]; exact hj) = row[j] := by
  have hAp := afterPark_other row fromHole park hole 2 j hp hh hfrom hj
  unfold rungRow afterTally
  have hR : ((2 : Nat) = 2) = True := by decide
  have hL : (false = true) = False := by decide
  simp only [hL, hR, ite_false, ite_true]
  have hlenA : j < (afterPark row fromHole park hole 2).length := by
    rw [afterPark_length]; exact hj
  have hred := paintRed_get_before (afterPark row fromHole park hole 2) t0 tally j hj0 hlenA
  let reds := paintRed (afterPark row fromHole park hole 2) t0 tally
  have hlenR : j < reds.length := by
    simpa [reds, paintRed_length, afterPark_length] using hj
  have hback := paintOnes_get_before reds t0 tally j hj0 hlenR
  let back := paintOnes reds t0 tally
  have hpre : j < t0 + tally := Nat.lt_of_lt_of_le hj0 (Nat.le_add_right _ _)
  have hlenB : j < back.length := by
    simpa [back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hone := paintOnes_get_before back (t0 + tally) tally j hpre hlenB
  let wide := paintOnes back (t0 + tally) tally
  have hlenW : j < wide.length := by
    simpa [wide, back, reds, paintOnes_length, paintRed_length, afterPark_length] using hj
  have hne : t0 + 2 * tally ≠ j := by omega
  have hset : (wide.set (t0 + 2 * tally) 1)[j]'(by
      rw [List.length_set]; exact hlenW) = wide[j] := by
    simp [List.getElem_set, hne]
  exact hset.trans (hone.trans (hback.trans (hred.trans hAp)))

/-- One rung preserves the non-cost fields of `ClimbInvKCore`. The absolute
    move and slide bounds are rebuilt by the caller from `RungDelta`. -/
theorem climbInvKCore_succ {done rest : List Nat} {r : Nat} {b b' : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget} {x : List Nat} {hole : Nat}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hinv : ClimbInv b' (modelRung s x r hole rest.isEmpty))
    (hδ : RungDelta b b' base s.tally)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hshape : ClimbShape b' (modelRung s x r hole rest.isEmpty) rest base)
    (hhole : hole < s.t0)
    (htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < (modelRung s x r hole rest.isEmpty).tally →
          tmax < 2 * (modelRung s x r hole rest.isEmpty).tally))
    (hAt : hole = climbAt base.ladder0 base.R s.ridx) :
    ClimbInvKCore (done ++ [r]) rest b' (modelRung s x r hole rest.isEmpty) base := by
  have hT := h.tally_le hCap
  refine
    { inv := hinv
      idx := ?_
      hn := ?_
      hbench := ?_
      htally0 := ?_
      kLe := ?_
      shape := hshape
      ops := ?_
      peak := ?_
      highTop := modelRung_highTop s x r hole rest.isEmpty h.highTop
      parkBelow := ?_
      holeBelow := ?_
      fromBelow := ?_
      finalLe := ?_
      tailFit := ?_
      tailZero := ?_
      openRoom := ?_
      openZero := ?_
      tmaxLt := htmax
      ctrlLe := ?_
      srcAbove := ?_ }
  · simp [modelRung, h.idx, List.length_append]
  · simp [modelRung, h.hn]
  · simp [modelRung, h.hbench]
  · rw [modelRung_tally, h.htally0]
    exact (climbTallyPrefix_snoc base.tally0 done rest r).symm
  · simpa [List.length_append, List.cons_append] using h.kLe
  · intro i hi
    have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hδ.opsSize]; exact hi
    obtain ⟨c, c', hc, hc', hle⟩ := hδ.ops i hi0
    obtain ⟨c0, hc0, hbound⟩ := h.ops i hi0
    have hcEq : c = c0 := ofNat_inj_nat (hc.symm.trans hc0)
    refine ⟨c', hc', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have h4 : (done.length + 1) * (base.mMax + 3) =
        done.length * (base.mMax + 3) + (base.mMax + 3) := by
      rw [Nat.succ_mul]
    omega
  · obtain ⟨pk, pk', hb, hb', hle⟩ := hδ.peak
    obtain ⟨pk0, hb0, hbound⟩ := h.peak
    have hpk : pk = pk0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨pk', hb', peak_carry base.peak0 pk pk' (by rw [hpk]; exact hbound) hle⟩
  · have hp : (modelRung s x r hole rest.isEmpty).parkAt = s.parkAt := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hp, ht0]
    exact h.parkBelow
  · have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have hri : (modelRung s x r hole rest.isEmpty).ridx = s.ridx + 1 := by
      simp [modelRung]
    rw [ht0, hri]
    have hi : s.ridx + 1 ≤ base.R := by
      rw [h.idx]
      have hk := h.kLe
      simp [List.length_append, List.length_cons] at hk
      omega
    exact climb_hole_next base.ladder0 base.R s.ridx s.t0 h.shape.park.l0pos hi h.holeBelow
  · intro _hnn
    have hf : (modelRung s x r hole rest.isEmpty).fromHole = (hole : Int) := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hf, ht0]
    simpa [Int.toNat_ofNat] using hhole
  · rw [modelRung_tally]
    have hstep : tallyAfter s.tally r rest.isEmpty ≤
        climbTally (tallyAfter s.tally r rest.isEmpty) rest :=
      climbTally_ge _ _
    have hwhole : climbTally (tallyAfter s.tally r rest.isEmpty) rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally] using hpre
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    rw [happ, ← hwhole]
    exact hstep
  · have hlen : (modelRung s x r hole rest.isEmpty).row.length = s.row.length := by
      simp [modelRung, rungRow_length]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hlen, ht0]
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    simpa [happ] using h.tailFit
  · intro k hk hlt hix
    have hrow : (modelRung s x r hole rest.isEmpty).row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    have hk0 : s.tally ≤ k :=
      Nat.le_trans (tallyAfter_ge s.tally r rest.isEmpty) (by simpa [htall] using hk)
    have hlt0 : k < climbTally base.tally0 (done ++ r :: rest) := by
      simpa [happ] using hlt
    have hix0 : s.t0 + k < s.row.length := by
      have hlen : (modelRung s x r hole rest.isEmpty).row.length = s.row.length := by
        rw [hrow, rungRow_length]
      have hix' : s.t0 + k < (modelRung s x r hole rest.isEmpty).row.length := by
        simpa [ht0] using hix
      simpa [hlen] using hix'
    have h0 := h.tailZero k hk0 hlt0 hix0
    have hfrom : s.fromHole < 0 ∨ s.fromHole.toNat < s.t0 := by
      by_cases hf : s.fromHole < 0
      · exact Or.inl hf
      · exact Or.inr (h.fromBelow (by omega))
    have hnew : s.t0 + tallyAfter s.tally r rest.isEmpty ≤ s.t0 + k := by
      have hk' : tallyAfter s.tally r rest.isEmpty ≤ k := by simpa [htall] using hk
      omega
    have hpast := rungRow_past s.row s.fromHole s.parkAt hole s.t0 s.tally r
      (s.t0 + k) rest.isEmpty h.parkBelow hhole hfrom hnew hix0
    simp only [hrow, ht0] at hix ⊢
    exact hpast.trans h0
  · intro hrest
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    rw [ht0, htall]
    have hdouble := double_le_final (tallyAfter s.tally r rest.isEmpty) rest hrest
    have hwhole : climbTally (tallyAfter s.tally r rest.isEmpty) rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally] using hpre
    have hle2 : 2 * tallyAfter s.tally r rest.isEmpty ≤
        climbTally base.tally0 (done ++ r :: rest) := by
      rw [← hwhole]
      exact hdouble
    have hfit := h.tailFit
    rw [h.shape.rowLen] at hfit
    omega
  · intro hrest k hk hix
    have hrow : (modelRung s x r hole rest.isEmpty).row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    let newT := tallyAfter s.tally r rest.isEmpty
    have hkN : k < newT := by simpa [htall, newT] using hk
    have hnewT : newT ≤ newT + k := Nat.le_add_right _ _
    have htwo : newT + k < 2 * newT := by omega
    have hdouble := double_le_final newT rest hrest
    have hwhole : climbTally newT rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally, newT] using hpre
    have hlt0 : newT + k < climbTally base.tally0 (done ++ r :: rest) := by
      rw [← hwhole]
      exact Nat.lt_of_lt_of_le htwo hdouble
    have hk0 : s.tally ≤ newT + k :=
      Nat.le_trans (tallyAfter_ge s.tally r rest.isEmpty) hnewT
    let j := s.t0 + newT + k
    have hixj :
        j < (rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty).length := by
      simpa [hrow, ht0, htall, j, newT] using hix
    have hix0 : s.t0 + (newT + k) < s.row.length := by
      have hjl : j < s.row.length := by
        rw [← rungRow_length (s.row) s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty]
        exact hixj
      simpa [j, newT, Nat.add_assoc] using hjl
    have h0 := h.tailZero (newT + k) hk0 hlt0 hix0
    have hfrom : s.fromHole < 0 ∨ s.fromHole.toNat < s.t0 := by
      by_cases hf : s.fromHole < 0
      · exact Or.inl hf
      · exact Or.inr (h.fromBelow (by omega))
    have hpast := rungRow_past s.row s.fromHole s.parkAt hole s.t0 s.tally r j
      rest.isEmpty h.parkBelow hhole hfrom (Nat.le_add_right _ _)
      (by
        rw [← rungRow_length]
        exact hixj)
    have h0j : s.row[j]'(by
        rw [← rungRow_length]
        exact hixj) = 0 := by
      simpa [j, newT] using
        ((getElem_congr (Nat.add_assoc s.t0 newT k)).trans h0)
    have hcell :
        (rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty)[j]'hixj = 0 :=
      hpast.trans h0j
    simpa [hrow, ht0, htall, j, newT] using hcell
  · have hctrl : (modelRung s x r hole rest.isEmpty).ctrl =
        rungCtrl s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole)) := by
      simp [modelRung]
    rw [hctrl]
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have hinc := rungCtrl_inc s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole))
    have hmul : 3 * s.tally + 5 ≤ 3 * base.mMax + 5 := by
      have := Nat.mul_le_mul_left 3 hT
      omega
    have hgrow : s.ctrl + 3 * s.tally + 5 ≤
        base.ctrl0 + done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) := by
      have hle := h.ctrlLe
      omega
    have hsum : done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) =
        (done.length + 1) * (3 * base.mMax + 5) := by
      rw [← Nat.succ_mul]
    apply Nat.le_trans hinc
    apply Nat.le_trans hgrow
    rw [Nat.add_assoc, hsum]
    exact Nat.le_refl _
  · intro _
    have hf : (modelRung s x r hole rest.isEmpty).fromHole = (hole : Int) := by
      simp [modelRung]
    have hri : (modelRung s x r hole rest.isEmpty).ridx = s.ridx + 1 := by
      simp [modelRung]
    rw [hf, hri, hAt]
    have hdec : climbAt base.ladder0 base.R (s.ridx + 1) <
        climbAt base.ladder0 base.R s.ridx := by
      have hL := h.shape.park.l0pos
      have hidx : s.ridx < base.R := by
        rw [h.idx]
        have hk := h.kLe
        simp [List.length_append, List.length_cons] at hk
        omega
      have hi : s.ridx + 1 ≤ base.R := by omega
      by_cases hlt : s.ridx + 1 < base.R
      · have hpred := climbAt_pred base.ladder0 base.R s.ridx hlt
        have hge := climbAt_ge base.ladder0 base.R s.ridx hidx
        have hpos : 0 < climbAt base.ladder0 base.R s.ridx := by omega
        rw [hpred]
        omega
      · have heq : s.ridx + 1 = base.R := by omega
        have hend := climbAt_end base.ladder0 base.R s.ridx hL heq
        have hcur : climbAt base.ladder0 base.R s.ridx = base.ladder0 := by
          unfold climbAt
          have hr : s.ridx = base.R - 1 := by omega
          rw [hr]
          omega
        omega
    simpa [Int.toNat_ofNat] using hdec

/-- One rung preserves the counter bounds. The new tally is the model's
    `tallyAfter`, so it stays under `mMax` by `climbTallyPrefix_le`.
    The recorded high stays the last peg. The empty tail is the holes from
    the new tally up to the final tally of `done ++ r :: rest`; a rung only
    shortens that segment from the left. `tally_max` is still supplied by
    the step that builds the board. -/
theorem climbInvK_succ {done rest : List Nat} {r : Nat} {b b' : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget} {x : List Nat} {hole : Nat}
    (h : ClimbInvK done (r :: rest) b s base)
    (hinv : ClimbInv b' (modelRung s x r hole rest.isEmpty))
    (hδ : RungDelta b b' base s.tally)
    (hmoveCarry : ∃ (mv mv' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
      mv' + 2 * base.n ≤
        mv + (if s.onBench then 2 * base.n else 0) +
          rungCharge base.n base.bench s.tally)
    (hslideCarry : ∃ (sl sl' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
      sl' + 2 * base.n ≤
        sl + (if s.onBench then 2 * base.n else 0) +
          rungSlideCharge base.n s.tally)
    (hopsCarry : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c c' : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδ.opsSize ▸ hi) = (c' : Int) ∧
        c' + 1 ≤ c + (if s.onBench then 1 else 0) + (base.mMax + 3))
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hshape : ClimbShape b' (modelRung s x r hole rest.isEmpty) rest base)
    (hhole : hole < s.t0)
    (htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < (modelRung s x r hole rest.isEmpty).tally →
          tmax < 2 * (modelRung s x r hole rest.isEmpty).tally))
    (hAt : hole = climbAt base.ladder0 base.R s.ridx) :
    ClimbInvK (done ++ [r]) rest b' (modelRung s x r hole rest.isEmpty) base := by
  have hT := h.tally_le hCap
  have hm : rungCharge base.n base.bench s.tally ≤
      rungCharge base.n base.bench base.mMax :=
    rungCharge_mono base.n base.bench s.tally base.mMax hT
  have hs : rungSlideCharge base.n s.tally ≤ rungSlideCharge base.n base.mMax :=
    rungSlideCharge_mono base.n s.tally base.mMax hT
  refine
    { inv := hinv
      idx := ?_
      hn := ?_
      hbench := ?_
      htally0 := ?_
      kLe := ?_
      shape := hshape
      moves := ?_
      slides := ?_
      ops := ?_
      peak := ?_
      highTop := modelRung_highTop s x r hole rest.isEmpty h.highTop
      parkBelow := ?_
      holeBelow := ?_
      fromBelow := ?_
      finalLe := ?_
      tailFit := ?_
      tailZero := ?_
      openRoom := ?_
      openZero := ?_
      tmaxLt := htmax
      ctrlLe := ?_
      srcAbove := ?_ }
  · simp [modelRung, h.idx, List.length_append]
  · simp [modelRung, h.hn]
  · simp [modelRung, h.hbench]
  · rw [modelRung_tally, h.htally0]
    exact (climbTallyPrefix_snoc base.tally0 done rest r).symm
  · simpa [List.length_append, List.cons_append] using h.kLe
  · obtain ⟨mv, mv', hb, hb', hcarry⟩ := hmoveCarry
    obtain ⟨mv0, hb0, hbound⟩ := h.moves
    have hmv : mv = mv0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨mv', hb', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    have honS : (modelRung s x r hole rest.isEmpty).onBench = true := by
      simp [modelRung]
    rw [hlen]
    simp only [honS, ite_true]
    have hstep : mv' + 2 * base.n ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax := by
      have h1 : mv' + 2 * base.n ≤
          mv + (if s.onBench then 2 * base.n else 0) +
            rungCharge base.n base.bench s.tally := by
        simpa [hmv] using hcarry
      have h2 : mv + (if s.onBench then 2 * base.n else 0) +
            rungCharge base.n base.bench s.tally ≤
          mv + (if s.onBench then 2 * base.n else 0) +
            rungCharge base.n base.bench base.mMax :=
        Nat.add_le_add_left hm _
      have h3 : mv + (if s.onBench then 2 * base.n else 0) +
            rungCharge base.n base.bench base.mMax ≤
          base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
            rungCharge base.n base.bench base.mMax :=
        Nat.add_le_add_right (by simpa [hmv] using hbound) _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    have h4 : (done.length + 1) * rungCharge base.n base.bench base.mMax =
        done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax := by
      rw [Nat.succ_mul]
    have hgoal : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax =
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [h4, Nat.add_assoc]
    exact Nat.le_trans hstep (Nat.le_of_eq hgoal)
  · obtain ⟨sl, sl', hb, hb', hcarry⟩ := hslideCarry
    obtain ⟨sl0, hb0, hbound⟩ := h.slides
    have hsl : sl = sl0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨sl', hb', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    have honS : (modelRung s x r hole rest.isEmpty).onBench = true := by
      simp [modelRung]
    rw [hlen]
    simp only [honS, ite_true]
    have hstep : sl' + 2 * base.n ≤
        base.slides0 + done.length * rungSlideCharge base.n base.mMax +
          rungSlideCharge base.n base.mMax := by
      have h1 : sl' + 2 * base.n ≤
          sl + (if s.onBench then 2 * base.n else 0) +
            rungSlideCharge base.n s.tally := by
        simpa [hsl] using hcarry
      have h2 : sl + (if s.onBench then 2 * base.n else 0) +
            rungSlideCharge base.n s.tally ≤
          sl + (if s.onBench then 2 * base.n else 0) +
            rungSlideCharge base.n base.mMax :=
        Nat.add_le_add_left hs _
      have h3 : sl + (if s.onBench then 2 * base.n else 0) +
            rungSlideCharge base.n base.mMax ≤
          base.slides0 + done.length * rungSlideCharge base.n base.mMax +
            rungSlideCharge base.n base.mMax :=
        Nat.add_le_add_right (by simpa [hsl] using hbound) _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    have h4 : (done.length + 1) * rungSlideCharge base.n base.mMax =
        done.length * rungSlideCharge base.n base.mMax +
          rungSlideCharge base.n base.mMax := by
      rw [Nat.succ_mul]
    have hgoal : base.slides0 + done.length * rungSlideCharge base.n base.mMax +
          rungSlideCharge base.n base.mMax =
        base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
      rw [h4, Nat.add_assoc]
    exact Nat.le_trans hstep (Nat.le_of_eq hgoal)
  · intro i hi
    have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hδ.opsSize]; exact hi
    obtain ⟨c, c', hc, hc', hcarry⟩ := hopsCarry i hi0
    obtain ⟨c0, hc0, hbound⟩ := h.ops i hi0
    have hcEq : c = c0 := ofNat_inj_nat (hc.symm.trans hc0)
    refine ⟨c', ?_, ?_⟩
    · have hix :
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[i] =
            b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδ.opsSize ▸ hi0) := by
        have hfin : (⟨i, hi⟩ : Fin b'.sudo_5Board_4cost.sudo_5Costs_3ops.size) =
            ⟨i, hδ.opsSize ▸ hi0⟩ := Fin.ext rfl
        simp [hfin]
      exact hix.trans hc'
    · have hlen : (done ++ [r]).length = done.length + 1 := by simp
      have honS : (modelRung s x r hole rest.isEmpty).onBench = true := by
        simp [modelRung]
      rw [hlen]
      simp only [honS, ite_true]
      have hstep : c' + 1 ≤
          base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) := by
        have h1 : c' + 1 ≤
            c + (if s.onBench then 1 else 0) + (base.mMax + 3) := by
          simpa [hcEq] using hcarry
        have h2 : c + (if s.onBench then 1 else 0) + (base.mMax + 3) ≤
            base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) :=
          Nat.add_le_add_right (by simpa [hcEq] using hbound) _
        exact Nat.le_trans h1 h2
      have h4 : (done.length + 1) * (base.mMax + 3) =
          done.length * (base.mMax + 3) + (base.mMax + 3) := by
        rw [Nat.succ_mul]
      have hgoalO : base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) =
          base.ops0 + (done.length + 1) * (base.mMax + 3) := by
        rw [h4, Nat.add_assoc]
      exact Nat.le_trans hstep (Nat.le_of_eq hgoalO)
  · obtain ⟨pk, pk', hb, hb', hle⟩ := hδ.peak
    obtain ⟨pk0, hb0, hbound⟩ := h.peak
    have hpk : pk = pk0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨pk', hb', peak_carry base.peak0 pk pk' (by rw [hpk]; exact hbound) hle⟩
  · have hp : (modelRung s x r hole rest.isEmpty).parkAt = s.parkAt := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hp, ht0]
    exact h.parkBelow
  · have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have hri : (modelRung s x r hole rest.isEmpty).ridx = s.ridx + 1 := by
      simp [modelRung]
    rw [ht0, hri]
    have hi : s.ridx + 1 ≤ base.R := by
      rw [h.idx]
      have hk := h.kLe
      simp [List.length_append, List.length_cons] at hk
      omega
    exact climb_hole_next base.ladder0 base.R s.ridx s.t0 h.shape.park.l0pos hi h.holeBelow
  · intro _hnn
    have hf : (modelRung s x r hole rest.isEmpty).fromHole = (hole : Int) := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hf, ht0]
    simpa [Int.toNat_ofNat] using hhole
  · rw [modelRung_tally]
    have hstep : tallyAfter s.tally r rest.isEmpty ≤
        climbTally (tallyAfter s.tally r rest.isEmpty) rest :=
      climbTally_ge _ _
    have hwhole : climbTally (tallyAfter s.tally r rest.isEmpty) rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally] using hpre
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    rw [happ, ← hwhole]
    exact hstep
  · have hlen : (modelRung s x r hole rest.isEmpty).row.length = s.row.length := by
      simp [modelRung, rungRow_length]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    rw [hlen, ht0]
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    simpa [happ] using h.tailFit
  · intro k hk hlt hix
    have hrow : (modelRung s x r hole rest.isEmpty).row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    have happ : (done ++ [r]) ++ rest = done ++ r :: rest := by
      simp [List.append_assoc]
    have hk0 : s.tally ≤ k :=
      Nat.le_trans (tallyAfter_ge s.tally r rest.isEmpty) (by simpa [htall] using hk)
    have hlt0 : k < climbTally base.tally0 (done ++ r :: rest) := by
      simpa [happ] using hlt
    have hix0 : s.t0 + k < s.row.length := by
      have hlen : (modelRung s x r hole rest.isEmpty).row.length = s.row.length := by
        rw [hrow, rungRow_length]
      have hix' : s.t0 + k < (modelRung s x r hole rest.isEmpty).row.length := by
        simpa [ht0] using hix
      simpa [hlen] using hix'
    have h0 := h.tailZero k hk0 hlt0 hix0
    have hfrom : s.fromHole < 0 ∨ s.fromHole.toNat < s.t0 := by
      by_cases hf : s.fromHole < 0
      · exact Or.inl hf
      · exact Or.inr (h.fromBelow (by omega))
    have hnew : s.t0 + tallyAfter s.tally r rest.isEmpty ≤ s.t0 + k := by
      have hk' : tallyAfter s.tally r rest.isEmpty ≤ k := by simpa [htall] using hk
      omega
    have hpast := rungRow_past s.row s.fromHole s.parkAt hole s.t0 s.tally r
      (s.t0 + k) rest.isEmpty h.parkBelow hhole hfrom hnew hix0
    simp only [hrow, ht0] at hix ⊢
    exact hpast.trans h0
  · intro hrest
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    rw [ht0, htall]
    have hdouble := double_le_final (tallyAfter s.tally r rest.isEmpty) rest hrest
    have hwhole : climbTally (tallyAfter s.tally r rest.isEmpty) rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally] using hpre
    have hle2 : 2 * tallyAfter s.tally r rest.isEmpty ≤
        climbTally base.tally0 (done ++ r :: rest) := by
      rw [← hwhole]
      exact hdouble
    have hfit := h.tailFit
    rw [h.shape.rowLen] at hfit
    omega
  · intro hrest k hk hix
    have hrow : (modelRung s x r hole rest.isEmpty).row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty := by
      simp [modelRung]
    have ht0 : (modelRung s x r hole rest.isEmpty).t0 = s.t0 := by
      simp [modelRung]
    have htall : (modelRung s x r hole rest.isEmpty).tally =
        tallyAfter s.tally r rest.isEmpty :=
      modelRung_tally s x r hole rest.isEmpty
    let newT := tallyAfter s.tally r rest.isEmpty
    have hkN : k < newT := by simpa [htall, newT] using hk
    have hnewT : newT ≤ newT + k := Nat.le_add_right _ _
    have htwo : newT + k < 2 * newT := by omega
    have hdouble := double_le_final newT rest hrest
    have hwhole : climbTally newT rest =
        climbTally base.tally0 (done ++ r :: rest) := by
      have hpre : climbTally s.tally (r :: rest) =
          climbTally base.tally0 (done ++ (r :: rest)) := by
        rw [h.htally0]
        exact climbTally_prefix_rest base.tally0 done (r :: rest)
      simpa [climbTally, newT] using hpre
    have hlt0 : newT + k < climbTally base.tally0 (done ++ r :: rest) := by
      rw [← hwhole]
      exact Nat.lt_of_lt_of_le htwo hdouble
    have hk0 : s.tally ≤ newT + k :=
      Nat.le_trans (tallyAfter_ge s.tally r rest.isEmpty) hnewT
    let j := s.t0 + newT + k
    have hixj :
        j < (rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty).length := by
      simpa [hrow, ht0, htall, j, newT] using hix
    have hix0 : s.t0 + (newT + k) < s.row.length := by
      have hjl : j < s.row.length := by
        rw [← rungRow_length (s.row) s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty]
        exact hixj
      simpa [j, newT, Nat.add_assoc] using hjl
    have h0 := h.tailZero (newT + k) hk0 hlt0 hix0
    have hfrom : s.fromHole < 0 ∨ s.fromHole.toNat < s.t0 := by
      by_cases hf : s.fromHole < 0
      · exact Or.inl hf
      · exact Or.inr (h.fromBelow (by omega))
    have hpast := rungRow_past s.row s.fromHole s.parkAt hole s.t0 s.tally r j
      rest.isEmpty h.parkBelow hhole hfrom (Nat.le_add_right _ _)
      (by
        rw [← rungRow_length]
        exact hixj)
    have h0j : s.row[j]'(by
        rw [← rungRow_length]
        exact hixj) = 0 := by
      simpa [j, newT] using
        ((getElem_congr (Nat.add_assoc s.t0 newT k)).trans h0)
    have hcell :
        (rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r rest.isEmpty)[j]'hixj = 0 :=
      hpast.trans h0j
    simpa [hrow, ht0, htall, j, newT] using hcell
  · have hctrl : (modelRung s x r hole rest.isEmpty).ctrl =
        rungCtrl s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole)) := by
      simp [modelRung]
    rw [hctrl]
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have hinc := rungCtrl_inc s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole))
    have hmul : 3 * s.tally + 5 ≤ 3 * base.mMax + 5 := by
      have := Nat.mul_le_mul_left 3 hT
      omega
    have hgrow : s.ctrl + 3 * s.tally + 5 ≤
        base.ctrl0 + done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) := by
      have hle := h.ctrlLe
      omega
    have hsum : done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) =
        (done.length + 1) * (3 * base.mMax + 5) := by
      rw [← Nat.succ_mul]
    apply Nat.le_trans hinc
    apply Nat.le_trans hgrow
    rw [Nat.add_assoc, hsum]
    exact Nat.le_refl _
  · intro _
    have hf : (modelRung s x r hole rest.isEmpty).fromHole = (hole : Int) := by
      simp [modelRung]
    have hri : (modelRung s x r hole rest.isEmpty).ridx = s.ridx + 1 := by
      simp [modelRung]
    rw [hf, hri, hAt]
    have hdec : climbAt base.ladder0 base.R (s.ridx + 1) <
        climbAt base.ladder0 base.R s.ridx := by
      have hL := h.shape.park.l0pos
      have hidx : s.ridx < base.R := by
        rw [h.idx]
        have hk := h.kLe
        simp [List.length_append, List.length_cons] at hk
        omega
      have hi : s.ridx + 1 ≤ base.R := by omega
      by_cases hlt : s.ridx + 1 < base.R
      · have hpred := climbAt_pred base.ladder0 base.R s.ridx hlt
        have hge := climbAt_ge base.ladder0 base.R s.ridx hidx
        have hpos : 0 < climbAt base.ladder0 base.R s.ridx := by omega
        rw [hpred]
        omega
      · have heq : s.ridx + 1 = base.R := by omega
        have hend := climbAt_end base.ladder0 base.R s.ridx hL heq
        have hcur : climbAt base.ladder0 base.R s.ridx = base.ladder0 := by
          unfold climbAt
          have hr : s.ridx = base.R - 1 := by omega
          rw [hr]
          omega
        omega
    simpa [Int.toNat_ofNat] using hdec


end EcbsLink2.Link2
