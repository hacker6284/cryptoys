/-
  `mul gap across spare false true false` on the board `gap_v2z` leaves.
  The bench is aimed at the bottom, so the onto-keep test fails and the call
  is `mulElse`. That settles `v²Z` into the bottom, copies the held gap home
  onto the strip, and adds the across times the spare. The bench prefix is
  `u²Z + v·v²`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformV2z

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem nat_beq_false (a b : Nat) (h : a ≠ b) :
    SudoRt.SEq.beq (a : Int) (b : Int) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b] at hEq
    exact hEq))

private theorem bump_with (b : Ecbs.Board) (cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
      Ecbs.Board) =
      bumpOp b 0 cOps hops := by
  simp [bumpOp]

private theorem fold_ops_here (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

/-- Marker on, bench aimed at `seat`, which is not the destination. `onto` is
    true, so the keep test reads the bench and fails. The multiply is `mulElse`
    on the flagged board the marker step leaves. -/
private theorem onto_marker_miss (b : Ecbs.Board) (dst first second seat : Nat)
    (m ctrl mx script cOps n : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    let feed := markerUpFeed b m ctrl mx
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [markerUpFeed] using hops
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false true false =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false true false
        (markerOn (bumpOp feed 0 cOps hopsF)) := by
  intro feed hopsF
  rw [mul_keep_eq]
  unfold Ecbs.mulKeep
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl]
  conv =>
    lhs
    rw [atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
    dsimp only
    rw [bump_with b cOps hops]
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by
    simp [bumpOp, hm]
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simp [bumpOp, hc]
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simp [bumpOp, hx]
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simp [bumpOp, hscript]
  rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitMk hfitC hfit2]
  rw [← mul_up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  have hU : { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true } =
      markerOn (bumpOp feed 0 cOps hopsF) := by
    simp [markerOn, feed]
  rw [hU]
  have hnL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_1t.sudo_4Tier_1n =
      (n : Int) := by
    simp [bumpOp, markerUpFeed, hn]
  rw [hnL]
  have honL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_8bench_on = true := by
    simp [bumpOp, markerUpFeed, hon]
  have htoL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_8bench_to =
      (seat : Int) := by
    simp [bumpOp, markerUpFeed, hto]
  have hbeq : SudoRt.SEq.beq (seat : Int) ((dst : Nat) : Int) = false :=
    nat_beq_false seat dst hseat
  simp only [honL, htoL, hbeq, Bool.false_eq_true, if_false, if_true, pure_eq_ok, ok_bind]

/-- `mulElse` with `onto` settles a bench aimed at `seat`. The marker flag stays. -/
private theorem onto_else_settle (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (n moves slides peak : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n))) :
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false true false (markerOn b) =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false true false
        (markerOn (settleBoard b seat hH hD lane n moves slides peak)) := by
  have hsettle :
      Ecbs.settle (markerOn b) =
        .ok (markerOn (settleBoard b seat hH hD lane n moves slides peak)) := by
    rw [markerOn_def]
    rw [settle_flag b seat lane n moves slides peak hmk hH hD h7 hon hto hempty
        hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
    rw [settle_refines b seat lane n moves slides peak hH hD h7 hon hto hempty
        hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
    simp only [ok_bind, pure_eq_ok, ← markerOn_def]
  have hoffS :
      (markerOn (settleBoard b seat hH hD lane n moves slides peak)).sudo_5Board_8bench_on =
        false := by
    rw [markerOn_on]
    exact settle_bench_off b seat ⟨hH, hD⟩ lane n moves slides peak
  unfold Ecbs.mulElse
  conv =>
    lhs
    rw [hsettle, ok_bind]
  conv =>
    rhs
    rw [settle_off (markerOn (settleBoard b seat hH hD lane n moves slides peak)) hoffS, ok_bind]

/-- The marker step, then the settle inside the onto `mulElse`. The bench is
    aimed at `seat`, not at the destination, so the keep test fails. -/
private theorem onto_miss_else (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (m ctrl mx script cOps n moves slides peak : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n))) :
    let feed := markerUpFeed b m ctrl mx
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [markerUpFeed] using hops
    let bU := bumpOp feed 0 cOps hopsF
    let hHU : seat < bU.sudo_5Board_4home.size := by
      simpa [bU, bumpOp, feed, markerUpFeed] using hH
    let hDU : seat < bU.sudo_5Board_4held.size := by
      simpa [bU, bumpOp, feed, markerUpFeed] using hD
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false true false =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false true false
        (markerOn (settleBoard bU seat hHU hDU lane n moves slides peak)) := by
  intro feed hopsF bU hHU hDU
  rw [onto_marker_miss b dst first second seat m ctrl mx script cOps n
      hmk hon hto hseat hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops]
  have hmkU : bU.sudo_5Board_9marker_on = false := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have honU : bU.sudo_5Board_8bench_on = true := by
    simp [bU, bumpOp, feed, markerUpFeed, hon]
  have htoU : bU.sudo_5Board_8bench_to = (seat : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hto]
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using h7
  have hemptyU : bU.sudo_5Board_4held[seat] = false := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hempty
  have hbenchU : bU.sudo_5Board_5bench = embed lane := by
    simp [bU, bumpOp, feed, markerUpFeed, hbench]
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hn]
  have hmovesU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [bU, bumpOp, feed, markerUpFeed, hmoves]
  have hslidesU : bU.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [bU, bumpOp, feed, markerUpFeed, hslides]
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [bU, bumpOp, feed, markerUpFeed, hpeak]
  exact onto_else_settle bU dst first second seat lane n moves slides peak
    hmkU honU htoU hHU hDU h7U hemptyU hbenchU hnU hpos hnle hzero hf hfitL
    hmovesU hslidesU hpeakU hpeg hfitM hfitS

/-- The onto multiply after `gap_v2z`. `cOps` is the cell that multiply left,
    the rise's cell plus 5. This call leaves the rise's cell plus 6. The bench
    it reads holds `v²Z` and is aimed at the bottom, which is empty. The gap
    holds `u²Z`. The prefix left on the bench is `u²Z + v·v²`, aimed at the gap.
    The bottom keeps `v²Z`. The gap and the spare end empty. -/
theorem gap_sum_on_v2z (b : Ecbs.Board) (gap across sp bot : Nat)
    (u v v2 u2z z lane : List Nat)
    (m ctrl mx script cOps cRise n k w h r moves slides hole peak peakS bench : Nat)
    (hRead : cOps = cRise + 5)
    (hGH : gap < b.sudo_5Board_4home.size)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hHeldG : b.sudo_5Board_4held[gap] = true)
    (hArrG : b.sudo_5Board_4home[gap] = embed u2z)
    (hAH : across < b.sudo_5Board_4home.size)
    (hAD : across < b.sudo_5Board_4held.size)
    (hHeldA : b.sudo_5Board_4held[across] = true)
    (hArrA : b.sudo_5Board_4home[across] = embed v)
    (hSH : sp < b.sudo_5Board_4home.size)
    (hSD : sp < b.sudo_5Board_4held.size)
    (hHeldS : b.sudo_5Board_4held[sp] = true)
    (hArrS : b.sudo_5Board_4home[sp] = embed v2)
    (hBH : bot < b.sudo_5Board_4home.size)
    (hBD : bot < b.sudo_5Board_4held.size)
    (hemptyB : b.sudo_5Board_4held[bot] = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (bot : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (htake : lane.take n = fieldMul n k bench v2 z)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitSettle : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitSlide : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hneGB : gap ≠ bot) (hneGS : gap ≠ sp) (hneGA : gap ≠ across)
    (hneAS : across ≠ sp) (hneAB : across ≠ bot) (hneSB : sp ≠ bot)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenU : u2z.length = n) (hlenv : v.length = n) (hlenv2 : v2.length = n)
    (hu2 : u2z = fieldMul n k bench z (fieldMul n k bench u u))
    (hv2 : v2 = fieldMul n k bench v v)
    (hpeak7 : 7 ≤ peak)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList u2z) (hv : allTritList v)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen ((moves + 2 * pegCount (lane.take n)) + 2 * n))
    (hfitS : FitsLen ((slides + 2 * pegCount (lane.take n)) + 2 * n))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + 2 * n + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + 2 * n + n * (n + 1) +
        3 * (bench - n))) :
    ∃ (b' : Ecbs.Board) (lane' : List Nat),
      Ecbs.mul b ((gap : Nat) : Int) ((across : Nat) : Int) ((sp : Nat) : Int)
          false true false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n =
        fieldAdd n
          (fieldMul n k bench z (fieldMul n k bench u u))
          (fieldMul n k bench v (fieldMul n k bench v v)) ∧
      (∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h = Int.ofNat (cRise + 6)) ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = ((gap : Nat) : Int) ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      (∀ h : bot < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[bot]'h =
          embed (fieldMul n k bench (fieldMul n k bench v v) z)) ∧
      (∀ h : bot < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[bot]'h = true) ∧
      (∀ h : gap < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[gap]'h = false) ∧
      (∀ h : sp < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[sp]'h = false) := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : bot < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hBH
  let hDU : bot < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hBD
  let bS := markerOn (settleBoard bU bot hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU bot := ⟨hHU, hDU⟩
  have hflag := onto_miss_else b gap across sp bot lane m ctrl mx script cOps n moves slides
    peak hmk hon hto (Ne.symm hneGB) hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0
    hfops hBH hBD h7 hemptyB hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg
    hfitSettle hfitSlide
  let movesS := moves + 2 * pegCount (lane.take n)
  let slidesS := slides + 2 * pegCount (lane.take n)
  have hno : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨bot, hDU⟩ true) 7 := by
    have hle : countHeld (bU.sudo_5Board_4held.set ⟨bot, hDU⟩ true) 7 ≤ 7 :=
      countHeld_seven _
    omega
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [bU, bumpOp, feed, markerUpFeed, hpeak]
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakB : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [hcostS, settle_peak_eq bU bot hinS lane n moves slides peak hpeakU, if_neg hno,
      ofNat_eq_natCast]
  have hmovesB : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (movesS : Int) := by
    rw [hcostS, settle_moves_eq bU bot hinS lane n moves slides peak]
    simp [movesS, ofNat_eq_natCast]
  have hslidesB : bS.sudo_5Board_4cost.sudo_5Costs_6slides = (slidesS : Int) := by
    rw [hcostS, settle_slides_eq bU bot hinS lane n moves slides peak]
    simp [slidesS, ofNat_eq_natCast]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU bot ⟨hHU, hDU⟩ lane n moves slides peak
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [show bS.sudo_5Board_1t =
        (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_1t from by
          dsimp [bS, markerOn],
      settle_tier_eq bU bot hinS lane n moves slides peak]
    simp [bU, bumpOp, feed, markerUpFeed, hbl]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have hGapD : gap < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU bot hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hGD
  have hGapH : gap < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU bot hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hGH
  have hHeldGS : bS.sudo_5Board_4held[gap]'(hGapD) = true := by
    have hset := settle_held_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) gap hGapD
    rw [Array.getElem_set_ne (h := Ne.symm hneGB)] at hget
    have hGU : gap < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hGD
    exact (hget.trans (idx_eq hheldU gap hGU)).trans hHeldG
  have hHomeGS : bS.sudo_5Board_4home[gap]'(hGapH) = embed u2z := by
    have hset := settle_home_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) gap hGapH
    rw [Array.getElem_set_ne (h := Ne.symm hneGB)] at hget
    have hGU : gap < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hGH
    exact (hget.trans (idx_eq hhomeU gap hGU)).trans hArrG
  have hAccD : across < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU bot hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hAD
  have hAccH : across < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU bot hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hAH
  have hHeldAS : bS.sudo_5Board_4held[across]'(hAccD) = true := by
    have hset := settle_held_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) across hAccD
    rw [Array.getElem_set_ne (h := Ne.symm hneAB)] at hget
    have hAU : across < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hAD
    exact (hget.trans (idx_eq hheldU across hAU)).trans hHeldA
  have hHomeAS : bS.sudo_5Board_4home[across]'(hAccH) = embed v := by
    have hset := settle_home_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) across hAccH
    rw [Array.getElem_set_ne (h := Ne.symm hneAB)] at hget
    have hAU : across < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hAH
    exact (hget.trans (idx_eq hhomeU across hAU)).trans hArrA
  have hSpD : sp < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU bot hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hSD
  have hSpH : sp < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU bot hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hSH
  have hHeldSS : bS.sudo_5Board_4held[sp]'(hSpD) = true := by
    have hset := settle_held_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) sp hSpD
    rw [Array.getElem_set_ne (h := Ne.symm hneSB)] at hget
    have hSU : sp < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSD
    exact (hget.trans (idx_eq hheldU sp hSU)).trans hHeldS
  have hHomeSS : bS.sudo_5Board_4home[sp]'(hSpH) = embed v2 := by
    have hset := settle_home_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) sp hSpH
    rw [Array.getElem_set_ne (h := Ne.symm hneSB)] at hget
    have hSU : sp < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hSH
    exact (hget.trans (idx_eq hhomeU sp hSU)).trans hArrS
  have hBotD : bot < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU bot hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hBD
  have hBotH : bot < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU bot hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hBH
  have hHeldBS : bS.sudo_5Board_4held[bot]'(hBotD) = true := by
    have hset := settle_held_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) bot hBotD
    rw [hget]
    simp [Array.getElem_set]
  have hHomeBS : bS.sudo_5Board_4home[bot]'(hBotH) = embed (lane.take n) := by
    have hset := settle_home_eq bU bot hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) bot hBotH
    rw [hget]
    simp [Array.getElem_set]
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU bot hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU bot hinS lane n moves slides peak]
    simp [bU, bumpOp, feed, markerUpFeed, hstrict]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU bot hinS lane n moves slides peak]
    simp [bU, bumpOp, feed, markerUpFeed, hhole]
  have helse := mul_onto_else bS gap across sp u2z v v2 n movesS slidesS peakS bench
    hoffS hblS hGapD hGapH hHeldGS hHomeGS hAccD hAccH hHeldAS hHomeAS hSpD hSpH hHeldSS
    hHomeSS h7S hneGA hneGS hneAS hn0 hnb hlenU hlenv hlenv2 hf hmovesB hslidesB hstrictS
    hspan hhomeT hv hfi hfitM hfitS hfm
  let peg := pegCount u2z
  let pad := pref u2z bench n
  let sch := school n v v2 pad false
  let mvN := movesS + 2 * peg + schoolMoves v v2 n n
  let bFold := withMoves
      (mulPrep (ontoCharge bS gap hGapD hGapH movesS slidesS peg)
        ((gap : Nat) : Int) (embed pad) sp peakS
        (by rw [ontoCharge_held_size]; exact hSpD)
        (by rw [ontoCharge_home_size]; exact hSpH))
      (Int.ofNat mvN)
  have hschLen : sch.length = bench := by
    have hpad : pad.length = bench := pref_length hnb (Nat.le_of_eq hlenU.symm)
    simpa [sch, pad, hpad] using school_length v v2 pad false n
  have hschT : allTritList sch :=
    school_trits v v2 pad false n (pref_trits u2z bench n hhomeT hnb (Nat.le_of_eq hlenU.symm))
      (by
        intro i hi
        rw [pref_length hnb (Nat.le_of_eq hlenU.symm)]
        have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
        have hle : i + (n - 1) ≤ 2 * (n - 1) := by
          rw [Nat.two_mul]
          exact Nat.add_le_add_right hi' (n - 1)
        exact Nat.lt_of_le_of_lt hle hspan)
  have hmB : bFold.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvN := by
    simp [bFold]
  have hpeakF : bFold.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, ontoCharge, hpeakB]
  have hholeF : bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, ontoCharge, hholeS]
  have h7F : 7 ≤ bFold.sudo_5Board_4held.size := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, ontoCharge, Array.size_set]
    exact h7S
  have htierS : bS.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [show bS.sudo_5Board_1t =
        (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_1t from by
          dsimp [bS, markerOn],
      settle_tier_eq bU bot hinS lane n moves slides peak]
    simp [bU, bumpOp, feed, markerUpFeed]
  have htierF : bFold.sudo_5Board_1t =
      (ontoCharge bS gap hGapD hGapH movesS slidesS peg).sudo_5Board_1t := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed]
  have hwF : bFold.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierF, ontoCharge_tier, htierS, hw]
  have hhF : bFold.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierF, ontoCharge_tier, htierS, hh]
  have hrF : bFold.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierF, ontoCharge_tier, htierS, hr]
  have hnF : bFold.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    rw [htierF, ontoCharge_tier, htierS, hn, ofNat_eq_natCast]
  have hkF : bFold.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierF, ontoCharge_tier, htierS, hk]
  have hblF : bFold.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, ontoCharge, hblS]
  have hfitF : FitsLen (mvN + 3 * (sch.length - n)) := by
    rw [hschLen]
    refine FitsLen.of_le hfold ?_
    have hsch : schoolMoves v v2 n n ≤ n * (n + 1) := schoolMoves_bound v v2 n
    simp only [mvN, movesS, peg]
    have hpeg : pegCount u2z ≤ n := by simpa [hlenU] using pegCount_le u2z
    omega
  have hOk := mulAfter_ok bFold sch w h r n k mvN hole bench peak
      (by rw [hschLen]; exact hfitB) hwF hhF hrF hnF hkF hblF hw0 hh0 hrR hrP hnE hkLe hgapN
      hschT hmB hholeF hpeakF h7F (by rw [hschLen]; exact hsm) hnsm hfitF
      (by rw [hschLen]; exact Nat.le_refl bench) (Nat.lt_of_lt_of_le hn0 hnb)
  let bOut := ontoFoldBoard bFold sch n k mvN peak
  have hmul : Ecbs.mulElse ((n : Nat) : Int) ((gap : Nat) : Int) ((across : Nat) : Int)
      ((sp : Nat) : Int) false true false bS = .ok bOut := by
    erw [helse]
    change mulAfter (Int.ofNat 0, (bFold, embed sch)) = .ok bOut
    exact hOk
  have hlay : OntoLay bOut bS gap sp slidesS peg (mvN + foldCharge n (n - k) sch) := by
    simpa [bOut, bFold, peg, pad, sch, mvN] using
      onto_result_lay bS gap sp pad peakS movesS slidesS peg mvN n k peak sch
        hGapD hGapH
        (by rw [ontoCharge_held_size]; exact hSpD)
        (by rw [ontoCharge_home_size]; exact hSpH)
        hneGS
  have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops = bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops
        from by dsimp [bS, markerOn]]
    exact settle_ops bU bot hinS lane n moves slides peak
  have hopSet := bumpOp_ops feed 0 cOps hopsF
  have hszU : 0 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopSet, Array.size_set]
    exact hopsF
  have hopU : bU.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hszU = Int.ofNat (cOps + 1) :=
    cell_eq_of hopSet
      (Array.getElem_set_eq feed.sudo_5Board_4cost.sudo_5Costs_3ops ⟨0, hopsF⟩
        (Int.ofNat (cOps + 1)) rfl (by rw [Array.size_set]; exact hopsF))
  have hopsFeq : bFold.sudo_5Board_4cost.sudo_5Costs_3ops =
      bS.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, ontoCharge]
  have hopsOut : bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
      bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
        (ontoFoldBoard bFold sch n k mvN peak).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
      fold_ops_here bFold sch n k mvN peak, hopsFeq, hopsS]
  have hszOut : 0 < bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsOut]; exact hszU
  have hopOut : bOut.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hszOut = Int.ofNat (cOps + 1) :=
    cell_eq_of hopsOut hopU
  have hc : cOps + 1 = cRise + 6 := by
    rw [hRead]
  have hmU : bU.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hcU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hmS : bS.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    rw [show bS.sudo_5Board_6marker =
        (settleBoard bU bot hHU hDU lane n moves slides peak).sudo_5Board_6marker from by
          dsimp [bS, markerOn],
      settle_ix_eq bU bot hinS lane n moves slides peak, hmU]
  have hBotKeep : bOut.sudo_5Board_4home[bot]'(by rw [hlay.szH]; exact hBotH) =
      embed (lane.take n) := by
    have hget := hlay.homeK bot (Ne.symm hneGB) (Ne.symm hneSB) hBotH
      (by rw [hlay.szH]; exact hBotH)
    exact hget.trans hHomeBS
  have hBotHeld : bOut.sudo_5Board_4held[bot]'(by rw [hlay.szD]; exact hBotD) = true := by
    have hget := hlay.heldK bot (Ne.symm hneGB) (Ne.symm hneSB) hBotD
      (by rw [hlay.szD]; exact hBotD)
    exact hget.trans hHeldBS
  refine ⟨bOut, laneFold n (n - k) sch, ?_, ?_, ?_, ?_, hlay.on, hlay.to_,
      hlay.flag.trans (by simp [bS, markerOn]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hflag]
    exact hmul
  · simpa [bOut, sch, pad] using ontoFoldBoard_bench bFold sch n k mvN peak
  · rw [show (laneFold n (n - k) sch).take n =
        (laneFold n (n - k) (school n v v2 (pref u2z bench n) false)).take n from rfl]
    rw [mul_onto_add n k bench v v2 u2z hhomeT hlenU hspan hnb, hu2, hv2]
  · intro h
    simpa [hc] using (idx_irrel).trans hopOut
  · rw [hlay.marker, hmS]
  · intro h
    rw [(idx_irrel).trans hBotKeep, htake, hv2]
  · intro h
    exact (idx_irrel).trans hBotHeld
  · intro h
    exact hlay.heldD h
  · intro h
    exact hlay.heldS h

end EcbsLink2.Link2
