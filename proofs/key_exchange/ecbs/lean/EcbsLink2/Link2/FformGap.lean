/-
  The gap multiplies of `fform_add` do not lay onto the destination, so the
  onto-keep test fails before it reads the bench. The marker step is still
  `marker_step`, and `mulElse` still settles a bench aimed elsewhere.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAdd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A copy or nocopy multiply onto a zero strip, with the mirror flag off,
    folds to `fieldMul`. `laneFold` is `reduceStrip`. -/
theorem zero_school_mul (n k bench : Nat) (xs ys : List Nat) :
    (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)).take n =
      fieldMul n k bench xs ys := rfl

private theorem bump_with (b : Ecbs.Board) (cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
      Ecbs.Board) =
      bumpOp b 0 cOps hops := by
  simp [bumpOp]

/-- `onto = false`, so the keep test does not read the bench. The marker is on.
    `log_op` is `marker_step`, and the multiply continues as `mulElse` on the
    flagged board. `copy` and `mirror` are not inspected: the gap passes
    `copy = true` or `copy = false`, and `mirror = false` except the new up. -/
theorem off_marker (b : Ecbs.Board) (dst first second : Nat)
    (m ctrl mx script cOps n : Nat) (copy mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = true)
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
        copy false mirror =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) copy false mirror
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
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]

/-- `mulElse` settles a bench aimed at `seat` for any copy and mirror flags.
    The marker flag is not read. The multiply that follows is `mulElse` of the
    flagged settle. The gap uses this with `onto = false`. -/
theorem mul_else_flag (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (n moves slides peak : Nat) (copy mirror : Bool)
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
        ((second : Nat) : Int) copy false mirror (markerOn b) =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) copy false mirror
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

/-- The gap multiply's marker step, then the settle inside `mulElse`. `onto` is
    the constant `false`. The flag stays on. -/
theorem off_marker_else (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (m ctrl mx script cOps n moves slides peak : Nat)
    (copy mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
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
        copy false mirror =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) copy false mirror
        (markerOn (settleBoard bU seat hHU hDU lane n moves slides peak)) := by
  intro feed hopsF bU hHU hDU
  rw [off_marker b dst first second m ctrl mx script cOps n copy mirror
      hmk hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops]
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
  exact mul_else_flag bU dst first second seat lane n moves slides peak copy mirror
    hmkU honU htoU hHU hDU h7U hemptyU hbenchU hnU hpos hnle hzero hf hfitL
    hmovesU hslidesU hpeakU hpeg hfitM hfitS

end EcbsLink2.Link2
