/-
  `mul` with `onto = false` settles a live bench before it multiplies.
  The prologue is inlined, not a helper shared with `cube`: `cube` settles
  immediately after `log_op`, and `mul` settles only in the else of the
  onto-keep test.
-/
import EcbsLink2.Link2.Cube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem get_eq_of_array {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- `onto = false` and the bench on, aimed at an empty home `home`.
    `Ecbs.mul` bumps the op count and then settles. Settling first and then
    multiplying does the same thing: the second prologue's settle sees the
    bench already off, so it is the identity (`settle_off`; `settle_idem` is
    that fact on the unbumped settled board). The settled board has the bench off. -/
theorem mul_settles_first (b : Ecbs.Board) (dst s1 s2 : Int) (m : Bool)
    (home : Nat) (xs : List Nat) (n moves slides peak cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.mul b dst s1 s2 m false false =
      (Ecbs.settle b >>= fun b' => Ecbs.mul b' dst s1 s2 m false false) ∧
      (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8bench_on = false := by
  refine ⟨?_, settle_bench_off b home ⟨hH, hD⟩ xs n moves slides peak⟩
  have hset := settle_refines b home xs n moves slides peak hH hD h7 hon hto hempty
    hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  rw [hset, ok_bind]
  let bS := settleBoard b home hH hD xs n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
    · rw [show bS = settleBoard b home hH hD xs n moves slides peak from rfl,
        settle_peak b home ⟨hH, hD⟩ xs n moves slides peak hpk, hmk]
    · rw [show bS = settleBoard b home hH hD xs n moves slides peak from rfl,
        settle_keep b home ⟨hH, hD⟩ xs n moves slides peak hpk, hmk]
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b home ⟨hH, hD⟩ xs n moves slides peak
  have hmkRaw :
      (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9marker_on = false :=
    hmkS
  unfold Ecbs.mul Ecbs.log_op
  simp only [hmk, hmkRaw, Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind]
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 home hops ⟨hH, hD⟩ xs n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    have hget := get_eq_of_array (settle_ops b home ⟨hH, hD⟩ xs n moves slides peak) 0 hopsS
    exact hget.trans hop0
  conv =>
    lhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  conv =>
    rhs
    rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hopsS, hop0S, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hopsS, ok_bind]
  let bL : Ecbs.Board :=
    { b with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    lhs
    pattern (Ecbs.settle _)
    change Ecbs.settle bL
  have hbL : bL = bumpOp b 0 cOps hops := by
    apply board_ext
    case hmon => simp [bL, bumpOp, hmk]
    all_goals simp [bL, bumpOp]
  rw [hbL]
  have hsetL := settle_refines (bumpOp b 0 cOps hops) home xs n moves slides peak
      (bump_home_lt b 0 cOps home hops hH) (bump_held_lt b 0 cOps home hops hD) h7
      (by simp [bumpOp, hon]) (by simp [bumpOp, hto]) (by simpa [bumpOp] using hempty)
      (by simp [bumpOp, hbench]) hn hpos hnle hzero hf hfitL
      (by simp [bumpOp, hmoves]) (by simp [bumpOp, hslides]) (by simp [bumpOp, hpeak])
      hpeg hfitM hfitS
  rw [hsetL, ok_bind]
  rw [settle_bump_comm b 0 cOps hops home ⟨hH, hD⟩ xs n moves slides peak]
  let bR : Ecbs.Board :=
    { bS with
      sudo_5Board_9marker_on := false
      sudo_5Board_4cost := { bS.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          bS.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hopsS⟩ (Int.ofNat (cOps + 1)) } }
  conv =>
    rhs
    zeta
    pattern (Ecbs.settle _)
    change Ecbs.settle bR
  have hbR : bR = bumpOp bS 0 cOps hopsS := by
    apply board_ext
    case hmon => simp [bR, bumpOp, hmkS]
    all_goals simp [bR, bumpOp]
  rw [hbR]
  rw [settle_off (bumpOp bS 0 cOps hopsS) (by simp [bumpOp, hoffS]), ok_bind]
  have htier : (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
    unfold settleBoard
    split <;> rfl
  rw [htier]

end EcbsLink2.Link2
