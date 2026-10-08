/-
  Export-path multiplication: `onto = false`, `copy_second` does not change the polynomial,
  `mirror = false`. The zero strip, `school_loop_refines`, then `lane_fold_refines`.
  The first `n` holes are `Spec.fieldMul`. Holes at and above `n` are empty, which is what
  `settle` asserts before it slides. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Lane

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

/-- The `multiply` flags: lay `ys` against `xs` on a fresh bench, then the lane fold.
    Copying the second number onto the spare does not change the polynomial. -/
def exportMul (w h r n k bench : Nat) (xs ys : List Nat) (b : Ecbs.Board) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let st ← SudoRt.runLoopOn (ρ := Ecbs.Board)
      (Int.ofNat (n - 1), (b, embed (List.replicate bench 0)))
      (fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0))
      (rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int))
      (fun σ => pure σ.2)
      (fun _ => pure (b, embed (List.replicate bench 0)))
    laneFoldGo w h r n k (Int.ofNat bench) st.1 st.2

private theorem withMoves_here (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_hole (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold withMoves
  rfl

/-- Schoolbook on a zero bench, then the one lane-fold loop. The bench prefix is
    `Spec.fieldMul`, and every hole from `n` up is empty. -/
theorem mul_refines (xs ys : List Nat) (w h r n k moves hole bench : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (hn0 : 0 < n) (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (hspan : 2 * (n - 1) < bench)
    (hxs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfn : FitsLen n) (hfi : FitsLen (2 * (n - 1)))
    (hff : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    exportMul w h r n k bench xs ys b =
      .ok (noteBench (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)))
          (Int.ofNat (topIdx (school n xs ys (List.replicate bench 0) false)))
          (Int.ofNat (moves + schoolMoves xs ys n n +
            foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false))),
        embed (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false))) ∧
    (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)).take n =
      fieldMul n k bench xs ys ∧
    ∀ i, n ≤ i → i < bench →
      coeff (laneFold n (n - k) (school n xs ys (List.replicate bench 0) false)) i = 0 := by
  have hrep : allTritList (List.replicate bench 0) := replicate_trits bench
  have hlen0 : (List.replicate bench 0).length = bench := List.length_replicate bench 0
  have hfs : FitsLen (moves + n * (n + 1)) :=
    FitsLen.of_le hff (Nat.le_add_right _ _)
  have hschool := school_loop_refines xs ys (List.replicate bench 0) moves n false b
    (fun σ => pure σ.2) (fun _ => pure (b, embed (List.replicate bench 0)))
    hn0 hx hy (by rw [hlen0]; exact hspan) hxs hrep hm hfn hfi hfs
  unfold exportMul
  rw [hschool]
  dsimp
  rw [toPure_eq_ok, ok_bind]
  dsimp
  generalize hstEq : school n xs ys (List.replicate bench 0) false = hst
  have hlenS : hst.length = bench := by
    rw [← hstEq, school_length, hlen0]
  have htri : allTritList hst := by
    rw [← hstEq]
    refine school_trits xs ys (List.replicate bench 0) false n hrep ?_
    intro i hi
    rw [hlen0]
    have : i + (n - 1) ≤ 2 * (n - 1) := by omega
    exact Nat.lt_of_le_of_lt this hspan
  have hmov : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
  have hfitF : FitsLen (moves + schoolMoves xs ys n n + 3 * (hst.length - n)) := by
    rw [hlenS]
    exact FitsLen.of_le hff (by omega)
  have hnb : n ≤ bench := by omega
  have hgap0 : 0 < n - k := by
    rw [hgap]
    exact Nat.mul_pos hw hr0
  have hm' : (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n))).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + schoolMoves xs ys n n) := withMoves_here _ _
  have hh' : (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n))).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat hole := by rw [withMoves_hole, hhole]
  have hsm' : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ hst.length ≤ 1000001 := by
    rw [hlenS]
    exact hsm
  have hfitL : FitsLen hst.length := by
    rw [hlenS]
    unfold FitsLen i64MaxNat
    have := hsm.2.2.2
    omega
  rw [← ofNat_eq_natCast bench, ← ofNat_eq_natCast (moves + schoolMoves xs ys n n),
    ← ofNat_eq_natCast (topIdx hst),
    ← ofNat_eq_natCast (moves + schoolMoves xs ys n n + foldCharge n (n - k) hst)]
  rw [lane_fold_refines hst w h r n k (moves + schoolMoves xs ys n n) hole bench
    (withMoves b (Int.ofNat (moves + schoolMoves xs ys n n)))
    hw hh hr hr0 hn hk hgap htri hm' hh' hsm' hnsm hfitF
    hfitL (by rw [hlenS]; exact Nat.le_refl _) (by omega : 0 < bench)]
  refine ⟨rfl, ?_, ?_⟩
  · rw [← hstEq]
    unfold fieldMul laneFold
    rfl
  · intro i hlo hi
    exact laneFold_high n (n - k) hst i hn0 hgap0 (by rw [hlenS]; exact hnb) hlo
      (by rw [hlenS]; exact hi)

end EcbsLink2.Link2
