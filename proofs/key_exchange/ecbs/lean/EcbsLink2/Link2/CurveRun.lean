/-
  `on_curve` and `curve_test` from the prefix, the cube, the spare settle, and
  the add-through-clears tail. `settleBoard` and `placeBoard` stay irreducible
  here: each step is an equality on a variable board. Proof-only. Not a security
  claim.
-/
import EcbsLink2.Link2.CurveAsm
import EcbsLink2.Link2.CurveCube
import EcbsLink2.Link2.CurveSpare

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] settleBoard placeBoard

private theorem bind_assoc {α β γ}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m <;> simp [ok_bind]

/-- `on_curve` on the two-put board is the curve predicate. -/
theorem curve_on_refines (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (x y : List Nat) (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y) :
    ∃ bF, Ecbs.on_curve (boardCurve t x y) =
      .ok (onCurve t.n t.k t.benchlen x y, bF) := by
  obtain ⟨b, lane, moves, pk, peakS, holeN, h5H, h5D, hops1, hpres, hmk, hon, hto, hempty,
      hbench, hT, hmoves, hslides, hpeak, hhome2, hheld2, hhome3, hheld3, hhome4, hheld4,
      hheld6, hszH, hszD, hpos, hnle, hzero, hop1, hop0, hstrict, hhole, htake, hmv⟩ :=
    curve_on_prefix t lay sat x y hx hy hxt hyt
  obtain ⟨bC, pkC, peakC, holeC, mvC, slC, hC, hmkC, honC, htoC, hbenchC, htakeC, hlenC,
      hzeroC, hszHC, hszDC, hheld2C, hhome2C, hheld3C, hhome3C, hheld4C, hhome4C, hheld5C,
      hhome5C, hheld6C, hmovC, hslC, hpkC, hstC, hhC, hTC, hops0C, hop0C, hmvC, hslCle⟩ :=
    curve_cube_step t lay sat b x y lane moves pk peakS holeN h5H h5D hops1 hx hxt
      hmk hon hto hempty hbench hT hmoves hslides hpeak hhome2 hheld2 hhome3 hheld3
      hhome4 hheld4 hheld6 hszH hszD hpos hnle hzero hop1 hop0 hstrict hhole htake hmv
  rw [hpres, hC, ok_bind, bind_assoc]
  obtain ⟨bS, mvF, h2H, h2D, h5Hs, h5Ds, h6H, h6D, hS, hh2, ha2, hh5, ha5, hh6, ha6, hnS,
      hmS, hfit, hf, hfitC, hfitW, hfitG, hfitBot⟩ :=
    curve_spare_step t lay sat bC x y pkC peakC holeC mvC slC hx hxt
      hmkC honC htoC hszHC hszDC hheld2C hhome2C hheld3C hhome3C hheld4C hhome4C
      hheld5C hhome5C hheld6C hbenchC htakeC hlenC hzeroC hmovC hslC hpkC hstC hhC hTC
      hops0C hop0C hmvC hslCle
  rw [hS, ok_bind]
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  let x3 := fieldCube n k bench x
  let x2 := fieldMul n k bench x x
  let y2 := fieldMul n k bench y y
  have hnb : n ≤ bench := mul_span_n n bench lay.board.n_pos lay.mul_span
  have hspan : 3 * (n - 1) < bench := cube_span_le n bench t.combgap sat.cube_span
  have hx3 : x3.length = n := by simpa [x3, n, k, bench] using fieldCube_length n k bench x hnb
  have hx2 : x2.length = n := by simpa [x2, n, k, bench] using fieldMul_length n k bench x x hnb
  have hy2 : y2.length = n := by simpa [y2, n, k, bench] using fieldMul_length n k bench y y hnb
  have ht3 : allTritList x3 := by
    simpa [x3, n, k, bench] using fieldCube_trits n k bench x hxt hspan lay.k_le
  have ht2 : allTritList x2 := by
    have htk : x.take n = x := by simpa [n, hx] using List.take_length x
    simpa [x2, n, k, bench, htk] using fieldMul_trits n k bench x x hspan hnb
  obtain ⟨bF, htail⟩ := curve_suffix bS x y x3 x2 y2 n k bench mvF
    h2H h2D h5Hs h5Ds h6H h6D hh2 ha2 hh5 ha5 hh6 ha6 hnS hx3 hx2 hy2 lay.board.n_pos
    ht3 ht2 hmS hfit hf hfitC hfitW hfitG hfitBot rfl rfl rfl
  exact ⟨bF, htail⟩

/-- `curve_test` is `on_curve` of the point put at base across and base up. -/
theorem curve_test_refines (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (x y : List Nat) (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y) :
    Ecbs.curve_test (embTier t)
        { sudo_5Point_1x := embed x, sudo_5Point_1y := embed y } =
      .ok (onCurve t.n t.k t.benchlen x y) := by
  unfold Ecbs.curve_test
  rw [new_board_refines t lay.board, ok_bind]
  dsimp only
  rw [put_base_across t lay.board x hx, ok_bind]
  rw [put_curve t lay.board x y hx hy, ok_bind]
  obtain ⟨bF, h⟩ := curve_on_refines t lay sat x y hx hy hxt hyt
  rw [h, ok_bind]
  simp [pure_eq_ok]

private theorem tier_curve (t : Spec.Tier) (et : Ecbs.Tier) (het : embTier t = et)
    (lay : FieldLay t) (sat : TierSat t)
    (hone : onCurve t.n t.k t.benchlen (zeroPeg t.n) (onePeg t.n) = true) :
    Ecbs.curve_test et
        { sudo_5Point_1x := embed (zeroPeg t.n), sudo_5Point_1y := embed (onePeg t.n) } =
      .ok true := by
  rw [← het,
    curve_test_refines t lay sat (zeroPeg t.n) (onePeg t.n)
      (zeroPeg_length t.n) (onePeg_length t.n lay.board.n_pos)
      (zeroPeg_trits t.n) (onePeg_trits t.n),
    hone]

theorem demo_curve_zero_one :
    Ecbs.curve_test Ecbs.demo_tier
        { sudo_5Point_1x := embed (zeroPeg Spec.demo.n),
          sudo_5Point_1y := embed (onePeg Spec.demo.n) } =
      .ok true :=
  tier_curve Spec.demo Ecbs.demo_tier demo_emb demo_lay demo_tier_sat demo_onCurve_zero_one

theorem toy_curve_zero_one :
    Ecbs.curve_test Ecbs.toy_tier
        { sudo_5Point_1x := embed (zeroPeg Spec.toy.n),
          sudo_5Point_1y := embed (onePeg Spec.toy.n) } =
      .ok true :=
  tier_curve Spec.toy Ecbs.toy_tier toy_emb toy_lay toy_tier_sat toy_onCurve_zero_one

theorem hobby_curve_zero_one :
    Ecbs.curve_test Ecbs.hobby_tier
        { sudo_5Point_1x := embed (zeroPeg Spec.hobby.n),
          sudo_5Point_1y := embed (onePeg Spec.hobby.n) } =
      .ok true :=
  tier_curve Spec.hobby Ecbs.hobby_tier hobby_emb hobby_lay hobby_tier_sat hobby_onCurve_zero_one

theorem serious_curve_zero_one :
    Ecbs.curve_test Ecbs.serious_tier
        { sudo_5Point_1x := embed (zeroPeg Spec.serious.n),
          sudo_5Point_1y := embed (onePeg Spec.serious.n) } =
      .ok true :=
  tier_curve Spec.serious Ecbs.serious_tier serious_emb serious_lay serious_tier_sat
    serious_onCurve_zero_one

end EcbsLink2.Link2
