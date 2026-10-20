/-
  `invert_checked` on the walk board whose script marker is still `-1`.
  The climb copies that index; it does not run `marker_step`.
  A zero denominator is not a unit. The code asserts line 728.
  `Spec.basePoint` is `none` when the cofactor run is that zero home.
  Both refuse, so the affine clear is only the nonzero arm.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.InvertWalk
import EcbsLink2.Link2.OneField

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The zero home has no inverse. Its product with the climb gap is zero,
    so it is neither the white peg nor the red peg. -/
theorem fieldInv_zero (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    fieldInv n k bench (zeroPeg n) = none := by
  have hz := fieldMul_zero n k bench (invGap n k bench (zeroPeg n)) hn
  have hform : zeroPeg n = 0 :: List.replicate (n - 1) 0 := by
    have hsum : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    have hrep : List.replicate ((n - 1) + 1) 0 = 0 :: List.replicate (n - 1) 0 :=
      List.replicate_succ 0 (n - 1)
    simpa [zeroPeg, hsum] using hrep
  have h1 : (0 :: List.replicate (n - 1) 0) ≠ 1 :: List.replicate (n - 1) 0 := by
    intro h
    injection h with h0
    exact absurd h0 (by decide : (0 : Nat) ≠ 1)
  have h2 : (0 :: List.replicate (n - 1) 0) ≠ 2 :: List.replicate (n - 1) 0 := by
    intro h
    injection h with h0
    exact absurd h0 (by decide : (0 : Nat) ≠ 2)
  unfold fieldInv
  simp only [hz]
  rw [hform, if_neg h1, if_neg h2]

/-- Accepted check on the marker `-1` board. Home 5 is the list `fieldInv`
    returns, and the script marker is still `-1`. -/
theorem invert_checked_cold (b : Ecbs.Board) (t : Spec.Tier) (xs ans : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base)
    (hholeLe : lay.hole ≤ t.benchlen)
    (hacc : fieldInv t.n t.k t.benchlen xs = some ans)
    (hix : lay.markIx = -1) :
    ∃ (b' : Ecbs.Board) (h5 : 5 < b'.sudo_5Board_4home.size),
      Ecbs.invert_checked b ((2 : Nat) : Int) = .ok b' ∧
      b'.sudo_5Board_4home[5]'h5 = embed ans ∧
      b'.sudo_5Board_6marker = -1 ∧
      b'.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed lay.side0) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed lay.side1) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[2] = embed xs) := by
  obtain ⟨b', h5, _, hok, h5a, _, _, _, h2, _, h0, _, h1, _, _, _, hcarry, _⟩ :=
    open_checked b t xs ans lay hOk sat hR hsh base hm hholeLe hacc
  refine ⟨b', h5, hok, h5a, ?_, hcarry.benchOff, h0, h1, h2⟩
  exact hcarry.marker.trans hix

/-- `Z = 0`. `invert_checked` reads hole 0 of the check product and asserts
    it is not zero (generated line 728). The product of the zero home is zero,
    so the call is `AssertFailed` at that line.
    `Spec.basePoint` is `none` on the same zero run (`basePoint_zero_root`):
    the cofactor walk has no affine point. Both refuse. -/
theorem invert_checked_zero (b : Ecbs.Board) (t : Spec.Tier)
    (lay : OpenLay b t (zeroPeg t.n)) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t) (base : ClimbBudget)
    (hm : OpenMatch lay base) (hholeLe : lay.hole ≤ t.benchlen) :
    ∃ e, Ecbs.invert_checked b ((2 : Nat) : Int) = .error e ∧
      e.kind = "AssertFailed" ∧
      e.detail = s!"line {728}" := by
  have hpos : 0 < t.n := hOk.n_pos
  have hn := mul_span_n t.n t.benchlen hpos sat.mul_span
  have hmulZ := fieldMul_zero t.n t.k t.benchlen
    (invGap t.n t.k t.benchlen (zeroPeg t.n)) hn
  obtain ⟨_, _, _, v, _, hpack⟩ :=
    open_check_mul b t (zeroPeg t.n) lay hOk sat hR hsh base hm hholeLe
  have hinv := hpack.1
  have hmul := hpack.2.1
  have hread := hpack.2.2.1
  have hv := hpack.2.2.2.1
  have hP0 : 0 < (zeroPeg t.n).length := by
    simpa [zeroPeg, List.length_replicate] using hpos
  have hhead : (zeroPeg t.n)[0]'hP0 = 0 := by
    simp [zeroPeg, List.getElem_replicate]
  unfold Ecbs.invert_checked
  rw [hinv, ok_bind]
  conv => zeta
  rw [hmul, ok_bind]
  conv => zeta
  rw [hread, ok_bind]
  dsimp
  rw [show v = embed (zeroPeg t.n) by simpa [hmulZ] using hv]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed (zeroPeg t.n) 0 hP0, ok_bind,
    sEq_ofNat ((zeroPeg t.n)[0]'hP0) 0, hhead]
  rw [show decide ((0 : Nat) = 0) = true from rfl, Bool.not_true]
  unfold SudoRt.sudoAssert SudoRt.fail
  simp only [Bool.false_eq_true, if_false, bind, Except.bind, error_bind]
  exact ⟨{ kind := "AssertFailed", detail := s!"line {728}" }, rfl, rfl, rfl⟩

end EcbsLink2.Link2
