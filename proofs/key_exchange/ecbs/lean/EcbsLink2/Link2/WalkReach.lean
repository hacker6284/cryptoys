/-
  The emitted `walk_chord` through the opening copy. Empty cells leave the
  flagged base board. The first nonzero cell copies the base point, white or
  red, and the loop from there is the loop that still has the seat cell to run.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopySeat
import EcbsLink2.Link2.WalkPrefix

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem index_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hlen : i + 1 ≤ t.cells + 1 := by omega
  exact Nat.le_trans hlen (Nat.le_mul_of_pos_right (t.cells + 1) hpos)

private theorem reach_copy (t : Spec.Tier) (x y : List Nat) (zs rest : List Nat)
    (c : Nat) (b2 : Ecbs.Board) (tw : TierWalk t)
    (hz : ∀ z ∈ zs, z = 0) (hc : c = 1 ∨ c = 2)
    (hlen : (zs ++ (c :: rest)).length = t.cells) (hrest : 0 < rest.length)
    (hml : Ecbs.marker_lift (chordFlag (baseBoard t x y)) =
      .ok (chordFlag (baseBoard t x y)))
    (hcopy :
      (do
          let board ← Ecbs.copy_band (chordFlag (baseBoard t x y)) Ecbs.across
            Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up
            (SudoRt.SEq.beq (Int.ofNat c) (2 : Int))) = .ok b2) :
    let cells := zs ++ (c :: rest)
    let k := zs.length + 1
    let toN := t.cells - 1
    let bf := chordFlag (baseBoard t x y)
    SudoRt.runLoopOn (Int.ofNat 0, (bf, false))
        (fuelRange (Int.ofNat 0) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat k, (b2, true))
        (fuelRange (Int.ofNat k) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  intro cells k toN bf
  have hpos : 0 < t.cells := by
    have h := hlen
    simp [List.length_append] at h
    omega
  have hto : toN + 1 = t.cells := by
    have h := hpos
    omega
  have hk : k ≤ toN := by
    have h := hlen
    simp [List.length_append, k, toN] at h
    omega
  have hlenC : cells.length = toN + 1 := by rw [hlen, hto]
  let Inv : Nat → Ecbs.Board × Bool → Prop := fun i st =>
    if i ≤ zs.length then st = (bf, false) else st = (b2, true)
  have h0 : Inv 0 (bf, false) := by
    simp [Inv]
  have hstep : ∀ i s, 0 ≤ i → i < k → Inv i s →
      ∃ s', Inv (i + 1) s' ∧
        chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st _hi hlt hI
    have hiTo : i ≤ toN := by omega
    have hfiti := index_fit t tw i (by omega)
    have hne : i ≠ toN := by omega
    by_cases hzero : i < zs.length
    · have hI0 : st = (bf, false) := by
        have hle : i ≤ zs.length := by omega
        simpa [Inv, hle] using hI
      have hcell : cells[i]'(by rw [hlenC]; omega) = 0 := by
        have hiL : i < zs.length := hzero
        have hlenI : i < (zs ++ (c :: rest)).length := by
          simp [List.length_append]
          omega
        have hget := List.getElem_append_left (bs := c :: rest) hiL (h' := hlenI)
        have hz0 : zs[i]'hiL = 0 := hz _ (List.getElem_mem _)
        simpa [cells] using hget.trans hz0
      have hst := chordStep_zero cells i toN bf bf hiTo hlenC hcell hml hfiti
      refine ⟨(bf, false), ?_, ?_⟩
      · have hle : i + 1 ≤ zs.length := by omega
        simp [Inv, hle]
      · rw [hI0, hst, if_neg hne]
    · have hopen : i = zs.length := by omega
      have hI0 : st = (bf, false) := by
        have hle : i ≤ zs.length := by omega
        simpa [Inv, hle] using hI
      have hcell : cells[i]'(by rw [hlenC]; omega) = c := by
        have hiR : zs.length ≤ i := by omega
        have hlenI : i < (zs ++ (c :: rest)).length := by
          simp [List.length_append]
          omega
        have hget := List.getElem_append_right (bs := c :: rest) hiR (h₂ := hlenI)
        have h0i : i - zs.length = 0 := by omega
        have hhead : (c :: rest)[i - zs.length]'(by
            have hlenR : 0 < (c :: rest).length := by simp
            omega) = c := by simp [h0i]
        simpa [cells] using hget.trans hhead
      have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
      have hc2 : c ≤ 2 := by rcases hc with rfl | rfl <;> decide
      have hst := chordStep_fresh cells i toN c bf bf b2 hiTo hlenC hcell hc0 hc2
        hml hcopy hfiti
      refine ⟨(b2, true), ?_, ?_⟩
      · have hgt : ¬ i + 1 ≤ zs.length := by omega
        simp [Inv, hgt]
      · rw [hI0, hst, if_neg hne]
  obtain ⟨sK, hIK, heq⟩ := asc_resume
    (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r)
    Inv 0 k toN (bf, false) (Nat.zero_le _) hk h0 hstep
  have hgt : ¬ k ≤ zs.length := by simp [k]
  have hsK : sK = (b2, true) := by simpa [Inv, hgt] using hIK
  simpa [hsK] using heq

/-- Empty cells, then a white cell, then at least one more cell. The loop
    from the start is the loop at the seat cell, on the copied board. -/
theorem walk_reach_white (t : Spec.Tier) (x y : List Nat) (zs rest : List Nat)
    (tw : TierWalk t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hz : ∀ z ∈ zs, z = 0)
    (hlen : (zs ++ (1 :: rest)).length = t.cells) (hrest : 0 < rest.length) :
    ∃ b2 pk, ∃ out : OutLay t b2 x y y
        (pegCount x + pegCount y + pegCount x + pegCount y) pk,
      (out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
        out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
        out.high0 = t.script + tierR t + 1) ∧
      let cells := zs ++ (1 :: rest)
      let k := zs.length + 1
      let toN := t.cells - 1
      let bf := chordFlag (baseBoard t x y)
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      SudoRt.runLoopOn (Int.ofNat 0, (bf, false))
          (fuelRange (Int.ofNat 0) (Int.ofNat toN))
          (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat k, (b2, true))
          (fuelRange (Int.ofNat k) (Int.ofNat toN))
          (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  have hf : FitsLen t.n := by
    apply geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2
    omega
  have hfitx : FitsLen (pegCount x + pegCount y + pegCount x) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  have hfity : FitsLen (pegCount x + pegCount y + pegCount x + pegCount y) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  let bf := chordFlag (baseBoard t x y)
  obtain ⟨b2, _pk, out, hsl0, hctrl0, hops0, hstrict0, hhole0, hmx0, hhigh0, htmax0, hcopy⟩ :=
    white_copy_kept t bf x y (pegCount x + pegCount y) 2 (base_in_lay t x y hR)
      hx hy hf hfitx hfity
  rcases base_lay_fresh t x y hR with ⟨hsl, hopsZ, hstrict, hhole, hmx, htmax, hctrlZ, hhigh⟩
  have hfresh : out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
      out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
      out.high0 = t.script + tierR t + 1 :=
    ⟨hsl0.trans hsl, hops0.trans hopsZ, hstrict0.trans hstrict, hhole0.trans hhole,
      hmx0.trans hmx, htmax0.trans htmax, hctrl0.trans hctrlZ, hhigh0.trans hhigh⟩
  have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 1 2]
    decide
  have hcopyB :
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up
            (SudoRt.SEq.beq (Int.ofNat 1) (2 : Int))) = .ok b2 := by
    simpa [hbeq] using hcopy
  have hml := marker_lift_down bf (base_in_lay t x y hR).marker
  have hloop := reach_copy t x y zs rest 1 b2 tw hz (Or.inl rfl) hlen hrest hml hcopyB
  exact ⟨b2, _pk, out, hfresh, hcopy, hloop⟩

/-- Empty cells, then a red cell, then at least one more cell. Up on the
    copied board is the negated base up. -/
theorem walk_reach_red (t : Spec.Tier) (x y : List Nat) (zs rest : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n) (htriY : allTritList y)
    (hz : ∀ z ∈ zs, z = 0)
    (hlen : (zs ++ (2 :: rest)).length = t.cells) (hrest : 0 < rest.length) :
    ∃ b2 pk, ∃ out : OutLay t b2 x (mirrorTrits y) y
        (pegCount x + pegCount y + pegCount x + pegCount y) pk,
      (out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
        out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
        out.high0 = t.script + tierR t + 1) ∧
      let cells := zs ++ (2 :: rest)
      let k := zs.length + 1
      let toN := t.cells - 1
      let bf := chordFlag (baseBoard t x y)
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up true) = .ok b2 ∧
      SudoRt.runLoopOn (Int.ofNat 0, (bf, false))
          (fuelRange (Int.ofNat 0) (Int.ofNat toN))
          (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat k, (b2, true))
          (fuelRange (Int.ofNat k) (Int.ofNat toN))
          (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  have hf : FitsLen t.n := by
    apply geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2
    omega
  have hfitx : FitsLen (pegCount x + pegCount y + pegCount x) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  have hfity : FitsLen (pegCount x + pegCount y + pegCount x + pegCount y) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  let bf := chordFlag (baseBoard t x y)
  obtain ⟨b2, _pk, out, hsl0, hctrl0, hops0, hstrict0, hhole0, hmx0, hhigh0, htmax0, hcopy⟩ :=
    red_copy_kept t bf x y (pegCount x + pegCount y) 2 (base_in_lay t x y hR)
      hx hy hOk.n_pos htriY hf hfitx hfity
  rcases base_lay_fresh t x y hR with ⟨hsl, hopsZ, hstrict, hhole, hmx, htmax, hctrlZ, hhigh⟩
  have hfresh : out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
      out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
      out.high0 = t.script + tierR t + 1 :=
    ⟨hsl0.trans hsl, hops0.trans hopsZ, hstrict0.trans hstrict, hhole0.trans hhole,
      hmx0.trans hmx, htmax0.trans htmax, hctrl0.trans hctrlZ, hhigh0.trans hhigh⟩
  have hbeq : SudoRt.SEq.beq (Int.ofNat 2) (2 : Int) = true := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 2 2]
    decide
  have hcopyB :
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up
            (SudoRt.SEq.beq (Int.ofNat 2) (2 : Int))) = .ok b2 := by
    simpa [hbeq] using hcopy
  have hml := marker_lift_down bf (base_in_lay t x y hR).marker
  have hloop := reach_copy t x y zs rest 2 b2 tw hz (Or.inr rfl) hlen hrest hml hcopyB
  exact ⟨b2, _pk, out, hfresh, hcopy, hloop⟩

end EcbsLink2.Link2
