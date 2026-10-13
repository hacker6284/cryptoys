/-
  The run of `chord_add_demo`: copy the base across into the bottom and take the
  accumulator across away. That is `fieldSub`. An empty run is the reroll branch.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.WalkCopy
import EcbsLink2.Link2.OneField

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `a + (−a) = 0` in GF(3), for a trit. -/
theorem trit_cancel (c : Nat) (hc : c ≤ 2) : tritAdd c (flipTrit c) = 0 := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

/-- A length-`n` trit list subtracted from itself is the zero home. -/
theorem fieldSub_self (n : Nat) (xs : List Nat)
    (hx : xs.length = n) (htri : allTritList xs) :
    fieldSub n xs xs = List.replicate n 0 := by
  unfold fieldSub fieldAdd
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, List.length_replicate]
  · intro i h1 h2
    have hi : i < n := by simpa [List.length_replicate] using h2
    have hix : i < xs.length := by rw [hx]; exact hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    have hget : coeff xs i = xs[i] := by
      unfold coeff
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
      simp
    have hmir : coeff (mirrorTrits xs) i = flipTrit (xs[i]) := by
      rw [mirrorTrits_flip]
      unfold coeff
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hix]
      simp
    rw [hmir, hget, trit_cancel _ (trit_get htri hix)]

/-- The chord op bump. Slot `op_chord` grows by one; every other field stays. -/
theorem chord_bump (b : Ecbs.Board) (cOps : Nat)
    (hops : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'(hops) = (cOps : Int))
    (hf : FitsLen (cOps + 1)) :
    (do
        let t ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
        let t ← SudoRt.addI t (1 : Int)
        let t ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord t
        pure ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_3ops := t } } : Ecbs.Board)) =
      .ok (bumpOp b 3 cOps hops) := by
  rw [show Ecbs.op_chord = Int.ofNat 3 from rfl, atL_ofNat _ 3 hops, hop, ok_bind]
  rw [← ofNat_eq_natCast cOps, addI_ofNat_one cOps hf, ok_bind]
  rw [putL_ofNat _ 3 (Int.ofNat (cOps + 1)) hops, ok_bind, pure_eq_ok]
  rfl

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem place_moves_nat (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount xs : Nat) : Int) := by
  rw [place_moves_eq, ofNat_eq_natCast]

/-- Copy the base across into the empty bottom, then take the accumulator across
    away. On the board `chord_bump` leaves, that is `fieldSub` of the two across
    homes. `add` does not read the marker. -/
theorem chord_copy_add (b : Ecbs.Board) (baseX accX : List Nat)
    (n moves peak cOps : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hx : baseX.length = n) (hy : accX.length = n) (hpos : 0 < n)
    (htriB : allTritList baseX) (htriA : allTritList accX)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h2e : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h0t : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (h0a : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed accX)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed baseX) :
    ∃ bA,
      (do
          let t ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
          let t ← SudoRt.addI t (1 : Int)
          let t ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord t
          let b := ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_3ops := t } } : Ecbs.Board)
          let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
          Ecbs.add b Ecbs.bottom Ecbs.across true) = .ok bA ∧
      (∀ h : 2 < bA.sudo_5Board_4home.size,
        bA.sudo_5Board_4home[2] = embed (fieldSub n baseX accX)) ∧
      (∀ h : 2 < bA.sudo_5Board_4held.size, bA.sudo_5Board_4held[2] = true) ∧
      bA.sudo_5Board_4held.size = 8 ∧
      bA.sudo_5Board_4home.size = 8 ∧
      bA.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bA.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseX + pegCount accX : Nat) : Int) := by
  have hpegB : pegCount baseX ≤ n := by rw [← hx]; exact pegCount_le baseX
  have hpegA : pegCount accX ≤ n := by rw [← hy]; exact pegCount_le accX
  have hfitn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hfitC : FitsLen (moves + pegCount baseX) :=
    FitsLen.of_le hfit (by omega)
  have hfitA : FitsLen (moves + pegCount baseX + n) :=
    FitsLen.of_le hfit (by omega)
  let bB := bumpOp b 3 cOps hops
  have hszHB : bB.sudo_5Board_4home.size = 8 := by rw [show bB.sudo_5Board_4home = b.sudo_5Board_4home from bumpOp_home b 3 cOps hops, hszH]
  have hszDB : bB.sudo_5Board_4held.size = 8 := by rw [bumpOp_held b 3 cOps hops, hszD]
  have hnB : bB.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [bB, bumpOp, hn]
  have hmovesB : bB.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [bumpOp_moves b 3 cOps hops, hmoves]
  have hpeakB : bB.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [bumpOp_peak b 3 cOps hops, hpeak]
  have hheldB : bB.sudo_5Board_4held = b.sudo_5Board_4held := bumpOp_held b 3 cOps hops
  have hhomeB : bB.sudo_5Board_4home = b.sudo_5Board_4home := bumpOp_home b 3 cOps hops
  have h2eB : bB.sudo_5Board_4held[2]'(by rw [hszDB]; decide) = false := by
    simpa [hheldB] using h2e
  have h0tB : bB.sudo_5Board_4held[0]'(by rw [hszDB]; decide) = true := by
    simpa [hheldB] using h0t
  have h0aB : bB.sudo_5Board_4home[0]'(by rw [hszHB]; decide) = embed accX := by
    simpa [hhomeB] using h0a
  have h3tB : bB.sudo_5Board_4held[3]'(by rw [hszDB]; decide) = true := by
    simpa [hheldB] using h3t
  have h3aB : bB.sudo_5Board_4home[3]'(by rw [hszHB]; decide) = embed baseX := by
    simpa [hhomeB] using h3a
  have h7 : 7 ≤ bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h2H : 2 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h2D : 2 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h3H : 3 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h3D : 3 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have hflen : FitsLen baseX.length := by rw [hx]; exact hfitn
  have hnlen : bB.sudo_5Board_1t.sudo_4Tier_1n = (baseX.length : Int) := by rw [hnB, hx]
  have hcopy := copy_band_refines bB 2 3 baseX moves peak h2H h2D h3H h3D h7
    h3tB h3aB h2eB hnlen hflen hmovesB hpeakB hfitC
  let b1 := placeBoard bB 2 h2H h2D baseX moves peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, hszHB]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, hszDB]
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h2D1 : 2 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h0H1 : 0 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h0D1 : 0 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hheld1 : b1.sudo_5Board_4held[2]'h2D1 = true := by
    have hset := place_held_eq bB 2 h2H h2D baseX moves peak
    have hget := idx_eq hset 2 (by rw [hset, Array.size_set]; exact h2D)
    simp only [Array.getElem_set] at hget
    exact hget
  have hhome1 : b1.sudo_5Board_4home[2]'h2H1 = embed baseX := by
    have hset := place_home_eq bB 2 h2H h2D baseX moves peak
    have hget := idx_eq hset 2 (by rw [hset, Array.size_set]; exact h2H)
    simp only [Array.getElem_set] at hget
    exact hget
  have h0B : 0 < bB.sudo_5Board_4held.size := by rw [hszDB]; decide
  have h0HB : 0 < bB.sudo_5Board_4home.size := by rw [hszHB]; decide
  have h0t1 : b1.sudo_5Board_4held[0]'h0D1 = true := by
    have hset := place_held_eq bB 2 h2H h2D baseX moves peak
    have hget := idx_eq hset 0 (by rw [hset, Array.size_set]; exact h0B)
    have hne : (2 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h0tB
  have h0a1 : b1.sudo_5Board_4home[0]'h0H1 = embed accX := by
    have hset := place_home_eq bB 2 h2H h2D baseX moves peak
    have hget := idx_eq hset 0 (by rw [hset, Array.size_set]; exact h0HB)
    have hne : (2 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h0aB
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [place_tier_eq, hnB]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount baseX : Nat) : Int) :=
    place_moves_nat bB 2 h2H h2D baseX moves peak
  have hadd := add_refines b1 2 0 baseX accX n (moves + pegCount baseX)
    h2H1 h2D1 h0H1 h0D1 hheld1 hhome1 h0t1 h0a1 hn1 hy hx hpos htriB htriA
    hmoves1 hfitA
  let bA := addBoard b1 2 h2H1 (embed (fieldAdd n baseX (mirrorTrits accX)))
    (moves + pegCount baseX + pegCount accX)
  have hsub : fieldAdd n baseX (mirrorTrits accX) = fieldSub n baseX accX := rfl
  refine ⟨bA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.op_chord = Int.ofNat 3 from rfl, atL_ofNat _ 3 hops, hop, ok_bind]
    rw [← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind]
    rw [putL_ofNat _ 3 (Int.ofNat (cOps + 1)) hops, ok_bind]
    have hbEq : ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops := b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨3, hops⟩
          (Int.ofNat (cOps + 1)) } } : Ecbs.Board) = bB := rfl
    have hdo :
        (do
            let b ← Ecbs.copy_band bB Ecbs.bottom Ecbs.base_across false
            Ecbs.add b Ecbs.bottom Ecbs.across true) = .ok bA := by
      rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
          show Ecbs.base_across = ((3 : Nat) : Int) from rfl,
          show Ecbs.across = ((0 : Nat) : Int) from rfl, hcopy, ok_bind]
      simpa [b1, bA, hsub] using hadd
    simpa [hbEq] using hdo
  · intro h
    have hset : bA.sudo_5Board_4home =
        b1.sudo_5Board_4home.set ⟨2, h2H1⟩ (embed (fieldAdd n baseX (mirrorTrits accX))) := by
      simp [bA, addBoard, withMoves]
    have hget := idx_eq hset 2 h
    simp only [Array.getElem_set, if_true] at hget
    simpa [hsub] using hget
  · intro h
    have hheld : bA.sudo_5Board_4held = b1.sudo_5Board_4held := by
      simp [bA, addBoard, withMoves]
    simpa [hheld] using hheld1
  · have hheld : bA.sudo_5Board_4held = b1.sudo_5Board_4held := by
      simp [bA, addBoard, withMoves]
    rw [hheld, place_held_eq, Array.size_set, hszDB]
  · have hhome : bA.sudo_5Board_4home =
        b1.sudo_5Board_4home.set ⟨2, h2H1⟩ (embed (fieldAdd n baseX (mirrorTrits accX))) := by
      simp [bA, addBoard, withMoves]
    rw [hhome, Array.size_set, hszH1]
  · have ht : bA.sudo_5Board_1t = b1.sudo_5Board_1t := by
      simp [bA, addBoard, withMoves]
    rw [ht, place_tier_eq, hnB]
  · simp [bA, addBoard, withMoves]

/-- The zero home is not a unit and not the red peg in hole 0, so `specInv` rejects it. -/
theorem specInv_zero (n k bench : Nat) (hn0 : 0 < n) (hnb : n ≤ bench) :
    specInv n k bench (List.replicate n 0) = none := by
  have hz : fieldMul n k bench
      (invGapOf n k bench (List.replicate n 0) (specRungs (n - 1)))
      (List.replicate n 0) = List.replicate n 0 := by
    simpa [zeroPeg] using
      fieldMul_zero n k bench
        (invGapOf n k bench (zeroPeg n) (specRungs (n - 1))) hnb
  unfold specInv
  dsimp only
  rw [hz]
  cases n with
  | zero => omega
  | succ n =>
    have hne1 : List.replicate (n + 1) 0 ≠ whiteHole0 (n + 1) := by
      simp [whiteHole0, List.replicate_succ]
    have hsub : n + 1 - 1 = n := by omega
    have hne2 : List.replicate (n + 1) 0 ≠ 2 :: List.replicate (n + 1 - 1) 0 := by
      rw [hsub]
      simp [List.replicate_succ]
    rw [if_neg hne1, if_neg hne2]

/-- A live white or red cell whose run is the zero home is an exceptional chord.
    `walkStep` returns `none`. This does not claim `fieldInv` is the field inverse;
    it only uses that the zero home fails the peg-in-hole-0 check. -/
theorem walkStep_empty_run (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (hc : c = 1 ∨ c = 2)
    (hrun : fieldSub n base.1 (fieldCube n k bench acc.1) = List.replicate n 0)
    (hn0 : 0 < n) (hnb : n ≤ bench) :
    walkStep n k bench base true acc c = none := by
  unfold walkStep
  have hc0 : ¬ c = 0 := by
    cases hc with
    | inl h => simp [h]
    | inr h => simp [h]
  have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by
    cases hc with
    | inl h => simp [h]
    | inr h => simp [h]
  simp only [pointCube, hc0, if_false, hbad, if_false, if_true]
  unfold chordAdd
  dsimp only
  rw [hrun, specInv_zero n k bench hn0 hnb]

/-- `is_zero` on a held home that is `n` zeros. -/
theorem is_zero_replicate (b : Ecbs.Board) (home n : Nat)
    (hD : home < b.sudo_5Board_4held.size) (hH : home < b.sudo_5Board_4home.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed (List.replicate n 0))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hf : FitsLen n) :
    Ecbs.is_zero b (home : Int) = .ok true := by
  unfold Ecbs.is_zero
  rw [value_held_refines b home (List.replicate n 0) n hD hH hheld harr hn
      (by simp) hf, ok_bind]
  rw [List.take_replicate, Nat.min_eq_left (Nat.le_refl n)]
  have hfA : FitsLen (embed (List.replicate n 0)).size := by
    rw [size_embed, List.length_replicate]
    exact hf
  rw [is_empty_refines _ hfA]
  have hall : ∀ i (h : i < (embed (List.replicate n 0)).size),
      (embed (List.replicate n 0))[i] = 0 := by
    intro i hi
    rw [size_embed, List.length_replicate] at hi
    rw [get_embed, List.getElem_replicate]
    simp
  simp [hall, decide_True]

end EcbsLink2.Link2
