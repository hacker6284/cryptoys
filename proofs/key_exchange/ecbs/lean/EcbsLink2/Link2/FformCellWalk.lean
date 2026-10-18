/-
  One live cell of `fformStep`, tied to `walkStep`. A zero cell cubes.
  A white or red cell adds the base point, mirrored when the cell is red,
  and `across_on_x3` / `up_on_parts` are that chord on the common denominator.
  The loop breaks when the index is the last cell and continues otherwise.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformLine
import EcbsLink2.Link2.WalkFform

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The emitted red flag is the cell colour `2`. -/
theorem cell_red_flag (c : Nat) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat c 2]

/-- A successful step is colour 0, 1, or 2. -/
theorem walk_step_colour (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (p : Bool × (List Nat × List Nat))
    (h : walkStep n k bench base true acc c = some p) :
    c = 0 ∨ c = 1 ∨ c = 2 := by
  unfold walkStep at h
  by_cases h0 : c = 0
  · exact Or.inl h0
  · rw [if_neg h0] at h
    by_cases h1 : c = 1
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : c = 2
      · exact Or.inr (Or.inr h2)
      · simp [show c ≠ 1 ∧ c ≠ 2 from ⟨h1, h2⟩] at h

/-- A live zero cell cubes both coordinates. -/
theorem walk_zero_cubes (n k bench : Nat) (base : List Nat × List Nat)
    (ax ay ax' ay' : List Nat)
    (h : walkStep n k bench base true (ax, ay) 0 = some (true, (ax', ay'))) :
    ax' = fieldCube n k bench ax ∧ ay' = fieldCube n k bench ay := by
  unfold walkStep pointCube at h
  simp at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- A live white or red cell is the chord of the cubed accumulator and the
    base point. Red mirrors the base up. The coordinates are the ones
    `across_on_x3` and `up_on_parts` multiply by the new bottom. -/
theorem walk_chord_coords (n k bench : Nat) (x2 y2 ax ay x3 y3 : List Nat) (c : Nat)
    (hc : c = 1 ∨ c = 2)
    (h : walkStep n k bench (x2, y2) true (ax, ay) c = some (true, (x3, y3))) :
    ∃ g,
      fieldInv n k bench (fieldSub n x2 (fieldCube n k bench ax)) = some g ∧
      x3 = fieldAdd n (fieldAdd n (fieldAdd n
          (fieldMul n k bench
            (fieldMul n k bench
              (fieldSub n (if c = 2 then mirrorTrits y2 else y2) (fieldCube n k bench ay)) g)
            (fieldMul n k bench
              (fieldSub n (if c = 2 then mirrorTrits y2 else y2) (fieldCube n k bench ay)) g))
          (whiteHole0 n)) (fieldCube n k bench ax))
        (mirrorTrits (fieldSub n x2 (fieldCube n k bench ax))) ∧
      y3 = fieldSub n
        (fieldMul n k bench
          (fieldMul n k bench
            (fieldSub n (if c = 2 then mirrorTrits y2 else y2) (fieldCube n k bench ay)) g)
          (fieldSub n (fieldCube n k bench ax) x3))
        (fieldCube n k bench ay) := by
  let x := fieldCube n k bench ax
  let y := fieldCube n k bench ay
  let yB := if c = 2 then mirrorTrits y2 else y2
  let run := fieldSub n x2 x
  cases hg : fieldInv n k bench run with
  | none =>
    have h0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
    have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by rcases hc with rfl | rfl <;> decide
    unfold walkStep chordAdd at h
    simp only [ite_true, pointCube] at h
    rw [if_neg h0, if_neg hbad, specInv_eq] at h
    simp [run, x, hg] at h
  | some g =>
    obtain ⟨p, hwalk, hchord⟩ :=
      walkStep_chord n k bench (x2, y2) (ax, ay) c g hc hg
    have hp : (x3, y3) = p := by
      have heq := Option.some.inj (h.symm.trans hwalk)
      simpa using congrArg Prod.snd heq
    simp only [chordAdd, specInv_eq, pointCube, hg, hp] at hchord
    injection hchord with hxy
    have hpair := hp.trans hxy.symm
    cases hpair
    exact ⟨g, rfl, rfl, rfl⟩

/-- `across_on_x3`'s across home is `x₃ · Z₃` for the chord's `x₃`. -/
theorem across_is_chord (n k bench : Nat) (x y x2 y2 z g x3 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hx : allTritList x) (hy : allTritList y) (hx2 : allTritList x2) (hy2 : allTritList y2)
    (hz : allTritList z) (hg : allTritList g)
    (hxL : x.length = n) (hyL : y.length = n) (hx2L : x2.length = n) (hy2L : y2.length = n)
    (hzL : z.length = n) (hgL : g.length = n)
    (hinv : fieldMul n k bench g (fieldSub n x2 x) = onePeg n)
    (hx3 : x3 = fieldAdd n (fieldAdd n (fieldAdd n
        (fieldMul n k bench (fieldMul n k bench (fieldSub n y2 y) g)
          (fieldMul n k bench (fieldSub n y2 y) g)) (whiteHole0 n)) x)
        (mirrorTrits (fieldSub n x2 x))) :
    fformAcross n k bench x2
        (fformRise n k bench y2 z (fieldMul n k bench y z))
        (fformRun n k bench x2 z (fieldMul n k bench x z)) z =
      fieldMul n k bench x3
        (fformBottom n k bench
          (fformRun n k bench x2 z (fieldMul n k bench x z)) z) := by
  have hcross := across_on_x3 n k bench x y x2 y2 z g hn hk hb h2 h3
    hx hy hx2 hy2 hz hg hxL hyL hx2L hy2L hzL hgL hinv
  simpa [hx3] using hcross

/-- `up_on_parts`'s up home is `y₃ · Z₃` for the chord's `y₃`. -/
theorem up_is_chord (n k bench : Nat)
    (slope v a u z y2 x y x2 x3 y3 : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench)
    (hs : allTritList slope) (hv : allTritList v) (ha : allTritList a)
    (hz : allTritList z) (hy2 : allTritList y2) (hx : allTritList x) (hy : allTritList y)
    (hx2 : allTritList x2) (hx3 : allTritList x3)
    (hxL : x.length = n) (hyL : y.length = n) (hx2L : x2.length = n)
    (hy2L : y2.length = n) (hx3L : x3.length = n)
    (hu : u = fieldMul n k bench slope v)
    (hF : fformF n k bench u v z = fieldMul n k bench a (fieldSub n x3 x2))
    (hbot : fformBottom n k bench v z = fieldMul n k bench v a)
    (hlam : fieldMul n k bench slope (fieldSub n x2 x) = fieldSub n y2 y)
    (hy3 : y3 = fieldSub n (fieldMul n k bench slope (fieldSub n x x3)) y) :
    fformUp n k bench y2 u v z =
      fieldMul n k bench y3 (fformBottom n k bench v z) := by
  have hup := up_on_parts n k bench slope v a u z y2 x y x2 x3 hn hk hb h2
    hs hv ha hz hy2 hx hy hx2 hx3 hxL hyL hx2L hy2L hx3L hu hF hbot hlam
  rw [hy3, fieldSub]
  exact hup

/-- Break on the last cell, continue before it. The zero cell lands on the
    Frobenius board. A white or red cell lands on the `fform_add` board,
    and the red flag is `c = 2`. -/
theorem cell_walk_step (t : Spec.Tier) (cells : List Nat) (i c : Nat)
    (b0 b bF bA : Ecbs.Board) (base : List Nat × List Nat)
    (ax ay ax' ay' : List Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = c)
    (hstep : walkStep t.n t.k t.benchlen base true (ax, ay) c =
      some (true, (ax', ay')))
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_point b = .ok bF)
    (hadd : c ≠ 0 →
      Ecbs.fform_add bF (decide (c = 2)) = .ok (true, bA))
    (hfit : FitsLen (i + 1)) :
    ∃ sb, fformStep (embed cells) (Int.ofNat (t.cells - 1))
        (Int.ofNat i, (b0, true)) =
      (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb, true)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb, true)))) := by
  have hlen' : cells.length = (t.cells - 1) + 1 := by omega
  have hcol := walk_step_colour t.n t.k t.benchlen base (ax, ay) c _ hstep
  rcases hcol with rfl | rfl | rfl
  · exact ⟨bF, fformStep_point cells i (t.cells - 1) b0 b bF hi hlen' hc hml hfrob hfit⟩
  · have hc0 : (1 : Nat) ≠ 0 := by decide
    have hadd' : Ecbs.fform_add bF (SudoRt.SEq.beq (Int.ofNat 1) (2 : Int)) =
        .ok (true, bA) := by
      rw [cell_red_flag 1]
      exact hadd hc0
    exact ⟨bA, fformStep_add cells i (t.cells - 1) 1 b0 b bF bA hi hlen' hc hc0
      (by decide) hml hfrob hadd' hfit⟩
  · have hc0 : (2 : Nat) ≠ 0 := by decide
    have hadd' : Ecbs.fform_add bF (SudoRt.SEq.beq (Int.ofNat 2) (2 : Int)) =
        .ok (true, bA) := by
      rw [cell_red_flag 2]
      exact hadd hc0
    exact ⟨bA, fformStep_add cells i (t.cells - 1) 2 b0 b bF bA hi hlen' hc hc0
      (by decide) hml hfrob hadd' hfit⟩

end EcbsLink2.Link2
