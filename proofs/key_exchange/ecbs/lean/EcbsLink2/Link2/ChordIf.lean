/-
  The generated `if is_zero` of `chord_add_demo`. The emitter's lets expand the
  cost update, so that prefix is restated as `chordCopyAddGo` and the bridge to
  the emitted function is `rfl`. An empty run returns `(false, board)`. A
  nonempty run is the marker-off inverse, then the rise and the chord tail.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordRun


namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Copy the base across into the bottom and take the accumulator across away.
    The same `do` block `chord_copy_add` refines. -/
def chordCopyAddGo (b : Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  do
    let t ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
    let t ← SudoRt.addI t (1 : Int)
    let t ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord t
    let b := ({ b with sudo_5Board_4cost :=
      { b.sudo_5Board_4cost with sudo_5Costs_3ops := t } } : Ecbs.Board)
    let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
    Ecbs.add b Ecbs.bottom Ecbs.across true

/-- After a nonempty run: hold the marker, invert the bottom, put the marker
    back, then the rise and `chord_tail`. -/
def chordAddTail (b : Ecbs.Board) (red : Bool) : Except SudoRt.Trap (Bool × Ecbs.Board) :=
  do
    let on := b.sudo_5Board_9marker_on
    let b := ({ b with sudo_5Board_9marker_on := false } : Ecbs.Board)
    let b ← Ecbs.invert_checked b Ecbs.bottom
    let b := ({ b with sudo_5Board_9marker_on := on } : Ecbs.Board)
    let b ← Ecbs.copy_band b Ecbs.spare Ecbs.base_up red
    let b ← Ecbs.add b Ecbs.spare Ecbs.up true
    let b ← Ecbs.chord_tail b Ecbs.across Ecbs.up
    pure (true, b)

/-- The emitted chord add, split at `is_zero`. -/
def chordAddGo (b : Ecbs.Board) (red : Bool) : Except SudoRt.Trap (Bool × Ecbs.Board) :=
  do
    let b ← chordCopyAddGo b
    let z ← Ecbs.is_zero b Ecbs.bottom
    if z then
      pure (false, b)
    else
      chordAddTail b red

/-- The generated body, copied so `Ecbs.chord_add_demo` bridges by `rfl`. -/
def chordAddEmit (b : Ecbs.Board) (red : Bool) :
    Except SudoRt.Trap (Bool × Ecbs.Board) :=
  do
    let _ix1318 := Ecbs.op_chord
    let _t1319 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
    let _t1320 ← SudoRt.addI _t1319 (1 : Int)
    let _t1321 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops _ix1318 _t1320
    let _t1322 := ({ b.sudo_5Board_4cost with sudo_5Costs_3ops := _t1321 } : Ecbs.Costs)
    let _t1323 := ({ b with sudo_5Board_4cost := _t1322 } : Ecbs.Board)
    let b := _t1323
    let _io1324 ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
    let b := _io1324
    let _io1325 ← Ecbs.add b Ecbs.bottom Ecbs.across true
    let b := _io1325
    let _t1326 ← Ecbs.is_zero b Ecbs.bottom
    if _t1326 then
      do
        pure (false, b)
    else
      do
        let on := b.sudo_5Board_9marker_on
        let _t1327 := ({ b with sudo_5Board_9marker_on := false } : Ecbs.Board)
        let b := _t1327
        let _io1328 ← Ecbs.invert_checked b Ecbs.bottom
        let b := _io1328
        let _t1329 := ({ b with sudo_5Board_9marker_on := on } : Ecbs.Board)
        let b := _t1329
        let _io1330 ← Ecbs.copy_band b Ecbs.spare Ecbs.base_up red
        let b := _io1330
        let _io1331 ← Ecbs.add b Ecbs.spare Ecbs.up true
        let b := _io1331
        let _io1332 ← Ecbs.chord_tail b Ecbs.across Ecbs.up
        let b := _io1332
        pure (true, b)

/-- Reassociate one `Except` bind so a continuation can move under a prefix. -/
theorem except_pull {ε α β γ} (m : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  cases m <;> rfl

/-- The generated cost lets, then `copy_band` and `add`, are `chordCopyAddGo`.
    A continuation stays attached. `simp` pushes it under the binds. -/
theorem chord_prefix_cont {α : Type} (b : Ecbs.Board) (k : Ecbs.Board → Except SudoRt.Trap α) :
    (do
      let _ix1318 := Ecbs.op_chord
      let _t1319 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
      let _t1320 ← SudoRt.addI _t1319 (1 : Int)
      let _t1321 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops _ix1318 _t1320
      let _t1322 := ({ b.sudo_5Board_4cost with sudo_5Costs_3ops := _t1321 } : Ecbs.Costs)
      let _t1323 := ({ b with sudo_5Board_4cost := _t1322 } : Ecbs.Board)
      let b := _t1323
      let _io1324 ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
      let b := _io1324
      let b ← Ecbs.add b Ecbs.bottom Ecbs.across true
      k b) = chordCopyAddGo b >>= k := by
  unfold chordCopyAddGo
  dsimp only
  simp only [except_pull]

/-- The generated `if is_zero` is the copy-then-add, then the empty check.
    The bridge to the emitted function is `rfl`; the lets reassociate by `except_pull`. -/
theorem chord_add_eq (b : Ecbs.Board) (red : Bool) :
    Ecbs.chord_add_demo b red = chordAddGo b red := by
  have hem : Ecbs.chord_add_demo b red = chordAddEmit b red := rfl
  rw [hem]
  unfold chordAddGo chordAddEmit
  simpa [chordAddTail] using
    chord_prefix_cont b (fun b =>
      do
        let z ← Ecbs.is_zero b Ecbs.bottom
        if z then pure (false, b) else chordAddTail b red)

theorem fieldSub_length (n : Nat) (a b : List Nat) : (fieldSub n a b).length = n := by
  simp [fieldSub, fieldAdd, List.length_map, List.length_range]

/-- Every entry of an embedded list is zero exactly when the list is `n` zeros. -/
theorem embed_all_zero_iff (xs : List Nat) (n : Nat) (hx : xs.length = n) :
    (∀ i (h : i < (embed xs).size), (embed xs)[i] = 0) ↔ xs = List.replicate n 0 := by
  constructor
  · intro hall
    apply List.ext_getElem
    · simp [hx, List.length_replicate]
    · intro i hi1 hi2
      have hi : i < n := by simpa [List.length_replicate] using hi2
      have hembed : i < (embed xs).size := by rw [size_embed, hx]; exact hi
      have hget := hall i hembed
      rw [get_embed] at hget
      have hnat : xs[i]'(by rw [hx]; exact hi) = 0 := by
        have hz : Int.ofNat (xs[i]'(by rw [hx]; exact hi)) = Int.ofNat 0 := by
          simpa using hget
        exact Int.ofNat.inj hz
      simpa [List.getElem_replicate] using hnat
  · intro hxs i hi
    subst hxs
    rw [get_embed, List.getElem_replicate]
    simp

/-- `is_zero` on a held home that embeds a length-`n` list. -/
theorem is_zero_embed (b : Ecbs.Board) (home n : Nat) (xs : List Nat)
    (hD : home < b.sudo_5Board_4held.size) (hH : home < b.sudo_5Board_4home.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : xs.length = n) (hf : FitsLen n) :
    Ecbs.is_zero b (home : Int) = .ok (decide (xs = List.replicate n 0)) := by
  unfold Ecbs.is_zero
  rw [value_held_refines b home xs n hD hH hheld harr hn
      (by rw [hx]; exact Nat.le_refl _) hf, ok_bind]
  rw [show xs.take n = xs from by rw [← hx]; exact List.take_length xs]
  have hfA : FitsLen (embed xs).size := by rw [size_embed, hx]; exact hf
  rw [is_empty_refines _ hfA, ok_bind, pure_eq_ok]
  have hiff := embed_all_zero_iff xs n hx
  have hbool :
      decide (∀ i (h : i < (embed xs).size), (embed xs)[i] = 0) =
        decide (xs = List.replicate n 0) := by
    by_cases hq : xs = List.replicate n 0
    · have hp : ∀ i (h : i < (embed xs).size), (embed xs)[i] = 0 := hiff.2 hq
      rw [decide_eq_true hp, decide_eq_true hq]
    · have hp : ¬ ∀ i (h : i < (embed xs).size), (embed xs)[i] = 0 :=
        fun h => hq (hiff.1 h)
      rw [decide_eq_false hp, decide_eq_false hq]
  rw [hbool]

private theorem run_of_copy (b : Ecbs.Board) (baseX accX : List Nat)
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
      chordCopyAddGo b = .ok bA ∧
      (∀ h : 2 < bA.sudo_5Board_4home.size,
        bA.sudo_5Board_4home[2] = embed (fieldSub n baseX accX)) ∧
      (∀ h : 2 < bA.sudo_5Board_4held.size, bA.sudo_5Board_4held[2] = true) ∧
      bA.sudo_5Board_4held.size = 8 ∧
      bA.sudo_5Board_4home.size = 8 ∧
      bA.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bA.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseX + pegCount accX : Nat) : Int) := by
  have hrun := chord_copy_add b baseX accX n moves peak cOps hszH hszD hops hop hfops
    hx hy hpos htriB htriA hn hmoves hpeak hfit h2e h0t h0a h3t h3a
  simpa [chordCopyAddGo] using hrun

/-- An empty run. `chord_add_demo` returns not-ok and leaves the bottom as `n` zeros.
    The marker flag is whatever the copy-then-add left; the walk clears it. -/
theorem chord_add_empty (b : Ecbs.Board) (red : Bool) (baseX accX : List Nat)
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
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed baseX)
    (hzero : fieldSub n baseX accX = List.replicate n 0) :
    ∃ bA,
      Ecbs.chord_add_demo b red = .ok (false, bA) ∧
      (∀ h : 2 < bA.sudo_5Board_4home.size,
        bA.sudo_5Board_4home[2] = embed (List.replicate n 0)) ∧
      (∀ h : 2 < bA.sudo_5Board_4held.size, bA.sudo_5Board_4held[2] = true) ∧
      bA.sudo_5Board_4held.size = 8 ∧
      bA.sudo_5Board_4home.size = 8 ∧
      bA.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bA.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseX + pegCount accX : Nat) : Int) := by
  obtain ⟨bA, hrun, hhome, hheld, hszD', hszH', hn', hmv⟩ :=
    run_of_copy b baseX accX n moves peak cOps hszH hszD hops hop hfops
      hx hy hpos htriB htriA hn hmoves hpeak hfit h2e h0t h0a h3t h3a
  have hfitn : FitsLen n := FitsLen.of_le hfit (by omega)
  have h2H : 2 < bA.sudo_5Board_4home.size := by rw [hszH']; decide
  have h2D : 2 < bA.sudo_5Board_4held.size := by rw [hszD']; decide
  have harr : bA.sudo_5Board_4home[2] = embed (List.replicate n 0) := by
    rw [hhome h2H, hzero]
  rw [chord_add_eq]
  unfold chordAddGo
  rw [hrun, ok_bind]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
      is_zero_embed bA 2 n (List.replicate n 0) h2D h2H (hheld h2D) harr hn'
        (by simp) hfitn, ok_bind]
  simp only [decide_True, if_true, pure_eq_ok]
  refine ⟨bA, rfl, ?_, hheld, hszD', hszH', hn', hmv⟩
  intro h
  rw [hhome h, hzero]

/-- A nonempty run. `chord_add_demo` is the inverse, the rise, and the tail
    on the board the copy-then-add left. The bottom is `fieldSub` of the two
    across homes, and it is not `n` zeros. -/
theorem chord_add_open (b : Ecbs.Board) (red : Bool) (baseX accX : List Nat)
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
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed baseX)
    (hne : fieldSub n baseX accX ≠ List.replicate n 0) :
    ∃ bA,
      Ecbs.chord_add_demo b red = chordAddTail bA red ∧
      (∀ h : 2 < bA.sudo_5Board_4home.size,
        bA.sudo_5Board_4home[2] = embed (fieldSub n baseX accX)) ∧
      (∀ h : 2 < bA.sudo_5Board_4held.size, bA.sudo_5Board_4held[2] = true) ∧
      bA.sudo_5Board_4held.size = 8 ∧
      bA.sudo_5Board_4home.size = 8 ∧
      bA.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bA.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseX + pegCount accX : Nat) : Int) := by
  obtain ⟨bA, hrun, hhome, hheld, hszD', hszH', hn', hmv⟩ :=
    run_of_copy b baseX accX n moves peak cOps hszH hszD hops hop hfops
      hx hy hpos htriB htriA hn hmoves hpeak hfit h2e h0t h0a h3t h3a
  have hfitn : FitsLen n := FitsLen.of_le hfit (by omega)
  have h2H : 2 < bA.sudo_5Board_4home.size := by rw [hszH']; decide
  have h2D : 2 < bA.sudo_5Board_4held.size := by rw [hszD']; decide
  have hlen : (fieldSub n baseX accX).length = n := fieldSub_length n baseX accX
  rw [chord_add_eq]
  unfold chordAddGo
  rw [hrun, ok_bind]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
      is_zero_embed bA 2 n (fieldSub n baseX accX) h2D h2H (hheld h2D) (hhome h2H)
        hn' hlen hfitn, ok_bind]
  have hdec : decide (fieldSub n baseX accX = List.replicate n 0) = false :=
    decide_eq_false hne
  rw [hdec]
  simp only [Bool.false_eq_true, if_false]
  exact ⟨bA, rfl, hhome, hheld, hszD', hszH', hn', hmv⟩

end EcbsLink2.Link2
