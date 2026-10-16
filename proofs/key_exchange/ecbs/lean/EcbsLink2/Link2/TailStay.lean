/-
  Fields the chord tail does not write. Homes 0, 1, 2, 5, and 6 move; home 3
  is the base point and home 4 is the base up. The control frame (ladder, park,
  tally origin, parked-from, rung index, tally length, tally max) stays.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

/-- Read home `i`, or the empty band when `i` is past the end. -/
def homeD (b : Ecbs.Board) (i : Nat) : Array Int :=
  (b.sudo_5Board_4home[i]?).getD #[]

/-- Read the held flag at `i`, or `false` when `i` is past the end. -/
def heldD (b : Ecbs.Board) (i : Nat) : Bool :=
  (b.sudo_5Board_4held[i]?).getD false

/-- Ladder, park, tally origin, and the tally counters. A multiply writes
    homes and the bench; these stay. Proof-only. Not an export result. -/
structure FrameScalar (b0 b : Ecbs.Board) : Prop where
  ladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder
  l0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0
  nr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs
  park : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole
  fromH : b.sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from
  ridx : b.sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx
  tlen : b.sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len
  t0 : b.sudo_5Board_6tally0 = b0.sudo_5Board_6tally0
  tmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
    b0.sudo_5Board_4cost.sudo_5Costs_9tally_max

theorem FrameScalar.refl (b : Ecbs.Board) : FrameScalar b b :=
  { ladder := rfl, l0 := rfl, nr := rfl, park := rfl, fromH := rfl, ridx := rfl
    tlen := rfl, t0 := rfl, tmax := rfl }

theorem FrameScalar.trans {a b c : Ecbs.Board} (h : FrameScalar a b) (h' : FrameScalar b c) :
    FrameScalar a c :=
  { ladder := h'.ladder.trans h.ladder
    l0 := h'.l0.trans h.l0
    nr := h'.nr.trans h.nr
    park := h'.park.trans h.park
    fromH := h'.fromH.trans h.fromH
    ridx := h'.ridx.trans h.ridx
    tlen := h'.tlen.trans h.tlen
    t0 := h'.t0.trans h.t0
    tmax := h'.tmax.trans h.tmax }

theorem FrameScalar.of_eq {b0 b : Ecbs.Board}
    (hladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder)
    (hl0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0)
    (hnr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs)
    (hpark : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole)
    (hfrom : b.sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from)
    (hridx : b.sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx)
    (htlen : b.sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len)
    (ht0 : b.sudo_5Board_6tally0 = b0.sudo_5Board_6tally0)
    (htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b0.sudo_5Board_4cost.sudo_5Costs_9tally_max) :
    FrameScalar b0 b :=
  { ladder := hladder, l0 := hl0, nr := hnr, park := hpark, fromH := hfrom
    ridx := hridx, tlen := htlen, t0 := ht0, tmax := htmax }

/-- The control frame and the two base homes, unchanged by one tail step. -/
structure TailStay (b0 b : Ecbs.Board) : Prop where
  ladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder
  l0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0
  nr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs
  park : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole
  fromH : b.sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from
  ridx : b.sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx
  tlen : b.sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len
  t0 : b.sudo_5Board_6tally0 = b0.sudo_5Board_6tally0
  tmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
    b0.sudo_5Board_4cost.sudo_5Costs_9tally_max
  tier : b.sudo_5Board_1t = b0.sudo_5Board_1t
  home3 : homeD b 3 = homeD b0 3
  held3 : heldD b 3 = heldD b0 3
  home4 : homeD b 4 = homeD b0 4
  held4 : heldD b 4 = heldD b0 4

theorem TailStay.refl (b : Ecbs.Board) : TailStay b b := by
  refine
    { ladder := rfl, l0 := rfl, nr := rfl, park := rfl, fromH := rfl, ridx := rfl
      tlen := rfl, t0 := rfl, tmax := rfl, tier := rfl
      home3 := rfl, held3 := rfl, home4 := rfl, held4 := rfl }

theorem TailStay.trans {a b c : Ecbs.Board} (h : TailStay a b) (h' : TailStay b c) :
    TailStay a c := by
  refine
    { ladder := h'.ladder.trans h.ladder
      l0 := h'.l0.trans h.l0
      nr := h'.nr.trans h.nr
      park := h'.park.trans h.park
      fromH := h'.fromH.trans h.fromH
      ridx := h'.ridx.trans h.ridx
      tlen := h'.tlen.trans h.tlen
      t0 := h'.t0.trans h.t0
      tmax := h'.tmax.trans h.tmax
      tier := h'.tier.trans h.tier
      home3 := h'.home3.trans h.home3
      held3 := h'.held3.trans h.held3
      home4 := h'.home4.trans h.home4
      held4 := h'.held4.trans h.held4 }

theorem homeD_set_ne (b : Ecbs.Board) (i : Nat) (hi : i < b.sudo_5Board_4home.size)
    (arr : Array Int) (j : Nat) (hne : i ≠ j) :
    homeD { b with sudo_5Board_4home := b.sudo_5Board_4home.set ⟨i, hi⟩ arr } j =
      homeD b j := by
  unfold homeD
  have hne' : (⟨i, hi⟩ : Fin _).1 ≠ j := hne
  simp only
  rw [Array.getElem?_set_ne (b.sudo_5Board_4home) ⟨i, hi⟩ arr hne']

theorem heldD_set_ne (b : Ecbs.Board) (i : Nat) (hi : i < b.sudo_5Board_4held.size)
    (flag : Bool) (j : Nat) (hne : i ≠ j) :
    heldD { b with sudo_5Board_4held := b.sudo_5Board_4held.set ⟨i, hi⟩ flag } j =
      heldD b j := by
  unfold heldD
  have hne' : (⟨i, hi⟩ : Fin _).1 ≠ j := hne
  simp only
  rw [Array.getElem?_set_ne (b.sudo_5Board_4held) ⟨i, hi⟩ flag hne']

/-- A cost-only update, or any update that leaves the frame fields and the two
    base homes definitionally alone. -/
theorem TailStay.of_eq {b0 b : Ecbs.Board}
    (hladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder)
    (hl0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0)
    (hnr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs)
    (hpark : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole)
    (hfrom : b.sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from)
    (hridx : b.sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx)
    (htlen : b.sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len)
    (ht0 : b.sudo_5Board_6tally0 = b0.sudo_5Board_6tally0)
    (htmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b0.sudo_5Board_4cost.sudo_5Costs_9tally_max)
    (htier : b.sudo_5Board_1t = b0.sudo_5Board_1t)
    (h3 : homeD b 3 = homeD b0 3) (hd3 : heldD b 3 = heldD b0 3)
    (h4 : homeD b 4 = homeD b0 4) (hd4 : heldD b 4 = heldD b0 4) :
    TailStay b0 b :=
  { ladder := hladder, l0 := hl0, nr := hnr, park := hpark, fromH := hfrom
    ridx := hridx, tlen := htlen, t0 := ht0, tmax := htmax, tier := htier
    home3 := h3, held3 := hd3, home4 := h4, held4 := hd4 }

/-- Replacing the bench and the move counter. The control frame stays. -/
theorem TailStay.bench_moves (b : Ecbs.Board) (arr : Array Int) (mv : Int) :
    TailStay b
      { { b with sudo_5Board_5bench := arr } with
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := mv } } :=
  TailStay.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Clearing one home other than the two base homes, and charging moves.
    The control frame stays. -/
theorem TailStay.set_cell (b : Ecbs.Board) (i : Nat)
    (hiH : i < b.sudo_5Board_4home.size)
    (hiD : i < b.sudo_5Board_4held.size)
    (arr : Array Int) (flag : Bool) (moves : Int)
    (h3 : i ≠ 3) (h4 : i ≠ 4) :
    TailStay b
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨i, hiH⟩ arr
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨i, hiD⟩ flag
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := moves } } := by
  refine TailStay.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · unfold homeD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h3)]
  · unfold heldD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h3)]
  · unfold homeD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h4)]
  · unfold heldD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h4)]

end EcbsLink2.Link2
