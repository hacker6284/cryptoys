/-
  A miss empties the five homes and leaves a board the next hole can plant
  into. The counters stay inside the budget the plant started with, with one
  hole's room spent.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchSeat

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem some_idx {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : i < a.size := by
  by_cases hlt : i < a.size
  · exact hlt
  · rw [Array.getElem?_ge a (by omega)] at h
    cases h

private theorem some_get {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : a[i]'(some_idx a i v h) = v := by
  rw [Array.getElem?_eq_getElem (some_idx a i v h)] at h
  injection h

/-- Fields one clear does not touch. -/
structure Kept (b0 b : Ecbs.Board) : Prop where
  marker : b.sudo_5Board_6marker = b0.sudo_5Board_6marker
  markerOn : b.sudo_5Board_9marker_on = b0.sudo_5Board_9marker_on
  bench : b.sudo_5Board_8bench_on = b0.sudo_5Board_8bench_on
  tier : b.sudo_5Board_1t = b0.sudo_5Board_1t
  szH : b.sudo_5Board_4home.size = b0.sudo_5Board_4home.size
  szD : b.sudo_5Board_4held.size = b0.sudo_5Board_4held.size
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = b0.sudo_5Board_4cost.sudo_5Costs_4ctrl
  slides : b.sudo_5Board_4cost.sudo_5Costs_6slides = b0.sudo_5Board_4cost.sudo_5Costs_6slides
  ops : b.sudo_5Board_4cost.sudo_5Costs_3ops = b0.sudo_5Board_4cost.sudo_5Costs_3ops
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
    b0.sudo_5Board_4cost.sudo_5Costs_17script_marker_max
  peak : b.sudo_5Board_4cost.sudo_5Costs_4peak = b0.sudo_5Board_4cost.sudo_5Costs_4peak
  strict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
    b0.sudo_5Board_4cost.sudo_5Costs_11peak_strict
  hole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
    b0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole
  ladder : b.sudo_5Board_6ladder = b0.sudo_5Board_6ladder
  l0 : b.sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0
  nr : b.sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs
  park : b.sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole
  fromH : b.sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from
  ridx : b.sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx
  tlen : b.sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len
  t0 : b.sudo_5Board_6tally0 = b0.sudo_5Board_6tally0
  row : b.sudo_5Board_3row = b0.sudo_5Board_3row

private theorem kept_trans {b0 b1 b2 : Ecbs.Board} (h1 : Kept b0 b1) (h2 : Kept b1 b2) :
    Kept b0 b2 where
  marker := h2.marker.trans h1.marker
  markerOn := h2.markerOn.trans h1.markerOn
  bench := h2.bench.trans h1.bench
  tier := h2.tier.trans h1.tier
  szH := h2.szH.trans h1.szH
  szD := h2.szD.trans h1.szD
  ctrl := h2.ctrl.trans h1.ctrl
  slides := h2.slides.trans h1.slides
  ops := h2.ops.trans h1.ops
  mx := h2.mx.trans h1.mx
  peak := h2.peak.trans h1.peak
  strict := h2.strict.trans h1.strict
  hole := h2.hole.trans h1.hole
  ladder := h2.ladder.trans h1.ladder
  l0 := h2.l0.trans h1.l0
  nr := h2.nr.trans h1.nr
  park := h2.park.trans h1.park
  fromH := h2.fromH.trans h1.fromH
  ridx := h2.ridx.trans h1.ridx
  tlen := h2.tlen.trans h1.tlen
  t0 := h2.t0.trans h1.t0
  row := h2.row.trans h1.row

/-- One held home, emptied. The other fields stay. -/
private theorem clear_one (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hhome : b.sudo_5Board_4home[home]? = some (embed xs))
    (hheld? : b.sudo_5Board_4held[home]? = some true)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hf : FitsLen xs.length)
    (hfit : FitsLen (moves + pegCount xs)) :
    ∃ b',
      Ecbs.clear b (home : Int) = .ok b' ∧
      Kept b b' ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount xs) ∧
      b'.sudo_5Board_4home[home]? = some (#[] : Array Int) ∧
      b'.sudo_5Board_4held[home]? = some false ∧
      (∀ j, home ≠ j → b'.sudo_5Board_4home[j]? = b.sudo_5Board_4home[j]?) ∧
      (∀ j, home ≠ j → b'.sudo_5Board_4held[j]? = b.sudo_5Board_4held[j]?) := by
  have hH := some_idx _ _ _ hhome
  have hD := some_idx _ _ _ hheld?
  have harr := some_get _ _ _ hhome
  have hheld := some_get _ _ _ hheld?
  have hm' : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [ofNat_eq_natCast] using hm
  have hcl := clear_held_refines b home xs moves hH hD hheld harr hm' hf hfit
  let b' := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }
  refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcl
  · exact
      { marker := by simp [b']
        markerOn := by simp [b']
        bench := by simp [b']
        tier := by simp [b']
        szH := by simp [b', Array.size_set]
        szD := by simp [b', Array.size_set]
        ctrl := by simp [b']
        slides := by simp [b']
        ops := by simp [b']
        mx := by simp [b']
        peak := by simp [b']
        strict := by simp [b']
        hole := by simp [b']
        ladder := by simp [b']
        l0 := by simp [b']
        nr := by simp [b']
        park := by simp [b']
        fromH := by simp [b']
        ridx := by simp [b']
        tlen := by simp [b']
        t0 := by simp [b']
        row := by simp [b'] }
  · simp [b']
  · simp only [b']
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set]
  · simp only [b']
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · intro j hne
    simp only [b']
    exact Array.getElem?_set_ne _ ⟨home, hH⟩ _ hne
  · intro j hne
    simp only [b']
    exact Array.getElem?_set_ne _ ⟨home, hD⟩ _ hne

private theorem fit_prefix (a b c d e f : Nat) (h : FitsLen (a + b + c + d + e + f)) :
    FitsLen (a + b) ∧ FitsLen (a + b + c) ∧ FitsLen (a + b + c + d) ∧
      FitsLen (a + b + c + d + e) := by
  exact ⟨FitsLen.of_le h (by omega), FitsLen.of_le h (by omega),
    FitsLen.of_le h (by omega), FitsLen.of_le h (by omega)⟩

private theorem len_fit (n bench : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001) :
    FitsLen n := by
  apply curveLayFit n bench n hn hb
  have h : n ≤ 24 * n + 8 := by
    exact Nat.le_trans (Nat.le_mul_of_pos_left n (by decide : 0 < 24)) (Nat.le_add_right _ _)
  omega

/-- The five clears after a miss. Counters other than moves stay put. -/
theorem miss_drop (b : Ecbs.Board)
    (gapXs side y ax bx : List Nat) (moves : Nat)
    (hgap : b.sudo_5Board_4home[searchGap]? = some (embed gapXs))
    (hgapD : b.sudo_5Board_4held[searchGap]? = some true)
    (hbot : b.sudo_5Board_4home[searchBottom]? = some (embed side))
    (hbotD : b.sudo_5Board_4held[searchBottom]? = some true)
    (hup : b.sudo_5Board_4home[searchUp]? = some (embed y))
    (hupD : b.sudo_5Board_4held[searchUp]? = some true)
    (hax : b.sudo_5Board_4home[searchAcross]? = some (embed ax))
    (haxD : b.sudo_5Board_4held[searchAcross]? = some true)
    (hbx : b.sudo_5Board_4home[searchBase]? = some (embed bx))
    (hbxD : b.sudo_5Board_4held[searchBase]? = some true)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfg : FitsLen gapXs.length) (hfs : FitsLen side.length) (hfy : FitsLen y.length)
    (hfa : FitsLen ax.length) (hfb : FitsLen bx.length)
    (hfit : FitsLen (moves + pegCount gapXs + pegCount side + pegCount y +
      pegCount ax + pegCount bx)) :
    ∃ bM,
      searchMiss b = .ok bM ∧
      MissAt bM ∧
      Kept b bM ∧
      bM.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount gapXs + pegCount side + pegCount y +
          pegCount ax + pegCount bx) ∧
      bM.sudo_5Board_4held[6]? = b.sudo_5Board_4held[6]? ∧
      bM.sudo_5Board_4held[4]? = b.sudo_5Board_4held[4]? ∧
      bM.sudo_5Board_4home[4]? = b.sudo_5Board_4home[4]? := by
  obtain ⟨h1, h2, h3, h4⟩ := fit_prefix moves (pegCount gapXs) (pegCount side)
    (pegCount y) (pegCount ax) (pegCount bx) hfit
  obtain ⟨b1, hc1, k1, hmv1, hgapE, hgapF, hH1, hD1⟩ :=
    clear_one b searchGap gapXs moves hgap hgapD hm hfg h1
  have hbot1 := (hH1 searchBottom (by decide)).trans hbot
  have hbotD1 := (hD1 searchBottom (by decide)).trans hbotD
  have hup1 := (hH1 searchUp (by decide)).trans hup
  have hupD1 := (hD1 searchUp (by decide)).trans hupD
  have hax1 := (hH1 searchAcross (by decide)).trans hax
  have haxD1 := (hD1 searchAcross (by decide)).trans haxD
  have hbx1 := (hH1 searchBase (by decide)).trans hbx
  have hbxD1 := (hD1 searchBase (by decide)).trans hbxD
  obtain ⟨b2, hc2, k2, hmv2, hbotE, hbotF, hH2, hD2⟩ :=
    clear_one b1 searchBottom side (moves + pegCount gapXs) hbot1 hbotD1 hmv1 hfs h2
  have hgap2 := (hH2 searchGap (by decide)).trans hgapE
  have hgapF2 := (hD2 searchGap (by decide)).trans hgapF
  have hup2 := (hH2 searchUp (by decide)).trans hup1
  have hupD2 := (hD2 searchUp (by decide)).trans hupD1
  have hax2 := (hH2 searchAcross (by decide)).trans hax1
  have haxD2 := (hD2 searchAcross (by decide)).trans haxD1
  have hbx2 := (hH2 searchBase (by decide)).trans hbx1
  have hbxD2 := (hD2 searchBase (by decide)).trans hbxD1
  obtain ⟨b3, hc3, k3, hmv3, hupE, hupF, hH3, hD3⟩ :=
    clear_one b2 searchUp y (moves + pegCount gapXs + pegCount side) hup2 hupD2 hmv2 hfy h3
  have hgap3 := (hH3 searchGap (by decide)).trans hgap2
  have hgapF3 := (hD3 searchGap (by decide)).trans hgapF2
  have hbot3 := (hH3 searchBottom (by decide)).trans hbotE
  have hbotF3 := (hD3 searchBottom (by decide)).trans hbotF
  have hax3 := (hH3 searchAcross (by decide)).trans hax2
  have haxD3 := (hD3 searchAcross (by decide)).trans haxD2
  have hbx3 := (hH3 searchBase (by decide)).trans hbx2
  have hbxD3 := (hD3 searchBase (by decide)).trans hbxD2
  obtain ⟨b4, hc4, k4, hmv4, haxE, haxF, hH4, hD4⟩ :=
    clear_one b3 searchAcross ax
      (moves + pegCount gapXs + pegCount side + pegCount y) hax3 haxD3 hmv3 hfa h4
  have hgap4 := (hH4 searchGap (by decide)).trans hgap3
  have hgapF4 := (hD4 searchGap (by decide)).trans hgapF3
  have hbot4 := (hH4 searchBottom (by decide)).trans hbot3
  have hbotF4 := (hD4 searchBottom (by decide)).trans hbotF3
  have hup4 := (hH4 searchUp (by decide)).trans hupE
  have hupF4 := (hD4 searchUp (by decide)).trans hupF
  have hbx4 := (hH4 searchBase (by decide)).trans hbx3
  have hbxD4 := (hD4 searchBase (by decide)).trans hbxD3
  obtain ⟨b5, hc5, k5, hmv5, hbxE, hbxF, hH5, hD5⟩ :=
    clear_one b4 searchBase bx
      (moves + pegCount gapXs + pegCount side + pegCount y + pegCount ax)
      hbx4 hbxD4 hmv4 hfb hfit
  refine ⟨b5, ?_, ?_, ?_, hmv5, ?_, ?_, ?_⟩
  · unfold searchMiss
    rw [hc1, ok_bind, hc2, ok_bind, hc3, ok_bind, hc4, ok_bind, hc5]
  · exact
      { gapHeld := (hD5 searchGap (by decide)).trans hgapF4
        botHeld := (hD5 searchBottom (by decide)).trans hbotF4
        upHeld := (hD5 searchUp (by decide)).trans hupF4
        axHeld := hD5 searchAcross (by decide) |>.trans haxF
        bxHeld := hbxF
        gapHome := (hH5 searchGap (by decide)).trans hgap4
        botHome := (hH5 searchBottom (by decide)).trans hbot4
        upHome := (hH5 searchUp (by decide)).trans hup4
        axHome := (hH5 searchAcross (by decide)).trans haxE
        bxHome := hbxE }
  · exact kept_trans (kept_trans (kept_trans (kept_trans k1 k2) k3) k4) k5
  · exact (hD5 6 (by decide)).trans
      ((hD4 6 (by decide)).trans
        ((hD3 6 (by decide)).trans
          ((hD2 6 (by decide)).trans (hD1 6 (by decide)))))
  · exact (hD5 4 (by decide)).trans
      ((hD4 4 (by decide)).trans
        ((hD3 4 (by decide)).trans
          ((hD2 4 (by decide)).trans (hD1 4 (by decide)))))
  · exact (hH5 4 (by decide)).trans
      ((hH4 4 (by decide)).trans
        ((hH3 4 (by decide)).trans
          ((hH2 4 (by decide)).trans (hH1 4 (by decide)))))

private theorem gap_in_plant (n bench : Nat) :
    gapCap n bench + 1 + n ≤ plantRoom n bench := by
  unfold gapCap sideCap plantRoom
  omega

private theorem plant_hole_under (n bench : Nat) :
    gapCap n bench + 1 + n + powMove n bench * (n - 1) + searchMove n bench ≤
      perHole n bench := by
  have hg := gap_in_plant n bench
  have hp : powMove n bench * (n - 1) ≤ powMove n bench * n :=
    Nat.mul_le_mul_left _ (Nat.sub_le n 1)
  have hsum : gapCap n bench + 1 + n + powMove n bench * (n - 1) ≤
      plantRoom n bench + powMove n bench * n :=
    Nat.add_le_add hg hp
  have hper : perHole n bench =
      plantRoom n bench + powMove n bench * n + searchMove n bench := by
    simp [perHole, powMove, searchMove]
  rw [hper]
  exact Nat.add_le_add_right hsum _

private theorem move_one (mv0 mv total n bench : Nat)
    (hm : mv ≤ mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1))
    (ht : total ≤ mv + searchMove n bench) :
    total ≤ mv0 + perHole n bench := by
  have h1 : total ≤ mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1) +
      searchMove n bench := by
    have hstep := Nat.add_le_add hm (Nat.le_refl (searchMove n bench))
    exact Nat.le_trans ht hstep
  have hassoc : mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1) +
      searchMove n bench =
      mv0 + (gapCap n bench + 1 + n + powMove n bench * (n - 1) + searchMove n bench) := by
    simp [Nat.add_assoc]
  rw [hassoc] at h1
  exact Nat.le_trans h1 (Nat.add_le_add_left (plant_hole_under n bench) mv0)

private theorem room_next (base spent per k : Nat)
    (h : FitsLen (base + per * (k + 1)))
    (hs : spent ≤ base + per) :
    FitsLen (spent + per * k) := by
  have hsplit : per * (k + 1) = per + per * k := by
    rw [Nat.mul_succ, Nat.add_comm]
  apply FitsLen.of_le h
  rw [hsplit, ← Nat.add_assoc]
  exact Nat.add_le_add_right hs _

private theorem room_drop (base spent per k : Nat) (hk : 1 < k)
    (h : FitsLen (base + per * k))
    (hs : spent ≤ base + per) :
    FitsLen (spent + per * (k - 1)) := by
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.le_of_lt hk)
  rw [← hk1] at h
  exact room_next base spent per (k - 1) h hs

private theorem slide_body (n : Nat) (hn : 0 < n) :
    6 * n + (4 * n) * (n - 1) + 2 * n ≤ 4 * (n * n) + 6 * n := by
  have hcancel : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have h4 : (4 * n) * (n - 1) + 4 * n = (4 * n) * n := by
    have h := Nat.mul_add (4 * n) (n - 1) 1
    rw [hcancel, Nat.mul_one] at h
    exact h.symm
  have hsq : (4 * n) * n = 4 * (n * n) := Nat.mul_assoc 4 n n
  have h8 : 6 * n + 2 * n = 8 * n := by
    rw [← Nat.add_mul]
  have hsplit : 8 * n = 4 * n + 4 * n := by
    simpa using Nat.add_mul 4 4 n
  have hre : 6 * n + (4 * n) * (n - 1) + 2 * n =
      (4 * n) * (n - 1) + 4 * n + 4 * n := by
    calc
      6 * n + (4 * n) * (n - 1) + 2 * n = (4 * n) * (n - 1) + (6 * n + 2 * n) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = (4 * n) * (n - 1) + 8 * n := by rw [h8]
      _ = (4 * n) * (n - 1) + (4 * n + 4 * n) := by rw [hsplit]
      _ = (4 * n) * (n - 1) + 4 * n + 4 * n := by rw [← Nat.add_assoc]
  rw [hre, h4, hsq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right n (by decide : (4 : Nat) ≤ 6)) _

private theorem slide_one (n sl0 sl sl2 : Nat) (hn : 0 < n)
    (hs : sl ≤ sl0 + 6 * n + (4 * n) * (n - 1))
    (h2 : sl2 ≤ sl + 2 * n) :
    sl2 ≤ sl0 + perSlide n := by
  have h1 : sl2 ≤ sl0 + 6 * n + (4 * n) * (n - 1) + 2 * n :=
    Nat.le_trans h2 (Nat.add_le_add_right hs _)
  have hbody := slide_body n hn
  have hassoc : sl0 + 6 * n + (4 * n) * (n - 1) + 2 * n =
      sl0 + (6 * n + (4 * n) * (n - 1) + 2 * n) := by
    simp [Nat.add_assoc]
  have hpoly : 4 * (n * n) + 6 * n = perSlide n := by
    unfold perSlide
    rw [Nat.mul_assoc]
  rw [hassoc] at h1
  rw [← hpoly]
  exact Nat.le_trans h1 (Nat.add_le_add_left hbody sl0)

private theorem ctrl_one (base c n : Nat) (hc : c ≤ base + 4 * (n - 1)) :
    c + 1 ≤ base + (4 * n + 4) := by
  have h4 : 4 * (n - 1) ≤ 4 * n := Nat.mul_le_mul_left 4 (Nat.sub_le n 1)
  have h1 : c + 1 ≤ base + 4 * (n - 1) + 1 := Nat.add_le_add_right hc 1
  have hassoc : base + 4 * (n - 1) + 1 = base + (4 * (n - 1) + 1) := Nat.add_assoc _ _ _
  have hstep : 4 * (n - 1) + 1 ≤ 4 * n + 1 := Nat.add_le_add_right h4 1
  have hpad : 4 * n + 1 ≤ 4 * n + 4 := Nat.add_le_add_left (by decide : (1 : Nat) ≤ 4) _
  rw [hassoc] at h1
  exact Nat.le_trans h1 (Nat.add_le_add_left (Nat.le_trans hstep hpad) base)

private theorem op0_one (o c n : Nat) (hn : 0 < n) (hc : c ≤ o + 2 + (n - 1)) :
    c + 1 ≤ o + (n + 2) := by
  have hcancel : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have h1 : c + 1 ≤ o + 2 + (n - 1) + 1 := Nat.add_le_add_right hc 1
  have hsum : 2 + (n - 1) + 1 = n + 2 := by
    calc
      2 + (n - 1) + 1 = 2 + ((n - 1) + 1) := Nat.add_assoc 2 (n - 1) 1
      _ = 2 + n := by rw [hcancel]
      _ = n + 2 := Nat.add_comm 2 n
  have hassoc : o + 2 + (n - 1) + 1 = o + (2 + (n - 1) + 1) := by
    simp [Nat.add_assoc]
  rw [hassoc, hsum] at h1
  exact h1

private theorem op1_one (o c n : Nat) (hc : c ≤ o + 1 + (n - 1)) :
    c ≤ o + (n + 2) := by
  have hstep : 1 + (n - 1) ≤ 1 + n := Nat.add_le_add_left (Nat.sub_le n 1) _
  have hcomm : 1 + n = n + 1 := Nat.add_comm _ _
  have hone : n + 1 ≤ n + 2 := Nat.le_succ _
  have hsum : 1 + (n - 1) ≤ n + 2 :=
    Nat.le_trans hstep (Nat.le_trans (by rw [hcomm]; exact Nat.le_refl _) hone)
  have hassoc : o + 1 + (n - 1) = o + (1 + (n - 1)) := Nat.add_assoc _ _ _
  rw [hassoc] at hc
  exact Nat.le_trans hc (Nat.add_le_add_left hsum o)

private theorem slot_nat (a : Array Int) (i c : Nat)
    (h : a[i]? = some (Int.ofNat c)) (hi : i < a.size) :
    a[i] = (c : Int) := by
  rw [Array.getElem?_eq_getElem hi] at h
  injection h

/-- A planted hole that misses is the next plant. `holesLeft` drops by one. -/
theorem miss_plantAt (b0 : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n)
    (mv0 sl0 c0 : Nat)
    (hmv0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t))
    (hmiss : rootHit t.n t.k t.benchlen (basisPeg t.n j) = false)
    (hnext : 1 < holesLeft) :
    ∃ bM,
      (do
          let b ← (do
            let b ← (do
              let b ← (do
                let b ← (do
                  let b ← (do
                    let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
                    let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
                    let b ← Ecbs.put b0 Ecbs.base_across x
                    Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
                  let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
                  Ecbs.settle b)
                Ecbs.white0 b Ecbs.up)
              let strip ← emittedStrip t.n
              let b ← Ecbs.put b Ecbs.across strip
              pure ({ b with sudo_5Board_9marker_on := true }))
            powRun b (rootDigits t.n))
          let r ← searchCheck b
          searchMiss r.2) = .ok bM ∧
        MissAt bM ∧
        PlantAt bM t (holesLeft - 1) ∧
        ∃ c0', bM.sudo_5Board_4cost.sudo_5Costs_4ctrl =
          Int.ofNat (c0' + tierR t) := by
  have hleft1 : (1 : Nat) ≤ holesLeft := Nat.le_of_lt hnext
  obtain ⟨bR, o0, o1, hready, hAt, hseat⟩ :=
    search_ready_at b0 t holesLeft hp hOk hsh sat j hj0 hj hn3 mv0 sl0 c0
      hmv0 hsl0 hc0 1 (by decide) hleft1
  let x := basisPeg t.n j
  let y := rootY t.n t.k t.benchlen x
  let side := curveSide t.n t.k t.benchlen x
  let gapXs := fieldMul t.n t.k t.benchlen side side
  let ax := rootStrip t.n
  let bx := x
  obtain ⟨bC, bit, movesS, hck, hbit, hhit, hmvS, hfit, hkeep, hspent⟩ :=
    search_check_at bR t x y side gapXs ax bx 1 hAt
  have hfalse : bit = false := by rw [hbit, hmiss]
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hOk.n_pos sat.mul_span
  have hfn : FitsLen t.n := len_fit t.n t.benchlen hsh.n_small hsh.small.2.2.2
  have hgap : bC.sudo_5Board_4home[searchGap]? = some (embed (fieldMul t.n t.k t.benchlen y y)) := by
    simpa [y, hAt.yIs] using hhit.gapHome
  have hbot : bC.sudo_5Board_4home[searchBottom]? = some (embed side) := by
    simpa [side, hAt.sideIs] using hhit.botHome
  have hup : bC.sudo_5Board_4home[searchUp]? = some (embed y) := by
    simpa [y, hAt.yIs] using hhit.upHome
  have hlenSq : (fieldMul t.n t.k t.benchlen y y).length = t.n :=
    fieldMul_length t.n t.k t.benchlen y y hnb
  obtain ⟨bM, hdrop, hmissAt, hk, hmvM, hspM, hbuD, hbuH⟩ :=
    miss_drop bC (fieldMul t.n t.k t.benchlen y y) side y ax bx movesS
      hgap hhit.gapHeld hbot hhit.botHeld hup hhit.upHeld
      hhit.axHome hhit.axHeld hhit.bxHome hhit.bxHeld
      hmvS (by rw [hlenSq]; exact hfn) (by rw [hAt.sideLen]; exact hfn)
      (by rw [hAt.yLen]; exact hfn) (by rw [hAt.axLen]; exact hfn)
      (by rw [hAt.bxLen]; exact hfn) hfit
  refine ⟨bM, ?_, hmissAt, ?_, ?_⟩
  · rw [hready, ok_bind]
    have hck' : searchCheck bR = .ok (false, bC) := by simpa [hfalse] using hck
    rw [hck', ok_bind]
    exact hdrop
  · rcases hseat.moves with ⟨mv, hmvR, hmvLe⟩
    rcases hspent with ⟨moves0, hmv0R, hspLe⟩
    have hmvSame : moves0 = mv := Int.ofNat.inj (hmv0R.symm.trans hmvR)
    have htotal : movesS + pegCount (fieldMul t.n t.k t.benchlen y y) + pegCount side +
        pegCount y + pegCount ax + pegCount bx ≤ mv0 + perHole t.n t.benchlen :=
      move_one mv0 mv _ t.n t.benchlen hmvLe (by rw [← hmvSame]; exact hspLe)
    rcases hp.moves with ⟨mvP, hmvP, hfitM⟩
    have hmvP0 : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv0)
    have hmovRoom : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
      simpa [hmvP0] using hfitM
    have hmovF : bM.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (movesS + pegCount (fieldMul t.n t.k t.benchlen y y) + pegCount side +
          pegCount y + pegCount ax + pegCount bx) := hmvM
    rcases hseat.slides with ⟨sl, hslR, hslLe⟩
    rcases hkeep.slides with ⟨sl0s, sl2, hsl0s, hsl2, hslStep⟩
    have hslSame : sl0s = sl := Int.ofNat.inj (hsl0s.symm.trans hslR)
    have hslFin : sl2 ≤ sl0 + perSlide t.n := by
      rw [hslSame] at hslStep
      simpa [powSlide] using slide_one t.n sl0 sl sl2 hOk.n_pos hslLe hslStep
    rcases hp.slides with ⟨slP, hslP, hfitS⟩
    have hslP0 : slP = sl0 := Int.ofNat.inj (hslP.symm.trans hsl0)
    have hslideRoom : FitsLen (sl0 + perSlide t.n * holesLeft) := by
      simpa [hslP0] using hfitS
    have hslideF : bM.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl2 :=
      hk.slides.trans hsl2
    rcases hseat.ctrl with ⟨cR, hcR, hlo, hcLe⟩
    rcases hkeep.ctrl with ⟨cIn, hcIn, hcOut⟩
    have hcSame : cIn = cR := Int.ofNat.inj (hcIn.symm.trans hcR)
    have hcFin : cIn + 1 ≤ (c0 + tierR t) + perCtrl t.n := by
      rw [hcSame]
      unfold powCtrl at hcLe
      unfold perCtrl
      exact ctrl_one (c0 + tierR t) cR t.n hcLe
    rcases hp.ctrl with ⟨cP, hcP, hfitC⟩
    have hcP0 : cP = c0 + tierR t := Int.ofNat.inj (hcP.symm.trans hc0)
    have hctrlRoom : FitsLen (c0 + tierR t + perCtrl t.n * holesLeft) := by
      simpa [hcP0, Nat.add_assoc] using hfitC
    have hctrlF : bM.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (cIn + 1) :=
      hk.ctrl.trans hcOut
    rcases hseat.ops0 with ⟨cOp, hopR, hopLe⟩
    rcases hkeep.ops0 with ⟨cOp0, hop0, hop1⟩
    have hopSame : cOp0 = cOp := by
      have hslot : some (Int.ofNat cOp0) = some (Int.ofNat cOp) := hop0.symm.trans hopR
      injection hslot with hEq
      exact Int.ofNat.inj hEq
    have hopFin : cOp0 + 1 ≤ o0 + perOp t.n := by
      rw [hopSame]
      unfold perOp
      exact op0_one o0 cOp t.n hOk.n_pos hopLe
    rcases hseat.ops1 with ⟨c1, hop1R, hop1Le⟩
    have hop1F : bM.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) := by
      have hC : bC.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) :=
        hkeep.ops1.trans hop1R
      exact (congrArg (fun a => a[1]?) hk.ops).trans hC
    have hop1Fin : c1 ≤ o1 + perOp t.n := by
      unfold perOp
      exact op1_one o1 c1 t.n hop1Le
    have hopSzM : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
      rw [congrArg Array.size hk.ops, hkeep.opsSz, hseat.opsSz]
    have h0M : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hopSzM]; decide
    have h1M : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hopSzM]; decide
    have hop0M : bM.sudo_5Board_4cost.sudo_5Costs_3ops[0]? =
        some (Int.ofNat (cOp0 + 1)) := by
      have hC : bC.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat (cOp0 + 1)) := hop1
      exact (congrArg (fun a => a[0]?) hk.ops).trans hC
    exact
      { tier := hk.tier.trans (hkeep.tier.trans hAt.tier)
        szH := hk.szH.trans (hkeep.szH.trans hseat.szH)
        szD := hk.szD.trans (hkeep.szD.trans hseat.szD)
        baseOff := hmissAt.bxHeld
        botOff := hmissAt.botHeld
        axOff := hmissAt.axHeld
        upOff := hmissAt.upHeld
        gapOff := hmissAt.gapHeld
        spareOff := hspM.trans hkeep.spare
        buOff := hbuD.trans hhit.buOff
        buHome := hbuH.trans hhit.buHome
        axHome := hmissAt.axHome
        upHome := hmissAt.upHome
        gapHome := hmissAt.gapHome
        marker := hk.marker.trans hkeep.marker
        markerOn := hk.markerOn.trans hkeep.markerOn
        benchOff := hk.bench.trans hkeep.benchOff
        holesPos := Nat.sub_pos_of_lt hnext
        moves := ⟨_, hmovF, room_drop mv0 _ (perHole t.n t.benchlen) holesLeft hnext hmovRoom htotal⟩
        slides := ⟨sl2, hslideF, room_drop sl0 sl2 (perSlide t.n) holesLeft hnext hslideRoom hslFin⟩
        ctrl := ⟨cIn + 1, hctrlF,
          room_drop (c0 + tierR t) (cIn + 1) (perCtrl t.n) holesLeft hnext hctrlRoom hcFin⟩
        peak := by
          rcases hkeep.peak with ⟨pk, hpk⟩
          exact ⟨pk, hk.peak.trans hpk⟩
        strict := by
          rcases hkeep.strict with ⟨ps, hps⟩
          exact ⟨ps, hk.strict.trans hps⟩
        hole := by
          rcases hkeep.hole with ⟨holeN, hhole⟩
          exact ⟨holeN, hk.hole.trans hhole⟩
        mx := by
          rcases hseat.mx with ⟨mxN, hmx⟩
          exact ⟨mxN, hk.mx.trans (hkeep.mx.trans hmx)⟩
        opsSz := hopSzM
        ops0 := ⟨cOp0 + 1, fun _ => slot_nat _ 0 (cOp0 + 1) hop0M h0M,
          room_drop o0 (cOp0 + 1) (perOp t.n) holesLeft hnext hseat.ops0Room hopFin⟩
        ops1 := ⟨c1, fun _ => slot_nat _ 1 c1 hop1F h1M,
          room_drop o1 c1 (perOp t.n) holesLeft hnext hseat.ops1Room hop1Fin⟩ }
  · rcases hseat.ctrl with ⟨cR, hcR, hlo, _⟩
    rcases hkeep.ctrl with ⟨cIn, hcIn, hcOut⟩
    have hcSame : cIn = cR := Int.ofNat.inj (hcIn.symm.trans hcR)
    have hctrlF : bM.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (cIn + 1) :=
      hk.ctrl.trans hcOut
    have hge : tierR t ≤ cIn + 1 := by
      have hstep : cR ≤ cIn + 1 := by
        rw [hcSame]
        exact Nat.le_succ _
      exact Nat.le_trans (Nat.le_add_left (tierR t) c0) (Nat.le_trans hlo hstep)
    have hsplit : (cIn + 1) - tierR t + tierR t = cIn + 1 :=
      Nat.sub_add_cancel hge
    exact ⟨(cIn + 1) - tierR t, by
      rw [hsplit]
      exact hctrlF⟩

end EcbsLink2.Link2
