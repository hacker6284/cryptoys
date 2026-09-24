/-
  GridCycle (MixColumns stand-in) — walk placement + row-major scoop/lay.
  Proves invMixColumns ∘ mixColumns = id. Correctness, zero sorry. No Mathlib.
-/
import TwoDeck.Basic
import TwoDeck.Grid

namespace TwoDeck

/-! ## Geometry -/

def asStart : Fin 4 × Fin 13 := (⟨2, by decide⟩, ⟨0, by decide⟩)

def gridStep (card : Nat) (pos : Fin 4 × Fin 13) : Fin 4 × Fin 13 :=
  (⟨(pos.1.val + suit card) % 4, Nat.mod_lt _ (by decide)⟩,
   ⟨(pos.2.val + rank card) % 13, Nat.mod_lt _ (by decide)⟩)

/-! ## Occupancy -/

abbrev Occ := Fin 4 → Fin 13 → Bool

def emptyOcc : Occ := fun _ _ => false

def setOcc (occ : Occ) (p : Fin 4 × Fin 13) : Occ :=
  fun r c => decide (r = p.1 ∧ c = p.2) || occ r c

abbrev occAt (occ : Occ) (p : Fin 4 × Fin 13) : Bool := occ p.1 p.2

theorem setOcc_at_self (occ : Occ) (p : Fin 4 × Fin 13) :
    occAt (setOcc occ p) p = true := by
  simp [occAt, setOcc]

theorem setOcc_at_ne (occ : Occ) {p q : Fin 4 × Fin 13} (hne : p ≠ q) :
    occAt (setOcc occ p) q = occAt occ q := by
  simp only [occAt, setOcc]
  by_cases hq : q.1 = p.1 ∧ q.2 = p.2
  · exact False.elim (hne (Prod.ext hq.1 hq.2).symm)
  · simp [decide_eq_false hq]

theorem eq_false_of_ne_true {b : Bool} (h : ¬b = true) : b = false := by
  cases b <;> simp_all

def fins13 : List (Fin 13) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def fins4 : List (Fin 4) := [0, 1, 2, 3]

theorem length_fins13 : fins13.length = 13 := rfl
theorem length_fins4 : fins4.length = 4 := rfl

theorem mem_fins13 (c : Fin 13) : c ∈ fins13 := by
  have : c.val < 13 := c.isLt
  simp [fins13, List.mem_cons]; omega

theorem mem_fins4 (r : Fin 4) : r ∈ fins4 := by
  have : r.val < 4 := r.isLt
  simp [fins4, List.mem_cons]; omega

theorem nodup_fins13 : fins13.Nodup := by decide
theorem nodup_fins4 : fins4.Nodup := by decide

def countCols (occ : Occ) (r : Fin 4) : Nat :=
  (fins13.filter (fun c => occ r c)).length

def occCount (occ : Occ) : Nat :=
  (fins4.map (countCols occ)).sum

theorem countCols_le (occ : Occ) (r : Fin 4) : countCols occ r ≤ 13 := by
  simpa [countCols, length_fins13] using List.length_filter_le (fun c => occ r c) fins13

theorem occCount_le (occ : Occ) : occCount occ ≤ 52 := by
  simp only [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
  have a0 := countCols_le occ 0
  have a1 := countCols_le occ 1
  have a2 := countCols_le occ 2
  have a3 := countCols_le occ 3
  omega

theorem occCount_empty : occCount emptyOcc = 0 := rfl

theorem countCols_full (occ : Occ) (r : Fin 4) (h : ∀ c, occ r c = true) :
    countCols occ r = 13 := by
  simp only [countCols]
  have : fins13.filter (fun c => occ r c) = fins13 :=
    List.filter_eq_self.mpr fun c _ => h c
  simp [this, length_fins13]

theorem occCount_full (occ : Occ) (h : ∀ p : Fin 4 × Fin 13, occAt occ p = true) :
    occCount occ = 52 := by
  simp only [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hr : ∀ r : Fin 4, ∀ c, occ r c = true := fun r c => h (r, c)
  simp [countCols_full occ 0 (hr 0), countCols_full occ 1 (hr 1),
        countCols_full occ 2 (hr 2), countCols_full occ 3 (hr 3)]

theorem exists_free_of_count_lt (occ : Occ) (h : occCount occ < 52) :
    ∃ p : Fin 4 × Fin 13, occAt occ p = false := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ p, occAt occ p = true := by
    intro p
    by_cases hp : occAt occ p = true
    · exact hp
    · exact False.elim (hne ⟨p, eq_false_of_ne_true hp⟩)
  have := occCount_full occ hall
  omega

theorem nodup_cons_iff {α : Type} {a : α} {l : List α} :
    (a :: l).Nodup ↔ (∀ a', a' ∈ l → a ≠ a') ∧ l.Nodup := by
  simp only [List.Nodup, List.pairwise_cons]

theorem map_eq_of_mem {α β} (f g : α → β) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := (List.map_eq_map_iff).mpr h

theorem filter_mark_one {α : Type} [DecidableEq α]
    (target : α) (f : α → Bool) (xs : List α)
    (hn : xs.Nodup) (hc : target ∈ xs) (hf : f target = false) :
    (xs.filter (fun x => decide (x = target) || f x)).length =
      (xs.filter f).length + 1 := by
  induction xs with
  | nil => cases hc
  | cons a rest ih =>
    have ⟨hnotin_head, hnRest⟩ := (nodup_cons_iff).mp hn
    simp only [List.mem_cons] at hc
    simp only [List.filter]
    cases hc with
    | inl heq =>
      cases heq
      have ht : (decide (target = target) || f target) = true := by simp
      simp only [ht, ↓reduceIte, hf]
      have heqRest :
          rest.filter (fun x => decide (x = target) || f x) = rest.filter f :=
        List.filter_congr fun x hx => by
          have hxne : x ≠ target := fun he => hnotin_head x hx he.symm
          simp [decide_eq_false hxne]
      simp [heqRest]
    | inr hrest =>
      have ih' := ih hnRest hrest
      by_cases ha : a = target
      · cases ha
        exact False.elim (hnotin_head target hrest rfl)
      · simp only [decide_eq_false ha, Bool.false_or]
        split <;> simp [ih']

theorem countCols_set_free (occ : Occ) (r : Fin 4) (c : Fin 13)
    (hfree : occ r c = false) :
    countCols (setOcc occ (r, c)) r = countCols occ r + 1 := by
  simp only [countCols, setOcc, true_and]
  exact filter_mark_one c (occ r) fins13 nodup_fins13 (mem_fins13 c) hfree

theorem countCols_set_other_row (occ : Occ) (r : Fin 4) (p : Fin 4 × Fin 13)
    (hne : r ≠ p.1) :
    countCols (setOcc occ p) r = countCols occ r := by
  simp only [countCols, setOcc]
  apply congrArg List.length
  exact List.filter_congr fun col _ => by
    have : decide (r = p.1 ∧ col = p.2) = false :=
      decide_eq_false fun ⟨hr, _⟩ => hne hr
    simp [this]

theorem sum_incr_at {α : Type} [DecidableEq α]
    (f : α → Nat) (r0 : α) (xs : List α)
    (hn : xs.Nodup) (hc : r0 ∈ xs) :
    (xs.map (fun r => if r = r0 then f r + 1 else f r)).sum =
      (xs.map f).sum + 1 := by
  induction xs with
  | nil => cases hc
  | cons a rest ih =>
    have ⟨hhead, hnRest⟩ := (nodup_cons_iff).mp hn
    simp only [List.mem_cons] at hc
    simp only [List.map, List.sum_cons]
    cases hc with
    | inl heq =>
      cases heq
      simp only [ite_true]
      have heqRest :
          rest.map (fun r => if r = r0 then f r + 1 else f r) = rest.map f :=
        map_eq_of_mem _ _ rest fun r hr => by
          have : r ≠ r0 := fun he => hhead r hr he.symm
          simp [this]
      rw [heqRest]; omega
    | inr hrest =>
      have hne : a ≠ r0 := fun he => hhead r0 hrest he
      simp only [hne, ite_false]
      have := ih hnRest hrest
      omega

theorem occCount_set_free (occ : Occ) (p : Fin 4 × Fin 13)
    (hfree : occAt occ p = false) :
    occCount (setOcc occ p) = occCount occ + 1 := by
  simp only [occCount]
  have hmap :
      fins4.map (countCols (setOcc occ p)) =
        fins4.map (fun r => if r = p.1 then countCols occ r + 1 else countCols occ r) := by
    apply map_eq_of_mem
    intro r _
    by_cases he : r = p.1
    · cases he
      simp [countCols_set_free occ p.1 p.2 hfree]
    · simp [he, countCols_set_other_row occ r p he]
  rw [hmap]
  exact sum_incr_at (countCols occ) p.1 fins4 nodup_fins4 (mem_fins4 p.1)


/-! ## Overflow scan -/

def scanRowN (occ : Occ) (row : Fin 4) : Nat → Nat → Option (Fin 13)
  | 0, _ => none
  | fuel + 1, col =>
      if h : col < 13 then
        let c : Fin 13 := ⟨col, h⟩
        if occ row c then scanRowN occ row fuel (col + 1) else some c
      else none

def scanRow (occ : Occ) (row : Fin 4) : Option (Fin 13) :=
  scanRowN occ row 13 0

theorem scanRowN_some_free (occ : Occ) (row : Fin 4) :
    ∀ (fuel col : Nat) (c : Fin 13),
      scanRowN occ row fuel col = some c → occ row c = false
  | 0, col, c, h => by cases h
  | fuel + 1, col, c, h => by
      simp only [scanRowN] at h
      split at h
      · next hcol =>
        split at h
        · next => exact scanRowN_some_free occ row fuel (col + 1) c h
        · next hne =>
            injection h with heq; cases heq
            exact eq_false_of_ne_true hne
      · next => cases h

theorem scanRowN_none_occupied (occ : Occ) (row : Fin 4) :
    ∀ (fuel col : Nat), scanRowN occ row fuel col = none →
      ∀ c : Fin 13, col ≤ c.val → c.val < col + fuel → occ row c = true
  | 0, col, _, c, hc1, hc2 => by omega
  | fuel + 1, col, hnone, c, hc1, hc2 => by
      simp only [scanRowN] at hnone
      split at hnone
      · next hcol =>
        split at hnone
        · next hocc =>
          have ih := scanRowN_none_occupied occ row fuel (col + 1) hnone
          by_cases heq : c.val = col
          · have : c = ⟨col, hcol⟩ := Fin.ext heq
            simpa [this] using hocc
          · exact ih c (by omega) (by omega)
        · next => cases hnone
      · next => omega

theorem scanRow_none_full (occ : Occ) (row : Fin 4) (h : scanRow occ row = none) :
    ∀ c : Fin 13, occ row c = true := by
  intro c
  exact scanRowN_none_occupied occ row 13 0 h c (by omega) (by have := c.isLt; omega)

theorem scanRow_some_free (occ : Occ) (row : Fin 4) (c : Fin 13)
    (h : scanRow occ row = some c) : occ row c = false :=
  scanRowN_some_free occ row 13 0 c h

def overflowN (occ : Occ) : Nat → Nat → Option ((Fin 4 × Fin 13) × Nat)
  | 0, _ => none
  | fuel + 1, t =>
      let row : Fin 4 := ⟨t % 4, Nat.mod_lt _ (by decide)⟩
      match scanRow occ row with
      | some c => some ((row, c), (t + 1) % 4)
      | none => overflowN occ fuel ((t + 1) % 4)

def overflowSeat (occ : Occ) (t : Nat) : Option ((Fin 4 × Fin 13) × Nat) :=
  overflowN occ 4 t

theorem overflowN_some_free (occ : Occ) :
    ∀ (fuel t : Nat) (p : Fin 4 × Fin 13) (t' : Nat),
      overflowN occ fuel t = some (p, t') → occAt occ p = false
  | 0, t, p, t', h => by cases h
  | fuel + 1, t, p, t', h => by
      match hs : scanRow occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ with
      | some c =>
          have h' : overflowN occ (fuel + 1) t = some ((⟨t % 4, Nat.mod_lt _ (by decide)⟩, c), (t + 1) % 4) := by
            simp only [overflowN, hs]
          rw [h'] at h
          injection h with hp
          injection hp with hp1 _
          cases hp1
          exact scanRow_some_free occ _ c hs
      | none =>
          have h' : overflowN occ (fuel + 1) t = overflowN occ fuel ((t + 1) % 4) := by
            simp only [overflowN, hs]
          rw [h'] at h
          exact overflowN_some_free occ fuel ((t + 1) % 4) p t' h

theorem add_left_mod_mod (a b n : Nat) : (a + b % n) % n = (a + b) % n := by
  calc (a + b % n) % n
      = (a % n + b % n % n) % n := by rw [Nat.add_mod]
    _ = (a % n + b % n) % n := by rw [Nat.mod_mod]
    _ = (a + b) % n := by rw [← Nat.add_mod]

theorem mod4_cover (t : Nat) (r : Fin 4) :
    ∃ i : Fin 4, (t + i.val) % 4 = r.val := by
  have ht : t % 4 < 4 := Nat.mod_lt t (by decide)
  have hr : r.val < 4 := r.isLt
  let iVal := (r.val + 4 - t % 4) % 4
  have hi : iVal < 4 := Nat.mod_lt _ (by decide)
  refine ⟨⟨iVal, hi⟩, ?_⟩
  have h1 : (t + iVal) % 4 = (t % 4 + iVal) % 4 := by
    calc (t + iVal) % 4
        = (t % 4 + iVal % 4) % 4 := Nat.add_mod t iVal 4
      _ = (t % 4 + iVal) % 4 := by rw [Nat.mod_eq_of_lt hi]
  rw [h1]
  show (t % 4 + (r.val + 4 - t % 4) % 4) % 4 = r.val
  rw [add_left_mod_mod]
  have : t % 4 + (r.val + 4 - t % 4) = r.val + 4 := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hr

theorem overflowN_none_row_full (occ : Occ) :
    ∀ (fuel t : Nat), overflowN occ fuel t = none →
      ∀ i : Nat, i < fuel → ∀ c : Fin 13,
        occ ⟨(t + i) % 4, Nat.mod_lt _ (by decide)⟩ c = true
  | 0, t, _, i, hi, c => by omega
  | fuel + 1, t, hnone, i, hi, c => by
      match hs : scanRow occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ with
      | some c0 =>
          simp only [overflowN, hs] at hnone
          cases hnone
      | none =>
          have hrec : overflowN occ (fuel + 1) t = overflowN occ fuel ((t + 1) % 4) := by
            simp only [overflowN, hs]
          rw [hrec] at hnone
          cases i with
          | zero =>
              exact scanRow_none_full occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ hs c
          | succ j =>
              have hj : j < fuel := by omega
              have ih := overflowN_none_row_full occ fuel ((t + 1) % 4) hnone j hj c
              have heq : (((t + 1) % 4) + j) % 4 = (t + (j + 1)) % 4 := by
                rw [Nat.mod_add_mod]; ac_rfl
              have hrow :
                  (⟨(((t + 1) % 4) + j) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
                  ⟨(t + (j + 1)) % 4, Nat.mod_lt _ (by decide)⟩ := Fin.ext heq
              rw [← hrow]; exact ih

theorem overflow_none_full (occ : Occ) (t : Nat)
    (h : overflowSeat occ t = none) :
    ∀ p : Fin 4 × Fin 13, occAt occ p = true := by
  intro ⟨r, c⟩
  obtain ⟨i, hi⟩ := mod4_cover t r
  have hocc := overflowN_none_row_full occ 4 t h i.val i.isLt c
  have hrow : (⟨(t + i.val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = r := Fin.ext hi
  simpa [occAt, hrow] using hocc

theorem overflow_some_of_count_lt (occ : Occ) (t : Nat) (h : occCount occ < 52) :
    ∃ p t', overflowSeat occ t = some (p, t') ∧ occAt occ p = false := by
  cases hs : overflowSeat occ t with
  | none =>
      have := occCount_full occ (overflow_none_full occ t hs)
      omega
  | some pair =>
      refine ⟨pair.1, pair.2, rfl, overflowN_some_free occ 4 t pair.1 pair.2 hs⟩

/-! ## Shared walk step -/

structure WalkState where
  occ : Occ
  t : Nat
  prev : Option (Nat × (Fin 4 × Fin 13))

def initWalk : WalkState :=
  { occ := emptyOcc, t := 0, prev := none }

def advance (st : WalkState) (card : Nat) (pos : Fin 4 × Fin 13) (t' : Nat) : WalkState where
  occ := setOcc st.occ pos
  t := t'
  prev := some (card, pos)

def chooseSeat? (st : WalkState) : Option ((Fin 4 × Fin 13) × Nat) :=
  match st.prev with
  | none => some (asStart, st.t)
  | some (card, pos) =>
      let target := gridStep card pos
      if occAt st.occ target then overflowSeat st.occ st.t
      else some (target, st.t)

/-- Total choose; fallback unused when count < 52. -/
def chooseSeat! (st : WalkState) : (Fin 4 × Fin 13) × Nat :=
  match chooseSeat? st with
  | some x => x
  | none => (asStart, st.t)

theorem chooseSeat!_free (st : WalkState) (hct : occCount st.occ < 52)
    (hprev : st.prev.isSome ∨ occAt st.occ asStart = false) :
    occAt st.occ (chooseSeat! st).1 = false := by
  match hprev_eq : st.prev with
  | none =>
      have : chooseSeat? st = some (asStart, st.t) := by simp [chooseSeat?, hprev_eq]
      simp only [chooseSeat!, this]
      cases hprev with
      | inl h => simp [hprev_eq] at h
      | inr h => exact h
  | some pair =>
      simp only [chooseSeat!, chooseSeat?, hprev_eq]
      by_cases ht : occAt st.occ (gridStep pair.1 pair.2)
      · simp only [ht, ↓reduceIte]
        obtain ⟨p, t', hs, hf⟩ := overflow_some_of_count_lt st.occ st.t hct
        simp only [hs]
        exact hf
      · have hf := eq_false_of_ne_true ht
        simp [hf]

/-! ## Placement and inverse on Fin 52 → Nat -/

abbrev NatGrid := Grid Nat

def setGrid (g : NatGrid) (p : Fin 4 × Fin 13) (card : Nat) : NatGrid :=
  fun r c => if decide (r = p.1 ∧ c = p.2) then card else g r c

theorem get_setGrid_self (g : NatGrid) (p : Fin 4 × Fin 13) (card : Nat) :
    setGrid g p card p.1 p.2 = card := by
  simp [setGrid]

theorem get_setGrid_ne (g : NatGrid) {p q : Fin 4 × Fin 13} (card : Nat) (hne : p ≠ q) :
    setGrid g p card q.1 q.2 = g q.1 q.2 := by
  simp only [setGrid]
  by_cases hq : q.1 = p.1 ∧ q.2 = p.2
  · exact False.elim (hne (Prod.ext hq.1 hq.2).symm)
  · simp [decide_eq_false hq]

/-- Place first `n` cards of `hand` (n ≤ 52). -/
def placeN (hand : Fin 52 → Nat) : Nat → NatGrid × WalkState
  | 0 => ((fun _ _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (g, st) := placeN hand n
      if h : n < 52 then
        let (pos, t') := chooseSeat! st
        let card := hand ⟨n, h⟩
        (setGrid g pos card, advance st card pos t')
      else (g, st)

def placedGrid (hand : Fin 52 → Nat) : NatGrid := (placeN hand 52).1

/-- MixColumns: place then scoop row-major. -/
def mixColumns (hand : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopRowMajor (placedGrid hand)

/-- Recover first `n` cards from grid by the same walk. -/
def invN (g : NatGrid) : Nat → (Fin 52 → Nat) × WalkState
  | 0 => ((fun _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (out, st) := invN g n
      if _h : n < 52 then
        let (pos, t') := chooseSeat! st
        let card := g pos.1 pos.2
        (fun j => if j.val = n then card else out j, advance st card pos t')
      else (out, st)

/-- Inv MixColumns: lay row-major then walk-recover. -/
def invMixColumns (packet : Fin 52 → Nat) : Fin 52 → Nat :=
  (invN (layRowMajor packet) 52).1

/-! ## Placement succeeds: after n ≤ 52 steps, occCount = n and last choose was free -/

theorem placeN_count (hand : Fin 52 → Nat) :
    ∀ n : Nat, n ≤ 52 → occCount (placeN hand n).2.occ = n
  | 0, _ => by simp [placeN, initWalk, occCount_empty]
  | n + 1, hn => by
      have hn' : n ≤ 52 := by omega
      have hc := placeN_count hand n hn'
      have hlt : n < 52 := by omega
      simp only [placeN, hlt, ↓reduceDIte]
      -- After simp, goal is about advance (placeN hand n).2 ...
      have hct : occCount (placeN hand n).2.occ < 52 := by omega
      have hfree :
          occAt (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1 = false := by
        refine chooseSeat!_free (placeN hand n).2 hct ?_
        cases hpv : (placeN hand n).2.prev with
        | none =>
            cases n with
            | zero =>
                exact Or.inr (by simp [placeN, initWalk, occAt, emptyOcc])
            | succ n' =>
                simp only [placeN, show n' < 52 by omega, ↓reduceDIte, advance] at hpv
                cases hpv
        | some _ =>
            exact Or.inl (by simp [Option.isSome, hpv])
      change occCount
          (setOcc (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1) = n + 1
      have hset := occCount_set_free (placeN hand n).2.occ
          (chooseSeat! (placeN hand n).2).1 hfree
      omega

/-- Alias kept for Round imports / length lemmas. -/
def gridCycle (deck : List Nat) : List Nat :=
  if h : deck.length = 52 then
    let f := fun i : Fin 52 => deck[i.val]'(by omega)
    (Array.ofFn (mixColumns f)).toList
  else deck

theorem gridCycle_length_le (deck : List Nat) :
    (gridCycle deck).length ≤ deck.length := by
  simp only [gridCycle]
  split
  · next _h =>
      have : ((Array.ofFn (mixColumns fun i : Fin 52 =>
          deck[i.val]'(by omega))).toList).length = 52 := Array.size_ofFn _
      omega
  · exact Nat.le_refl _

/-! ## Round-trip helpers -/

theorem placeN_choose_free (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    occAt (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1 = false := by
  have hc := placeN_count hand n (Nat.le_of_lt hn)
  have hct : occCount (placeN hand n).2.occ < 52 := by omega
  refine chooseSeat!_free (placeN hand n).2 hct ?_
  cases hpv : (placeN hand n).2.prev with
  | none =>
      cases n with
      | zero => exact Or.inr (by simp [placeN, initWalk, occAt, emptyOcc])
      | succ n' =>
          simp only [placeN, show n' < 52 by omega, ↓reduceDIte, advance] at hpv
          cases hpv
  | some _ => exact Or.inl (by simp [Option.isSome, hpv])

def placeSeat (hand : Fin 52 → Nat) (n : Nat) (_hn : n < 52) : Fin 4 × Fin 13 :=
  (chooseSeat! (placeN hand n).2).1

theorem occ_mono (hand : Fin 52 → Nat) :
    ∀ (m n : Nat), n ≤ m → m ≤ 52 → ∀ (p : Fin 4 × Fin 13),
      occAt (placeN hand n).2.occ p = true →
      occAt (placeN hand m).2.occ p = true
  | 0, n, hnm, hm, p, hp => by
      have : n = 0 := by omega
      subst this; exact hp
  | m + 1, n, hnm, hm, p, hp => by
      by_cases hnm' : n ≤ m
      · have hprev := occ_mono hand m n hnm' (by omega) p hp
        have hlt : m < 52 := by omega
        simp only [placeN, hlt, ↓reduceDIte, advance]
        by_cases he : p = (chooseSeat! (placeN hand m).2).1
        · cases he; exact setOcc_at_self _ _
        · rw [setOcc_at_ne (placeN hand m).2.occ (Ne.symm he)]; exact hprev
      · have : n = m + 1 := by omega
        cases this; exact hp

theorem seat_occupied_after (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    occAt (placeN hand (n + 1)).2.occ (placeSeat hand n hn) = true := by
  simp only [placeN, placeSeat, hn, ↓reduceDIte, advance]
  exact setOcc_at_self _ _

theorem place_write_stable (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52)
    (m : Nat) (hnm : n < m) (hm : m ≤ 52) :
    (placeN hand m).1 (placeSeat hand n hn).1 (placeSeat hand n hn).2 =
      hand ⟨n, hn⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hlt : m < 52 := by omega
      simp only [placeN, hlt, ↓reduceDIte]
      by_cases heq : (chooseSeat! (placeN hand m).2).1 = placeSeat hand n hn
      · by_cases hmn : m = n
        · cases hmn
          simp only [placeSeat, get_setGrid_self]
        · have hocc := occ_mono hand m (n + 1) (by omega) (by omega)
            (placeSeat hand n hn) (seat_occupied_after hand n hn)
          have hfree := placeN_choose_free hand m hlt
          rw [heq] at hfree
          simp only [hocc] at hfree
          exact (Bool.noConfusion hfree)
      · have hne : (chooseSeat! (placeN hand m).2).1 ≠ placeSeat hand n hn := heq
        rw [get_setGrid_ne (placeN hand m).1 (hand ⟨m, hlt⟩) hne]
        rcases Nat.lt_trichotomy n m with hlt' | heq' | hgt
        · exact ih hlt' (by omega)
        · cases heq'; exact False.elim (hne rfl)
        · omega

theorem placed_at_seat (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    placedGrid hand (placeSeat hand n hn).1 (placeSeat hand n hn).2 =
      hand ⟨n, hn⟩ :=
  place_write_stable hand n hn 52 (by omega) (by omega)

theorem inv_place_agree (hand : Fin 52 → Nat) (n : Nat) (hn : n ≤ 52) :
    (invN (placedGrid hand) n).2 = (placeN hand n).2 ∧
    ∀ (i : Fin 52), i.val < n → (invN (placedGrid hand) n).1 i = hand i := by
  induction n with
  | zero =>
      constructor
      · rfl
      · intro i hi; omega
  | succ n ih =>
      have hn' : n ≤ 52 := by omega
      have ⟨hst, hout⟩ := ih hn'
      have hlt : n < 52 := by omega
      have hchoose :
          chooseSeat! (invN (placedGrid hand) n).2 =
            chooseSeat! (placeN hand n).2 := by rw [hst]
      have hcard :
          placedGrid hand
              (chooseSeat! (placeN hand n).2).1.1
              (chooseSeat! (placeN hand n).2).1.2 =
            hand ⟨n, hlt⟩ := by
        simpa [placeSeat] using placed_at_seat hand n hlt
      simp only [invN, hlt, ↓reduceDIte]
      constructor
      · simp only [placeN, hlt, ↓reduceDIte]
        rw [hst]
        have : placedGrid hand
            (chooseSeat! (placeN hand n).2).1.1
            (chooseSeat! (placeN hand n).2).1.2 = hand ⟨n, hlt⟩ := hcard
        simp only [this]
      · intro i hi
        by_cases he : i.val = n
        · simp only [he, ↓reduceIte]
          have : i = ⟨n, hlt⟩ := Fin.ext he
          rw [hst]
          simpa [placeSeat, this] using placed_at_seat hand n hlt
        · have hil : i.val < n := by omega
          simp only [he, ↓reduceIte]
          exact hout i hil

set_option maxHeartbeats 400000 in
theorem invMixColumns_mixColumns (hand : Fin 52 → Nat) :
    invMixColumns (mixColumns hand) = hand := by
  funext i
  unfold invMixColumns mixColumns placedGrid
  rw [lay_scoop_rowMajor]
  exact (inv_place_agree hand 52 (by omega)).2 i i.isLt

end TwoDeck
