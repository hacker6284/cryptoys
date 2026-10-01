/-
  BS Link 2: §4.3 READ. The emitted `ship_holes`, `ship_pass`, `peg_pass` and `read_key`
  against the model `Spec.readKey`, on every well-formed key (`Spec.Grid.Wf` pages).
  Proof-only.
-/
import BsLink2.Link2.Check

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- A model piece as the emitted `Kind`. -/
def embKind : Spec.Kind → Bs.Kind
  | .destroyer => .Sudo_4Kind_9Destroyer
  | .sub => .Sudo_4Kind_3Sub
  | .cruiser => .Sudo_4Kind_7Cruiser
  | .battleship => .Sudo_4Kind_10Battleship
  | .carrier => .Sudo_4Kind_7Carrier

/-- A model ship as the emitted `Ship` (row and column as non-negative `Int`s). -/
def embShip (s : Spec.Ship) : Bs.Ship :=
  { sudo_4Ship_4kind := embKind s.kind, sudo_4Ship_4down := s.down,
    sudo_4Ship_3row := Int.ofNat s.row, sudo_4Ship_3col := Int.ofNat s.col,
    sudo_4Ship_8bow_last := s.bowLast }

/-- A model key grid as the emitted `KeyGrid`. -/
def embGrid (g : Spec.Grid) : Bs.KeyGrid :=
  { sudo_7KeyGrid_5ships := (g.ships.map embShip).toArray,
    sudo_7KeyGrid_4pegs := embed g.pegs }

/-- A model key (its pages) as the emitted `List<KeyGrid>`. -/
def embKey (pages : List Spec.Grid) : Array Bs.KeyGrid := (pages.map embGrid).toArray

theorem ship_length_spec (k : Spec.Kind) : Bs.ship_length (embKind k) = .ok (Int.ofNat k.len) := by
  cases k <;> rfl


/-- §4.1. The emitted `ship_holes` of a ship on the grid is the model's list of holes. -/
theorem ship_holes_spec (s : Spec.Ship) (hs : s.OnGrid) :
    Bs.ship_holes (embShip s) = .ok (embed s.holes) := by
  have h2 := s.kind.two_le_len
  have h5 := s.kind.len_le_five
  unfold Bs.ship_holes
  rw [show (embShip s).sudo_4Ship_4kind = embKind s.kind from rfl, ship_length_spec, ok_bind]
  unfold Spec.Ship.OnGrid at hs
  have hfl : FitsLen s.kind.len := fits_small (by omega)
  cases hd : s.down
  · rw [hd] at hs
    simp only [Bool.false_eq_true, if_false] at hs
    obtain ⟨hr, hc⟩ := hs
    simp only [embShip, hd, Bs.grid_cols, Bs.grid_rows, Bool.false_eq_true, if_false]
    simp only [dec_ofNat_ge0, dec_ofNat_lt_ten _ hr, if_true, pure_eq_ok, ok_bind,
      sudoAssert_true, addI_ofNat s.col s.kind.len (fits_small (by omega)),
      dec_ofNat_le_ten _ hc, mulI_ten s.row (by omega),
      addI_ofNat (s.row * 10) s.col (fits_small (by omega)),
      subI_ofNat_one _ (by omega) hfl]
    rw [bind_ok_right, fuelRange_eq]
    refine asc_goal (fromN := 0) (toN := s.kind.len - 1)
      (fun t (hs : Array Int) => hs = embed ((List.range t).map (fun t => s.row * 10 + s.col + t * 1)))
      (Nat.zero_le _) rfl ?_ ?_
    · intro t hs _ ht hI
      subst hI
      refine ⟨_, rfl, ?_⟩
      dsimp only
      rw [if_neg (ofNat_not_gt ht), mulI_one t (by omega), ok_bind,
        addI_ofNat (s.row * 10 + s.col) (t * 1) (fits_small (by omega)), ok_bind]
      simp only [pure_eq_ok, ok_bind, appendL_spec]
      rw [show (embed ((List.range t).map (fun t => s.row * 10 + s.col + t * 1))).push
          (Int.ofNat (s.row * 10 + s.col + t * 1)) =
          embed ((List.range (t + 1)).map (fun t => s.row * 10 + s.col + t * 1)) by
        rw [List.range_succ, List.map_append, embed_append]; rfl]
      exact asc_tail _ t (fits_small (by omega)) _
    · intro hs hI
      subst hI
      rw [show s.kind.len - 1 + 1 = s.kind.len by omega]
      unfold Spec.Ship.holes Spec.Ship.step Spec.Ship.first
      rw [hd, Nat.mul_comm 10 s.row]; rfl
  · rw [hd] at hs
    simp only [if_true] at hs
    obtain ⟨hc, hr⟩ := hs
    simp only [embShip, hd, Bs.grid_cols, Bs.grid_rows, if_true]
    simp only [dec_ofNat_ge0, dec_ofNat_lt_ten _ hc, if_true, pure_eq_ok, ok_bind,
      sudoAssert_true, addI_ofNat s.row s.kind.len (fits_small (by omega)),
      dec_ofNat_le_ten _ hr, mulI_ten s.row (by omega),
      addI_ofNat (s.row * 10) s.col (fits_small (by omega)),
      subI_ofNat_one _ (by omega) hfl]
    rw [bind_ok_right, fuelRange_eq]
    refine asc_goal (fromN := 0) (toN := s.kind.len - 1)
      (fun t (hs : Array Int) => hs = embed ((List.range t).map (fun t => s.row * 10 + s.col + t * 10)))
      (Nat.zero_le _) rfl ?_ ?_
    · intro t hs _ ht hI
      subst hI
      refine ⟨_, rfl, ?_⟩
      dsimp only
      rw [if_neg (ofNat_not_gt ht), mulI_ten t (by omega), ok_bind,
        addI_ofNat (s.row * 10 + s.col) (t * 10) (fits_small (by omega)), ok_bind]
      simp only [pure_eq_ok, ok_bind, appendL_spec]
      rw [show (embed ((List.range t).map (fun t => s.row * 10 + s.col + t * 10))).push
          (Int.ofNat (s.row * 10 + s.col + t * 10)) =
          embed ((List.range (t + 1)).map (fun t => s.row * 10 + s.col + t * 10)) by
        rw [List.range_succ, List.map_append, embed_append]; rfl]
      exact asc_tail _ t (fits_small (by omega)) _
    · intro hs hI
      subst hI
      rw [show s.kind.len - 1 + 1 = s.kind.len by omega]
      unfold Spec.Ship.holes Spec.Ship.step Spec.Ship.first
      rw [hd, Nat.mul_comm 10 s.row]; rfl

/-! ### The ship pass's four tables, as functions of the ships placed so far -/

/-- The 100-entry table holding `f h` at hole `h`. -/
def tab {α} (f : Nat → α) : Array α := ((List.range 100).map f).toArray

theorem tab_size {α} (f : Nat → α) : (tab f).size = 100 := by simp [tab]

theorem tab_get {α} (f : Nat → α) (h : Nat) (hh : h < (tab f).size) : (tab f)[h] = f h := by
  simp [tab]

theorem tab_set {α} (f : Nat → α) (i : Nat) (hi : i < (tab f).size) (v : α) :
    (tab f).set ⟨i, hi⟩ v = tab (fun h => if h = i then v else f h) := by
  apply Array.ext _ _ (by simp [tab_size])
  intro h h1 h2
  rw [Array.getElem_set, tab_get, tab_get]
  by_cases e : h = i
  · subst e; simp
  · simp [e, Ne.symm e]

theorem tab_const {α} (v : α) : Array.mkArray 100 v = tab (fun _ => v) := by
  apply Array.ext _ _ (by simp [tab_size])
  intro h h1 h2
  rw [tab_get]; simp

/-- `covered[h]`: some ship of `P` covers `h`. -/
def covered (P : List Spec.Ship) (h : Nat) : Bool := P.any (fun s => decide (h ∈ s.holes))

/-- `first_cell[h]`: the first-hole cell of the ship whose first hole is `h`, else `-1`. -/
def firstCell (P : List Spec.Ship) (h : Nat) : Int :=
  match Spec.shipAt P h with
  | none => -1
  | some s => if h = s.first then (if s.down then 2 else 1) else -1

/-- `last_cell[h]`: the last-hole cell of the ship whose last hole is `h`, else `-1`. -/
def lastCell (P : List Spec.Ship) (h : Nat) : Int :=
  match Spec.shipAt P h with
  | none => -1
  | some s => if h = s.last then (if s.bowLast then 2 else 1) else -1

/-- The extra cell of a 3-holer (`-1`: none). -/
def extraOf : Spec.Kind → Int
  | .sub => 0
  | .cruiser => 1
  | _ => -1

/-- `extra_cell[h]`: the extra cell of the 3-holer whose last hole is `h`, else `-1`. -/
def extraCell (P : List Spec.Ship) (h : Nat) : Int :=
  match Spec.shipAt P h with
  | none => -1
  | some s => if h = s.last then extraOf s.kind else -1

theorem first_mem_holes (s : Spec.Ship) : s.first ∈ s.holes := by
  unfold Spec.Ship.holes
  rw [List.mem_map]
  exact ⟨0, List.mem_range.mpr (by have := s.kind.two_le_len; omega), by simp⟩

theorem last_mem_holes (s : Spec.Ship) : s.last ∈ s.holes := by
  unfold Spec.Ship.holes Spec.Ship.last
  rw [List.mem_map]
  exact ⟨s.kind.len - 1, List.mem_range.mpr (by have := s.kind.two_le_len; omega), rfl⟩

theorem step_pos (s : Spec.Ship) : 1 ≤ s.step := by
  unfold Spec.Ship.step; split <;> decide

theorem first_ne_last (s : Spec.Ship) : s.first ≠ s.last := by
  unfold Spec.Ship.last
  have := s.kind.two_le_len
  have := step_pos s
  have : 1 * 1 ≤ (s.kind.len - 1) * s.step := Nat.mul_le_mul (by omega : 1 ≤ s.kind.len - 1) this
  omega

theorem mem_holes {s : Spec.Ship} {h : Nat} :
    h ∈ s.holes ↔ ∃ t, t < s.kind.len ∧ h = s.first + t * s.step := by
  unfold Spec.Ship.holes
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem holes_lt (s : Spec.Ship) (hs : s.OnGrid) {h : Nat} (hh : h ∈ s.holes) : h < 100 := by
  obtain ⟨t, ht, rfl⟩ := mem_holes.mp hh
  unfold Spec.Ship.OnGrid at hs
  unfold Spec.Ship.first Spec.Ship.step
  split at hs
  · next hd => rw [if_pos hd]; omega
  · next hd => rw [if_neg hd]; omega

theorem length_holes (s : Spec.Ship) : s.holes.length = s.kind.len := by
  simp [Spec.Ship.holes]

theorem getElem_holes (s : Spec.Ship) (t : Nat) (ht : t < s.holes.length) :
    s.holes[t] = s.first + t * s.step := by
  simp [Spec.Ship.holes]

theorem holes_get_not_mem_take (s : Spec.Ship) (t : Nat) (ht : t < s.holes.length) :
    s.holes[t] ∉ s.holes.take t := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.mem_take_iff_getElem.mp hm
  have hi' : i < t := by omega
  rw [getElem_holes, getElem_holes] at he
  have := step_pos s
  have : i * s.step < t * s.step := Nat.mul_lt_mul_of_pos_right hi' (by omega)
  omega

/-- Placing a ship disjoint from `P`: the ship found at `h` is the new ship on its holes,
    and the old one elsewhere. -/
theorem shipAt_snoc (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) (h : Nat) :
    Spec.shipAt (P ++ [s]) h = if h ∈ s.holes then some s else Spec.shipAt P h := by
  unfold Spec.shipAt
  rw [List.find?_append]
  by_cases hm : h ∈ s.holes
  · rw [if_pos hm]
    have : P.find? (fun s => decide (h ∈ s.holes)) = none := by
      rw [List.find?_eq_none]
      intro x hx hp
      exact hdis x hx h hm (of_decide_eq_true hp)
    rw [this]; simp [hm]
  · rw [if_neg hm]
    cases P.find? (fun s => decide (h ∈ s.holes)) <;> simp [hm]

theorem covered_snoc (P : List Spec.Ship) (s : Spec.Ship) (h : Nat) :
    covered (P ++ [s]) h = (covered P h || decide (h ∈ s.holes)) := by
  simp [covered, List.any_append]

theorem firstCell_snoc (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) (h : Nat) :
    firstCell (P ++ [s]) h = if h = s.first then (if s.down then 2 else 1) else firstCell P h := by
  unfold firstCell
  rw [shipAt_snoc P s hdis]
  by_cases hm : h ∈ s.holes
  · rw [if_pos hm]
    have hn : Spec.shipAt P h = none := by
      have := shipAt_snoc P s hdis h
      unfold Spec.shipAt at this ⊢
      rw [List.find?_eq_none]
      intro x hx hp
      exact hdis x hx h hm (of_decide_eq_true hp)
    rw [hn]
  · rw [if_neg hm]
    have : h ≠ s.first := fun e => hm (e ▸ first_mem_holes s)
    simp [this]

theorem shipAt_none_of_mem (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) {h : Nat} (hm : h ∈ s.holes) :
    Spec.shipAt P h = none := by
  unfold Spec.shipAt
  rw [List.find?_eq_none]
  intro x hx hp
  exact hdis x hx h hm (of_decide_eq_true hp)

theorem lastCell_snoc (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) (h : Nat) :
    lastCell (P ++ [s]) h = if h = s.last then (if s.bowLast then 2 else 1) else lastCell P h := by
  unfold lastCell
  rw [shipAt_snoc P s hdis]
  by_cases hm : h ∈ s.holes
  · rw [if_pos hm, shipAt_none_of_mem P s hdis hm]
  · rw [if_neg hm]
    have : h ≠ s.last := fun e => hm (e ▸ last_mem_holes s)
    simp [this]

theorem extraCell_snoc (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) (h : Nat) :
    extraCell (P ++ [s]) h = if h = s.last then extraOf s.kind else extraCell P h := by
  unfold extraCell
  rw [shipAt_snoc P s hdis]
  by_cases hm : h ∈ s.holes
  · rw [if_pos hm, shipAt_none_of_mem P s hdis hm]
  · rw [if_neg hm]
    have : h ≠ s.last := fun e => hm (e ▸ last_mem_holes s)
    simp [this]

theorem extraCell_last_old (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) : extraCell P s.last = -1 := by
  unfold extraCell
  rw [shipAt_none_of_mem P s hdis (last_mem_holes s)]

/-- The emitted cell loop's choice at one hole, from the three tables. -/
def cellsOf (fc lc ec : Int) : List Int :=
  if fc ≥ 0 then [fc] else if lc ≥ 0 then [lc] ++ (if ec ≥ 0 then [ec] else []) else [0]

theorem cellsOf_1 {fc lc ec : Int} (h1 : fc ≥ 0) : cellsOf fc lc ec = [fc] := by
  simp [cellsOf, h1]

theorem cellsOf_2 {fc lc ec : Int} (h1 : ¬ fc ≥ 0) (h2 : lc ≥ 0) (h3 : ec ≥ 0) :
    cellsOf fc lc ec = [lc, ec] := by
  simp [cellsOf, h1, h2, h3]

theorem cellsOf_3 {fc lc ec : Int} (h1 : ¬ fc ≥ 0) (h2 : lc ≥ 0) (h3 : ¬ ec ≥ 0) :
    cellsOf fc lc ec = [lc] := by
  simp [cellsOf, h1, h2, h3]

theorem cellsOf_4 {fc lc ec : Int} (h1 : ¬ fc ≥ 0) (h2 : ¬ lc ≥ 0) :
    cellsOf fc lc ec = [0] := by
  simp [cellsOf, h1, h2]

theorem cellsOf_eq (P : List Spec.Ship) (h : Nat) :
    cellsOf (firstCell P h) (lastCell P h) (extraCell P h) = (Spec.holeCells P h).map Int.ofNat := by
  unfold cellsOf firstCell lastCell extraCell Spec.holeCells
  cases Spec.shipAt P h with
  | none => simp
  | some s =>
    simp only
    by_cases e1 : h = s.first
    · have e2 : h ≠ s.last := fun e => first_ne_last s (e1 ▸ e)
      cases hd : s.down <;> simp [e1, e2, hd]
    · by_cases e2 : h = s.last
      · subst e2
        cases hb : s.bowLast <;> cases hk : s.kind <;> simp [e1, hb, hk, extraOf]
      · simp [e1, e2]

/-- Distinct naturals below `N` number at most `N`. -/
theorem len_le_of_nodup_lt : ∀ (N : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < N) →
    l.length ≤ N
  | 0, l, _, h => by
    cases l with
    | nil => exact Nat.le_refl _
    | cons x _ => exact absurd (h x (List.mem_cons_self _ _)) (Nat.not_lt_zero _)
  | N + 1, l, hnd, h => by
    have h1 := len_le_of_nodup_lt N (l.filter (fun x => x != N))
      (hnd.sublist (List.filter_sublist _)) (by
        intro x hx
        rw [List.mem_filter] at hx
        have := h x hx.1
        have : x ≠ N := by simpa using hx.2
        omega)
    have h2 : (l.filter (fun x => decide ¬ ((x != N) = true))).length ≤ 1 := by
      generalize hL : l.filter (fun x => decide ¬ ((x != N) = true)) = L
      have hndL : L.Nodup := hL ▸ hnd.sublist (List.filter_sublist _)
      have hall : ∀ x ∈ L, x = N := by
        intro x hx
        rw [← hL, List.mem_filter] at hx
        simpa using hx.2
      match L, hndL, hall with
      | [], _, _ => exact Nat.zero_le _
      | [_], _, _ => exact Nat.le_refl _
      | a :: b :: _, hnd', hall' =>
        exfalso
        have ha := hall' a (List.mem_cons_self _ _)
        have hb := hall' b (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
        exact (List.nodup_cons.mp hnd').1 (by rw [ha, ← hb]; exact List.mem_cons_self _ _)
    have := List.length_eq_countP_add_countP (fun x => x != N) l
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at this
    omega

/-- A page's ships, never sharing a hole, number at most 100 (their first holes are
    distinct holes of the grid). -/
theorem ships_length_le (g : Spec.Grid) (hon : ∀ s ∈ g.ships, s.OnGrid)
    (hdis : g.ships.Pairwise (fun a b => ∀ h ∈ a.holes, h ∉ b.holes)) :
    g.ships.length ≤ 100 := by
  have hnd : (g.ships.map Spec.Ship.first).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hdis.imp (fun {a b} hab (e : a.first = b.first) =>
      hab a.first (first_mem_holes a) (e ▸ first_mem_holes b))
  have := len_le_of_nodup_lt 100 _ hnd (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact holes_lt s (hon s hs) (first_mem_holes s))
  simpa using this

/-- The four tables after placing the ships `P`. -/
def tables (P : List Spec.Ship) : Array Bool × Array Int × Array Int × Array Int :=
  (tab (covered P), tab (firstCell P), tab (lastCell P), tab (extraCell P))

theorem putL_tab {α} (f : Nat → α) {i : Nat} (hi : i < 100) (v : α) :
    SudoRt.putL (tab f) (Int.ofNat i) v = .ok (tab (fun h => if h = i then v else f h)) := by
  rw [putL_ofNat _ _ _ (by rw [tab_size]; exact hi), tab_set]

theorem atL_tab {α} (f : Nat → α) {i : Nat} (hi : i < 100) :
    SudoRt.atL (tab f) (Int.ofNat i) = .ok (f i) := by
  rw [atL_ofNat _ _ (by rw [tab_size]; exact hi), tab_get]

/-- Placing one more ship `s`, disjoint from `P`, in table form. -/
theorem tables_snoc (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) :
    tables (P ++ [s]) =
      (tab (fun h => covered P h || decide (h ∈ s.holes)),
       tab (fun h => if h = s.first then (if s.down then 2 else 1) else firstCell P h),
       tab (fun h => if h = s.last then (if s.bowLast then 2 else 1) else lastCell P h),
       tab (fun h => if h = s.last then extraOf s.kind else extraCell P h)) := by
  unfold tables
  rw [show covered (P ++ [s]) = _ from funext (covered_snoc P s),
    show firstCell (P ++ [s]) = _ from funext (firstCell_snoc P s hdis),
    show lastCell (P ++ [s]) = _ from funext (lastCell_snoc P s hdis),
    show extraCell (P ++ [s]) = _ from funext (extraCell_snoc P s hdis)]

theorem tab_extraCell_keep (P : List Spec.Ship) (s : Spec.Ship)
    (hdis : ∀ s' ∈ P, ∀ h ∈ s.holes, h ∉ s'.holes) :
    tab (fun h => if h = s.last then (-1 : Int) else extraCell P h) = tab (extraCell P) := by
  congr 1; funext h
  by_cases e : h = s.last
  · rw [if_pos e, e, extraCell_last_old P s hdis]
  · rw [if_neg e]

set_option maxHeartbeats 4000000 in
/-- §4.3, the ship pass. On a page whose ships all lie on the grid and never share a hole,
    the emitted `ship_pass` succeeds and returns the model's ship pass. -/
theorem ship_pass_spec (g : Spec.Grid) (hon : ∀ s ∈ g.ships, s.OnGrid)
    (hdis : g.ships.Pairwise (fun a b => ∀ h ∈ a.holes, h ∉ b.holes)) :
    Bs.ship_pass (embGrid g) = .ok (embed (Spec.shipPass g)) := by
  unfold Bs.ship_pass
  simp only [Bs.grid_rows, Bs.grid_cols]
  rw [show SudoRt.mulI 10 10 = .ok 100 from rfl, ok_bind,
    show SudoRt.filledL (100 : Int) false = .ok (tab (covered [])) by
      rw [show (100 : Int) = Int.ofNat 100 from rfl, filledL_ofNat, tab_const]; rfl,
    ok_bind, show SudoRt.negI 1 = .ok (-1) from rfl, ok_bind,
    show SudoRt.filledL (100 : Int) (-1 : Int) = .ok (tab (firstCell [])) by
      rw [show (100 : Int) = Int.ofNat 100 from rfl, filledL_ofNat, tab_const]; rfl,
    ok_bind]
  rw [ok_bind, show SudoRt.filledL (100 : Int) (-1 : Int) = .ok (tab (lastCell [])) by
      rw [show (100 : Int) = Int.ofNat 100 from rfl, filledL_ofNat, tab_const]; rfl,
    ok_bind, ok_bind,
    show SudoRt.filledL (100 : Int) (-1 : Int) = .ok (tab (extraCell [])) by
      rw [show (100 : Int) = Int.ofNat 100 from rfl, filledL_ofNat, tab_const]; rfl,
    ok_bind]
  have hlen : SudoRt.listLen (embGrid g).sudo_7KeyGrid_5ships = Int.ofNat g.ships.length := by
    simp [embGrid, listLen_eq]
  have hfn : FitsLen g.ships.length := fits_small (by have := ships_length_le g hon hdis; omega)
  rw [hlen, subI_len_one _ hfn, ok_bind, except_bind_pure, fuelRange_eq]
  refine asc_goal_upto (fun i (st : Array Bool × Array Int × Array Int × Array Int) =>
      st = tables (g.ships.take i)) rfl ?_ ?_ ?_
  · intro hn
    dsimp only
    rw [if_pos (by rw [hn]; decide)]
    rfl
  · intro i st hi hI
    subst hI
    have hsi : g.ships[i] ∈ g.ships := List.getElem_mem hi
    have htake : g.ships.take (i + 1) = g.ships.take i ++ [g.ships[i]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hi]; rfl
    have hd' : ∀ s' ∈ g.ships.take i, ∀ h ∈ g.ships[i].holes, h ∉ s'.holes := by
      intro s' hs' h hh hh'
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hs'
      have hji : j < i := by omega
      exact List.pairwise_iff_getElem.mp hdis j i (by omega) hi hji h hh' hh
    generalize hsdef : g.ships[i] = s at hsi htake hd'
    have hon' := hon s hsi
    refine ⟨tables (g.ships.take i ++ [s]), by dsimp only; rw [htake], ?_⟩
    dsimp only
    have hat : SudoRt.atL (embGrid g).sudo_7KeyGrid_5ships (Int.ofNat i) = .ok (embShip s) := by
      rw [atL_ofNat _ _ (by simp [embGrid]; exact hi)]
      simp [embGrid, hsdef]
    have h2 := s.kind.two_le_len
    have h5 := s.kind.len_le_five
    rw [if_neg (not_gt_len hi), hat, ok_bind, ship_holes_spec s hon', ok_bind, listLen_embed,
      length_holes, subI_ofNat_one _ (by omega) (fits_small (by omega)), ok_bind,
      except_bind_pure, fuelRange_eq, tables_snoc _ s hd']
    generalize hP : g.ships.take i = P at hd'
    have hf100 : s.first < 100 := holes_lt s hon' (first_mem_holes s)
    have hl100 : s.last < 100 := holes_lt s hon' (last_mem_holes s)
    have hfit : FitsLen (i + 1) := fits_small (by have := ships_length_le g hon hdis; omega)
    refine asc_goal_bind (fromN := 0) (toN := s.kind.len - 1)
      (fun t (cov : Array Bool) => cov = tab (fun h => covered P h || decide (h ∈ s.holes.take t)))
      (Nat.zero_le _) (by dsimp only [tables]; congr 1; funext h; simp) ?_ ?_
    · intro t cov _ ht hI
      subst hI
      have htl : t < s.holes.length := by rw [length_holes]; omega
      have hh100 : s.holes[t] < 100 := holes_lt s hon' (List.getElem_mem htl)
      refine ⟨_, rfl, ?_⟩
      dsimp only
      rw [if_neg (show ¬ (Int.ofNat t > Int.ofNat (s.kind.len - 1)) by
          rw [ofNat_eq_natCast, ofNat_eq_natCast]; omega),
        atL_embed _ _ htl, ok_bind, atL_tab _ hh100, ok_bind]
      have hnc : (covered P s.holes[t] || decide (s.holes[t] ∈ s.holes.take t)) = false := by
        have h1 : covered P s.holes[t] = false := by
          unfold covered
          rw [List.any_eq_false]
          intro x hx hp
          exact hd' x hx _ (List.getElem_mem htl) (of_decide_eq_true hp)
        rw [h1, decide_eq_false (holes_get_not_mem_take s t htl)]; rfl
      rw [hnc, sudoAssert_not_false, ok_bind,
        ok_bind, putL_tab _ hh100, ok_bind]
      dsimp only [pure_eq_ok]
      have hcov : tab (fun h => if h = s.holes[t] then true
            else (covered P h || decide (h ∈ s.holes.take t))) =
          tab (fun h => covered P h || decide (h ∈ s.holes.take (t + 1))) := by
        congr 1; funext h
        rw [List.take_succ, List.getElem?_eq_getElem htl]
        by_cases e : h = s.holes[t]
        · rw [if_pos e]; simp [e]
        · rw [if_neg e]; simp [e]
      rw [hcov]
      exact asc_tail (s.kind.len - 1) t (fits_small (by omega)) _
    · intro cov hI
      subst hI
      have htk : s.holes.take (s.kind.len - 1 + 1) = s.holes := by
        rw [Nat.sub_add_cancel (by omega), ← length_holes, List.take_length]
      rw [htk]
      dsimp only
      have hfa : SudoRt.atL (embed s.holes) 0 = .ok (Int.ofNat s.first) := by
        have := atL_embed s.holes 0 (by rw [length_holes]; omega)
        show SudoRt.atL (embed s.holes) (Int.ofNat 0) = _
        rw [this]; simp [Spec.Ship.holes]
      have hla : SudoRt.atL (embed s.holes) (Int.ofNat (s.kind.len - 1)) =
          .ok (Int.ofNat s.last) := by
        rw [atL_embed s.holes _ (by rw [length_holes]; omega)]
        simp [Spec.Ship.holes, Spec.Ship.last]
      rw [hfa, ok_bind, ok_bind, hla, ok_bind]
      have hE := tab_extraCell_keep P s hd'
      simp only [embShip]
      cases hd : s.down <;> cases hb : s.bowLast <;> cases hk : s.kind <;>
        simp only [tables, embKind, putL_tab _ hf100, putL_tab _ hl100, ok_bind, pure_eq_ok,
          Bool.false_eq_true, if_true, if_false, extraOf, hk] <;>
        (try rw [hE]) <;>
        exact asc_tail_len _ i hi hfit _
  · intro j st hst
    subst hst
    rw [List.take_length]
    dsimp only [tables]
    rw [show SudoRt.subI 100 1 = .ok 99 from rfl, ok_bind, except_bind_pure, fuelRange_eq]
    refine asc_goal (fromN := 0) (toN := 99) (fun h (cs : Array Int) =>
        cs = ((List.range h).flatMap (fun h =>
          cellsOf (firstCell g.ships h) (lastCell g.ships h) (extraCell g.ships h))).toArray)
      (by decide) rfl ?_ ?_
    · intro h cs _ hh hI
      subst hI
      refine ⟨_, rfl, ?_⟩
      have h100 : h < 100 := by omega
      dsimp only
      rw [if_neg (show ¬ (Int.ofNat h > 99) from ofNat_not_gt hh)]
      have e1 := atL_ofNat (tab (firstCell g.ships)) h (by rw [tab_size]; exact h100)
      have e2 := atL_ofNat (tab (lastCell g.ships)) h (by rw [tab_size]; exact h100)
      have e3 := atL_ofNat (tab (extraCell g.ships)) h (by rw [tab_size]; exact h100)
      rw [tab_get] at e1 e2 e3
      have hfi : FitsLen (h + 1) := fits_small (by omega)
      simp only [e1, e2, e3, ok_bind, pure_eq_ok, appendL_spec]
      rw [List.range_succ, List.flatMap_append,
        show ∀ F : Nat → List Int, [h].flatMap F = F h from fun F => by simp]
      by_cases c1 : firstCell g.ships h ≥ 0
      · simp only [c1, decide_True, if_true, ok_bind]
        rw [cellsOf_1 c1, List.push_toArray]
        exact asc_tail 99 h hfi _
      · by_cases c2 : lastCell g.ships h ≥ 0
        · by_cases c3 : extraCell g.ships h ≥ 0
          · simp only [c1, c2, c3, decide_True, decide_False, if_true, Bool.false_eq_true,
              if_false, ok_bind]
            rw [cellsOf_2 c1 c2 c3, List.push_toArray, List.push_toArray, List.append_assoc]
            exact asc_tail 99 h hfi _
          · simp only [c1, c2, c3, decide_True, decide_False, if_true, Bool.false_eq_true,
              if_false, ok_bind]
            rw [cellsOf_3 c1 c2 c3, List.push_toArray]
            exact asc_tail 99 h hfi _
        · simp only [c1, c2, decide_False, Bool.false_eq_true, if_false, ok_bind]
          rw [cellsOf_4 c1 c2, List.push_toArray]
          exact asc_tail 99 h hfi _
    · intro cs hI
      subst hI
      congr 1
      unfold Spec.shipPass embed
      show List.toArray _ = Array.mk _
      congr 1
      rw [List.map_flatMap]
      congr 1
      funext h
      exact cellsOf_eq g.ships h

/-- §4.3, the peg pass. On a page with 100 pegs, each a trit, the emitted `peg_pass`
    succeeds and returns the pegs in reading order. -/
theorem peg_pass_spec (g : Spec.Grid) (hlen : g.pegs.length = 100)
    (ht : ∀ t ∈ g.pegs, t ≤ 2) :
    Bs.peg_pass (embGrid g) = .ok (embed (Spec.pegPass g)) := by
  unfold Bs.peg_pass
  simp only [Bs.grid_rows, Bs.grid_cols]
  rw [show SudoRt.mulI 10 10 = .ok 100 from rfl, ok_bind]
  dsimp only [embGrid]
  rw [sudoAssertEq_int (by rw [listLen_embed, hlen]; rfl), ok_bind,
    is_trits_spec (embed g.pegs) 100 (by rw [size_embed, hlen]) (by decide)
      (fits_small (by decide)), ok_bind]
  have hall : (∀ v ∈ (embed g.pegs).toList, 0 ≤ v ∧ v ≤ 2) := by
    intro v hv
    simp only [embed, List.mem_map] at hv
    obtain ⟨t, htm, rfl⟩ := hv
    have := ht t htm
    rw [ofNat_eq_natCast]
    constructor <;> omega
  rw [decide_eq_true hall, sudoAssert_true, ok_bind]
  rfl


/-- A page's ship pass has at most two cells per hole. -/
theorem length_holeCells_le (ships : List Spec.Ship) (h : Nat) :
    (Spec.holeCells ships h).length ≤ 2 := by
  unfold Spec.holeCells
  split
  · simp
  · split
    · simp
    · split
      · split <;> split <;> simp
      · simp

theorem length_shipPass_le (g : Spec.Grid) : (Spec.shipPass g).length ≤ 200 := by
  have := length_flatMap_le (List.range 100) (Spec.holeCells g.ships) 2
    (fun h _ => length_holeCells_le g.ships h)
  simpa [Spec.shipPass] using this

/-- The key reader's output is at most 1 + 300 cells per page. -/
theorem length_readKey_le (pages : List Spec.Grid) (hwf : ∀ g ∈ pages, g.Wf) :
    (Spec.readKey pages).length ≤ 300 * pages.length + 1 := by
  unfold Spec.readKey
  rw [List.length_cons]
  have := length_flatMap_le pages (fun g => Spec.shipPass g ++ Spec.pegPass g) 300 (by
    intro g hg
    rw [List.length_append]
    have := length_shipPass_le g
    have := (hwf g hg).pegs_len
    simp only [Spec.pegPass]
    omega)
  omega

theorem holeCells_trits (ships : List Spec.Ship) (h : Nat) :
    ∀ c ∈ Spec.holeCells ships h, c ≤ 2 := by
  unfold Spec.holeCells
  split
  · simp
  · split
    · intro c hc; simp at hc; split at hc <;> omega
    · split
      · intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · split at hc <;> omega
        · split at hc <;> simp at hc <;> omega
      · simp

/-- The key reader's cells are trits. -/
theorem readKey_trits (pages : List Spec.Grid) (hwf : ∀ g ∈ pages, g.Wf) :
    ∀ c ∈ Spec.readKey pages, c ≤ 2 := by
  intro c hc
  unfold Spec.readKey at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  rw [List.mem_flatMap] at hc
  obtain ⟨g, hg, hc⟩ := hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · unfold Spec.shipPass at hc
    rw [List.mem_flatMap] at hc
    obtain ⟨h, _, hc⟩ := hc
    exact holeCells_trits _ h c hc
  · exact (hwf g hg).pegs_trits c hc

theorem expOf_foldl_ge (cs : List Nat) (e : Nat) :
    e * 3 ^ cs.length ≤ cs.foldl (fun e c => 3 * e + c) e := by
  induction cs generalizing e with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have := ih (3 * e + c)
    have : e * (3 ^ cs.length * 3) ≤ (3 * e + c) * 3 ^ cs.length := by
      rw [Nat.mul_comm (3 ^ cs.length) 3, ← Nat.mul_assoc, Nat.mul_comm e 3, Nat.add_mul]
      exact Nat.le_add_right _ _
    omega

/-- §4.3: the start marker (a white cell) leads, so the key exponent is at least
    `3^(cells − 1)`. -/
theorem expOf_readKey_ge (pages : List Spec.Grid) :
    3 ^ ((Spec.readKey pages).length - 1) ≤ Spec.expOf (Spec.readKey pages) := by
  unfold Spec.expOf Spec.readKey
  rw [List.foldl_cons, List.length_cons, Nat.add_sub_cancel]
  have := expOf_foldl_ge (pages.flatMap (fun g => Spec.shipPass g ++ Spec.pegPass g))
    (3 * 0 + 1)
  rw [show 3 * 0 + 1 = 1 from rfl, Nat.one_mul] at this
  exact this

/-- §4.3: the start marker makes the key exponent non-zero. -/
theorem expOf_readKey_pos (pages : List Spec.Grid) : 0 < Spec.expOf (Spec.readKey pages) :=
  Nat.lt_of_lt_of_le (Nat.pos_pow_of_pos _ (by decide)) (expOf_readKey_ge pages)

theorem readKey_head (pages : List Spec.Grid) : (Spec.readKey pages).head? = some 1 := rfl

set_option maxHeartbeats 1000000 in
/-- §4.3 READ. For a key of one or more well-formed pages (every ship on the grid, no two
    ships sharing a hole, 100 trit pegs a page), the emitted `read_key` succeeds and returns
    the model's cells: the start marker, then each page's ship pass and peg pass. The bound
    on the page count only keeps the loop counter in the emitted 64-bit range. -/
theorem read_key_spec (pages : List Spec.Grid) (hk : Spec.KeyWf pages)
    (hfit : FitsLen pages.length) :
    Bs.read_key (embKey pages) = .ok (embed (Spec.readKey pages)) := by
  obtain ⟨hne, hwf⟩ := hk
  have hpos : 0 < pages.length := List.length_pos.mpr hne
  unfold Bs.read_key
  have hlen : SudoRt.listLen (embKey pages) = Int.ofNat pages.length := by
    simp [embKey, listLen_eq]
  rw [hlen, decide_eq_true (show Int.ofNat pages.length ≥ (1 : Int) by
      rw [ofNat_eq_natCast]; omega), sudoAssert_true, ok_bind,
    subI_ofNat_one _ hpos hfit, ok_bind, except_bind_pure, fuelRange_eq]
  refine asc_goal (fromN := 0) (toN := pages.length - 1)
    (fun i (cs : Array Int) => cs = embed (1 :: (pages.take i).flatMap
      (fun g => Spec.shipPass g ++ Spec.pegPass g)))
    (Nat.zero_le _) rfl ?_ ?_
  · intro i cs _ hi hI
    subst hI
    have hil : i < pages.length := by omega
    refine ⟨_, rfl, ?_⟩
    dsimp only
    have hat : SudoRt.atL (embKey pages) (Int.ofNat i) = .ok (embGrid pages[i]) := by
      rw [atL_ofNat _ _ (by simp [embKey]; exact hil)]
      simp [embKey]
    have hw := hwf pages[i] (List.getElem_mem hil)
    rw [if_neg (show ¬ (Int.ofNat i > Int.ofNat (pages.length - 1)) by
        rw [ofNat_eq_natCast, ofNat_eq_natCast]; omega),
      hat, ok_bind, ship_pass_spec _ hw.onGrid hw.disjoint, ok_bind, ok_bind,
      peg_pass_spec _ hw.pegs_len hw.pegs_trits, ok_bind]
    dsimp only [pure_eq_ok]
    have hcat : SudoRt.concatL (SudoRt.concatL
        (embed (1 :: (pages.take i).flatMap (fun g => Spec.shipPass g ++ Spec.pegPass g)))
        (embed (Spec.shipPass pages[i]))) (embed (Spec.pegPass pages[i])) =
        embed (1 :: (pages.take (i + 1)).flatMap
          (fun g => Spec.shipPass g ++ Spec.pegPass g)) := by
      unfold SudoRt.concatL
      rw [← embed_append, ← embed_append, List.take_succ, List.getElem?_eq_getElem hil]
      simp [List.flatMap_append, List.append_assoc]
    rw [hcat]
    exact asc_tail (pages.length - 1) i (FitsLen.of_le hfit (by omega)) _
  · intro cs hI
    subst hI
    rw [Nat.sub_add_cancel hpos, List.take_length]
    rfl

end BsLink2.Link2
