/-
  T1: weight-sum SumRanks versus relabellings. Exact iff (constant weight
  shift), the v8 rank-preserving case, and the 52-element v9 group `v9Sym`.

  DEPRECATED MODELS. `sumRanks rowW colW` is the v8/v9 SumRanks shape (every
  row / column rotated by a plain weight sum). The cipher is v10
  (`DoubleDeal.sumRanksV10`, chained position-aware rows and GF(4) suit
  columns); its relabelling theorem is in `SumRanksV10.lean`. These v8/v9
  statements are kept as the models of the deprecated ciphers (v9 is
  deprecated by its K♣↔Q♥ distinguisher, `proofs/deprecated/doubledeal-v9/`)
  and as the generic rotation lemmas `SumRanksV10.lean` reuses.
-/
import DoubleDealSecurity.Relabel
import DoubleDealSecurity.PermWitness

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## 2. SumRanks commutes with σ iff σ shifts both weights by a constant

The cipher rotates row `r` left by (Σ row weights) mod 13 and column `c`
down by (Σ column weights) mod 4. A 13-card row has 13 cells, so a constant
shift `k` of every row weight changes the row sum by `13k ≡ 0 (mod 13)`;
likewise a constant column-weight shift changes a 4-card column sum by
`4k ≡ 0 (mod 4)`. So the exact condition is a constant *shift*, not
preservation. -/

/-- `w ∘ σ ≡ w + k (mod M)` on every card, for one constant `k`. -/
def WeightShift (σ : Relabel) (w : Nat → Nat) (M : Nat) : Prop :=
  ∃ k, ∀ c : Fin 52, w (σ c).val % M = (w c.val + k) % M

theorem weightSum_map_app_mod (σ : Relabel) (w : Nat → Nat) (M k : Nat)
    (hk : ∀ c : Fin 52, w (σ c).val % M = (w c.val + k) % M) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 52) →
      weightSum w (xs.map σ.app) % M = (weightSum w xs + xs.length * k) % M
  | [], _ => by simp [weightSum, sumNats]
  | x :: xs, hx => by
    have hx0 : x < 52 := hx x (List.mem_cons_self _ _)
    have ih := weightSum_map_app_mod σ w M k hk xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have h1 : w (σ.app x) % M = (w x + k) % M := by
      have := hk ⟨x, hx0⟩
      rwa [← σ.app_fin ⟨x, hx0⟩] at this
    simp only [weightSum, List.map, sumNats] at ih ⊢
    rw [Nat.add_mod, h1, ih, ← Nat.add_mod]
    congr 1
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem ofList13_map (f : α → β) (xs : List α) (h : xs.length = 13)
    (h' : (xs.map f).length = 13) (i : Fin 13) :
    ofList13 (xs.map f) h' i = f (ofList13 xs h i) := by
  simp [ofList13]

theorem ofList4_map (f : α → β) (xs : List α) (h : xs.length = 4)
    (h' : (xs.map f).length = 4) (i : Fin 4) :
    ofList4 (xs.map f) h' i = f (ofList4 xs h i) := by
  simp [ofList4]

theorem rowRotate_rel (σ : Relabel) (g : Grid Nat) (t t' : Fin 4 → Nat)
    (h : ∀ r, t' r % 13 = t r % 13) :
    rowRotate (relG σ g) t' = relG σ (rowRotate g t) := by
  funext r c
  have hl : toList13 (relG σ g r) = (toList13 (g r)).map σ.app := rfl
  have hrot : rotL (toList13 (relG σ g r)) (t' r) = (rotL (toList13 (g r)) (t r)).map σ.app := by
    rw [hl, map_rotL]
    apply rotL_congr_mod
    simp only [List.length_map, length_toList13]
    exact h r
  simp only [rowRotate, relG]
  rw [congrFun (ofList13_eq _ (by simp [length_rotL, length_toList13]) hrot) c]
  exact ofList13_map σ.app _ (by rw [length_rotL, length_toList13]) _ c

theorem colRotate_rel (σ : Relabel) (g : Grid Nat) (s s' : Fin 13 → Nat)
    (h : ∀ c, s' c % 4 = s c % 4) :
    colRotate (relG σ g) s' = relG σ (colRotate g s) := by
  funext r c
  have hl : toList4 (fun r' => relG σ g r' c) = (toList4 (fun r' => g r' c)).map σ.app := rfl
  have hrot : rotR (toList4 (fun r' => relG σ g r' c)) (s' c) =
      (rotR (toList4 (fun r' => g r' c)) (s c)).map σ.app := by
    rw [hl, map_rotR]
    apply rotR_congr_mod
    simp only [List.length_map, length_toList4]
    exact h c
  show colRotate (relG σ g) s' r c = σ.app (colRotate g s r c)
  unfold colRotate
  rw [congrFun (ofList4_eq _ (by simp [length_rotR, length_toList4]) hrot) r]
  exact ofList4_map σ.app _ (by rw [length_rotR, length_toList4]) _ r

theorem applyRowRotates_rel (σ : Relabel) (w : Nat → Nat) (hs : WeightShift σ w 13)
    (g : Grid Nat) (hg : CardsG g) :
    applyRowRotates w (relG σ g) = relG σ (applyRowRotates w g) := by
  obtain ⟨k, hk⟩ := hs
  apply rowRotate_rel
  intro r
  have hl : toList13 (relG σ g r) = (toList13 (g r)).map σ.app := rfl
  simp only [rowWeightSum]
  rw [hl, weightSum_map_app_mod σ w 13 k hk _ (fun x hx => by
    obtain ⟨c, rfl⟩ := mem_toList13 hx; exact hg r c)]
  rw [length_toList13, Nat.add_mul_mod_self_left]

theorem applyColRotates_rel (σ : Relabel) (w : Nat → Nat) (hs : WeightShift σ w 4)
    (g : Grid Nat) (hg : CardsG g) :
    applyColRotates w (relG σ g) = relG σ (applyColRotates w g) := by
  obtain ⟨k, hk⟩ := hs
  apply colRotate_rel
  intro c
  have hl : toList4 (fun r => relG σ g r c) = (toList4 (fun r => g r c)).map σ.app := rfl
  simp only [colWeightSum]
  rw [hl, weightSum_map_app_mod σ w 4 k hk _ (fun x hx => by
    obtain ⟨r, rfl⟩ := mem_toList4 hx; exact hg r c)]
  rw [length_toList4, Nat.add_mul_mod_self_left]

/-- **SumRanks, "if"** (PROVED): constant weight shifts ⇒ SumRanks commutes with σ
    on every card-valued grid. Any weights; the cipher uses rank / rank + suit. -/
theorem sumRanks_commutes_of_shift (σ : Relabel) (rowW colW : Nat → Nat)
    (hr : WeightShift σ rowW 13) (hc : WeightShift σ colW 4) :
    CommutesG σ (sumRanks rowW colW) := by
  intro g hg
  unfold sumRanks
  rw [applyRowRotates_rel σ rowW hr g hg,
    applyColRotates_rel σ colW hc _ (applyRowRotates_bound (· < 52) rowW g hg)]

/-! ### SumRanks "only if": pair-swap witnesses

Explicit formulas for the rotations, then: commuting on one deck forces equal
rotation amounts (`commute_rotations`); two decks that differ by exchanging
`a` and `b` give `w(σa) − w a ≡ w(σb) − w b` (`row_pair`, `col_pair`); that
is exactly a constant weight shift. -/

theorem rowRotate_apply {α : Type} (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) (c : Fin 13) :
    rowRotate g t r c = g r ⟨(c.val + t r % 13) % 13, Nat.mod_lt _ (by decide)⟩ := by
  unfold rowRotate ofList13
  have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
  have hget := rotL_get_eq (toList13 (g r)) (t r) c.val hne (by rw [length_toList13]; exact c.isLt)
  rw [hget]
  simp only [length_toList13]
  have hj : (c.val + t r % 13) % 13 < 13 := Nat.mod_lt _ (by decide)
  exact getElem_toList13 (g r) ⟨(c.val + t r % 13) % 13, hj⟩

theorem rowRotateInv_apply {α : Type} (g : Grid α) (t : Fin 4 → Nat) (r : Fin 4) (c : Fin 13) :
    rowRotateInv g t r c = g r ⟨(c.val + (13 - t r % 13)) % 13, Nat.mod_lt _ (by decide)⟩ := by
  unfold rowRotateInv ofList13
  have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
  have hget := getElem_rotR (toList13 (g r)) (t r) c.val hne (by rw [length_toList13]; exact c.isLt)
  rw [hget]
  simp only [length_toList13]
  have hj : (c.val + (13 - t r % 13)) % 13 < 13 := Nat.mod_lt _ (by decide)
  exact getElem_toList13 (g r) ⟨(c.val + (13 - t r % 13)) % 13, hj⟩

theorem colRotate_apply {α : Type} (g : Grid α) (s : Fin 13 → Nat) (r : Fin 4) (c : Fin 13) :
    colRotate g s r c = g ⟨(r.val + (4 - s c % 4)) % 4, Nat.mod_lt _ (by decide)⟩ c := by
  unfold colRotate ofList4
  have hne : (toList4 (fun r' => g r' c)).length ≠ 0 := by simp [length_toList4]
  have hget := getElem_rotR (toList4 (fun r' => g r' c)) (s c) r.val hne
    (by rw [length_toList4]; exact r.isLt)
  rw [hget]
  have hj : (r.val + (4 - s c % 4)) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcell := getElem_toList4 (fun r' => g r' c) ⟨(r.val + (4 - s c % 4)) % 4, hj⟩
  simpa [length_toList4] using hcell

/-- A grid read column-major is a deck iff its cells are distinct card values. -/
theorem isDeckG_iff (g : Grid Nat) :
    IsDeck (scoopColumnMajor g) ↔
      CardsG g ∧ ∀ r c r' c', g r c = g r' c' → r = r' ∧ c = c' := by
  constructor
  · rintro ⟨hc, hi⟩
    refine ⟨fun r c => ?_, fun r c r' c' h => ?_⟩
    · have := hc (cmFlat r c)
      simpa [scoopColumnMajor, (cm_cmFlat r c).1, (cm_cmFlat r c).2] using this
    · have h' : scoopColumnMajor g (cmFlat r c) = scoopColumnMajor g (cmFlat r' c') := by
        simpa [scoopColumnMajor, (cm_cmFlat r c).1, (cm_cmFlat r c).2,
          (cm_cmFlat r' c').1, (cm_cmFlat r' c').2] using h
      have hf := hi h'
      have e1 := cm_cmFlat r c
      have e2 := cm_cmFlat r' c'
      rw [hf] at e1
      exact ⟨e1.1.symm.trans e2.1, e1.2.symm.trans e2.2⟩
  · rintro ⟨hc, hi⟩
    refine ⟨fun i => hc _ _, fun i j h => ?_⟩
    have ⟨hr, hcol⟩ := hi _ _ _ _ h
    rw [← cmFlat_cm i, ← cmFlat_cm j, hr, hcol]

theorem grid_inj {g : Grid Nat} (hg : IsDeck (scoopColumnMajor g)) {r r' : Fin 4} {c c' : Fin 13}
    (h : g r c = g r' c') : r = r' ∧ c = c' := ((isDeckG_iff g).1 hg).2 _ _ _ _ h

theorem rot_match (t t' : Fin 4 → Nat) (s s' : Fin 13 → Nat)
    (h : ∀ (r : Fin 4) (c : Fin 13),
      (⟨(r.val + (4 - s' c % 4)) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
          ⟨(r.val + (4 - s c % 4)) % 4, Nat.mod_lt _ (by decide)⟩ ∧
      (⟨(c.val + t' ⟨(r.val + (4 - s' c % 4)) % 4, Nat.mod_lt _ (by decide)⟩ % 13) % 13,
          Nat.mod_lt _ (by decide)⟩ : Fin 13) =
        ⟨(c.val + t ⟨(r.val + (4 - s c % 4)) % 4, Nat.mod_lt _ (by decide)⟩ % 13) % 13,
          Nat.mod_lt _ (by decide)⟩) :
    (∀ ρ, t' ρ % 13 = t ρ % 13) ∧ (∀ c, s' c % 4 = s c % 4) := by
  constructor
  · intro ρ
    obtain ⟨h1, h2⟩ := h ⟨(ρ.val + s 0 % 4) % 4, Nat.mod_lt _ (by decide)⟩ 0
    rw [h1] at h2
    have hR : (⟨((ρ.val + s 0 % 4) % 4 + (4 - s 0 % 4)) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ρ := by
      apply Fin.ext; simp only; have := ρ.isLt; omega
    rw [hR] at h2
    have := congrArg Fin.val h2
    simp only [Fin.val_zero, Nat.zero_add, Nat.mod_mod] at this
    exact this
  · intro c
    have := congrArg Fin.val (h 0 c).1
    simp only [Fin.val_zero, Nat.zero_add] at this
    omega

/-- Commuting on one deck forces equal row rotations (mod 13) and, after the
    row stage, equal column rotations (mod 4). -/
theorem commute_rotations (σ : Relabel) (rowW colW : Nat → Nat) (g : Grid Nat)
    (hg : IsDeck (scoopColumnMajor g))
    (hc : sumRanks rowW colW (relG σ g) = relG σ (sumRanks rowW colW g)) :
    (∀ ρ, rowWeightSum rowW (relG σ g) ρ % 13 = rowWeightSum rowW g ρ % 13) ∧
    (∀ c, colWeightSum colW (applyRowRotates rowW (relG σ g)) c % 4 =
          colWeightSum colW (applyRowRotates rowW g) c % 4) := by
  have key : ∀ r c, _ := fun r c => congrFun (congrFun hc r) c
  simp only [sumRanks, applyColRotates, colRotate_apply, applyRowRotates, rowRotate_apply,
    relG] at key
  have key2 := fun r c => grid_inj hg (σ.app_inj (key r c))
  exact rot_match (fun r => rowWeightSum rowW g r) (fun r => rowWeightSum rowW (relG σ g) r)
    (fun c => colWeightSum colW (rowRotate g fun r => rowWeightSum rowW g r) c)
    (fun c => colWeightSum colW (rowRotate (relG σ g) fun r => rowWeightSum rowW (relG σ g) r) c)
    key2

/-! ### Witness decks for the pair-swap argument -/

/-- The deck read off a permutation of positions. -/
def permDeck (π : Equiv.Perm (Fin 52)) : Fin 52 → Nat := fun k => (π k).val

theorem isDeck_permDeck (π : Equiv.Perm (Fin 52)) : IsDeck (permDeck π) :=
  ⟨fun k => (π k).isLt, fun _ _ h => π.injective (Fin.ext h)⟩

theorem isDeck_lay_permDeck (π : Equiv.Perm (Fin 52)) :
    IsDeck (scoopColumnMajor (layColumnMajor (permDeck π))) := by
  rw [scoop_lay_columnMajor]; exact isDeck_permDeck π

theorem rowWeightSum_swap0 (w : Nat → Nat) (G1 G2 : Grid Nat)
    (h : ∀ c : Fin 13, c ≠ 0 → G1 0 c = G2 0 c) :
    rowWeightSum w G1 0 + w (G2 0 0) = rowWeightSum w G2 0 + w (G1 0 0) := by
  simp only [rowWeightSum, weightSum, toList13, List.map, sumNats,
    h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide)]
  omega

theorem colWeightSum_swap0 (w : Nat → Nat) (G1 G2 : Grid Nat)
    (h : ∀ r : Fin 4, r ≠ 0 → G1 r 0 = G2 r 0) :
    colWeightSum w G1 0 + w (G2 0 0) = colWeightSum w G2 0 + w (G1 0 0) := by
  simp only [colWeightSum, weightSum, toList4, List.map, sumNats,
    h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  omega

/-- Row pair relation: commuting on all decks forces
    `w(σa) − w a ≡ w(σb) − w b (mod 13)` for the row weight. -/
theorem row_pair (σ : Relabel) (rowW colW : Nat → Nat)
    (h : CommutesOnDecksG σ (sumRanks rowW colW)) (a b : Fin 52) :
    (rowW (σ a).val + rowW b.val) % 13 = (rowW (σ b).val + rowW a.val) % 13 := by
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨π, hπa, hπb⟩ := PermCount.exists_perm_two 0 1 a b (by decide) hab
  let g1 := layColumnMajor (permDeck π)
  let g2 := layColumnMajor (permDeck (π * Equiv.swap 0 1))
  have hd1 : IsDeck (scoopColumnMajor g1) := isDeck_lay_permDeck π
  have hd2 : IsDeck (scoopColumnMajor g2) := isDeck_lay_permDeck _
  have A1 := (commute_rotations σ rowW colW g1 hd1 (h g1 hd1)).1 0
  have A2 := (commute_rotations σ rowW colW g2 hd2 (h g2 hd2)).1 0
  have hrow : ∀ c : Fin 13, c ≠ 0 → g1 0 c = g2 0 c := by
    intro c hc
    simp only [g1, g2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e; apply hc; apply Fin.ext
      have := congrArg Fin.val e; simp [cmFlat] at this; omega
    · intro e; have := congrArg Fin.val e; simp [cmFlat] at this
  have B := rowWeightSum_swap0 rowW g1 g2 hrow
  have B' := rowWeightSum_swap0 rowW (relG σ g1) (relG σ g2)
    (fun c hc => by simp only [relG]; rw [hrow c hc])
  have e1 : g1 0 0 = a.val := by simp [g1, layColumnMajor, permDeck, cmFlat, ← hπa]
  have e2 : g2 0 0 = b.val := by
    simp only [g2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    have : cmFlat 0 0 = 0 := rfl
    rw [this, Equiv.swap_apply_left, hπb]
  simp only [relG, e1, e2, σ.app_fin] at B'
  rw [e1, e2] at B
  omega


theorem isDeckG_rowRotateInv (G : Grid Nat) (t : Fin 4 → Nat) (hG : IsDeck (scoopColumnMajor G)) :
    IsDeck (scoopColumnMajor (rowRotateInv G t)) := by
  obtain ⟨hc, hi⟩ := (isDeckG_iff G).1 hG
  refine (isDeckG_iff _).2 ⟨fun r c => ?_, fun r c r' c' h => ?_⟩
  · rw [rowRotateInv_apply]; exact hc _ _
  · rw [rowRotateInv_apply, rowRotateInv_apply] at h
    obtain ⟨hr, hcol⟩ := hi _ _ _ _ h
    subst hr
    refine ⟨rfl, Fin.ext ?_⟩
    have := congrArg Fin.val hcol
    simp only at this
    have := c.isLt; have := c'.isLt
    omega

/-- Column pair relation: commuting on all decks forces
    `w(σa) − w a ≡ w(σb) − w b (mod 4)` for the column weight. -/
theorem col_pair (σ : Relabel) (rowW colW : Nat → Nat)
    (h : CommutesOnDecksG σ (sumRanks rowW colW)) (a b : Fin 52) :
    (colW (σ a).val + colW b.val) % 4 = (colW (σ b).val + colW a.val) % 4 := by
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨π, hπa, hπb⟩ := PermCount.exists_perm_two 0 4 a b (by decide) hab
  let H1 := layColumnMajor (permDeck π)
  let H2 := layColumnMajor (permDeck (π * Equiv.swap 0 4))
  -- post-row grids H_i, pre-images g_i under the row stage
  have side : ∀ H : Grid Nat, IsDeck (scoopColumnMajor H) →
      colWeightSum colW (relG σ H) 0 % 4 = colWeightSum colW H 0 % 4 := by
    intro H hH
    let g := applyRowRotatesInv rowW H
    have hg : IsDeck (scoopColumnMajor g) := isDeckG_rowRotateInv H _ hH
    have hrows : applyRowRotates rowW g = H := applyRowRotates_applyRowRotatesInv rowW H
    obtain ⟨hr, hcl⟩ := commute_rotations σ rowW colW g hg (h g hg)
    have hH' : applyRowRotates rowW (relG σ g) = relG σ H := by
      rw [← hrows]
      exact rowRotate_rel σ g _ _ hr
    have := hcl 0
    rwa [hH', hrows] at this
  have A1 := side H1 (isDeck_lay_permDeck π)
  have A2 := side H2 (isDeck_lay_permDeck _)
  have hcol : ∀ r : Fin 4, r ≠ 0 → H1 r 0 = H2 r 0 := by
    intro r hr
    simp only [H1, H2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e; apply hr; apply Fin.ext
      have := congrArg Fin.val e; simp [cmFlat] at this; omega
    · intro e; have := congrArg Fin.val e; simp [cmFlat] at this; omega
  have B := colWeightSum_swap0 colW H1 H2 hcol
  have B' := colWeightSum_swap0 colW (relG σ H1) (relG σ H2)
    (fun r hr => by simp only [relG]; rw [hcol r hr])
  have e1 : H1 0 0 = a.val := by simp [H1, layColumnMajor, permDeck, cmFlat, ← hπa]
  have e2 : H2 0 0 = b.val := by
    simp only [H2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    have : cmFlat 0 0 = 0 := rfl
    rw [this, Equiv.swap_apply_left, hπb]
  simp only [relG, e1, e2, σ.app_fin] at B'
  rw [e1, e2] at B
  omega

theorem weightShift_of_pair13 (σ : Relabel) (w : Nat → Nat)
    (hp : ∀ a b : Fin 52, (w (σ a).val + w b.val) % 13 = (w (σ b).val + w a.val) % 13) :
    WeightShift σ w 13 := by
  refine ⟨w (σ 0).val + 12 * w (0 : Fin 52).val, fun c => ?_⟩
  have := hp c 0
  omega

theorem weightShift_of_pair4 (σ : Relabel) (w : Nat → Nat)
    (hp : ∀ a b : Fin 52, (w (σ a).val + w b.val) % 4 = (w (σ b).val + w a.val) % 4) :
    WeightShift σ w 4 := by
  refine ⟨w (σ 0).val + 3 * w (0 : Fin 52).val, fun c => ?_⟩
  have := hp c 0
  omega

/-- **SumRanks, "only if"** (PROVED): if SumRanks commutes with σ on all
    well-formed decks, both weights shift by a constant. Any weights. -/
theorem sumRanks_shift_of_commutes (σ : Relabel) (rowW colW : Nat → Nat)
    (h : CommutesOnDecksG σ (sumRanks rowW colW)) :
    WeightShift σ rowW 13 ∧ WeightShift σ colW 4 :=
  ⟨weightShift_of_pair13 σ rowW (row_pair σ rowW colW h),
   weightShift_of_pair4 σ colW (col_pair σ rowW colW h)⟩

/-- SumRanks characterisation (iff), any weights. -/
theorem sumRanks_commutes_iff (σ : Relabel) (rowW colW : Nat → Nat) :
    CommutesOnDecksG σ (sumRanks rowW colW) ↔
      WeightShift σ rowW 13 ∧ WeightShift σ colW 4 :=
  ⟨sumRanks_shift_of_commutes σ rowW colW,
   fun ⟨hr, hc⟩ => (sumRanks_commutes_of_shift σ rowW colW hr hc).onDecks⟩

/-! ### 2a. v8 weights (rows rank, columns rank): exactly the rank-preserving σ -/

/-- v8 (frozen) SumRanks: column weight is rank, as in the deprecated cipher. -/
def sumRanksV8 : Grid Nat → Grid Nat := sumRanks cardRank cardRank

/-- v9 (deprecated) SumRanks: column weight rank + suit (A2). Not the cipher;
    v10 is `sumRanksV10`. -/
def sumRanksV9 : Grid Nat → Grid Nat := sumRanks cardRank cardColumnWeight

/-- (PROVED) For the v8 weights, the two shift conditions hold iff σ preserves
    every card's rank. (A nonzero rank shift mod 13 wraps K→A somewhere, which
    changes the rank difference by 13 ≡ 1 (mod 4) and breaks the column shift.) -/
theorem v8_shift_iff_rank_preserving (σ : Relabel) :
    (WeightShift σ cardRank 13 ∧ WeightShift σ cardRank 4) ↔
      ∀ c : Fin 52, rank (σ c).val = rank c.val := by
  constructor
  · rintro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
    have a1 := h1 ⟨0, by decide⟩
    have a2 := h2 ⟨0, by decide⟩
    have b1 := h1 ⟨12, by decide⟩
    have b2 := h2 ⟨12, by decide⟩
    have hx := (σ ⟨0, by decide⟩).isLt
    have hy := (σ ⟨12, by decide⟩).isLt
    simp only [cardRank, rank] at a1 a2 b1 b2
    have hk : k1 % 13 = 0 := by omega
    intro c
    have := h1 c
    have hc := (σ c).isLt
    simp only [cardRank, rank] at this ⊢
    omega
  · intro h
    refine ⟨⟨0, fun c => ?_⟩, ⟨0, fun c => ?_⟩⟩ <;> simp [cardRank, h c]

/-- Corollary (PROVED): every rank-preserving σ — in particular every same-rank
    swap such as K♣↔K♦ — commutes with v8 SumRanks. -/
theorem v8_sumRanks_commutes_of_rank_preserving (σ : Relabel)
    (h : ∀ c : Fin 52, rank (σ c).val = rank c.val) : CommutesG σ sumRanksV8 := by
  obtain ⟨hr, hc⟩ := (v8_shift_iff_rank_preserving σ).2 h
  exact sumRanks_commutes_of_shift σ _ _ hr hc

theorem rank_swap_same (a b : Fin 52) (hab : rank a.val = rank b.val) (c : Fin 52) :
    rank ((swap a b) c).val = rank c.val := by
  rw [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hab.symm
  · subst hb; exact hab
  · rfl

/-! ### 2b. v9 weights (rows rank, columns rank + suit): a 52-element group

SURPRISE vs the expected shape: v9 SumRanks does NOT force σ = id. The σ with
`rank ∘ σ ≡ rank + a (mod 13)` and `(rank+suit) ∘ σ ≡ (rank+suit) + b (mod 4)`
form a group of exactly 52 relabellings `v9Sym a b` (≅ ℤ/13 × ℤ/4 ≅ ℤ/52), e.g.
`v9Sym 0 1` is the suit rotation ♣→♥→♠→♦→♣ within each rank. -/

/-- `v9Sym a b`: rank index `+a (mod 13)`; suit chosen so that
    `(rank + suit) mod 4` moves by exactly `b`. -/
def v9SymFn (a : Fin 13) (b : Fin 4) (c : Fin 52) : Fin 52 :=
  let r0 := c.val % 13
  let su := c.val / 13
  let wrap := if r0 + a.val < 13 then 0 else 13
  ⟨13 * ((su + b.val + 16 - a.val + wrap) % 4) + (r0 + a.val) % 13, by omega⟩

def neg13 (a : Fin 13) : Fin 13 := ⟨(13 - a.val) % 13, Nat.mod_lt _ (by decide)⟩
def neg4 (b : Fin 4) : Fin 4 := ⟨(4 - b.val) % 4, Nat.mod_lt _ (by decide)⟩

theorem v9SymFn_left : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn (neg13 a) (neg4 b) (v9SymFn a b c) = c := by decide!

theorem v9SymFn_right : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn a b (v9SymFn (neg13 a) (neg4 b) c) = c := by decide!

def v9Sym (a : Fin 13) (b : Fin 4) : Relabel where
  toFun := v9SymFn a b
  invFun := v9SymFn (neg13 a) (neg4 b)
  left_inv := v9SymFn_left a b
  right_inv := v9SymFn_right a b

theorem v9SymFn_weights : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    cardRank (v9SymFn a b c).val % 13 = (cardRank c.val + a.val) % 13 ∧
    cardColumnWeight (v9SymFn a b c).val % 4 = (cardColumnWeight c.val + b.val) % 4 := by
  decide!

/-- A card is determined by (rank mod 13, (rank + suit) mod 4). -/
theorem card_eq_of_weights : ∀ x y : Fin 52,
    cardRank x.val % 13 = cardRank y.val % 13 →
    cardColumnWeight x.val % 4 = cardColumnWeight y.val % 4 → x = y := by
  decide!

/-- (PROVED) The v9 shift conditions hold iff σ is one of the 52 `v9Sym a b`. -/
theorem v9_shift_iff (σ : Relabel) :
    (WeightShift σ cardRank 13 ∧ WeightShift σ cardColumnWeight 4) ↔
      ∃ a b, ∀ c, σ c = v9SymFn a b c := by
  constructor
  · rintro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
    refine ⟨⟨k1 % 13, Nat.mod_lt _ (by decide)⟩, ⟨k2 % 4, Nat.mod_lt _ (by decide)⟩, fun c => ?_⟩
    have ⟨w1, w2⟩ := v9SymFn_weights ⟨k1 % 13, Nat.mod_lt _ (by decide)⟩
      ⟨k2 % 4, Nat.mod_lt _ (by decide)⟩ c
    apply card_eq_of_weights
    · rw [h1 c, w1]; simp only; omega
    · rw [h2 c, w2]; simp only; omega
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a.val, fun c => by rw [h]; exact (v9SymFn_weights a b c).1⟩,
           ⟨b.val, fun c => by rw [h]; exact (v9SymFn_weights a b c).2⟩⟩

theorem v9SymFn_fixed : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn a b c = c → a = 0 ∧ b = 0 := by decide!

theorem v9SymFn_zero (c : Fin 52) : v9SymFn 0 0 c = c := by
  revert c; decide!

/-- (PROVED) v9 SumRanks commutes with σ on all decks iff σ is one of the 52
    `v9Sym a b`. -/
theorem v9_sumRanks_commutes_iff (σ : Relabel) :
    CommutesOnDecksG σ sumRanksV9 ↔ ∃ a b, ∀ c, σ c = v9SymFn a b c :=
  (sumRanks_commutes_iff σ _ _).trans (v9_shift_iff σ)

/-- (PROVED) No transposition commutes with v9 SumRanks:
    a transposition fixes 50 cards, so it would be `v9Sym 0 0 = id`. -/
theorem v9_no_swap_commutes_sumRanks (a b : Fin 52) (hab : a ≠ b) :
    ¬ CommutesOnDecksG (swap a b) sumRanksV9 := by
  intro h
  obtain ⟨x, y, hxy⟩ := (v9_sumRanks_commutes_iff _).1 h
  -- two fixed cards pin (x, y) = (0, 0), then σ = id contradicts σ a = b
  have key : ∀ (x : Fin 13) (y : Fin 4) (a b : Fin 52), a ≠ b →
      (∀ c, (swap a b) c = v9SymFn x y c) → False := by
    intro x y a b hab hxy
    -- some card among 0, 1, 2 is fixed by the swap; a fixed card forces (x, y) = (0, 0)
    have hfix : ∃ c : Fin 52, c ≠ a ∧ c ≠ b := by
      by_cases h0 : (⟨0, by decide⟩ : Fin 52) ≠ a ∧ (⟨0, by decide⟩ : Fin 52) ≠ b
      · exact ⟨_, h0⟩
      by_cases h1 : (⟨1, by decide⟩ : Fin 52) ≠ a ∧ (⟨1, by decide⟩ : Fin 52) ≠ b
      · exact ⟨_, h1⟩
      refine ⟨⟨2, by decide⟩, ?_, ?_⟩ <;> intro e <;> subst e <;>
        simp_all [Fin.ext_iff] <;> omega
    obtain ⟨c, hca, hcb⟩ := hfix
    have hc : v9SymFn x y c = c := by
      rw [← hxy c]; exact Equiv.swap_apply_of_ne_of_ne hca hcb
    obtain ⟨rfl, rfl⟩ := v9SymFn_fixed x y c hc
    have := hxy a
    rw [v9SymFn_zero] at this
    rw [Equiv.swap_apply_left] at this
    exact hab this.symm
  exact key x y a b hab hxy

end DoubleDeal.Security
