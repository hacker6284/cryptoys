import MegaDreifach.M9Canon
import MegaDreifach.M9Read
import MegaDreifach.M9Dec0
import MegaDreifach.M9Dec1
import MegaDreifach.M9Dec2
import MegaDreifach.M9Dec3
import MegaDreifach.M9Dec4
import MegaDreifach.M9Dec5

/-!
# M9 (v2): two-card windows — the different-first-card half, and the full 2-card statement

Owns: the kernel-checked M9 theorems `m9_canon`, `twoCard_diff_first_ne` and
`twoCard_ne`, and the proof route from the decoder checks to them.

Statement (`twoCard_ne`): from a position `W` with `InjPos W`, on any `GripOk` grip
`o`, two 2-card windows `(a, b) ≠ (c, d)` of card ids `< 52`, dealt at the same deal
positions `pos1`, `pos2` (any values, so both read parities), never reach the same
state.  Scope: 2-card windows only.  Not block-level (two windows that end in
different states can still meet later in the block) and not collision resistance.

Route for different first cards `a ≠ c`:

1. `twoCard_diff_first_ne` reduces grip `o = rotAt s` to `gripId` by rotation
   covariance (`G2CovRead.g2Step_cov` twice; `conj_inj`, `rotG_inj`,
   `injPos_unconj`).
2. `m9_canon` at `gripId`: equal states give equal net products
   (`G2Nets.twoCard_collision_nets`), which are `compose (conj s1 (N0 b)) (N0 a)`
   with `rotAt s1` the intermediate grip (`net2_cov`, `n0_table`).  The decoder checks
   `m9dec_0` … `m9dec_59` (`M9Dec*.lean`, collected in `dec_all`) map every such
   product to its first card, or to an ambiguity group of the certificate.  Equal
   products decode alike, so `a ≠ c` forces a shared group.
3. In a shared group, entries with different first cards read different `W`-slots
   at the second read (`amb_table`, `amb_sep`; corner slot for odd `pos2`, edge slot
   for even).  Equal final grips give equal colour pairs (`readColours_of_readGrip`),
   equal pieces (`corner_read_piece`, `edge_read_piece`), hence equal `W`-slots by
   injectivity of `W` — a contradiction.

Zero sorry, no `native_decide`, no new axioms.
-/

namespace MegaDreifach.M9

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifach.G2Cov MegaDreifach.M9Cert

/-! ## Ambiguity groups -/

/-- Within a group, entries with different first cards (`e / 10⁸`) read different
    corner slots (`e / 100 % 100`) and different edge slots (`e % 100`). -/
def pairOk (g : List Nat) : Bool :=
  g.all fun e => g.all fun e' =>
    Nat.beq (e / 100000000) (e' / 100000000) ||
      (!Nat.beq (e / 100 % 100) (e' / 100 % 100) && !Nat.beq (e % 100) (e' % 100))

theorem amb_table : ambG.all pairOk = true := by decide!

theorem getD_mem_or_nil : ∀ (l : List (List Nat)) (i : Nat), l.getD i [] ∈ l ∨ l.getD i [] = []
  | [], _ => Or.inr rfl
  | x :: l, 0 => Or.inl (List.mem_cons_self x l)
  | x :: l, i + 1 => (getD_mem_or_nil l i).imp (fun h => List.mem_cons_of_mem x h) id

theorem pairOk_spec {g : List Nat} (hg : pairOk g = true) {e e' : Nat} (he : e ∈ g) (he' : e' ∈ g)
    (hne : e / 100000000 ≠ e' / 100000000) :
    e / 100 % 100 ≠ e' / 100 % 100 ∧ e % 100 ≠ e' % 100 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hg e he) e' he'
  cases h1 : Nat.beq (e / 100000000) (e' / 100000000)
  · cases h2 : Nat.beq (e / 100 % 100) (e' / 100 % 100) <;>
      cases h3 : Nat.beq (e % 100) (e' % 100) <;> simp only [h1, h2, h3] at h <;>
      first | exact absurd h (by decide) | exact ⟨Nat.ne_of_beq_eq_false h2, Nat.ne_of_beq_eq_false h3⟩
  · exact absurd (Nat.eq_of_beq_eq_true h1) hne

theorem inAmb_spec {a s1 b r : Nat} (h : inAmb a s1 b r = true) :
    ∃ e ∈ ambG.getD (r - 100) [], e / 10000 = a * 10000 + s1 * 100 + b ∧ e % 10000 = wsl a s1 b := by
  unfold inAmb at h
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨e, he, h⟩

/-- Two items that decode to the same ambiguity group, with different first cards,
    read different `W`-slots (corner and edge). -/
theorem amb_sep {a s1 b c s2 d r : Nat} (hs1 : s1 < 60) (hb : b < 52) (hs2 : s2 < 60) (hd : d < 52)
    (hac : a ≠ c) (h1 : inAmb a s1 b r = true) (h2 : inAmb c s2 d r = true) :
    wsl a s1 b / 100 ≠ wsl c s2 d / 100 ∧ wsl a s1 b % 100 ≠ wsl c s2 d % 100 := by
  obtain ⟨e, he, ek, ew⟩ := inAmb_spec h1
  obtain ⟨e', he', ek', ew'⟩ := inAmb_spec h2
  have hG : pairOk (ambG.getD (r - 100) []) = true := by
    rcases getD_mem_or_nil ambG (r - 100) with hm | hm
    · exact List.all_eq_true.mp amb_table _ hm
    · rw [hm] at he; exact absurd he (List.not_mem_nil e)
  have hne : e / 100000000 ≠ e' / 100000000 := by omega
  have := pairOk_spec hG he he' hne
  omega

/-! ## Slots -/

theorem wsl_div (a s1 b : Nat) :
    wsl a s1 b / 100 = ((mid a s1 b).1.cp (cornerSlot ((mid a s1 b).2.1 (mid a s1 b).2.2)
      (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1)
      (cornerAfterNoon ((mid a s1 b).2.1 (mid a s1 b).2.2)
        (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1)))).val := by
  unfold wsl
  have := ((mid a s1 b).1.ep (edgeSlot ((mid a s1 b).2.1 (mid a s1 b).2.2)
    (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1))).isLt
  dsimp only
  omega

theorem wsl_mod (a s1 b : Nat) :
    wsl a s1 b % 100 = ((mid a s1 b).1.ep (edgeSlot ((mid a s1 b).2.1 (mid a s1 b).2.2)
      (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1))).val := by
  unfold wsl
  have := ((mid a s1 b).1.ep (edgeSlot ((mid a s1 b).2.1 (mid a s1 b).2.2)
    (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1))).isLt
  dsimp only
  omega

/-! ## The canonical grip -/

theorem g2Step_canon_fst (W : Position) {a : Nat} (ha : a < 52) (pos1 : Nat) :
    (g2Step (W, gripId) a pos1).1 = compose (N0 a) W := by
  rw [G2Nets.g2Step_fst_net, net2_gripId a ha]

/-- The final grip of the window `(a, b)` from `(W, gripId)` with intermediate grip
    `rotAt s1` is the read of `compose Y W`, `Y = (mid a s1 b).1`. -/
theorem final_grip (W : Position) {a : Nat} (ha : a < 52) (pos1 : Nat) {s1 : Nat}
    (ho : (g2Step (W, gripId) a pos1).2 = rotAt s1) (b pos2 : Nat) :
    (g2Step (g2Step (W, gripId) a pos1) b pos2).2 =
      readGrip (compose (mid a s1 b).1 W) ((mid a s1 b).2.1 (mid a s1 b).2.2)
        (visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1) pos2 := by
  have hst : g2Step (W, gripId) a pos1 = (compose (N0 a) W, rotAt s1) :=
    Prod.ext (g2Step_canon_fst W ha pos1) ho
  rw [hst, g2Step_eq]
  dsimp only
  rw [g2Mid_compose]
  rfl

theorem mid_noon {a s1 : Nat} (hs1 : s1 < 60) (b : Nat) :
    visualNoon (mid a s1 b).2.2 (mid a s1 b).2.1 ∈ nbrs ((mid a s1 b).2.1 (mid a s1 b).2.2) :=
  visualNoon_mem _ (gripOk_g2Mid (N0 a, rotAt s1) b ⟨s1, hs1, rfl⟩) _

/-- M9 at `gripId`, given the decoder checks: from an `InjPos` position, two 2-card
    windows with different first cards `< 52` (second cards `< 52`, same deal
    positions) never reach the same state. -/
theorem m9_canon_of (hdec : ∀ s, s < 60 → allN 52 (fun b => chkB s b) = true)
    (W : Position) (hW : InjPos W) {a b c d : Nat} (ha : a < 52) (hb : b < 52) (hc : c < 52)
    (hd : d < 52) (hac : a ≠ c) (pos1 pos2 : Nat) :
    g2Step (g2Step (W, gripId) a pos1) b pos2 ≠ g2Step (g2Step (W, gripId) c pos1) d pos2 := by
  intro heq
  have hP := G2Nets.twoCard_collision_nets W hW.1 hW.2 gripId a b c d pos1 pos2 (congrArg Prod.fst heq)
  obtain ⟨s1, hs1, ho1⟩ := gripOk_g2Step (W, gripId) a pos1 gripOk_id
  obtain ⟨s2, hs2, ho2⟩ := gripOk_g2Step (W, gripId) c pos1 gripOk_id
  have hg := congrArg Prod.snd heq
  rw [final_grip W ha pos1 ho1, final_grip W hc pos1 ho2] at hg
  rw [ho1, ho2, G2Cov.net2_cov s1 hs1, G2Cov.net2_cov s2 hs2, net2_gripId b hb, net2_gripId d hd,
    net2_gripId a ha, net2_gripId c hc] at hP
  have d1 := decOk_spec (chkB_spec (allN_spec (hdec s1 hs1) b hb) a ha)
  have d2 := decOk_spec (chkB_spec (allN_spec (hdec s2 hs2) d hd) c hc)
  rw [hP] at d1
  generalize walk (codeOf (compose (conj s2 (N0 d)) (N0 c))) 40 0 = r at d1 d2
  have hamb : inAmb a s1 b r = true ∧ inAmb c s2 d r = true := by
    rcases d1 with h1 | ⟨h1, h1'⟩ <;> rcases d2 with h2 | ⟨h2, h2'⟩
    · exact absurd (h1.symm.trans h2) hac
    · omega
    · omega
    · exact ⟨h1', h2'⟩
  have hsep := amb_sep hs1 hb hs2 hd hac hamb.1 hamb.2
  have hcol := readColours_of_readGrip pos2 (mid_noon hs1 b) (mid_noon hs2 d) hg
  unfold readColours at hcol
  by_cases hpar : pos2 % 2 = 1
  · simp only [hpar, if_true] at hcol
    have hp := corner_read_piece (G := compose (mid a s1 b).1 W) (G' := compose (mid c s2 d).1 W)
      (mid_noon hs1 b) (mid_noon hs2 d) hcol
    have hq := hW.1 hp
    rw [wsl_div, wsl_div, hq] at hsep
    exact hsep.1 rfl
  · simp only [hpar, if_false] at hcol
    have hp := edge_read_piece (G := compose (mid a s1 b).1 W) (G' := compose (mid c s2 d).1 W) hcol
    have hq := hW.2 hp
    rw [wsl_mod, wsl_mod, hq] at hsep
    exact hsep.2 rfl

/-! ## The decoder checks, collected -/

/-- `fun s hs => if h : s = 0 then … m9dec_0 else … absurd hs (by omega)`. -/
macro "m9dec_cases%" : term => do
  let mut body ← `(absurd hs (by omega))
  for s in (List.range 60).reverse do
    let id := Lean.mkIdent (Lean.Name.mkSimple s!"m9dec_{s}")
    let n := Lean.Syntax.mkNumLit (toString s)
    body ← `(if h : s = $n then by subst h; exact $id else $body)
  `(fun s hs => $body)

theorem dec_all : ∀ s, s < 60 → allN 52 (fun b => chkB s b) = true := m9dec_cases%

/-- M9 at the identity grip, different first cards: from an `InjPos` position `W`,
    two 2-card windows with first cards `a ≠ c` (all four cards `< 52`), dealt at the
    same deal positions `pos1`, `pos2`, never reach the same state. -/
theorem m9_canon (W : Position) (hW : InjPos W) {a b c d : Nat} (ha : a < 52) (hb : b < 52)
    (hc : c < 52) (hd : d < 52) (hac : a ≠ c) (pos1 pos2 : Nat) :
    g2Step (g2Step (W, gripId) a pos1) b pos2 ≠ g2Step (g2Step (W, gripId) c pos1) d pos2 :=
  m9_canon_of dec_all W hW ha hb hc hd hac pos1 pos2

/-! ## Any grip, by rotation covariance -/

/-- A 2-card window from `(W, rotAt s)` is the rotation `s` of the window from
    `(unconj s W, gripId)`. -/
theorem twoCard_cov (s : Nat) (hs : s < 60) (W : Position) (x y pos1 pos2 : Nat) :
    g2Step (g2Step (W, rotAt s) x pos1) y pos2 =
      (conj s (g2Step (g2Step (unconj s W, gripId) x pos1) y pos2).1,
        rotG s (g2Step (g2Step (unconj s W, gripId) x pos1) y pos2).2) := by
  have hW : W = conj s (unconj s W) := (conj_unconj s hs W).symm
  have h1 := g2Step_cov s hs (unconj s W) gripId gripOk_id x pos1
  rw [rotG_gripId, ← hW] at h1
  rw [h1, g2Step_cov s hs _ _ (gripOk_g2Step (unconj s W, gripId) x pos1 gripOk_id)]

/-- M9, different-first-card half: from an `InjPos` position `W` on any `GripOk` grip
    `o`, two 2-card windows with first cards `a ≠ c` (all four cards `< 52`), dealt at
    the same deal positions `pos1`, `pos2`, never reach the same state. -/
theorem twoCard_diff_first_ne (W : Position) (hW : InjPos W) (o : Grip) (ho : GripOk o)
    {a b c d : Nat} (ha : a < 52) (hb : b < 52) (hc : c < 52) (hd : d < 52) (hac : a ≠ c)
    (pos1 pos2 : Nat) :
    g2Step (g2Step (W, o) a pos1) b pos2 ≠ g2Step (g2Step (W, o) c pos1) d pos2 := by
  obtain ⟨s, hs, rfl⟩ := ho
  intro heq
  rw [twoCard_cov s hs, twoCard_cov s hs] at heq
  have h1 := conj_inj s hs (congrArg Prod.fst heq)
  have h2 := rotG_inj s hs (congrArg Prod.snd heq)
  exact m9_canon (unconj s W) (injPos_unconj s hs W hW) ha hb hc hd hac pos1 pos2 (Prod.ext h1 h2)

/-- M9 (v2, 2-card windows): from an `InjPos` position `W` on any `GripOk` grip `o`,
    two different 2-card windows `(a, b) ≠ (c, d)` of card ids `< 52`, dealt at the
    same deal positions `pos1`, `pos2`, never reach the same state.  Not block-level. -/
theorem twoCard_ne (W : Position) (hW : InjPos W) (o : Grip) (ho : GripOk o)
    {a b c d : Nat} (ha : a < 52) (hb : b < 52) (hc : c < 52) (hd : d < 52)
    (hne : (a, b) ≠ (c, d)) (pos1 pos2 : Nat) :
    g2Step (g2Step (W, o) a pos1) b pos2 ≠ g2Step (g2Step (W, o) c pos1) d pos2 := by
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun h => hne (by rw [h])
    exact G2Nets.twoCard_same_first_ne W hW o ho a pos1 hb hd hbd pos2
  · exact twoCard_diff_first_ne W hW o ho ha hb hc hd hac pos1 pos2

end MegaDreifach.M9
