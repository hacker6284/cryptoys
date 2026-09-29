/-
  SECURITY (structural weakness, proved) — RESULT ABOUT v1 OF THE GRIP RULE.

  Grip-rule status: these theorems are about the current (v1) E_m, whose grip
  choice (Recipe A, `Em.recipeA`) reads only corner cubies
  (`recipeA_sameCorners`).  They document why the grip rule is being
  redesigned.  They need not hold for a redesigned rule that reads edges,
  and must then be deleted or restated.  Exceptions, which do not use the
  corner-only read: the digest arithmetic at the end of the file
  (`cornerRank`, `edgeRank`, `rankPosition_split`, `edgeRank_lt`,
  `rankPosition_div`, `cornerRank_sameCorners`), and the step-unfolding
  lemmas `leftIter_compose`, `faceTurn_compose`, `faceTurn_eq`, `g2Step_fst`,
  `f3Step_fst` (they unfold the current `Em.g2Step` / `Em.f3Step` and need
  re-proof only if those definitions change).

  Under v1 the MegaDreifach compression is *corner-driven*:

  * `emBlock_word`: for chaining values `h, h'` with the same corner part
    (`cp`, `co`), the block map applies the SAME face-turn word `W`:
    `E_m(h) = W ∘ h`, `E_m(h') = W ∘ h'` (left multiplication).  The grips
    (Recipe A reads) only ever look at corner cubies.
  * `dmStep_word`: hence `dm(h, m) = h ∘ W ∘ h` with `W` a function of the
    corner part of `h` and the deal only.
  * `dmStep_sameCorners`, `foldl_dmBlock_sameCorners`: the corner part of the
    chaining value evolves autonomously (its own ~90.2-bit MD hash).
  * `rankPosition_split`: the digest integer is
    `cornerRank · (30!/2 · 2^29) + edgeRank` with `edgeRank < 30!/2 · 2^29`,
    so the corner chain alone fixes the top ≈ 90.2 bits of the digest.

  This is what the Joux-style corner-multicollision attacks in
  `proofs/megadreifach/security/REPORT.md` exploit (paper attacks; their
  costs are estimates extrapolated from toy runs).

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.MDReduction

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-- Same corner part (corner permutation and corner orientation). -/
def SameCorners (p q : Position) : Prop := p.cp = q.cp ∧ p.co = q.co

theorem SameCorners.refl (p : Position) : SameCorners p p := ⟨rfl, rfl⟩

/-- `compose W h` and `compose W h'` have the same corners when `h, h'` do. -/
theorem sameCorners_compose_left (W h h' : Position) (hc : SameCorners h h') :
    SameCorners (compose W h) (compose W h') := by
  refine ⟨?_, ?_⟩
  · show h.cp ∘ W.cp = h'.cp ∘ W.cp; rw [hc.1]
  · funext s; show h.co (W.cp s) + W.co s = h'.co (W.cp s) + W.co s; rw [hc.2]

theorem sameCorners_compose (a a' b b' : Position) (ha : SameCorners a a')
    (hb : SameCorners b b') : SameCorners (compose a b) (compose a' b') := by
  refine ⟨?_, ?_⟩
  · show b.cp ∘ a.cp = b'.cp ∘ a'.cp; rw [ha.1, hb.1]
  · funext s; show b.co (a.cp s) + a.co s = b'.co (a'.cp s) + a'.co s
    rw [ha.1, ha.2, hb.2]

/-- Recipe A reads only corner cubies. -/
theorem recipeA_sameCorners (g g' : Position) (hc : SameCorners g g') (phys : Fin 12)
    (o : Em.Grip) : Em.recipeA g phys o = Em.recipeA g' phys o := by
  unfold Em.recipeA Em.coloursAt
  rw [hc.1, hc.2]

theorem leftIter_compose (T : Position) : ∀ (n : Nat) (W h : Position),
    Em.leftIter T n (compose W h) = compose (Em.leftIter T n W) h
  | 0, _, _ => rfl
  | n + 1, W, h => by
      simp only [Em.leftIter]
      rw [leftIter_compose T n W h, compose_assoc]

theorem faceTurn_compose (W h : Position) (f : Fin 12) (a : Nat) :
    Em.faceTurn (compose W h) f a = compose (Em.faceTurn W f a) h :=
  leftIter_compose _ _ _ _

theorem faceTurn_eq (g : Position) (f : Fin 12) (a : Nat) :
    Em.faceTurn g f a = compose (Em.faceTurn identity f a) g := by
  rw [← faceTurn_compose, compose_id_left]

/-- The block-map invariant: both runs are `(compose W h, o)`, `(compose W h', o)`. -/
def WordInv (h h' : Position) (st st' : Position × Em.Grip) : Prop :=
  st.2 = st'.2 ∧ ∃ W, st.1 = compose W h ∧ st'.1 = compose W h'

/-- The position part of a G2 step is a left multiplication whose word depends
    only on the grip and the card. -/
theorem g2Step_fst (g : Position) (o : Em.Grip) (card : Nat) :
    (Em.g2Step (g, o) card).1 = compose (Em.g2Step (identity, o) card).1 g := by
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    split
    · rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]
    · rw [← faceTurn_compose, ← faceTurn_compose, compose_id_left]
  · simp only [hr, dite_false]
    split
    · rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]
    · rw [← faceTurn_compose, ← faceTurn_compose, compose_id_left]

/-- Held physical face and working grip of a G2 step (grip and card only). -/
def g2Held (o : Em.Grip) (card : Nat) : Fin 12 × Em.Grip :=
  if h : card / 4 < 12 then (o ⟨card / 4, h⟩, o)
  else (spinAboutUp' o (card % 4 + 1) 0, spinAboutUp' o (card % 4 + 1))
where spinAboutUp' := Em.spinAboutUp

/-- The new grip of a G2 step is the Recipe A read of the new position. -/
theorem g2Step_snd (g : Position) (o : Em.Grip) (card : Nat) :
    (Em.g2Step (g, o) card).2 =
      Em.recipeA (Em.g2Step (g, o) card).1 (g2Held o card).1 (g2Held o card).2 := by
  unfold Em.g2Step g2Held g2Held.spinAboutUp'
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
  · simp only [hr, dite_false]

theorem wordInv_g2Step (h h' : Position) (hc : SameCorners h h') (st st' : Position × Em.Grip)
    (hi : WordInv h h' st st') (card : Nat) :
    WordInv h h' (Em.g2Step st card) (Em.g2Step st' card) := by
  obtain ⟨st1, st2⟩ := st
  obtain ⟨st1', st2'⟩ := st'
  obtain ⟨ho, W, e1, e2⟩ := hi
  dsimp only at ho e1 e2
  subst ho; subst e1; subst e2
  have f1 := g2Step_fst (compose W h) st2 card
  have f2 := g2Step_fst (compose W h') st2 card
  rw [← compose_assoc] at f1 f2
  refine ⟨?_, _, f1, f2⟩
  rw [g2Step_snd, g2Step_snd, f1, f2]
  exact recipeA_sameCorners _ _ (sameCorners_compose_left _ _ _ hc) _ _

theorem f3Step_fst (g : Position) (o : Em.Grip) :
    (Em.f3Step (g, o)).1 = compose (Em.faceTurn identity (o 0) 1) g := faceTurn_eq _ _ _

theorem wordInv_f3Step (h h' : Position) (hc : SameCorners h h') (st st' : Position × Em.Grip)
    (hi : WordInv h h' st st') : WordInv h h' (Em.f3Step st) (Em.f3Step st') := by
  obtain ⟨st1, st2⟩ := st
  obtain ⟨st1', st2'⟩ := st'
  obtain ⟨ho, W, e1, e2⟩ := hi
  dsimp only at ho e1 e2
  subst ho; subst e1; subst e2
  have f1 := f3Step_fst (compose W h) st2
  have f2 := f3Step_fst (compose W h') st2
  rw [← compose_assoc] at f1 f2
  refine ⟨?_, _, f1, f2⟩
  show Em.recipeA (Em.f3Step (compose W h, st2)).1 (st2 0) st2 =
    Em.recipeA (Em.f3Step (compose W h', st2)).1 (st2 0) st2
  rw [f1, f2]
  exact recipeA_sameCorners _ _ (sameCorners_compose_left _ _ _ hc) _ _

theorem wordInv_f3Iter (h h' : Position) (hc : SameCorners h h') :
    ∀ (n : Nat) (st st' : Position × Em.Grip), WordInv h h' st st' →
      WordInv h h' (Em.f3Iter n st) (Em.f3Iter n st')
  | 0, _, _, hi => hi
  | n + 1, st, st', hi =>
      wordInv_f3Iter h h' hc n _ _ (wordInv_f3Step h h' hc st st' hi)

theorem wordInv_foldl (h h' : Position) (hc : SameCorners h h') :
    ∀ (cards : List Nat) (st st' : Position × Em.Grip), WordInv h h' st st' →
      WordInv h h' (cards.foldl Em.g2Step st) (cards.foldl Em.g2Step st')
  | [], _, _, hi => hi
  | c :: cs, st, st', hi =>
      wordInv_foldl h h' hc cs _ _ (wordInv_g2Step h h' hc st st' hi c)

/-- **Corner-driven block map.**  Same corners ⇒ same face-turn word. -/
theorem emBlock_word (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    ∃ W, Em.emBlock h deal = compose W h ∧ Em.emBlock h' deal = compose W h' := by
  have h0 : WordInv h h' (h, Em.gripId) (h', Em.gripId) :=
    ⟨rfl, identity, (compose_id_left h).symm, (compose_id_left h').symm⟩
  obtain ⟨_, W, e1, e2⟩ :=
    wordInv_f3Iter h h' hc f3T _ _ (wordInv_foldl h h' hc (deal.take 52) _ _ h0)
  exact ⟨W, e1, e2⟩

/-- Every block map is a left multiplication: `E_m(h) = W ∘ h`. -/
theorem emBlock_is_leftMul (h : Position) (deal : List Nat) :
    ∃ W, Em.emBlock h deal = compose W h := by
  obtain ⟨W, e, _⟩ := emBlock_word h h (SameCorners.refl h) deal
  exact ⟨W, e⟩

/-- **DM form.**  `dm(h, m) = h ∘ W ∘ h`, and `W` is shared by all chaining
    values with the corner part of `h`. -/
theorem dmStep_word (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    ∃ W, Em.dmStep h deal = compose h (compose W h) ∧
      Em.dmStep h' deal = compose h' (compose W h') := by
  obtain ⟨W, e1, e2⟩ := emBlock_word h h' hc deal
  exact ⟨W, by unfold Em.dmStep; rw [e1], by unfold Em.dmStep; rw [e2]⟩

/-- The corner part of the next chaining value depends only on the corner part
    of the current one (and the block). -/
theorem dmStep_sameCorners (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    SameCorners (Em.dmStep h deal) (Em.dmStep h' deal) := by
  obtain ⟨W, e1, e2⟩ := dmStep_word h h' hc deal
  rw [e1, e2]
  exact sameCorners_compose _ _ _ _ hc (sameCorners_compose_left _ _ _ hc)

theorem foldl_dmBlock_sameCorners :
    ∀ (bs : List (List Nat)) (h h' : Position), SameCorners h h' →
      SameCorners (bs.foldl dmBlock h) (bs.foldl dmBlock h')
  | [], _, _, hc => hc
  | _ :: bs, h, h', hc =>
      foldl_dmBlock_sameCorners bs _ _ (dmStep_sameCorners h h' hc _)

/-- Joux-style gluing: once two block sequences reach chaining values with the
    same corners, every common continuation keeps the corners equal. -/
theorem corner_collision_extends (h h' : Position) (hc : SameCorners h h')
    (suffix : List (List Nat)) :
    SameCorners (suffix.foldl dmBlock h) (suffix.foldl dmBlock h') :=
  foldl_dmBlock_sameCorners suffix h h' hc

/-! ## The digest is (corner rank ‖ edge rank) -/

/-- Corner part of the digest rank. -/
def cornerRank (p : Position) : Nat := evenRank (listOf p.cp) * 3 ^ 19 + packOri3 (listOfOri p.co)

/-- Edge part of the digest rank. -/
def edgeRank (p : Position) : Nat := evenRank (listOf p.ep) * 2 ^ 29 + packOri2 (listOfOri p.eo)

/-- Radix of the edge part: `30!/2 · 2^29`. -/
def edgeRadix : Nat := evenPermCount 30 * 2 ^ 29

theorem rankPosition_split (p : Position) :
    rankPosition p = cornerRank p * edgeRadix + edgeRank p := by
  unfold rankPosition cornerRank edgeRank edgeRadix
  rw [rankLists_horner]
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

theorem edgeRank_lt (p : Position) (h : InjPos p) : edgeRank p < edgeRadix := by
  unfold edgeRank edgeRadix
  have h3 := evenRank_lt_countN 30 _ (permNWf_listOf p.ep h.2) (by decide)
  have h4 := packOri2_lt _ (ori2Wf_listOfOri p.eo)
  exact mix_lt _ _ _ _ h3 h4

/-- The top part of the digest integer is the corner rank. -/
theorem rankPosition_div (p : Position) (h : InjPos p) :
    rankPosition p / edgeRadix = cornerRank p := by
  rw [rankPosition_split]
  have hpos : 0 < edgeRadix := Nat.lt_of_le_of_lt (Nat.zero_le _) (edgeRank_lt p h)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (edgeRank_lt p h),
    Nat.zero_add]

theorem cornerRank_sameCorners (p q : Position) (hc : SameCorners p q) :
    cornerRank p = cornerRank q := by
  unfold cornerRank; rw [hc.1, hc.2]

/-- **Truncated-digest consequence.**  Two block sequences whose chaining
    values share corners at any point, followed by a common suffix, give
    digests whose integer values agree in the top part `⌊digest / (30!/2·2^29)⌋`
    (≈ 90.2 of the ≈ 225.9 bits). -/
theorem digest_top_collision (h h' : Position) (hh : InjPos h) (hh' : InjPos h')
    (hc : SameCorners h h') (suffix : List (List Nat)) :
    rankPosition (suffix.foldl dmBlock h) / edgeRadix =
      rankPosition (suffix.foldl dmBlock h') / edgeRadix := by
  have i1 : InjPos (suffix.foldl dmBlock h) := by
    rw [foldl_eq_chR]
    exact injPos_chR_from h hh _
  have i2 : InjPos (suffix.foldl dmBlock h') := by
    rw [foldl_eq_chR]
    exact injPos_chR_from h' hh' _
  rw [rankPosition_div _ i1, rankPosition_div _ i2]
  exact cornerRank_sameCorners _ _ (foldl_dmBlock_sameCorners suffix h h' hc)
where
  injPos_chR_from (h : Position) (hh : InjPos h) :
      ∀ r : List (List Nat), InjPos (chR dmBlock h r)
    | [] => hh
    | _ :: r => by
        simp only [chR]; unfold dmBlock
        exact injPos_dmStep _ _ (injPos_chR_from h hh r)

end MegaDreifach.Security
