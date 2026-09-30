import MegaDreifach.G2CovRead

/-!
# M9 read model: which piece of `W` the second read sees, and that the read is
injective on pieces

Owns: the read-model lemmas used by the M9 different-first-card proof.

* `g2Mid_compose`: the held-face turn commutes with right multiplication, so the
  pre-read position of a card step from `compose X W` is `compose Y W` with `Y` the
  pre-read position from `X`, and the read configuration does not depend on `W`.
* `readGrip_colours`: on a neighbour pair `(phys, noon)` the new grip determines the
  colour pair read (`absReorient` is injective on adjacent pairs).
* `corner_read_piece` / `edge_read_piece`: an ordered colour pair determines the
  piece it was read from, across all read configurations (corner: the two colours are
  cyclically consecutive on the cubie; edge: the two colours are the edge's faces).

All finite facts are small kernel `decide!` tables.  Zero sorry, no `native_decide`.
-/

namespace MegaDreifach.M9

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifach.G2Cov

/-! ## The held-face turn and right multiplication -/

theorem g2Mid_compose (X W : Position) (o : Grip) (card : Nat) :
    g2Mid (compose X W, o) card = (compose (g2Mid (X, o) card).1 W, (g2Mid (X, o) card).2) := by
  unfold g2Mid
  by_cases h : card / 4 < 12
  · simp only [dif_pos h, Security.faceTurn_compose]
  · simp only [dif_neg h, Security.faceTurn_compose]

/-! ## The grip determines the colour pair -/

theorem readGrip_colours (G : Position) (phys noon : Fin 12) (pos : Nat) (hn : noon ∈ nbrs phys) :
    readGrip G phys noon pos 0 = (readColours G phys noon pos).1 ∧
      readGrip G phys noon pos 1 = (readColours G phys noon pos).2 := by
  have hadj := readColours_adj G phys noon pos hn
  rw [readGrip_eq]
  generalize readColours G phys noon pos = cc at hadj ⊢
  obtain ⟨c1, c2⟩ := cc
  have hs : (absReorient? c1 c2).isSome := by rw [absReorient?_some_iff]; exact decide_eq_true hadj
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have hA : absReorient c1 c2 = r := by unfold absReorient; rw [hr]; rfl
  have := (absReorient?_spec c1 c2 r hr).2
  simp only
  rw [hA]
  exact this

theorem readColours_of_readGrip {G G' : Position} {p x p' x' : Fin 12} (pos : Nat)
    (hx : x ∈ nbrs p) (hx' : x' ∈ nbrs p') (h : readGrip G p x pos = readGrip G' p' x' pos) :
    readColours G p x pos = readColours G' p' x' pos := by
  have h1 := readGrip_colours G p x pos hx
  have h2 := readGrip_colours G' p' x' pos hx'
  rw [h] at h1
  exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)

/-! ## Finite tables -/

/-- In every corner read configuration, the noon face sits one step after the held
    face in the slot's cyclic face order. -/
theorem loc_next_table :
    allF 12 (fun p => allF 12 (fun x => !decide (x ∈ nbrs p) ||
      (let t := (cornerSlot p x (cornerAfterNoon p x)).val
       Nat.beq (locOf x (cornerFace t 1) (cornerFace t 2))
         ((locOf p (cornerFace t 1) (cornerFace t 2) + 1) % 3)))) = true := by
  decide!

/-- Two cyclically consecutive colours determine the corner cubie. -/
theorem corner_pair_table :
    allN 20 (fun c => allN 20 (fun c' => allN 3 (fun k => allN 3 (fun k' =>
      !(Nat.beq (cornerFace c k).val (cornerFace c' k').val &&
        Nat.beq (cornerFace c ((k + 1) % 3)).val (cornerFace c' ((k' + 1) % 3)).val) ||
      Nat.beq c c')))) = true := by
  decide!

/-- The two colours of an edge, in either order, determine the edge piece. -/
theorem edge_pair_table :
    allN 30 (fun e => allN 30 (fun e' => allN 2 (fun j => allN 2 (fun j' =>
      !(Nat.beq (edgeFace e j).val (edgeFace e' j').val &&
        Nat.beq (edgeFace e (1 - j)).val (edgeFace e' (1 - j')).val) ||
      Nat.beq e e')))) = true := by
  decide!

theorem loc_next (p x : Fin 12) (hx : x ∈ nbrs p) :
    locOf x (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 1)
        (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 2) =
      (locOf p (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 1)
        (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 2) + 1) % 3 := by
  have h := allF_spec (allF_spec loc_next_table p) x
  simp only [hx, decide_True, Bool.not_true, Bool.false_or] at h
  exact Nat.eq_of_beq_eq_true h

theorem corner_pair {c c' k k' : Nat} (hc : c < 20) (hc' : c' < 20) (hk : k < 3) (hk' : k' < 3)
    (h1 : cornerFace c k = cornerFace c' k')
    (h2 : cornerFace c ((k + 1) % 3) = cornerFace c' ((k' + 1) % 3)) : c = c' := by
  have h := allN_spec (allN_spec (allN_spec (allN_spec corner_pair_table c hc) c' hc') k hk) k' hk'
  rw [h1, h2, Nat.beq_refl, Nat.beq_refl] at h
  exact Nat.eq_of_beq_eq_true (by simpa using h)

theorem edge_pair {e e' j j' : Nat} (he : e < 30) (he' : e' < 30) (hj : j < 2) (hj' : j' < 2)
    (h1 : edgeFace e j = edgeFace e' j') (h2 : edgeFace e (1 - j) = edgeFace e' (1 - j')) :
    e = e' := by
  have h := allN_spec (allN_spec (allN_spec (allN_spec edge_pair_table e he) e' he') j hj) j' hj'
  rw [h1, h2, Nat.beq_refl, Nat.beq_refl] at h
  exact Nat.eq_of_beq_eq_true (by simpa using h)

/-! ## The colour pair determines the piece -/

theorem coloursAt_cyc (G : Position) (p x : Fin 12) (hx : x ∈ nbrs p) :
    ∃ k, k < 3 ∧
      coloursAt G p x (cornerAfterNoon p x) =
        (cornerFace (G.cp (cornerSlot p x (cornerAfterNoon p x))).val k,
         cornerFace (G.cp (cornerSlot p x (cornerAfterNoon p x))).val ((k + 1) % 3)) := by
  rw [coloursAt_eq, loc_next p x hx]
  have h1 := locOf_lt p (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 1)
    (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 2)
  have h2 := (G.co (cornerSlot p x (cornerAfterNoon p x))).isLt
  generalize locOf p (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 1)
    (cornerFace (cornerSlot p x (cornerAfterNoon p x)).val 2) = L at h1
  generalize (G.co (cornerSlot p x (cornerAfterNoon p x))).val = o at h2
  refine ⟨(L + 3 - o) % 3, Nat.mod_lt _ (by decide), ?_⟩
  have : ((L + 1) % 3 + 3 - o) % 3 = ((L + 3 - o) % 3 + 1) % 3 := by omega
  rw [this]

theorem corner_read_piece {G G' : Position} {p x p' x' : Fin 12} (hx : x ∈ nbrs p)
    (hx' : x' ∈ nbrs p')
    (h : coloursAt G p x (cornerAfterNoon p x) = coloursAt G' p' x' (cornerAfterNoon p' x')) :
    G.cp (cornerSlot p x (cornerAfterNoon p x)) =
      G'.cp (cornerSlot p' x' (cornerAfterNoon p' x')) := by
  obtain ⟨k, hk, e1⟩ := coloursAt_cyc G p x hx
  obtain ⟨k', hk', e2⟩ := coloursAt_cyc G' p' x' hx'
  rw [e1, e2] at h
  simp only [Prod.mk.injEq] at h
  exact Fin.ext (corner_pair (Fin.isLt _) (Fin.isLt _) hk hk' h.1 h.2)

theorem edgeColoursAt_pair (G : Position) (a b : Fin 12) :
    ∃ j, j < 2 ∧ edgeColoursAt G a b =
      (edgeFace (G.ep (edgeSlot a b)).val j, edgeFace (G.ep (edgeSlot a b)).val (1 - j)) := by
  unfold edgeColoursAt
  dsimp only
  split <;> split
  all_goals first | exact ⟨0, by decide, rfl⟩ | exact ⟨1, by decide, rfl⟩

theorem edge_read_piece {G G' : Position} {p x p' x' : Fin 12}
    (h : edgeColoursAt G p x = edgeColoursAt G' p' x') :
    G.ep (edgeSlot p x) = G'.ep (edgeSlot p' x') := by
  obtain ⟨j, hj, e1⟩ := edgeColoursAt_pair G p x
  obtain ⟨j', hj', e2⟩ := edgeColoursAt_pair G' p' x'
  rw [e1, e2] at h
  simp only [Prod.mk.injEq] at h
  exact Fin.ext (edge_pair (Fin.isLt _) (Fin.isLt _) hj hj' h.1 h.2)

end MegaDreifach.M9
