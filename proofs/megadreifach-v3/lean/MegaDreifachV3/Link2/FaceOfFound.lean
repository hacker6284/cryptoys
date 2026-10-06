/-
  The found-invariant of the v3 piece searches: on a position whose edge (resp. corner)
  table is bijective, `edgeFaceOf?` / `cornerFaceOf?` return `some` for every colour of the
  named piece; with `triples_ok`, for the colours every card step and echo asks for. No sorry.
  No native_decide.
-/
import MegaDreifachV3.Link2.FaceOf
import MegaDreifach.Link2.InjPos

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifachV3.Em

theorem lastIdx_some_of (n : Nat) (p : Nat → Bool) (t : Nat) (ht : t < n) (hp : p t = true) :
    ∃ u, lastIdx n p = some u := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [lastIdx_succ]
    by_cases hk : p k = true
    · exact ⟨k, by rw [if_pos hk]⟩
    · rw [if_neg hk]
      have htk : t ≠ k := fun e => hk (e ▸ hp)
      exact ih (by omega)

theorem pair_found (p q x u v : Fin 12) (hx : x = p ∨ x = q) (cs : Fin 12 × Fin 12)
    (hcs : cs = (p, q) ∨ cs = (q, p)) :
    ∃ y, (if cs.1 = x then some u else if cs.2 = x then some v else none) = some y := by
  by_cases h1 : cs.1 = x
  · exact ⟨u, if_pos h1⟩
  by_cases h2 : cs.2 = x
  · exact ⟨v, by rw [if_neg h1, if_pos h2]⟩
  exfalso
  rcases hcs with rfl | rfl <;> rcases hx with rfl | rfl <;> simp_all

/-- Edge found-invariant: bijective edge table, `x` a colour of the edge piece `(a, b)`. -/
theorem edgeFaceOf_found (g : Position) (hg : Injective g.ep) (a b x : Fin 12) (s : Fin 30)
    (hs : edgeSlot? a b = some s) (hx : x = edgeFace s.val 0 ∨ x = edgeFace s.val 1) :
    ∃ y, edgeFaceOf? g a b x = some y := by
  have hpc : edgeSlot a b = s := by simp [edgeSlot, hs]
  obtain ⟨s0, hs0⟩ := injective_surjective_fin g.ep hg s
  obtain ⟨sl, hl⟩ := lastIdx_some_of 30
    (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) s0.val s0.isLt
    (by simp [Nat.mod_eq_of_lt s0.isLt, hs0])
  have hsl : sl < 30 := lastIdx_lt 30 _ sl hl
  have hpsl := lastIdx_spec 30 _ sl hl
  simp only [decide_eq_true_eq, Nat.mod_eq_of_lt hsl] at hpsl
  have hslot : edgeSlot (edgeFace sl 0) (edgeFace sl 1) = ⟨sl, hsl⟩ := by
    simp [edgeSlot, edgeSlot?_faces ⟨sl, hsl⟩]
  unfold edgeFaceOf?
  rw [hpc]
  dsimp only
  rw [hl]
  dsimp only
  unfold edgeColoursAt
  rw [hslot]
  dsimp only
  rw [hpsl]
  exact pair_found _ _ x _ _ hx _ (by split <;> split <;> simp)

/-- The twist index `colour_on` reads: `colourOn` picks `c0`, `c1`, `c2` by it. -/
def kOf (face f1 f2 : Fin 12) (ori : Fin 3) : Nat :=
  ((if face = f2 then 2 else if face = f1 then 1 else 0) + 3 - ori.val) % 3

theorem colourOn_eq (face f1 f2 c0 c1 c2 : Fin 12) (ori : Fin 3) :
    colourOn face f1 f2 c0 c1 c2 ori =
      if kOf face f1 f2 ori = 0 then c0 else if kOf face f1 f2 ori = 1 then c1 else c2 := rfl

/-- On every corner slot and twist, the slot's three faces show all three colour indices
    (finite check, kernel `decide`). -/
theorem corner_cover : ∀ sl : Fin 20, ∀ ori : Fin 3, ∀ m : Fin 3,
    kOf (cornerFace sl.val 0) (cornerFace sl.val 1) (cornerFace sl.val 2) ori = m.val ∨
    kOf (cornerFace sl.val 1) (cornerFace sl.val 1) (cornerFace sl.val 2) ori = m.val ∨
    kOf (cornerFace sl.val 2) (cornerFace sl.val 1) (cornerFace sl.val 2) ori = m.val := by
  decide

theorem triple_found (x c0 c1 c2 u0 u1 u2 : Fin 12) (k0 k1 k2 : Nat)
    (hcov : ∀ m : Fin 3, k0 = m.val ∨ k1 = m.val ∨ k2 = m.val)
    (hx : x = c0 ∨ x = c1 ∨ x = c2) :
    ∃ y, (if (if k2 = 0 then c0 else if k2 = 1 then c1 else c2) = x then some u2 else
      if (if k1 = 0 then c0 else if k1 = 1 then c1 else c2) = x then some u1 else
      if (if k0 = 0 then c0 else if k0 = 1 then c1 else c2) = x then some u0 else none) =
        some y := by
  by_cases h2 : (if k2 = 0 then c0 else if k2 = 1 then c1 else c2) = x
  · exact ⟨u2, if_pos h2⟩
  by_cases h1 : (if k1 = 0 then c0 else if k1 = 1 then c1 else c2) = x
  · exact ⟨u1, by rw [if_neg h2, if_pos h1]⟩
  by_cases h0 : (if k0 = 0 then c0 else if k0 = 1 then c1 else c2) = x
  · exact ⟨u0, by rw [if_neg h2, if_neg h1, if_pos h0]⟩
  exfalso
  have key : ∀ m : Fin 3, ∀ k : Nat, k = m.val →
      (if k = 0 then c0 else if k = 1 then c1 else c2) =
        (if m.val = 0 then c0 else if m.val = 1 then c1 else c2) := by
    intro m k hk; rw [hk]
  rcases hx with hx | hx | hx
  · rcases hcov ⟨0, by decide⟩ with h | h | h
    · exact h0 (by rw [key _ _ h]; simp [hx])
    · exact h1 (by rw [key _ _ h]; simp [hx])
    · exact h2 (by rw [key _ _ h]; simp [hx])
  · rcases hcov ⟨1, by decide⟩ with h | h | h
    · exact h0 (by rw [key _ _ h]; simp [hx])
    · exact h1 (by rw [key _ _ h]; simp [hx])
    · exact h2 (by rw [key _ _ h]; simp [hx])
  · rcases hcov ⟨2, by decide⟩ with h | h | h
    · exact h0 (by rw [key _ _ h]; simp [hx])
    · exact h1 (by rw [key _ _ h]; simp [hx])
    · exact h2 (by rw [key _ _ h]; simp [hx])

/-- Corner found-invariant: bijective corner table, `x` a colour of the corner piece
    `(a, b, c)`. -/
theorem cornerFaceOf_found (g : Position) (hg : Injective g.cp) (a b c x : Fin 12) (t : Fin 20)
    (ht : cornerSlot? a b c = some t)
    (hx : x = cornerFace t.val 0 ∨ x = cornerFace t.val 1 ∨ x = cornerFace t.val 2) :
    ∃ y, cornerFaceOf? g a b c x = some y := by
  have hpc : cornerSlot a b c = t := by simp [cornerSlot, ht]
  obtain ⟨s0, hs0⟩ := injective_surjective_fin g.cp hg t
  obtain ⟨sl, hl⟩ := lastIdx_some_of 20
    (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) s0.val s0.isLt
    (by simp [Nat.mod_eq_of_lt s0.isLt, hs0])
  have hsl : sl < 20 := lastIdx_lt 20 _ sl hl
  unfold cornerFaceOf?
  rw [hpc]
  dsimp only
  rw [hl]
  dsimp only
  simp only [colourOn_eq]
  exact triple_found x _ _ _ _ _ _ _ _ _ (corner_cover ⟨sl, hsl⟩ _) hx

theorem tripleOk_edge (c : Fin 12) (k : Nat) (h : tripleOk c k = true) :
    ∃ s, edgeSlot? c (suitNbrs c k).1 = some s ∧
      (c = edgeFace s.val 0 ∨ c = edgeFace s.val 1) ∧
      ((suitNbrs c k).1 = edgeFace s.val 0 ∨ (suitNbrs c k).1 = edgeFace s.val 1) := by
  unfold tripleOk at h
  cases he : edgeSlot? c (suitNbrs c k).1 with
  | none => simp [he] at h
  | some s =>
    refine ⟨s, rfl, ?_⟩
    simp only [he, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1.symm, Or.inr h2.symm⟩
    · exact ⟨Or.inr h2.symm, Or.inl h1.symm⟩

theorem tripleOk_corner (c : Fin 12) (k : Nat) (h : tripleOk c k = true) :
    ∃ t, cornerSlot? c (suitNbrs c k).1 (suitNbrs c k).2 = some t ∧
      (c = cornerFace t.val 0 ∨ c = cornerFace t.val 1 ∨ c = cornerFace t.val 2) ∧
      ((suitNbrs c k).1 = cornerFace t.val 0 ∨ (suitNbrs c k).1 = cornerFace t.val 1 ∨
        (suitNbrs c k).1 = cornerFace t.val 2) := by
  unfold tripleOk at h
  cases he : cornerSlot? c (suitNbrs c k).1 (suitNbrs c k).2 with
  | none => simp [he] at h
  | some t =>
    refine ⟨t, rfl, ?_⟩
    simp only [he, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at h
    rcases h.2 with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩
    · exact ⟨Or.inl h1.symm, Or.inr (Or.inl h2.symm)⟩
    · exact ⟨Or.inr (Or.inr h3.symm), Or.inl h1.symm⟩
    · exact ⟨Or.inr (Or.inl h2.symm), Or.inr (Or.inr h3.symm)⟩

/-- Card naming, edge: for every colour `c` and suit amount `k ∈ 1..4`, on a position with
    a bijective edge table, the edge `(c, n)` has a slot and both its colours are found. -/
theorem card_edge_found (g : Position) (hg : Injective g.ep) (c : Fin 12) (k : Nat)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    ∃ s, edgeSlot? c (suitNbrs c k).1 = some s ∧
      (∃ y, edgeFaceOf? g c (suitNbrs c k).1 c = some y) ∧
      (∃ y, edgeFaceOf? g c (suitNbrs c k).1 (suitNbrs c k).1 = some y) := by
  have hk : k = (⟨k - 1, by omega⟩ : Fin 4).val + 1 := by simp; omega
  obtain ⟨s, hs, hc, hn⟩ := tripleOk_edge c k (by rw [hk]; exact triples_ok c _)
  exact ⟨s, hs, edgeFaceOf_found g hg _ _ _ s hs hc, edgeFaceOf_found g hg _ _ _ s hs hn⟩

/-- Card naming, corner: the corner `(c, n, n2)` has a slot and its `c`- and `n`-coloured
    stickers are found, on a position with a bijective corner table. -/
theorem card_corner_found (g : Position) (hg : Injective g.cp) (c : Fin 12) (k : Nat)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    ∃ t, cornerSlot? c (suitNbrs c k).1 (suitNbrs c k).2 = some t ∧
      (∃ y, cornerFaceOf? g c (suitNbrs c k).1 (suitNbrs c k).2 c = some y) ∧
      (∃ y, cornerFaceOf? g c (suitNbrs c k).1 (suitNbrs c k).2 (suitNbrs c k).1 = some y) := by
  have hk : k = (⟨k - 1, by omega⟩ : Fin 4).val + 1 := by simp; omega
  obtain ⟨t, ht, hc, hn⟩ := tripleOk_corner c k (by rw [hk]; exact triples_ok c _)
  exact ⟨t, ht, cornerFaceOf_found g hg _ _ _ _ t ht hc,
    cornerFaceOf_found g hg _ _ _ _ t ht hn⟩

end MegaDreifachV3.Link2
