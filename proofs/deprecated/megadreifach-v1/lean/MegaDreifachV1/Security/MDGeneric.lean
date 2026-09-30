/-
  SECURITY (reduction, not a security claim).  Generic Merkle–Damgård
  collision / second-preimage extraction for an arbitrary compression
  function `dm : α → β → α` and IV `iv`.

  Chaining is written over the *reversed* block list (newest block first):
  `chR dm iv [bₖ, …, b₁] = dm (… (dm iv b₁) …) bₖ = [b₁,…,bₖ].foldl dm iv`.

  `findR` walks two reversed block lists from the end of the messages and
  returns the first pair of compression inputs `(h, b) ≠ (h', b')` whose
  outputs agree.  If it returns `none`, one reversed list is a prefix of
  the other (forward: one block list is a suffix of the other) and the
  leftover blocks chain back to the IV (an "IV preimage").

  Grip-rule status: INDEPENDENT of the grip rule and of E_m.  Everything
  here is generic in `dm` and `iv`; nothing needs repair if E_m changes.

  Zero sorry.  No native_decide.  Core Lean only.
-/

namespace MegaDreifachV1.Security

universe u v

variable {α : Type u} {β : Type v}

/-- Chaining value of a reversed block list (newest block first). -/
def chR (dm : α → β → α) (iv : α) : List β → α
  | [] => iv
  | b :: r => dm (chR dm iv r) b

theorem chR_eq_foldl (dm : α → β → α) (iv : α) (bs : List β) :
    chR dm iv bs = bs.reverse.foldl dm iv := by
  induction bs with
  | nil => rfl
  | cons b r ih => simp [chR, ih, List.foldl_append]

/-- Forward MD fold as `chR` of the reversed list. -/
theorem foldl_eq_chR (dm : α → β → α) (iv : α) (bs : List β) :
    bs.foldl dm iv = chR dm iv bs.reverse := by
  rw [chR_eq_foldl, List.reverse_reverse]

/-- The compression inputs along a reversed block list: `(h_{i-1}, b_i)`. -/
def pairsR (dm : α → β → α) (iv : α) : List β → List (α × β)
  | [] => []
  | b :: r => (chR dm iv r, b) :: pairsR dm iv r

/-- A pair of compression inputs. -/
structure CompPair (α : Type u) (β : Type v) where
  h1 : α
  b1 : β
  h2 : α
  b2 : β

/-- A compression collision: distinct inputs, equal outputs. -/
def CompPair.IsCollision (dm : α → β → α) (c : CompPair α β) : Prop :=
  (c.h1 ≠ c.h2 ∨ c.b1 ≠ c.b2) ∧ dm c.h1 c.b1 = dm c.h2 c.b2

section Find

variable [DecidableEq α] [DecidableEq β]

/-- The MD extractor.  Walk both reversed block lists in lock step; stop at
    the first step whose compression inputs differ. -/
def findR (dm : α → β → α) (iv : α) : List β → List β → Option (CompPair α β)
  | b :: r, b' :: r' =>
      if chR dm iv r = chR dm iv r' ∧ b = b' then findR dm iv r r'
      else some ⟨chR dm iv r, b, chR dm iv r', b'⟩
  | _, _ => none

/-- `findR` correctness, `some` branch: a genuine compression collision, whose
    two sides are compression inputs of the first and second chain respectively. -/
theorem findR_some (dm : α → β → α) (iv : α) :
    ∀ (rx ry : List β) (c : CompPair α β),
      chR dm iv rx = chR dm iv ry → findR dm iv rx ry = some c →
      c.IsCollision dm ∧ (c.h1, c.b1) ∈ pairsR dm iv rx ∧ (c.h2, c.b2) ∈ pairsR dm iv ry
  | [], _, c, _, hf => by simp [findR] at hf
  | _ :: _, [], c, _, hf => by simp [findR] at hf
  | b :: r, b' :: r', c, heq, hf => by
      simp only [findR] at hf
      split at hf
      · next hc =>
          have ⟨h1, h2, h3⟩ := findR_some dm iv r r' c hc.1 hf
          exact ⟨h1, List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
      · next hc =>
          cases hf
          refine ⟨⟨?_, heq⟩, List.mem_cons_self _ _, List.mem_cons_self _ _⟩
          dsimp only
          by_cases h1 : chR dm iv r = chR dm iv r'
          · right; intro h2; exact hc ⟨h1, h2⟩
          · left; exact h1

/-- `findR` correctness, `none` branch: the reversed lists share a prefix `p`,
    one of the leftovers is empty, and the leftovers chain to the same value
    (so the non-empty leftover, if any, chains back to `iv`). -/
theorem findR_none (dm : α → β → α) (iv : α) :
    ∀ (rx ry : List β),
      chR dm iv rx = chR dm iv ry → findR dm iv rx ry = none →
      ∃ p sx sy : List β, rx = p ++ sx ∧ ry = p ++ sy ∧ (sx = [] ∨ sy = []) ∧
        chR dm iv sx = chR dm iv sy
  | [], ry, heq, _ => ⟨[], [], ry, rfl, rfl, Or.inl rfl, heq⟩
  | b :: r, [], heq, _ => ⟨[], b :: r, [], rfl, rfl, Or.inr rfl, heq⟩
  | b :: r, b' :: r', _, hf => by
      simp only [findR] at hf
      split at hf
      · next hc =>
          obtain ⟨p, sx, sy, h1, h2, h3, h4⟩ := findR_none dm iv r r' hc.1 hf
          refine ⟨b :: p, sx, sy, ?_, ?_, h3, h4⟩
          · rw [h1]; rfl
          · rw [h2, hc.2]; rfl
      · cases hf

/-- Generic MD reduction (reversed-list form).  Equal chaining values from two
    reversed block lists, neither a prefix of the other, yield a compression
    collision, found by `findR`. -/
theorem findR_collision (dm : α → β → α) (iv : α) (rx ry : List β)
    (heq : chR dm iv rx = chR dm iv ry)
    (hxy : ¬ rx <+: ry) (hyx : ¬ ry <+: rx) :
    ∃ c, findR dm iv rx ry = some c ∧ c.IsCollision dm ∧
      (c.h1, c.b1) ∈ pairsR dm iv rx ∧ (c.h2, c.b2) ∈ pairsR dm iv ry := by
  cases hf : findR dm iv rx ry with
  | some c => exact ⟨c, rfl, findR_some dm iv rx ry c heq hf⟩
  | none =>
      exfalso
      obtain ⟨p, sx, sy, h1, h2, h3, _⟩ := findR_none dm iv rx ry heq hf
      rcases h3 with h3 | h3
      · subst h3; apply hxy; rw [h1, h2, List.append_nil]; exact ⟨sy, rfl⟩
      · subst h3; apply hyx; rw [h1, h2, List.append_nil]; exact ⟨sx, rfl⟩

/-- Without MD strengthening: the only other outcome is an IV preimage, i.e. a
    non-empty block list whose chain returns to `iv`, with the two messages'
    block lists suffix-related. -/
theorem findR_collision_or_iv (dm : α → β → α) (iv : α) (rx ry : List β)
    (heq : chR dm iv rx = chR dm iv ry) (hne : rx ≠ ry) :
    (∃ c, findR dm iv rx ry = some c ∧ c.IsCollision dm) ∨
    (∃ p s : List β, s ≠ [] ∧ chR dm iv s = iv ∧
      ((rx = p ∧ ry = p ++ s) ∨ (ry = p ∧ rx = p ++ s))) := by
  cases hf : findR dm iv rx ry with
  | some c => exact Or.inl ⟨c, rfl, (findR_some dm iv rx ry c heq hf).1⟩
  | none =>
      right
      obtain ⟨p, sx, sy, h1, h2, h3, h4⟩ := findR_none dm iv rx ry heq hf
      rcases h3 with h3 | h3
      · subst h3
        have hsy : sy ≠ [] := by
          intro h; subst h; exact hne (by rw [h1, h2])
        exact ⟨p, sy, hsy, h4.symm, Or.inl ⟨by rw [h1, List.append_nil], h2⟩⟩
      · subst h3
        have hsx : sx ≠ [] := by
          intro h; subst h; exact hne (by rw [h1, h2])
        exact ⟨p, sx, hsx, h4, Or.inr ⟨by rw [h2, List.append_nil], h1⟩⟩

/-- Forward-list form: equal MD chains of two block lists, neither a suffix of
    the other, give a compression collision between a compression input of
    the first chain and one of the second. -/
theorem md_collision (dm : α → β → α) (iv : α) (xs ys : List β)
    (heq : xs.foldl dm iv = ys.foldl dm iv)
    (hxy : ¬ xs <:+ ys) (hyx : ¬ ys <:+ xs) :
    ∃ c, findR dm iv xs.reverse ys.reverse = some c ∧ c.IsCollision dm ∧
      (c.h1, c.b1) ∈ pairsR dm iv xs.reverse ∧ (c.h2, c.b2) ∈ pairsR dm iv ys.reverse := by
  rw [foldl_eq_chR, foldl_eq_chR] at heq
  refine findR_collision dm iv _ _ heq ?_ ?_
  · rw [List.reverse_prefix]; exact hxy
  · rw [List.reverse_prefix]; exact hyx

end Find

theorem mem_pairsR {α β : Type} (dm : α → β → α) (iv : α) :
    ∀ (r : List β) (h : α) (b : β), (h, b) ∈ pairsR dm iv r →
      b ∈ r ∧ ∃ s, h = chR dm iv s ∧ s <:+ r
  | [], _, _, hm => by simp [pairsR] at hm
  | c :: r, h, b, hm => by
      simp only [pairsR, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨h1, h2⟩ | hm
      · rw [h1, h2]
        exact ⟨List.mem_cons_self _ _, r, rfl, List.suffix_cons _ _⟩
      · obtain ⟨hb, s, hs, hsuf⟩ := mem_pairsR dm iv r h b hm
        exact ⟨List.mem_cons_of_mem _ hb, s, hs, List.IsSuffix.trans hsuf (List.suffix_cons _ _)⟩

end MegaDreifachV1.Security
