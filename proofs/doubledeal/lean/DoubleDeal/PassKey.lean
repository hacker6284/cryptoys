/-
  PassKey = pass_to_key_cut_fallback — content preservation (SPEC §6 S3)
  and a constructive inverse (SPEC §6 S4). Cycle structure is not proved.
-/
import DoubleDeal.Basic
import DoubleDeal.Rotate

/- Lean 4.14 prelude has no `Function.LeftInverse` (that lives in Mathlib / later Init). -/
namespace Function
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def RightInverse (g : β → α) (f : α → β) : Prop := LeftInverse f g
end Function

namespace DoubleDeal

def rotateLeft (xs : List α) (n : Nat) : List α := rotL xs n

def cutProper (xs : List α) (r : Nat) : List α :=
  if r < xs.length then rotL xs r else xs

theorem cutProper_perm (xs : List α) (r : Nat) :
    List.Perm (cutProper xs r) xs := by
  unfold cutProper; split <;> first | exact rotL_perm xs r | exact .refl _

theorem length_cutProper (xs : List α) (r : Nat) :
    (cutProper xs r).length = xs.length := by
  unfold cutProper; split <;> first | exact length_rotL xs r | rfl

def maybeRotate (hand : List Nat) (c : Nat) : List Nat :=
  if hand.length = 0 then hand else rotateLeft hand (suit c % hand.length)

theorem maybeRotate_perm (hand : List Nat) (c : Nat) :
    List.Perm (maybeRotate hand c) hand := by
  unfold maybeRotate; split <;> first | exact .refl _ | exact rotL_perm hand _

theorem length_maybeRotate (hand : List Nat) (c : Nat) :
    (maybeRotate hand c).length = hand.length := by
  unfold maybeRotate; split <;> first | rfl | exact length_rotL hand _

def maybeCut (hand key : List Nat) (c : Nat) : List Nat × List Nat :=
  if _h : 0 < hand.length ∧ rank c < hand.length then (cutProper hand (rank c), key)
  else if _h2 : 0 < key.length ∧ rank c < key.length then (hand, cutProper key (rank c))
  else (hand, key)

theorem maybeCut_perm (hand key : List Nat) (c : Nat) :
    List.Perm ((maybeCut hand key c).1 ++ (maybeCut hand key c).2) (hand ++ key) := by
  unfold maybeCut
  split
  · exact (cutProper_perm hand (rank c)).append (.refl key)
  · split
    · exact (List.Perm.refl hand).append (cutProper_perm key (rank c))
    · exact .refl _

theorem length_maybeCut_fst (hand key : List Nat) (c : Nat) :
    (maybeCut hand key c).1.length = hand.length := by
  unfold maybeCut
  split
  · exact length_cutProper _ _
  · split <;> rfl

theorem length_maybeCut_snd (hand key : List Nat) (c : Nat) :
    (maybeCut hand key c).2.length = key.length := by
  unfold maybeCut
  split
  · rfl
  · split
    · exact length_cutProper _ _
    · rfl

def passKeyStep (hand key : List Nat) (c : Nat) : List Nat × List Nat :=
  let hand := maybeRotate hand c
  let p := maybeCut hand key c
  (p.1, c :: p.2)

theorem length_passKeyStep_fst (hand key : List Nat) (c : Nat) :
    (passKeyStep hand key c).1.length = hand.length := by
  simp only [passKeyStep, length_maybeCut_fst, length_maybeRotate]

theorem length_passKeyStep_snd (hand key : List Nat) (c : Nat) :
    (passKeyStep hand key c).2.length = key.length + 1 := by
  simp only [passKeyStep, length_maybeCut_snd, List.length_cons]

theorem passKeyStep_perm (hand key : List Nat) (c : Nat) :
    List.Perm ((passKeyStep hand key c).1 ++ (passKeyStep hand key c).2)
              (c :: hand ++ key) := by
  dsimp [passKeyStep]
  have hr := maybeRotate_perm hand c
  have hc := maybeCut_perm (maybeRotate hand c) key c
  have hmid : List.Perm
      ((maybeCut (maybeRotate hand c) key c).1 ++
        c :: (maybeCut (maybeRotate hand c) key c).2)
      (c :: ((maybeCut (maybeRotate hand c) key c).1 ++
        (maybeCut (maybeRotate hand c) key c).2)) := List.perm_middle
  refine hmid.trans ?_
  refine (hc.cons c).trans ?_
  refine ((hr.append (List.Perm.refl key)).cons c).trans ?_
  simp [List.cons_append]

/-- Fuel-indexed PassKey recursion (avoids structural-recursion friction). -/
def passKeyGoN : Nat → List Nat → List Nat → List Nat
  | 0, _, key => key
  | _n + 1, [], key => key
  | n + 1, c :: rest, key =>
      let p := passKeyStep rest key c
      passKeyGoN n p.1 p.2

def passToKeyCutFallback (deck : List Nat) : List Nat :=
  passKeyGoN deck.length deck []

theorem passKeyGoN_perm :
    ∀ (n : Nat) (hand key : List Nat),
      hand.length ≤ n →
      List.Perm (passKeyGoN n hand key) (hand ++ key)
  | 0, hand, key, hlen => by
      have : hand = [] := by cases hand <;> simp at hlen ⊢
      subst this; simp [passKeyGoN]
  | n + 1, [], key, _ => by simp [passKeyGoN]
  | n + 1, c :: rest, key, hlen => by
      simp only [passKeyGoN]
      have hs := passKeyStep_perm rest key c
      have hlen' : (passKeyStep rest key c).1.length ≤ n := by
        rw [length_passKeyStep_fst]
        simp at hlen; omega
      have ih := passKeyGoN_perm n (passKeyStep rest key c).1 (passKeyStep rest key c).2 hlen'
      exact ih.trans hs

/-- S3: PassKey preserves card multiset (`List.Perm`). -/
theorem passToKeyCutFallback_perm (deck : List Nat) :
    List.Perm (passToKeyCutFallback deck) deck := by
  simpa [passToKeyCutFallback] using
    passKeyGoN_perm deck.length deck [] (Nat.le_refl _)

theorem passKeyGoN_length (n : Nat) (hand key : List Nat) (h : hand.length ≤ n) :
    (passKeyGoN n hand key).length = hand.length + key.length := by
  have p := passKeyGoN_perm n hand key h
  simpa [List.length_append] using p.length_eq

/-! ## S4: constructive inverse

Each forward step is `maybeRotate` then `maybeCut` then "controller on top of key".
Branching uses only the controller and the two pile lengths, so the same
predicates invert the step. `F` is the composition of those bijections.
-/

def cutProperInv (xs : List α) (r : Nat) : List α :=
  if r < xs.length then rotR xs r else xs

theorem length_cutProperInv (xs : List α) (r : Nat) :
    (cutProperInv xs r).length = xs.length := by
  unfold cutProperInv; split <;> first | exact length_rotR xs r | rfl

theorem cutProperInv_cutProper (xs : List α) (r : Nat) :
    cutProperInv (cutProper xs r) r = xs := by
  unfold cutProper cutProperInv
  split
  · next h =>
    have hlen : (rotL xs r).length = xs.length := length_rotL xs r
    simp only [hlen, h, ↓reduceIte]
    exact rotR_rotL xs r
  · next h =>
    simp only [h, ↓reduceIte]

theorem cutProper_cutProperInv (xs : List α) (r : Nat) :
    cutProper (cutProperInv xs r) r = xs := by
  unfold cutProperInv
  split
  · next h =>
    have hlen : (rotR xs r).length = xs.length := length_rotR xs r
    unfold cutProper
    simp only [hlen, h, ↓reduceIte]
    exact rotL_rotR xs r
  · next h =>
    unfold cutProper
    simp only [h, ↓reduceIte]

def maybeRotateInv (hand : List Nat) (c : Nat) : List Nat :=
  if hand.length = 0 then hand else rotR hand (suit c % hand.length)

theorem length_maybeRotateInv (hand : List Nat) (c : Nat) :
    (maybeRotateInv hand c).length = hand.length := by
  unfold maybeRotateInv; split <;> first | rfl | exact length_rotR hand _

theorem maybeRotateInv_maybeRotate (hand : List Nat) (c : Nat) :
    maybeRotateInv (maybeRotate hand c) c = hand := by
  unfold maybeRotate
  split
  · next h => simp [maybeRotateInv, h]
  · next h =>
    simp only [rotateLeft, maybeRotateInv]
    have hlen : (rotL hand (suit c % hand.length)).length = hand.length :=
      length_rotL hand _
    have hne : ¬ (rotL hand (suit c % hand.length)).length = 0 := by
      rw [hlen]; exact h
    simp only [hne, ↓reduceIte, hlen, h]
    exact rotR_rotL hand (suit c % hand.length)

theorem maybeRotate_maybeRotateInv (hand : List Nat) (c : Nat) :
    maybeRotate (maybeRotateInv hand c) c = hand := by
  unfold maybeRotateInv
  split
  · next h => simp [maybeRotate, h]
  · next h =>
    simp only [maybeRotate, rotateLeft]
    have hlen : (rotR hand (suit c % hand.length)).length = hand.length :=
      length_rotR hand _
    have hne : ¬ (rotR hand (suit c % hand.length)).length = 0 := by
      rw [hlen]; exact h
    simp only [hne, ↓reduceIte, hlen, h]
    exact rotL_rotR hand (suit c % hand.length)

/-- Inverse of `maybeCut`. Lengths are invariant, so the same predicates fire. -/
def maybeCutInv (hand key : List Nat) (c : Nat) : List Nat × List Nat :=
  if _h : 0 < hand.length ∧ rank c < hand.length then (cutProperInv hand (rank c), key)
  else if _h2 : 0 < key.length ∧ rank c < key.length then (hand, cutProperInv key (rank c))
  else (hand, key)

theorem length_maybeCutInv_fst (hand key : List Nat) (c : Nat) :
    (maybeCutInv hand key c).1.length = hand.length := by
  unfold maybeCutInv
  split
  · exact length_cutProperInv _ _
  · split <;> rfl

theorem length_maybeCutInv_snd (hand key : List Nat) (c : Nat) :
    (maybeCutInv hand key c).2.length = key.length := by
  unfold maybeCutInv
  split
  · rfl
  · split
    · exact length_cutProperInv _ _
    · rfl

theorem maybeCutInv_maybeCut (hand key : List Nat) (c : Nat) :
    maybeCutInv (maybeCut hand key c).1 (maybeCut hand key c).2 c = (hand, key) := by
  unfold maybeCut
  split
  · next h =>
    have hlen := length_cutProper hand (rank c)
    unfold maybeCutInv
    have h' : 0 < (cutProper hand (rank c)).length ∧
        rank c < (cutProper hand (rank c)).length := by
      rw [hlen]; exact h
    rw [dif_pos h', cutProperInv_cutProper]
  · next hnot =>
    split
    · next h2 =>
      have hlen := length_cutProper key (rank c)
      unfold maybeCutInv
      rw [dif_neg hnot]
      have h2' : 0 < (cutProper key (rank c)).length ∧
          rank c < (cutProper key (rank c)).length := by
        rw [hlen]; exact h2
      rw [dif_pos h2', cutProperInv_cutProper]
    · next h2not =>
      unfold maybeCutInv
      rw [dif_neg hnot, dif_neg h2not]

theorem maybeCut_maybeCutInv (hand key : List Nat) (c : Nat) :
    maybeCut (maybeCutInv hand key c).1 (maybeCutInv hand key c).2 c = (hand, key) := by
  unfold maybeCutInv
  split
  · next h =>
    have hlen := length_cutProperInv hand (rank c)
    unfold maybeCut
    have h' : 0 < (cutProperInv hand (rank c)).length ∧
        rank c < (cutProperInv hand (rank c)).length := by
      rw [hlen]; exact h
    rw [dif_pos h', cutProper_cutProperInv]
  · next hnot =>
    split
    · next h2 =>
      have hlen := length_cutProperInv key (rank c)
      unfold maybeCut
      rw [dif_neg hnot]
      have h2' : 0 < (cutProperInv key (rank c)).length ∧
          rank c < (cutProperInv key (rank c)).length := by
        rw [hlen]; exact h2
      rw [dif_pos h2', cutProper_cutProperInv]
    · next h2not =>
      unfold maybeCut
      rw [dif_neg hnot, dif_neg h2not]

/-- Undo one PassKey step: pop the controller off the key, undo cut, undo suit rotate. -/
def invPassKeyStep (hand key : List Nat) : List Nat × List Nat :=
  match key with
  | [] => (hand, [])
  | c :: rest =>
      let p := maybeCutInv hand rest c
      (c :: maybeRotateInv p.1 c, p.2)

theorem length_invPassKeyStep_fst (hand : List Nat) (c : Nat) (rest : List Nat) :
    (invPassKeyStep hand (c :: rest)).1.length = hand.length + 1 := by
  simp [invPassKeyStep, length_maybeRotateInv, length_maybeCutInv_fst]

theorem length_invPassKeyStep_snd (hand : List Nat) (c : Nat) (rest : List Nat) :
    (invPassKeyStep hand (c :: rest)).2.length = rest.length := by
  simp [invPassKeyStep, length_maybeCutInv_snd]

/-- Per-step left inverse: invert after `passKeyStep` recovers `(c :: hand, key)`. -/
theorem invPassKeyStep_passKeyStep (hand key : List Nat) (c : Nat) :
    invPassKeyStep (passKeyStep hand key c).1 (passKeyStep hand key c).2
      = (c :: hand, key) := by
  simp only [passKeyStep]
  change invPassKeyStep
      (maybeCut (maybeRotate hand c) key c).1
      (c :: (maybeCut (maybeRotate hand c) key c).2) = (c :: hand, key)
  simp only [invPassKeyStep]
  have hc := maybeCutInv_maybeCut (maybeRotate hand c) key c
  simp [hc, maybeRotateInv_maybeRotate]

/-- Per-step right inverse on a nonempty key pile `c :: rest`. -/
theorem passKeyStep_invPassKeyStep (hand : List Nat) (c : Nat) (rest : List Nat) :
    passKeyStep (maybeRotateInv (maybeCutInv hand rest c).1 c)
        (maybeCutInv hand rest c).2 c
      = (hand, c :: rest) := by
  simp only [passKeyStep]
  have hr := maybeRotate_maybeRotateInv (maybeCutInv hand rest c).1 c
  simp only [hr]
  have hc := maybeCut_maybeCutInv hand rest c
  simp [hc]

/-- Fuel-indexed inverse walk (key pile shrinks). -/
def passKeyInvGoN : Nat → List Nat → List Nat → List Nat
  | 0, _, hand => hand
  | _n + 1, [], hand => hand
  | n + 1, c :: rest, hand =>
      let p := invPassKeyStep hand (c :: rest)
      passKeyInvGoN n p.2 p.1

def passToKeyCutFallbackInv (out : List Nat) : List Nat :=
  passKeyInvGoN out.length out []

theorem passKeyInvGoN_length :
    ∀ (n : Nat) (key hand : List Nat),
      key.length ≤ n →
      (passKeyInvGoN n key hand).length = key.length + hand.length
  | 0, key, hand, hlen => by
      have : key = [] := by cases key <;> simp at hlen ⊢
      subst this; simp [passKeyInvGoN]
  | n + 1, [], hand, _ => by simp [passKeyInvGoN]
  | n + 1, c :: rest, hand, hlen => by
      simp only [passKeyInvGoN]
      have hlen' : (invPassKeyStep hand (c :: rest)).2.length ≤ n := by
        rw [length_invPassKeyStep_snd]
        simp [List.length_cons] at hlen; omega
      have ih := passKeyInvGoN_length n (invPassKeyStep hand (c :: rest)).2
        (invPassKeyStep hand (c :: rest)).1 hlen'
      rw [ih, length_invPassKeyStep_snd, length_invPassKeyStep_fst]
      simp [List.length_cons]; omega

theorem passKeyInvGoN_cons (c : Nat) (rest hand : List Nat) :
    passKeyInvGoN (c :: rest).length (c :: rest) hand =
      let p := invPassKeyStep hand (c :: rest)
      passKeyInvGoN rest.length p.2 p.1 :=
  rfl

/-- Lifting the per-step left inverse: inverting the finished key recovers `hand`. -/
theorem passKeyInvGoN_passKeyGoN :
    ∀ (n : Nat) (hand key : List Nat),
      hand.length ≤ n →
      passKeyInvGoN (hand.length + key.length) (passKeyGoN n hand key) [] =
        passKeyInvGoN key.length key hand
  | 0, hand, key, hlen => by
      have : hand = [] := by cases hand <;> simp at hlen ⊢
      subst this
      simp [passKeyGoN]
  | n + 1, [], key, _ => by
      simp [passKeyGoN]
  | n + 1, c :: rest, key, hlen => by
      simp only [passKeyGoN]
      have hlen' : (passKeyStep rest key c).1.length ≤ n := by
        rw [length_passKeyStep_fst]
        simp [List.length_cons] at hlen; omega
      have ih := passKeyInvGoN_passKeyGoN n
        (passKeyStep rest key c).1 (passKeyStep rest key c).2 hlen'
      have hfuel :
          (c :: rest).length + key.length =
            (passKeyStep rest key c).1.length + (passKeyStep rest key c).2.length := by
        rw [length_passKeyStep_fst, length_passKeyStep_snd]
        simp [List.length_cons]; omega
      rw [hfuel, ih]
      -- p.2 is `c :: kAfter`; invert that cons
      let kAfter := (maybeCut (maybeRotate rest c) key c).2
      have hcons : (passKeyStep rest key c).2 = c :: kAfter := rfl
      rw [hcons, passKeyInvGoN_cons]
      have hinv : invPassKeyStep (passKeyStep rest key c).1 (c :: kAfter) =
          (c :: rest, key) := by
        simpa [hcons] using invPassKeyStep_passKeyStep rest key c
      rw [hinv]
      simp [kAfter, length_maybeCut_snd]

/-- Lifting the per-step right inverse. -/
theorem passKeyGoN_passKeyInvGoN :
    ∀ (n : Nat) (key hand : List Nat),
      key.length ≤ n →
      passKeyGoN (hand.length + key.length) (passKeyInvGoN n key hand) [] =
        passKeyGoN hand.length hand key
  | 0, key, hand, hlen => by
      have : key = [] := by cases key <;> simp at hlen ⊢
      subst this
      simp [passKeyInvGoN]
  | n + 1, [], hand, _ => by
      simp [passKeyInvGoN]
  | n + 1, c :: rest, hand, hlen => by
      simp only [passKeyInvGoN]
      have hlen' : (invPassKeyStep hand (c :: rest)).2.length ≤ n := by
        rw [length_invPassKeyStep_snd]
        simp at hlen; omega
      have ih := passKeyGoN_passKeyInvGoN n
        (invPassKeyStep hand (c :: rest)).2
        (invPassKeyStep hand (c :: rest)).1 hlen'
      have hfuel :
          hand.length + (c :: rest).length =
            (invPassKeyStep hand (c :: rest)).1.length +
              (invPassKeyStep hand (c :: rest)).2.length := by
        rw [length_invPassKeyStep_fst, length_invPassKeyStep_snd]
        simp; omega
      rw [hfuel, ih]
      -- go one reconstructed controller, then the right-inverse step
      have hstep := passKeyStep_invPassKeyStep hand c rest
      simp only [invPassKeyStep] at hstep ⊢
      -- (invPassKeyStep hand (c::rest)).1 = c :: maybeRotateInv ...
      -- passKeyGoN on that cons unfolds
      change passKeyGoN
          (c :: maybeRotateInv (maybeCutInv hand rest c).1 c).length
          (c :: maybeRotateInv (maybeCutInv hand rest c).1 c)
          (maybeCutInv hand rest c).2 =
        passKeyGoN hand.length hand (c :: rest)
      simp only [passKeyGoN]
      have hlenh :
          (maybeRotateInv (maybeCutInv hand rest c).1 c).length = hand.length := by
        rw [length_maybeRotateInv, length_maybeCutInv_fst]
      rw [hlenh, hstep]

/-- S4: `F_inv ∘ F = id`. -/
theorem passToKeyCutFallback_leftInverse (d : List Nat) :
    passToKeyCutFallbackInv (passToKeyCutFallback d) = d := by
  unfold passToKeyCutFallbackInv passToKeyCutFallback
  have hlen : (passKeyGoN d.length d []).length = d.length := by
    simpa using passKeyGoN_length d.length d [] (Nat.le_refl _)
  rw [hlen]
  have h := passKeyInvGoN_passKeyGoN d.length d [] (Nat.le_refl _)
  simpa [passKeyInvGoN] using h

/-- S4: `F ∘ F_inv = id`. -/
theorem passToKeyCutFallback_rightInverse (d : List Nat) :
    passToKeyCutFallback (passToKeyCutFallbackInv d) = d := by
  unfold passToKeyCutFallback passToKeyCutFallbackInv
  have hlen : (passKeyInvGoN d.length d []).length = d.length := by
    simpa using passKeyInvGoN_length d.length d [] (Nat.le_refl _)
  rw [show (passKeyInvGoN d.length d []).length = d.length + 0 from by
        simpa using passKeyInvGoN_length d.length d [] (Nat.le_refl _)]
  have h := passKeyGoN_passKeyInvGoN d.length d [] (Nat.le_refl _)
  simpa [passKeyGoN] using h

theorem passKey_leftInverse :
    Function.LeftInverse passToKeyCutFallbackInv passToKeyCutFallback :=
  passToKeyCutFallback_leftInverse

theorem passKey_rightInverse :
    Function.RightInverse passToKeyCutFallbackInv passToKeyCutFallback :=
  passToKeyCutFallback_rightInverse

/-- S4: PassKey is injective on lists (hence on \(S_{52}\)). -/
theorem passKey_injective {d₁ d₂ : List Nat}
    (h : passToKeyCutFallback d₁ = passToKeyCutFallback d₂) : d₁ = d₂ := by
  rw [← passToKeyCutFallback_leftInverse d₁, ← passToKeyCutFallback_leftInverse d₂, h]

end DoubleDeal
