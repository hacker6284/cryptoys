/-
  PassKey = pass_to_key_cut_fallback — content preservation (SPEC §6 S3).
  Injectivity is not claimed (open; see proofs/twodeck/STONES.md S4).
-/
import TwoDeck.Basic
import TwoDeck.Rotate

namespace TwoDeck

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

def passKeyStep (hand key : List Nat) (c : Nat) : List Nat × List Nat :=
  let hand := maybeRotate hand c
  let p := maybeCut hand key c
  (p.1, c :: p.2)

theorem length_passKeyStep_fst (hand key : List Nat) (c : Nat) :
    (passKeyStep hand key c).1.length = hand.length := by
  simp only [passKeyStep, length_maybeCut_fst, length_maybeRotate]

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

end TwoDeck
