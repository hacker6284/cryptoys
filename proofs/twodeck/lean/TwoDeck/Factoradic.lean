/-
  Factoradic / Lehmer unranking (SPEC §6 S5) and CTR counter_deck merge (S6).
  Correctness / combinatorial lemmas. Zero sorry.
-/
namespace TwoDeck

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl
@[simp] theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

theorem length_eraseIdx_lt (items : List α) (idx : Nat) (h : idx < items.length) :
    (items.eraseIdx idx).length < items.length := by
  rw [List.length_eraseIdx_of_lt h]; omega

theorem perm_getElem_eraseIdx (l : List α) (i : Nat) (hi : i < l.length) :
    List.Perm (l[i] :: l.eraseIdx i) l := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
  have htake : l.take i ++ l.drop i = l := List.take_append_drop i l
  have hmid : List.Perm (l[i] :: (l.take i ++ l.drop (i + 1)))
                        (l.take i ++ l[i] :: l.drop (i + 1)) :=
    (List.perm_middle (l₁ := l.take i) (a := l[i]) (l₂ := l.drop (i + 1))).symm
  refine hmid.trans ?_
  rw [← hdrop, htake]

def unrankPermGo {α} : Nat → List α → Nat → List α
  | 0, _, _ => []
  | _fuel + 1, [], _ => []
  | fuel + 1, items@(_ :: _), rank =>
      let idx := rank / factorial (items.length - 1)
      let rank' := rank % factorial (items.length - 1)
      if h : idx < items.length then
        items[idx] :: unrankPermGo fuel (items.eraseIdx idx) rank'
      else
        items

def unrankPerm {α} (items : List α) (rank : Nat) : List α :=
  let r := if items.length = 0 then 0 else rank % factorial items.length
  unrankPermGo items.length items r

theorem unrankPermGo_perm {α} (fuel : Nat) (items : List α) (rank : Nat)
    (hlen : items.length ≤ fuel) :
    List.Perm (unrankPermGo fuel items rank) items := by
  revert items rank
  induction fuel with
  | zero =>
      intro items rank hlen
      have : items = [] := by cases items <;> simp at hlen ⊢
      subst this; simp [unrankPermGo]
  | succ fuel ih =>
      intro items rank hlen
      match items with
      | [] => simp [unrankPermGo]
      | x :: xs =>
          dsimp only [unrankPermGo]
          split
          · next hidx =>
              let idx := rank / factorial ((x :: xs).length - 1)
              let rank' := rank % factorial ((x :: xs).length - 1)
              have hlen' : ((x :: xs).eraseIdx idx).length ≤ fuel := by
                have := length_eraseIdx_lt (x :: xs) idx hidx
                omega
              have ih' := ih ((x :: xs).eraseIdx idx) rank' hlen'
              exact (ih'.cons _).trans (perm_getElem_eraseIdx (x :: xs) idx hidx)
          · exact .refl _

/-- S5 (content): `unrankPerm` returns a permutation of `items`. -/
theorem unrankPerm_perm {α} (items : List α) (rank : Nat) :
    List.Perm (unrankPerm items rank) items := by
  unfold unrankPerm
  exact unrankPermGo_perm items.length items _ (Nat.le_refl _)

/-- S5 fragment: injective on Fin 3! via native_decide. -/
theorem unrankPerm_inj_3 :
    ∀ k m : Fin (factorial 3), k ≠ m →
      unrankPerm [0, 1, 2] k.val ≠ unrankPerm [0, 1, 2] m.val := by
  native_decide

def diamondCards : List Nat :=
  [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]

def chsCards : List Nat := List.range 39

def diamondPerm (i : Nat) : List Nat := unrankPerm diamondCards i

/-- CTR counter deck: nonce ‖ diamond_perm(ctr). -/
def counterDeck (nonceOrder : List Nat) (ctr : Nat) : List Nat :=
  nonceOrder ++ diamondPerm ctr

theorem diamondPerm_length (i : Nat) : (diamondPerm i).length = 13 := by
  simpa [diamondPerm] using (unrankPerm_perm diamondCards i).length_eq.symm ▸
    (rfl : diamondCards.length = 13)

theorem counterDeck_length (nonceOrder : List Nat) (ctr : Nat)
    (h : nonceOrder.length = 39) :
    (counterDeck nonceOrder ctr).length = 52 := by
  simp [counterDeck, h, diamondPerm_length]

/-- S6: consecutive counters agree on the nonce prefix. -/
theorem counterDeck_nonce_prefix (nonceOrder : List Nat) (i : Nat) :
    (counterDeck nonceOrder i).take nonceOrder.length = nonceOrder := by
  simp [counterDeck, List.take_left]

/-- S6: diamondPerm is a perm of AD..KD (hence Nodup if diamonds are). -/
theorem diamondPerm_perm (i : Nat) : List.Perm (diamondPerm i) diamondCards :=
  unrankPerm_perm diamondCards i

theorem diamondPerm_nodup (i : Nat) : (diamondPerm i).Nodup :=
  (diamondCards_nodup : diamondCards.Nodup).perm (diamondPerm_perm i).symm
where
  diamondCards_nodup : diamondCards.Nodup := by native_decide

end TwoDeck
