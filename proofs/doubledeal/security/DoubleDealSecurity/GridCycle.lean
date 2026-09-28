/-
  T1: GridCycle (MixColumns) versus relabellings: only the identity commutes,
  for the live v11 walk and for the frozen v8 model (`V8`).
-/
import DoubleDealSecurity.SumRanks
import DoubleDealSecurity.Walk

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## 3. GridCycle (MixColumns) commutes with no nontrivial σ

GridCycle is value-dependent in a different way: card `n` is placed at a seat
computed from card `n−1`'s (suit, rank) step, the current occupancy, and the
overflow marker `t` (v11: the step is taken from the ghost finger, the last
target; a blocked placement is scanned by the blocker's suit and rank from the
target, and the finger moves on by the blocker's step; v9/v10 scanned from the
blocked target's column). So on one deck, GridCycle commutes with σ exactly when the seat walk of
`σ·m` equals the walk of `m` (`mixColumns_rel_iff_walk`). Over all decks this
forces σ = id: the second card's seat is an injective function of the first
card, except that K♣ (step (0,0): the second target is the start seat (2,0), blocked by K♣
itself, and the scan sends the card to (0,0)) and K♠ (step
(2,0) from (2,0), lands on (0,0)) collide. -/

/-- Seat of card `n` in the GridCycle walk of `hand`. -/
def walkSeat (hand : Fin 52 → Nat) (n : Nat) : Fin 4 × Fin 13 :=
  (chooseSeat! (placeN hand n).2).1

/-- Seat of the second card as a function of the first card. -/
def seat2 (c : Nat) : Fin 4 × Fin 13 := (chooseSeat! (advance initWalk c asStart (0, asStart))).1

theorem walkSeat_zero (hand : Fin 52 → Nat) : walkSeat hand 0 = asStart := rfl

theorem walkSeat_one (hand : Fin 52 → Nat) : walkSeat hand 1 = seat2 (hand ⟨0, by decide⟩) := rfl

/-- (PROVED, kernel `decide!`) The second seat is injective in the first card,
    except for the single collision K♣/K♠. -/
theorem seat2_inj : ∀ a b : Fin 52, seat2 a.val = seat2 b.val →
    a = b ∨ (a = KC ∧ b = KS) ∨ (a = KS ∧ b = KC) := by
  decide!

theorem rel_scoopRowMajor (σ : Relabel) (g : NatGrid) :
    rel σ (scoopRowMajor g) = scoopRowMajor (relG σ g) := rfl

/-- (PROVED) Generic walk: on a well-formed deck, placing-then-scooping commutes
    with σ iff the seat walk is unchanged. Card `n` sits at seat `n`
    (`gridW_at_seat`), the 52 seats cover the grid (`seatW_surj`), and the cards
    are distinct. -/
theorem walkW_rel_iff (ch : Chooser) (hch : FreeChooser ch) (σ : Relabel)
    (m : Fin 52 → Nat) (hm : IsDeck m) :
    scoopRowMajor (gridW ch (rel σ m)) = rel σ (scoopRowMajor (gridW ch m)) ↔
      ∀ n < 52, seatW ch (rel σ m) n = seatW ch m n := by
  rw [rel_scoopRowMajor]
  constructor
  · intro h n hn
    have hg : gridW ch (rel σ m) = relG σ (gridW ch m) := by
      have := congrArg layRowMajor h
      rwa [lay_scoop_rowMajor, lay_scoop_rowMajor] at this
    obtain ⟨k, hk⟩ := seatW_surj ch hch m (seatW ch (rel σ m) n)
    have h1 := gridW_at_seat ch hch (rel σ m) ⟨n, hn⟩
    rw [hg, ← hk] at h1
    have h2 := gridW_at_seat ch hch m k
    simp only [relG, h2, rel] at h1
    have hkn := hm.2 (σ.app_inj h1)
    rw [← hk, hkn]
  · intro h
    suffices hg : gridW ch (rel σ m) = relG σ (gridW ch m) by rw [hg]
    funext r c
    obtain ⟨k, hk⟩ := seatW_surj ch hch m (r, c)
    have h1 := gridW_at_seat ch hch (rel σ m) k
    rw [h k.val k.isLt, hk] at h1
    have h2 := gridW_at_seat ch hch m k
    rw [hk] at h2
    simp only [relG]
    simp only at h1 h2
    rw [h1, h2]; rfl

theorem walkSeat_eq (hand : Fin 52 → Nat) (n : Nat) :
    walkSeat hand n = seatW chooseSeat! hand n := by
  simp only [walkSeat, seatW, placeN_eq_placeW]

theorem mixColumns_eq (hand : Fin 52 → Nat) :
    mixColumns hand = scoopRowMajor (gridW chooseSeat! hand) := by
  simp only [mixColumns, placedGrid, gridW, placeN_eq_placeW]

/-- (PROVED) On a well-formed deck, GridCycle commutes with σ iff the seat walk
    is unchanged. -/
theorem mixColumns_rel_iff_walk (σ : Relabel) (m : Fin 52 → Nat) (hm : IsDeck m) :
    mixColumns (rel σ m) = rel σ (mixColumns m) ↔
      ∀ n < 52, walkSeat (rel σ m) n = walkSeat m n := by
  simp only [mixColumns_eq, walkSeat_eq]
  exact walkW_rel_iff _ freeChooser σ m hm

/-- (PROVED, kernel `decide!`) K♣↔K♦ does not commute with v11 GridCycle:
    on the deck `K♦, A♣, 2♣, …` the second card goes to (1,0) but, after the
    swap, K♣ leads and the second card overflows to (0,0). -/
theorem mixColumns_KC_KD_fails :
    mixColumns (rel (swap KC KD) (firstDeck 51)) ≠ rel (swap KC KD) (mixColumns (firstDeck 51)) := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  revert this
  decide!

/-- (PROVED, kernel `decide!`) The K♣/K♠ collision is broken on the third card. -/
theorem mixColumns_KC_KS_fails :
    mixColumns (rel (swap KC KS) (firstDeck 12)) ≠ rel (swap KC KS) (mixColumns (firstDeck 12)) := by
  intro h
  have := congrFun h ⟨4, by decide⟩
  revert this
  decide!

theorem firstDeck_isDeck (c : Fin 52) : IsDeck (firstDeck c.val) := by
  have hc := c.isLt
  constructor
  · intro i; have := i.isLt; unfold firstDeck; split_ifs <;> omega
  · intro i j h; unfold firstDeck at h; apply Fin.ext; split_ifs at h <;> omega

theorem firstDeck_zero (c : Nat) : firstDeck c ⟨0, by decide⟩ = c := by simp [firstDeck]

/-- (PROVED) Generic "only identity" for a walk whose second seat is `seat2` of
    the first card and which separates K♣/K♠ on `firstDeck 12`. -/
theorem walkW_only_id (ch : Chooser) (hch : FreeChooser ch)
    (hs2 : ∀ hand : Fin 52 → Nat, hand ⟨0, by decide⟩ < 52 →
      seatW ch hand 1 = seat2 (hand ⟨0, by decide⟩))
    (hKS : scoopRowMajor (gridW ch (rel (swap KC KS) (firstDeck 12))) ≠
      rel (swap KC KS) (scoopRowMajor (gridW ch (firstDeck 12))))
    (σ : Relabel)
    (h : ∀ m, IsDeck m → scoopRowMajor (gridW ch (rel σ m)) = rel σ (scoopRowMajor (gridW ch m))) :
    σ = 1 := by
  have key : ∀ c : Fin 52, σ c = c ∨ (σ c = KC ∧ c = KS) ∨ (σ c = KS ∧ c = KC) := by
    intro c
    have hw := (walkW_rel_iff ch hch σ _ (firstDeck_isDeck c)).1
      (h _ (firstDeck_isDeck c)) 1 (by decide)
    have e1 : rel σ (firstDeck c.val) ⟨0, by decide⟩ = (σ c).val := by
      simp only [rel, firstDeck_zero, app_fin]
    rw [hs2 _ (by rw [e1]; exact (σ c).isLt), hs2 _ (by rw [firstDeck_zero]; exact c.isLt),
      e1, firstDeck_zero] at hw
    exact seat2_inj _ _ hw
  have hne : KC ≠ KS := by decide
  rw [Equiv.Perm.ext_iff]
  by_cases hKC : σ KC = KC
  · have hKS' : σ KS = KS := by
      rcases key KS with h1 | ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd (σ.injective (h1.trans hKC.symm)) hne.symm
      · exact absurd h2.symm hne
    intro c
    rcases key c with h1 | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact h1
    · exact absurd (h1.symm.trans hKS') hne
    · exact hKC
  · exfalso
    have hKCS : σ KC = KS := by
      rcases key KC with h1 | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h1 hKC
      · exact absurd h2 hne
      · exact h1
    have hKSC : σ KS = KC := by
      rcases key KS with h1 | ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd (σ.injective (h1.trans hKCS.symm)) hne.symm
      · exact h1
      · exact absurd h2.symm hne
    have hσ : σ = swap KC KS := by
      apply Equiv.ext; intro c
      rcases key c with h1 | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · have hc1 : c ≠ KC := fun e => hKC (e ▸ h1)
        have hc2 : c ≠ KS := fun e => by rw [e, hKSC] at h1; exact hne h1
        rw [h1, Equiv.swap_apply_of_ne_of_ne hc1 hc2]
      · rw [Equiv.swap_apply_right]; exact h1
      · rw [Equiv.swap_apply_left]; exact h1
    subst hσ
    exact hKS (h _ (firstDeck_isDeck KC))

/-- (PROVED) GridCycle commutes with σ on all decks iff σ = id. "Only if": for
    `c` moved by σ, the deck `firstDeck c` changes the second seat
    (`walkSeat_one`, `seat2_inj`) unless σ swaps K♣,K♠ and fixes all else,
    which `mixColumns_KC_KS_fails` excludes. -/
theorem mixColumns_commutes_iff_id (σ : Relabel) :
    CommutesOnDecks σ mixColumns ↔ σ = 1 := by
  constructor
  · intro h
    refine walkW_only_id chooseSeat! freeChooser
      (fun hand _ => by rw [← walkSeat_eq]; rfl) ?_ σ ?_
    · simpa only [mixColumns_eq] using mixColumns_KC_KS_fails
    · intro m hm; simpa only [mixColumns_eq] using h m hm
  · rintro rfl; exact commutesOnDecks_one _

/-! ### 3a. Frozen v8 GridCycle model (overflow scan starts at column 0)

Proof-only v8 seat chooser (overflow scan from column 0) plugged into the generic
walk of `Walk.lean`, for the v8 statements.
Checked against the frozen v8 known-answer vectors in `V8Vectors.lean`. -/

namespace V8

/-- v8 blocked placement: overflow rows from the marker, each scanned from
    column 0; the next marker is the row after the one used, and the finger is
    the seat the card landed on (no ghost finger). -/
def chooseSeat? (st : WalkState) : Option SeatChoice :=
  match st.prev with
  | none => some (asStart, (st.t, asStart))
  | some (card, pos) =>
      let target := gridStep card pos
      if occAt st.occ target then
        (overflowSeat st.occ st.t 0).map fun p => (p, ((p.1.val + 1) % 4, p))
      else some (target, (st.t, target))

def chooseSeat! (st : WalkState) : SeatChoice :=
  match chooseSeat? st with
  | some x => x
  | none => ((⟨0, by decide⟩, ⟨0, by decide⟩), (st.t, (⟨0, by decide⟩, ⟨0, by decide⟩)))

/-- v8 GridCycle: the generic walk (`Walk.lean`) with the v8 chooser. -/
def mixColumns (hand : Fin 52 → Nat) : Fin 52 → Nat := scoopRowMajor (gridW chooseSeat! hand)

def unkeyedNoMix (m : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopColumnMajor (shiftRows (sumRanksV8 (layColumnMajor m)))

def fullRound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  composeVec 52 Nat (mixColumns (unkeyedNoMix m)) pos

end V8

/-- (PROVED, kernel `decide!`) K♣↔K♦ does not commute with v8 GridCycle either
    (same deck, same second-seat split (1,0) vs (0,0)). -/
theorem v8_mixColumns_KC_KD_fails :
    V8.mixColumns (rel (swap KC KD) (firstDeck 51)) ≠
      rel (swap KC KD) (V8.mixColumns (firstDeck 51)) := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  revert this
  decide!

/-- (PROVED, kernel `decide!`) The K♣/K♠ collision is broken on the third card (v8). -/
theorem v8_mixColumns_KC_KS_fails :
    V8.mixColumns (rel (swap KC KS) (firstDeck 12)) ≠
      rel (swap KC KS) (V8.mixColumns (firstDeck 12)) := by
  intro h
  have := congrFun h ⟨4, by decide⟩
  revert this
  decide!

theorem V8.freeChooser : FreeChooser V8.chooseSeat! := by
  intro st hct hprev
  match hprev_eq : st.prev with
  | none =>
      have : V8.chooseSeat? st = some (asStart, (st.t, asStart)) := by
        simp [V8.chooseSeat?, hprev_eq]
      simp only [V8.chooseSeat!, this]
      cases hprev with
      | inl h => simp [hprev_eq] at h
      | inr h => exact h
  | some pair =>
      simp only [V8.chooseSeat!, V8.chooseSeat?, hprev_eq]
      by_cases ht : occAt st.occ (gridStep pair.1 pair.2)
      · simp only [ht, ↓reduceIte]
        obtain ⟨p, hs, hf⟩ := overflow_some_of_count_lt st.occ st.t 0 hct
        simp only [hs, Option.map_some']
        exact hf
      · have hf := eq_false_of_ne_true ht
        simp [hf]

/-- (PROVED, kernel `decide!`) v8 and v11 agree on the second seat. -/
theorem V8.seat2_eq : ∀ c : Fin 52,
    (V8.chooseSeat! (advance initWalk c.val asStart (0, asStart))).1 = seat2 c.val := by
  decide!

theorem V8.mixColumns_eq (hand : Fin 52 → Nat) :
    V8.mixColumns hand = scoopRowMajor (gridW V8.chooseSeat! hand) := rfl

/-- (PROVED) v8 GridCycle commutes with σ on all decks iff σ = id (same
    argument; v8 and v11 agree on the second seat, `V8.seat2_eq`). -/
theorem v8_mixColumns_commutes_iff_id (σ : Relabel) :
    CommutesOnDecks σ V8.mixColumns ↔ σ = 1 := by
  constructor
  · intro h
    refine walkW_only_id V8.chooseSeat! V8.freeChooser
      (fun hand h0 => by
        show (V8.chooseSeat! (advance initWalk (hand ⟨0, by decide⟩) asStart (0, asStart))).1 = _
        exact V8.seat2_eq ⟨_, h0⟩) ?_ σ ?_
    · simpa only [V8.mixColumns_eq] using v8_mixColumns_KC_KS_fails
    · intro m hm; simpa only [V8.mixColumns_eq] using h m hm
  · rintro rfl; exact commutesOnDecks_one _

end DoubleDeal.Security
