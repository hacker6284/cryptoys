/-
  LINK 2. Transfer S3/S4 from the list algebra onto emitted
  `Doubledeal.passkey` / `Doubledeal.passkey_inv`
  (`Except SudoRt.Trap` over `Array Int`).

  Rides `passkey_refines` and `passkey_inv_refines`. Does not re-induct
  on the twin `runLoopOn`. Domain is `FitsLen` (and `WellFormed` for a
  raw emitted array): card values need not be `< 52`.

  Algebraic correctness only. Not emitter soundness. Not bit-security.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.PassKey
import DoubleDeal.Link2.PassKeyInv

namespace DoubleDeal.Link2

theorem length_passToKeyCutFallback (deck : List Nat) :
    (passToKeyCutFallback deck).length = deck.length :=
  (passToKeyCutFallback_perm deck).length_eq

theorem fits_passToKeyCutFallback (deck : List Nat) (h : FitsLen deck.length) :
    FitsLen (passToKeyCutFallback deck).length := by
  rw [length_passToKeyCutFallback]
  exact h

theorem length_passToKeyCutFallbackInv (deck : List Nat) :
    (passToKeyCutFallbackInv deck).length = deck.length := by
  simpa [passToKeyCutFallbackInv, List.length_nil, Nat.add_zero] using
    passKeyInvGoN_length deck.length deck [] (Nat.le_refl _)

theorem fits_passToKeyCutFallbackInv (deck : List Nat) (h : FitsLen deck.length) :
    FitsLen (passToKeyCutFallbackInv deck).length := by
  rw [length_passToKeyCutFallbackInv]
  exact h

theorem length_decode (a : Array Int) : (decode a).length = a.size := by
  simp [decode]

theorem fits_decode (a : Array Int) (ha : WellFormed a) : FitsLen (decode a).length := by
  rw [length_decode]
  exact ha.fits

/-- List form of S3 for the algebraic inverse (length-preserving bijection). -/
theorem passToKeyCutFallbackInv_perm (deck : List Nat) :
    List.Perm (passToKeyCutFallbackInv deck) deck := by
  have h := passToKeyCutFallback_perm (passToKeyCutFallbackInv deck)
  rw [passToKeyCutFallback_rightInverse deck] at h
  exact h.symm

private theorem except_ok_inj {ε α} {a b : α}
    (h : (Except.ok a : Except ε α) = .ok b) : a = b := by
  injection h

/-! ## S3: card multiset on `Except Trap` -/

/-- S3: emitted `passkey` returns a permutation of the deck. Trap does not fire. -/
theorem passkey_perm (deck : List Nat) (hfits : FitsLen deck.length) :
    ∃ out, Doubledeal.passkey (embed deck) = .ok out ∧
      List.Perm (decode out) deck := by
  refine ⟨embed (passToKeyCutFallback deck), passkey_refines deck hfits, ?_⟩
  rw [decode_embed]
  exact passToKeyCutFallback_perm deck

/-- S3 for the emitted inverse: same multiset, no Trap. -/
theorem passkey_inv_perm (deck : List Nat) (hfits : FitsLen deck.length) :
    ∃ out, Doubledeal.passkey_inv (embed deck) = .ok out ∧
      List.Perm (decode out) deck := by
  refine ⟨embed (passToKeyCutFallbackInv deck), passkey_inv_refines deck hfits, ?_⟩
  rw [decode_embed]
  exact passToKeyCutFallbackInv_perm deck

/-- S3 on a well-formed emitted array. -/
theorem passkey_perm_wf (a : Array Int) (ha : WellFormed a) :
    ∃ out, Doubledeal.passkey a = .ok out ∧
      List.Perm (decode out) (decode a) := by
  have h := passkey_perm (decode a) (fits_decode a ha)
  rw [embed_decode a ha.nonneg] at h
  exact h

/-- S3 for `passkey_inv` on a well-formed emitted array. -/
theorem passkey_inv_perm_wf (a : Array Int) (ha : WellFormed a) :
    ∃ out, Doubledeal.passkey_inv a = .ok out ∧
      List.Perm (decode out) (decode a) := by
  have h := passkey_inv_perm (decode a) (fits_decode a ha)
  rw [embed_decode a ha.nonneg] at h
  exact h

/-! ## S4: inverse and injectivity on `Except Trap` -/

/-- S4: `passkey_inv ∘ passkey = id` on an embedded well-formed deck. -/
theorem passkey_leftInverse (deck : List Nat) (hfits : FitsLen deck.length) :
    (Doubledeal.passkey (embed deck) >>= Doubledeal.passkey_inv) =
      .ok (embed deck) := by
  rw [passkey_refines deck hfits]
  simp only [ok_bind]
  rw [passkey_inv_refines (passToKeyCutFallback deck) (fits_passToKeyCutFallback deck hfits)]
  rw [passToKeyCutFallback_leftInverse]

/-- S4: `passkey ∘ passkey_inv = id` on an embedded well-formed deck. -/
theorem passkey_rightInverse (deck : List Nat) (hfits : FitsLen deck.length) :
    (Doubledeal.passkey_inv (embed deck) >>= Doubledeal.passkey) =
      .ok (embed deck) := by
  rw [passkey_inv_refines deck hfits]
  simp only [ok_bind]
  rw [passkey_refines (passToKeyCutFallbackInv deck) (fits_passToKeyCutFallbackInv deck hfits)]
  rw [passToKeyCutFallback_rightInverse]

/-- S4: emitted `passkey` is injective on embedded well-formed decks. -/
theorem passkey_injective {d₁ d₂ : List Nat}
    (h₁ : FitsLen d₁.length) (h₂ : FitsLen d₂.length)
    (h : Doubledeal.passkey (embed d₁) = Doubledeal.passkey (embed d₂)) :
    d₁ = d₂ := by
  rw [passkey_refines d₁ h₁, passkey_refines d₂ h₂] at h
  exact passKey_injective (embed_inj (except_ok_inj h))

/-- S4: emitted `passkey_inv` is injective on embedded well-formed decks. -/
theorem passkey_inv_injective {d₁ d₂ : List Nat}
    (h₁ : FitsLen d₁.length) (h₂ : FitsLen d₂.length)
    (h : Doubledeal.passkey_inv (embed d₁) = Doubledeal.passkey_inv (embed d₂)) :
    d₁ = d₂ := by
  rw [passkey_inv_refines d₁ h₁, passkey_inv_refines d₂ h₂] at h
  have hout : passToKeyCutFallbackInv d₁ = passToKeyCutFallbackInv d₂ :=
    embed_inj (except_ok_inj h)
  have hF := congrArg passToKeyCutFallback hout
  rwa [passToKeyCutFallback_rightInverse, passToKeyCutFallback_rightInverse] at hF

/-- S4 on a well-formed emitted array: `passkey_inv ∘ passkey = id`. -/
theorem passkey_leftInverse_wf (a : Array Int) (ha : WellFormed a) :
    (Doubledeal.passkey a >>= Doubledeal.passkey_inv) = .ok a := by
  rw [← embed_decode a ha.nonneg]
  exact passkey_leftInverse (decode a) (fits_decode a ha)

/-- S4 on a well-formed emitted array: `passkey ∘ passkey_inv = id`. -/
theorem passkey_rightInverse_wf (a : Array Int) (ha : WellFormed a) :
    (Doubledeal.passkey_inv a >>= Doubledeal.passkey) = .ok a := by
  rw [← embed_decode a ha.nonneg]
  exact passkey_rightInverse (decode a) (fits_decode a ha)

/-- S4: emitted `passkey` is injective on `WellFormed` arrays. -/
theorem passkey_injective_wf {a b : Array Int}
    (ha : WellFormed a) (hb : WellFormed b)
    (h : Doubledeal.passkey a = Doubledeal.passkey b) : a = b := by
  rw [← embed_decode a ha.nonneg, ← embed_decode b hb.nonneg] at h
  have hdec :=
    passkey_injective (fits_decode a ha) (fits_decode b hb) h
  rw [← embed_decode a ha.nonneg, ← embed_decode b hb.nonneg, hdec]

/-- S4: emitted `passkey_inv` is injective on `WellFormed` arrays. -/
theorem passkey_inv_injective_wf {a b : Array Int}
    (ha : WellFormed a) (hb : WellFormed b)
    (h : Doubledeal.passkey_inv a = Doubledeal.passkey_inv b) : a = b := by
  rw [← embed_decode a ha.nonneg, ← embed_decode b hb.nonneg] at h
  have hdec :=
    passkey_inv_injective (fits_decode a ha) (fits_decode b hb) h
  rw [← embed_decode a ha.nonneg, ← embed_decode b hb.nonneg, hdec]

end DoubleDeal.Link2
