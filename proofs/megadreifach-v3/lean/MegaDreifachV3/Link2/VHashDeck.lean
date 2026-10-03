/-
  MegaDreifach v3 Link 2: `HashDeck`, `HashDeckBody`, `HashDeckBodyFrom` and the
  `MegaDreifach*` aliases.
  * `v_HashDeck_refines` (on `PhiInvWf`): `HashDeck(deal) = Hash(φ⁻¹(deal))`, i.e. `vhashAlg`
    of the deal's 28-byte Lehmer rank; `v_HashDeck_two_blocks`: one v3 DM block keyed by the
    deal from IV-COOK12, then the fixed pad block `deckPadBlock`.
  * `body_from_refines`, `v_HashDeckBody_refines`, `v_HashDeckBodyFrom_refines` (on
    permutations of `0..51`; `BodyFrom` also on a chaining value with bijective tables): the
    digest of `compose h (emBlock h deal)`.
  The φ round trip lemmas restate the v2 ones (v2 VHashDeck imports the v2-only EmBlock).
-/
import MegaDreifachV3.Link2.VHash
import MegaDreifach.Link2.PhiInv
import MegaDreifach.Link2.RequirePerm

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Link2

/-! ## φ round trip (M4) -/

/-- The Lehmer digit of `v` indexes `v` in `avail`. -/
theorem findIdx_beq_lt {avail : List Nat} {v : Nat} (hv : v ∈ avail) :
    avail.findIdx (· == v) < avail.length :=
  List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩

theorem getElem_findIdx_beq {avail : List Nat} {v : Nat} (hv : v ∈ avail) :
    avail[avail.findIdx (· == v)]'(findIdx_beq_lt hv) = v := by
  have := List.findIdx_getElem (xs := avail) (p := (· == v)) (w := findIdx_beq_lt hv)
  simpa using this

/-- After drawing `v`, the rest of a duplicate-free rearrangement is still inside the
    remaining cards. -/
theorem rest_mem_eraseIdx {v : Nat} {rest avail : List Nat} (hnd : (v :: rest).Nodup)
    (hsub : ∀ x ∈ v :: rest, x ∈ avail) :
    ∀ x ∈ rest, x ∈ avail.eraseIdx (avail.findIdx (· == v)) := by
  have hv : v ∈ avail := hsub v (List.mem_cons_self v rest)
  have hvr : v ∉ rest := (List.nodup_cons.mp hnd).1
  intro x hx
  have hxa : x ∈ avail := hsub x (List.mem_cons_of_mem v hx)
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxa
  rw [List.mem_eraseIdx_iff_getElem]
  refine ⟨i, hi, ?_, hix⟩
  intro hid
  subst hid
  have : x = v := by rw [← hix, getElem_findIdx_beq hv]
  exact hvr (this ▸ hx)

/-- Applying the Lehmer digits of `perm` (relative to `avail`) to `avail` gives
    `perm` back, when `perm` is a duplicate-free rearrangement of `avail`. -/
theorem applyDigits_lehmerDigits : ∀ (perm avail : List Nat),
    avail.Nodup → perm.Nodup → perm.length = avail.length → (∀ x ∈ perm, x ∈ avail) →
    applyDigits avail (lehmerDigits avail perm) = perm
  | [], avail, _, _, hlen, _ => by
      have : avail = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst this
      rfl
  | v :: rest, avail, hav, hnd, hlen, hsub => by
      have hv : v ∈ avail := hsub v (List.mem_cons_self v rest)
      have hd := findIdx_beq_lt hv
      have hlen' : rest.length = (avail.eraseIdx (avail.findIdx (· == v))).length := by
        rw [List.length_eraseIdx_of_lt hd]
        simp at hlen
        omega
      have ih := applyDigits_lehmerDigits rest (avail.eraseIdx (avail.findIdx (· == v)))
        (List.Nodup.eraseIdx _ hav) (List.nodup_cons.mp hnd).2 hlen'
        (rest_mem_eraseIdx hnd hsub)
      cases avail with
      | nil => exact absurd hv (List.not_mem_nil v)
      | cons a as =>
          simp only [lehmerDigits, applyDigits, dif_pos hd]
          rw [ih, getElem_findIdx_beq hv]

/-- The Lehmer digits of a duplicate-free rearrangement of `avail` are in range for
    the radices `|avail|, |avail| - 1, …, 1`. -/
theorem lehmerDigits_bound : ∀ (perm avail : List Nat),
    perm.Nodup → perm.length = avail.length → (∀ x ∈ perm, x ∈ avail) →
    ∀ i, i < perm.length →
      (lehmerDigits avail perm)[i]?.getD 0 < (descending avail.length)[i]?.getD 0
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | v :: rest, avail, hnd, hlen, hsub, i, hi => by
      have hv : v ∈ avail := hsub v (List.mem_cons_self v rest)
      have hd := findIdx_beq_lt hv
      obtain ⟨k, hk⟩ : ∃ k, avail.length = k + 1 := ⟨avail.length - 1, by omega⟩
      have hk' : (avail.eraseIdx (avail.findIdx (· == v))).length = k := by
        rw [List.length_eraseIdx_of_lt hd]; omega
      cases i with
      | zero =>
          simp only [lehmerDigits, hk, descending_succ, List.getElem?_cons_zero, Option.getD_some]
          omega
      | succ i =>
          simp only [lehmerDigits, hk, descending_succ, List.getElem?_cons_succ]
          have := lehmerDigits_bound rest (avail.eraseIdx (avail.findIdx (· == v)))
            (List.nodup_cons.mp hnd).2 (by rw [hk']; simp at hlen; omega)
            (rest_mem_eraseIdx hnd hsub) i (by simp at hi; omega)
          rw [hk'] at this
          exact this

/-- M4 round trip: Lehmer unrank after Lehmer rank is the identity on permutations
    of `0..n-1`. -/
theorem lehmerUnrank_lehmerRank (perm : List Nat) (hnd : perm.Nodup)
    (hb : ∀ x ∈ perm, x < perm.length) :
    lehmerUnrank perm.length (lehmerRank perm) = perm := by
  have hsub : ∀ x ∈ perm, x ∈ List.range perm.length :=
    fun x hx => List.mem_range.mpr (hb x hx)
  have hlenR : perm.length = (List.range perm.length).length := by rw [List.length_range]
  unfold lehmerUnrank lehmerRank
  rw [mixDecode_encode]
  · exact applyDigits_lehmerDigits perm _ (List.nodup_range _) hnd hlenR hsub
  · rw [lehmerDigits_length, descending_length]
  · intro i hi
    rw [lehmerDigits_length] at hi
    have := lehmerDigits_bound perm (List.range perm.length) hnd hlenR hsub i hi
    rwa [List.length_range] at this

/-- φ after φ⁻¹: `phiUnrank (lehmerRank deal) = deal` on a permutation of `0..51`. -/
theorem phiUnrank_lehmerRank (deal : List Nat) (hl : deal.length = 52) (hnd : deal.Nodup)
    (hb : ∀ x ∈ deal, x < 52) : phiUnrank (lehmerRank deal) = deal := by
  have := lehmerUnrank_lehmerRank deal hnd (by rw [hl]; exact hb)
  rw [hl] at this
  exact this

/-- The 28-byte message `toBE 28 r` (`r < 2^224`) is a well-formed `Hash` input. -/
theorem padWf_toBE28 (r : Nat) (hr : r < phiMax) : PadWf (toBE 28 r) where
  bytes := fun b hb => by
    have := toBE_mem_lt 28 r (by unfold phiMax at hr; omega) b hb
    unfold Byte; omega
  bitlen := by rw [toBE_length]; unfold FitsBitlen i64MaxNat; decide

/-- `HashDeck = Hash ∘ φ⁻¹` on `PhiInvWf` deals (the SPEC §3 definition, for the
    emitted code). -/
theorem v_HashDeck_eq_v_Hash (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.v_HashDeck (embed deal) =
      Megadreifach.v_Hash (embed (toBE 28 (lehmerRank deal))) := by
  unfold Megadreifach.v_HashDeck
  rw [(require_permutation_refines deal ⟨h.len, h.nodup, h.bound⟩).1, ok_bind]
  dsimp only
  rw [phi_inv_refines deal h, ok_bind]
  exact except_bind_pure _

/-- `v_HashDeck` ≃ the algebraic hash of the deal's 28-byte Lehmer rank. -/
theorem v_HashDeck_refines (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.v_HashDeck (embed deal) =
      .ok (embed (vhashAlg (toBE 28 (lehmerRank deal)))) := by
  rw [v_HashDeck_eq_v_Hash deal h, v_Hash_refines _ (padWf_toBE28 _ h.small)]

/-- Array form of `v_HashDeck_refines` on `WellFormedPhiInv`. -/
theorem v_HashDeck_refines_array (a : Array Int) (h : WellFormedPhiInv a) :
    Megadreifach.v_HashDeck a = .ok (embed (vhashAlg (toBE 28 (lehmerRank (decode a))))) := by
  have hr := v_HashDeck_refines (decode a) (phiInv_decode a h)
  rwa [embed_decode a h.nn] at hr

/-- The `MegaDreifachDeck` alias. -/
theorem v_MegaDreifachDeck_refines (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.v_MegaDreifachDeck (embed deal) =
      .ok (embed (vhashAlg (toBE 28 (lehmerRank deal)))) := by
  unfold Megadreifach.v_MegaDreifachDeck
  rw [v_HashDeck_refines deal h, ok_bind]
  rfl

/-- The second (last) padded block of every 28-byte message: `0x80`, 19 zero bytes,
    and the 8-byte bit length `224`. -/
def deckPadBlock : List Nat := [0x80] ++ List.replicate (padZ 28) 0 ++ toBE 8 (8 * 28)

theorem deckPadBlock_length : deckPadBlock.length = 28 := by decide

theorem pad_len28 (msg : List Nat) (hl : msg.length = 28) : pad msg = msg ++ deckPadBlock := by
  unfold pad deckPadBlock
  rw [hl]
  simp only [List.append_assoc]

/-- A 28-byte message hashes as exactly two DM blocks: the message, then `deckPadBlock`. -/
theorem vhashAlg_len28 (msg : List Nat) (hl : msg.length = 28) :
    vhashAlg msg = positionToBytes (dmBlock (dmBlock Em.ivCook12 msg) deckPadBlock) := by
  unfold vhashAlg
  rw [pad_len28 msg hl]
  have hlen : (msg ++ deckPadBlock).length / 28 = 2 := by
    rw [List.length_append, hl, deckPadBlock_length]
  rw [hlen, chainPre_succ, chainPre_succ, chainPre_zero]
  have h0 : blockAt (msg ++ deckPadBlock) 0 = msg := by
    unfold blockAt
    rw [Nat.mul_zero, List.drop_zero, List.take_append_eq_append_take, hl,
      List.take_of_length_le (by omega), Nat.sub_self, List.take_zero, List.append_nil]
  have h1 : blockAt (msg ++ deckPadBlock) 1 = deckPadBlock := by
    unfold blockAt
    rw [Nat.mul_one, List.drop_append_eq_append_drop, hl,
      List.drop_of_length_le (by omega), Nat.sub_self, List.drop_zero, List.nil_append,
      List.take_of_length_le (Nat.le_of_eq deckPadBlock_length)]
  rw [h0, h1]

/-- The algebraic `HashDeck` digest: the first DM block is keyed by the deal itself. -/
theorem vhashAlg_deck (deal : List Nat) (h : PhiInvWf deal) :
    vhashAlg (toBE 28 (lehmerRank deal)) =
      positionToBytes (dmBlock (MegaDreifachV3.Em.dmStep Em.ivCook12 deal) deckPadBlock) := by
  rw [vhashAlg_len28 _ (toBE_length 28 _)]
  unfold dmBlock
  rw [fromBE_toBE 28 _ (by have := h.small; unfold phiMax at this; omega),
    phiUnrank_lehmerRank deal h.len h.nodup h.bound]

/-- `v_HashDeck` on a `PhiInvWf` deal: one DM block keyed by the deal from IV-COOK12,
    then the fixed pad block, then the 29-byte digest. -/
theorem v_HashDeck_two_blocks (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.v_HashDeck (embed deal) =
      .ok (embed (positionToBytes (dmBlock (MegaDreifachV3.Em.dmStep Em.ivCook12 deal) deckPadBlock))) := by
  rw [v_HashDeck_refines deal h, vhashAlg_deck deal h]

/-! ## Body -/

theorem body_from_refines (h : Position) (hh : InjPos h) (deal : List Nat)
    (hp : isPermutation52 deal) :
    Megadreifach.body_from (embed deal) (embedPos h) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep h deal))) := by
  unfold Megadreifach.body_from
  rw [(require_permutation_refines deal hp).1, ok_bind]
  dsimp only
  rw [em_block_refines h hh deal (by rw [hp.1]; exact Nat.le_refl _) hp.2.2, ok_bind, compose_refines, ok_bind,
    position_to_bytes_refines_gen _ (injPos_compose' _ _ hh (emBlock_inj h hh deal)), ok_bind]
  rfl

theorem v_HashDeckBody_refines (deal : List Nat) (hp : isPermutation52 deal) :
    Megadreifach.v_HashDeckBody (embed deal) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep Em.ivCook12 deal))) := by
  unfold Megadreifach.v_HashDeckBody
  rw [iv_cook12_refines, ok_bind, body_from_refines _ injPos_ivCook12' deal hp, ok_bind]
  rfl

theorem v_MegaDreifachBody_refines (deal : List Nat) (hp : isPermutation52 deal) :
    Megadreifach.v_MegaDreifachBody (embed deal) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep Em.ivCook12 deal))) := by
  unfold Megadreifach.v_MegaDreifachBody
  rw [v_HashDeckBody_refines deal hp, ok_bind]
  rfl

theorem v_HashDeckBodyFrom_refines (deal : List Nat) (h : Position) (hh : InjPos h)
    (hp : isPermutation52 deal) :
    Megadreifach.v_HashDeckBodyFrom (embed deal) (embedPos h) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep h deal))) := by
  unfold Megadreifach.v_HashDeckBodyFrom
  rw [body_from_refines h hh deal hp, ok_bind]
  rfl

theorem v_MegaDreifachBodyFrom_refines (deal : List Nat) (h : Position) (hh : InjPos h)
    (hp : isPermutation52 deal) :
    Megadreifach.v_MegaDreifachBodyFrom (embed deal) (embedPos h) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep h deal))) := by
  unfold Megadreifach.v_MegaDreifachBodyFrom
  rw [v_HashDeckBodyFrom_refines deal h hh hp, ok_bind]
  rfl

end MegaDreifachV3.Link2
