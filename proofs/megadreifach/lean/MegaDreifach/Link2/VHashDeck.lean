/-
  LINK 2. `Generated.v_HashDeck` (`HashDeck(deal) = Hash(φ⁻¹(deal))`) refines the
  algebraic hash of the 28-byte Lehmer rank of the deal.

  * `lehmerUnrank_lehmerRank` / `phiUnrank_lehmerRank`: φ after φ⁻¹ is the identity
    on permutations (the M4 round trip, now in PhiInv; M4 itself only proved injectivity of φ).
  * `v_HashDeck_eq_v_Hash`, `v_HashDeck_refines`: on `PhiInvWf` (a permutation of
    `0..51` whose Lehmer rank is `< 2^224`), `v_HashDeck` is `v_Hash` of
    `toBE 28 (lehmerRank deal)`, i.e. `vhashAlg` of those 28 bytes.
  * `vhashAlg_deck`, `v_HashDeck_two_blocks`: that message pads to exactly two blocks;
    the first block's φ is the deal itself and the second is the fixed pad block
    `deckPadBlock`, so the digest is
    `positionToBytes (dmBlock (Em.dmStep Em.ivCook12 deal) deckPadBlock)`.

  Built from `require_permutation_refines`, `phi_inv_refines` and `v_Hash_refines`.
  Algebraic Link 2 only: not emitter soundness (Link 1), not collision resistance.
  Zero sorry.  No native_decide.
-/
import MegaDreifach.Link2.VHash
import MegaDreifach.Link2.PhiInv
import MegaDreifach.Link2.RequirePerm

namespace MegaDreifach.Link2

open MegaDreifach

/-! ## `v_HashDeck` -/

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
      positionToBytes (dmBlock (Em.dmStep Em.ivCook12 deal) deckPadBlock) := by
  rw [vhashAlg_len28 _ (toBE_length 28 _)]
  unfold dmBlock
  rw [fromBE_toBE 28 _ (by have := h.small; unfold phiMax at this; omega),
    phiUnrank_lehmerRank deal h.len h.nodup h.bound]

/-- `v_HashDeck` on a `PhiInvWf` deal: one DM block keyed by the deal from IV-COOK12,
    then the fixed pad block, then the 29-byte digest. -/
theorem v_HashDeck_two_blocks (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.v_HashDeck (embed deal) =
      .ok (embed (positionToBytes (dmBlock (Em.dmStep Em.ivCook12 deal) deckPadBlock))) := by
  rw [v_HashDeck_refines deal h, vhashAlg_deck deal h]

end MegaDreifach.Link2
