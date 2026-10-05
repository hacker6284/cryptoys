/-
  MegaDreifach v3 Link 2: `HashDeck`, `HashDeckBody`, `HashDeckBodyFrom`, `HashDecksBody` and the
  `MegaDreifach*` aliases.
  * `v_HashDeck_refines` (on `PhiInvWf`): `HashDeck(deal) = Hash(φ⁻¹(deal))`, i.e. `vhashAlg`
    of the deal's 28-byte Lehmer rank; `v_HashDeck_two_blocks`: one v3 DM block keyed by the
    deal from IV-COOK12, then the fixed pad block `deckPadBlock`.
  * `body_from_refines`, `v_HashDeckBody_refines`, `v_HashDeckBodyFrom_refines` (on
    permutations of `0..51`; `BodyFrom` also on a chaining value with bijective tables): the
    digest of `dmStep h deal = compose h (emBlock h deal)` (the sudo's `dm_step`).
  * `v_HashDecksBody_refines` (on a non-empty list of permutations of `0..51`): one
    `dmStep` per whole deal from IV-COOK12 (`decksBody`), no pad and no φ.
  The φ round trip lemmas are v2 PhiInv's; `padWf_toBE28` and `deckPadBlock` are in VHashCommon.
-/
import MegaDreifachV3.Link2.VHash
import MegaDreifach.Link2.PhiInv
import MegaDreifach.Link2.RequirePerm

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Link2

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
  rw [dm_step_refines h hh deal (by rw [hp.1]; exact Nat.le_refl _) hp.2.2, ok_bind,
    position_to_bytes_refines_gen _ (dmStep_inj h hh deal), ok_bind]
  rfl

theorem v_HashDeckBody_refines (deal : List Nat) (hp : isPermutation52 deal) :
    Megadreifach.v_HashDeckBody (embed deal) =
      .ok (embed (positionToBytes (MegaDreifachV3.Em.dmStep Em.ivCook12 deal))) := by
  unfold Megadreifach.v_HashDeckBody
  rw [iv_cook12_refines, ok_bind, body_from_refines _ injPos_ivCook12 deal hp, ok_bind]
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

/-! ## Decks body (`HashDecksBody`) -/

/-- A list of decks as the emitted `List<List<int>>`. -/
def embedDecks (deals : List (List Nat)) : Array (Array Int) := Array.mk (deals.map embed)

theorem listLen_embedDecks (deals : List (List Nat)) :
    SudoRt.listLen (embedDecks deals) = Int.ofNat deals.length := by
  rw [listLen_eq]
  simp [embedDecks]

theorem atL_embedDecks (deals : List (List Nat)) (i : Nat) (h : i < deals.length) :
    SudoRt.atL (embedDecks deals) (Int.ofNat i) = .ok (embed (deals[i])) := by
  have hsz : i < (embedDecks deals).size := by simp [embedDecks, h]
  rw [atL_ofNat _ i hsz]
  simp [embedDecks]

/-- The model of `HashDecksBody`: one v3 Davies–Meyer step (`dmStep`, the sudo's `dm_step`)
    per whole deal, from IV-COOK12, no pad and no φ; digest = the 29-byte rank. -/
def decksBody (deals : List (List Nat)) : List Nat :=
  positionToBytes (deals.foldl MegaDreifachV3.Em.dmStep Em.ivCook12)

/-- Chaining value after the first `i` deals. -/
def decksPre (deals : List (List Nat)) (i : Nat) : Position :=
  (deals.take i).foldl MegaDreifachV3.Em.dmStep Em.ivCook12

theorem decksPre_succ (deals : List (List Nat)) (i : Nat) (h : i < deals.length) :
    decksPre deals (i + 1) = MegaDreifachV3.Em.dmStep (decksPre deals i) (deals[i]) := by
  unfold decksPre
  rw [List.take_succ, List.getElem?_eq_getElem h, List.foldl_append]
  rfl

theorem injPos_foldl_dmStep (l : List (List Nat)) : ∀ h, InjPos h →
    InjPos (l.foldl MegaDreifachV3.Em.dmStep h) := by
  induction l with
  | nil => intro h hh; exact hh
  | cons d ds ih => intro h hh; exact ih _ (dmStep_inj h hh d)

theorem injPos_decksPre (deals : List (List Nat)) (i : Nat) : InjPos (decksPre deals i) :=
  injPos_foldl_dmStep _ _ injPos_ivCook12

/-- `HashDecksBody` on a non-empty list of permutations of `0..51` (whose length fits the
    emitted `int`): the model `decksBody`. -/
theorem v_HashDecksBody_refines (deals : List (List Nat)) (hne : 0 < deals.length)
    (hfit : FitsLen deals.length) (hp : ∀ d ∈ deals, isPermutation52 d) :
    Megadreifach.v_HashDecksBody (embedDecks deals) = .ok (embed (decksBody deals)) := by
  unfold Megadreifach.v_HashDecksBody
  rw [listLen_embedDecks, decide_ofNat_pos, decide_eq_true hne, sudoAssert_true, ok_bind,
    iv_cook12_refines, ok_bind]
  dsimp only
  rw [subI_ofNat_one _ hne hfit, ok_bind, except_bind_pure]
  have h0 : Em.ivCook12 = decksPre deals 0 := by
    unfold decksPre; rw [List.take_zero, List.foldl_nil]
  rw [h0]
  apply chain_loop (f := fun i => embedPos (decksPre deals i)) (fromN := 0)
    (toN := deals.length - 1) (hle := Nat.zero_le _)
  · intro i _ hi
    have hil : i < deals.length := by omega
    have hpi := hp (deals[i]) (List.getElem_mem hil)
    dsimp only
    rw [if_neg (ofNat_not_gt hi), atL_embedDecks deals i hil, ok_bind,
      (require_permutation_refines _ hpi).1, ok_bind,
      dm_step_refines _ (injPos_decksPre _ _) _ (by rw [hpi.1]; exact Nat.le_refl _) hpi.2.2,
      ok_bind, ← decksPre_succ deals i hil, pure_bind]
    exact loopTailN i _ hi (FitsLen.succ_le hil hfit) _
  · dsimp only
    rw [position_to_bytes_refines_gen _ (injPos_decksPre _ _), ok_bind, Nat.sub_add_cancel hne]
    unfold decksBody decksPre
    rw [List.take_of_length_le (Nat.le_refl _)]
    rfl

end MegaDreifachV3.Link2
