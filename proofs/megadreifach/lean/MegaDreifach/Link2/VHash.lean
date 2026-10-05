/-
  LINK 2 capstone. `Generated.v_Hash` refines the algebraic MD hash:
  pad, split into 28-byte blocks, `phiUnrank ∘ fromBE`, Davies–Meyer with
  `Em.dmStep` from `Em.ivCook12`, then the 29-byte rank digest.
  Zero sorry.  No native_decide.
-/
import MegaDreifach.Link2.InjInv
import MegaDreifach.Link2.PadRef
import MegaDreifach.Link2.PhiChunk
import MegaDreifach.Link2.EmBlock
import MegaDreifach.Link2.EmIv
import MegaDreifach.Chain
import MegaDreifach.Link2.VHashCommon

namespace MegaDreifach.Link2

open MegaDreifach

/-! ## Algebraic hash -/

/-- One Davies–Meyer step on a 28-byte block. -/
def dmBlock (h : Position) (blk : List Nat) : Position :=
  Em.dmStep h (phiUnrank (fromBE blk))

/-- The 28-byte blocks of `xs` (first `k`). -/
def blocksOf (xs : List Nat) (k : Nat) : List (List Nat) := (List.range k).map (blockAt xs)

/-- Chaining value after the first `k` blocks. -/
def chainPre (xs : List Nat) (k : Nat) : Position := (blocksOf xs k).foldl dmBlock Em.ivCook12

theorem chainPre_zero (xs : List Nat) : chainPre xs 0 = Em.ivCook12 := by
  unfold chainPre blocksOf
  rw [List.range_zero, List.map_nil, List.foldl_nil]

theorem chainPre_succ (xs : List Nat) (k : Nat) :
    chainPre xs (k + 1) = dmBlock (chainPre xs k) (blockAt xs k) := by
  unfold chainPre blocksOf
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

/-- Algebraic MegaDreifach hash. -/
def vhashAlg (msg : List Nat) : List Nat :=
  positionToBytes (chainPre (pad msg) ((pad msg).length / 28))

theorem injPos_foldl_dmBlock (l : List (List Nat)) : ∀ h, InjPos h →
    InjPos (l.foldl dmBlock h) := by
  induction l with
  | nil => intro h hh; exact hh
  | cons b bs ih => intro h hh; exact ih _ (injPos_dmStep h _ hh)

theorem injPos_chainPre (xs : List Nat) (k : Nat) : InjPos (chainPre xs k) :=
  injPos_foldl_dmBlock _ _ injPos_ivCook12

theorem v_Hash_refines (msg : List Nat) (hp : PadWf msg) :
    Megadreifach.v_Hash (embed msg) = .ok (embed (vhashAlg msg)) := by
  unfold Megadreifach.v_Hash
  rw [pad_message_refines msg hp, ok_bind]
  dsimp only
  rw [listLen_embed]
  have hmod : (pad msg).length % 28 = 0 := pad_length_mod msg
  have hpos : 0 < (pad msg).length := pad_length_pos msg
  have hNpos : 0 < (pad msg).length / 28 := by omega
  have hfitsP : FitsLen (pad msg).length := by
    have hb := hp.bitlen
    have hl := pad_length msg
    have hz : padZ msg.length < 28 := by unfold padZ padBlock lenField; omega
    unfold FitsBitlen at hb; unfold FitsLen; unfold i64MaxNat at *; omega
  rw [decide_ofNat_pos, decide_eq_true hpos, sudoAssert_true, ok_bind]
  rw [show Megadreifach.pad_block = Int.ofNat 28 from rfl, modI_ofNat _ (by decide), ok_bind]
  unfold SudoRt.sudoAssertEq
  rw [sEq_ofNat_zero, decide_eq_true hmod, if_pos rfl, ok_bind]
  rw [iv_cook12_refines, ok_bind, divI_ofNat _ (by decide), ok_bind,
    subI_ofNat_one _ hNpos (FitsLen.of_le hfitsP (Nat.div_le_self _ _)), ok_bind]
  rw [except_bind_pure, ← chainPre_zero (pad msg)]
  apply chain_loop (f := fun b => embedPos (chainPre (pad msg) b)) (fromN := 0)
    (toN := (pad msg).length / 28 - 1) (hle := Nat.zero_le _)
  · intro b _ hb
    have hbN : 28 * b + 28 ≤ (pad msg).length := by omega
    dsimp only
    rw [if_neg (ofNat_not_gt hb), mulI_ofNat b 28 (FitsLen.of_le hfitsP (by omega)), ok_bind,
      Nat.mul_comm b 28]
    erw [chunk_loop (pad msg) (28 * b) _ _ hbN hfitsP]
    have hwf := blockAt_wf (pad msg) b hbN (pad_bytes msg hp)
    dsimp only
    rw [show List.take 28 (List.drop (28 * b) (pad msg)) = blockAt (pad msg) b from rfl,
      phi_chunk_refines _ hwf, ok_bind,
      em_block_refines _ _ (by rw [phiUnrank_length_of_wf _ hwf]; exact Nat.le_refl _), ok_bind,
      compose_refines, ok_bind, pure_bind]
    rw [show compose (chainPre (pad msg) b) (Em.emBlock (chainPre (pad msg) b)
        (phiUnrank (fromBE (blockAt (pad msg) b)))) = chainPre (pad msg) (b + 1) from
      (chainPre_succ _ _).symm, pure_bind]
    dsimp only
    exact loopTailN b _ hb (FitsLen.of_le hfitsP (by omega)) _
  · dsimp only
    rw [position_to_bytes_refines_gen _ (injPos_chainPre _ _), ok_bind]
    unfold vhashAlg
    rw [Nat.sub_add_cancel hNpos]
    rfl

/-- Array-level form: any `pad_message`-well-formed input array. -/
theorem v_Hash_refines_array (a : Array Int) (h : WellFormedPad a) :
    Megadreifach.v_Hash a = .ok (embed (vhashAlg (decode a))) := by
  have hr := v_Hash_refines (decode a) (padWf_decode a h)
  rwa [embed_decode a h.nonneg] at hr

theorem v_MegaDreifach_refines (msg : List Nat) (hp : PadWf msg) :
    Megadreifach.v_MegaDreifach (embed msg) = .ok (embed (vhashAlg msg)) := by
  unfold Megadreifach.v_MegaDreifach
  rw [v_Hash_refines msg hp, ok_bind]
  rfl

/-- The algebraic hash is the M12 `hashBlocks` fold, instantiated with the concrete
    Davies–Meyer step, the M3 rank, the concrete IV and the big-endian block values. -/
theorem vhashAlg_eq_hashBlocks (msg : List Nat) :
    vhashAlg msg =
      hashBlocks (fun h b => Em.dmStep h (phiUnrank b)) rankPosition Em.ivCook12
        ((blocksOf (pad msg) ((pad msg).length / 28)).map fromBE) := by
  unfold vhashAlg hashBlocks digestOf mdChain positionToBytes chainPre
  rw [List.foldl_map]
  rfl

/-- Capstone in M12 form. -/
theorem v_Hash_eq_hashBlocks (msg : List Nat) (hp : PadWf msg) :
    Megadreifach.v_Hash (embed msg) =
      .ok (embed (hashBlocks (fun h b => Em.dmStep h (phiUnrank b)) rankPosition Em.ivCook12
        ((blocksOf (pad msg) ((pad msg).length / 28)).map fromBE))) := by
  rw [v_Hash_refines msg hp, vhashAlg_eq_hashBlocks]

/-- Digest length: every emitted hash is 29 bytes. -/
theorem vhashAlg_length (msg : List Nat) : (vhashAlg msg).length = 29 := by
  unfold vhashAlg positionToBytes
  rw [toBE_length]
  rfl

/-- M3 glue (partial injectivity): on injective positions, equal digests force equal
    component ranks (corner rank, packed corner ori, edge rank, packed edge ori). -/
theorem positionToBytes_components_eq (p q : Position) (hp : InjPos p) (hq : InjPos q)
    (heq : positionToBytes p = positionToBytes q) :
    evenRank (listOf p.cp) = evenRank (listOf q.cp) ∧
    packOri3 (listOfOri p.co) = packOri3 (listOfOri q.co) ∧
    evenRank (listOf p.ep) = evenRank (listOf q.ep) ∧
    packOri2 (listOfOri p.eo) = packOri2 (listOfOri q.eo) := by
  have hr := positionToBytes_rank_inj p q (rankPosition_lt_group p hp)
    (rankPosition_lt_group q hq) heq
  exact rankLists_components_eq _ _ _ _ _ _ _ _
    (evenRank_lt_countN 20 _ (permNWf_listOf p.cp hp.1) (by decide))
    (evenRank_lt_countN 20 _ (permNWf_listOf q.cp hq.1) (by decide))
    (packOri3_lt' _ (ori3Wf_listOfOri p.co)) (packOri3_lt' _ (ori3Wf_listOfOri q.co))
    (evenRank_lt_countN 30 _ (permNWf_listOf p.ep hp.2) (by decide))
    (evenRank_lt_countN 30 _ (permNWf_listOf q.ep hq.2) (by decide))
    (packOri2_lt _ (ori2Wf_listOfOri p.eo)) (packOri2_lt _ (ori2Wf_listOfOri q.eo)) hr

/-- `body_from` fully refined (digest bytes) for every injective chaining value. -/
theorem body_from_refines_full (h : Position) (deal : List Nat) (hh : InjPos h)
    (hp : isPermutation52 deal) :
    Megadreifach.body_from (embed deal) (embedPos h) =
      .ok (embed (positionToBytes (Em.dmStep h deal))) := by
  rw [body_from_refines h deal hp, position_to_bytes_dm_refines h deal hh]

/-- `HashDeckBody` (one DM block from the IV on a raw 52-card deal). -/
theorem v_HashDeckBody_refines (deal : List Nat) (hp : isPermutation52 deal) :
    Megadreifach.v_HashDeckBody (embed deal) =
      .ok (embed (positionToBytes (Em.dmStep Em.ivCook12 deal))) := by
  unfold Megadreifach.v_HashDeckBody
  rw [iv_cook12_refines, ok_bind, body_from_refines_full _ _ injPos_ivCook12 hp, ok_bind]
  rfl

end MegaDreifach.Link2
