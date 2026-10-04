/-
  MegaDreifach v3 Link 2: `iv_cook12` and `Hash`.
  `iv_cook12_refines`: the emitted IV is the v2 model `Em.ivCook12` (v3 keeps the IV).
  `v_Hash_refines` (on `PadWf`): the emitted v3 `Hash` is the algebraic MD hash: pad, split
  into 28-byte blocks, `phiUnrank ∘ fromBE`, Davies–Meyer with the v3 `Em.dmStep` (the
  sudo's `dm_step`, `compose h (emBlock h deal)`) from `ivCook12`, then the 29-byte rank
  digest.
  The chunk-copy loop lemmas are shared with v2 (`MegaDreifach/Link2/VHashCommon.lean`).
-/
import MegaDreifachV3.Link2.EmRun
import MegaDreifachV3.Link2.Codec
import MegaDreifach.Link2.PadRef
import MegaDreifach.Link2.PhiChunk
import MegaDreifach.Link2.VHashCommon

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Link2

/-- Identity cooked by the first `i` unit face turns. -/
def ivPre (i : Nat) : Position :=
  (List.range i).foldl (fun g f => if hf : f < 12 then Em.faceTurn g ⟨f, hf⟩ 1 else g)
    MegaDreifach.identity

theorem ivPre_succ (i : Nat) (hi : i < 12) : ivPre (i + 1) = Em.faceTurn (ivPre i) ⟨i, hi⟩ 1 := by
  unfold ivPre
  rw [List.range_succ, List.foldl_append]
  simp [hi]

theorem iv_cook12_refines : Megadreifach.iv_cook12 = .ok (embedPos Em.ivCook12) := by
  unfold Megadreifach.iv_cook12
  rw [identity_refines, ok_bind]
  dsimp only
  rw [except_bind_pure]
  apply chain_loop (f := fun i => embedPos (ivPre i)) (fromN := 0) (toN := 11) (hle := by decide)
  · intro i _ hi
    dsimp only
    rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hi),
      show (1 : Int) = Int.ofNat 1 from rfl,
      show Int.ofNat i = Int.ofNat (⟨i, by omega⟩ : Fin 12).val from rfl,
      face_turn_refines, ok_bind]
    dsimp only
    rw [pure_bind, ← ivPre_succ i (by omega)]
    exact loopTailN i 11 hi (by unfold FitsLen i64MaxNat; omega) _
  · rfl

theorem injPos_identity : InjPos MegaDreifach.identity :=
  by
  constructor <;> intro a b h <;> exact h

theorem injPos_ivCook12' : InjPos Em.ivCook12 := by
  unfold Em.ivCook12
  generalize List.range 12 = l
  have key : ∀ (l : List Nat) (g : Position), InjPos g →
      InjPos (l.foldl (fun g f => if hf : f < 12 then Em.faceTurn g ⟨f, hf⟩ 1 else g) g) := by
    intro l
    induction l with
    | nil => intro g hg; exact hg
    | cons f l ih =>
      intro g hg
      apply ih
      dsimp only
      split
      · exact injPos_faceTurn g _ 1 hg
      · exact hg
  exact key l _ injPos_identity

/-! ## Algebraic v3 hash -/

theorem phiUnrank_cards (bs : List Nat) (h : PhiChunkWf bs) :
    ∀ c ∈ phiUnrank (fromBE bs), c < 52 := by
  intro c hc
  have hp := lehmerUnrank_perm 52 (fromBE bs) (phiChunk_rank_lt bs h)
  have := hp.mem_iff.mp hc
  simpa using this

/-- One v3 Davies–Meyer step on a 28-byte block. -/
def dmBlock (h : Position) (blk : List Nat) : Position :=
  MegaDreifachV3.Em.dmStep h (phiUnrank (fromBE blk))

/-- The 28-byte blocks of `xs` (first `k`). -/
def blocksOf (xs : List Nat) (k : Nat) : List (List Nat) := (List.range k).map (blockAt xs)

/-- v3 chaining value after the first `k` blocks. -/
def chainPre (xs : List Nat) (k : Nat) : Position := (blocksOf xs k).foldl dmBlock Em.ivCook12

theorem chainPre_zero (xs : List Nat) : chainPre xs 0 = Em.ivCook12 := by
  unfold chainPre blocksOf
  rw [List.range_zero, List.map_nil, List.foldl_nil]

theorem chainPre_succ (xs : List Nat) (k : Nat) :
    chainPre xs (k + 1) = dmBlock (chainPre xs k) (blockAt xs k) := by
  unfold chainPre blocksOf
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

/-- Algebraic MegaDreifach v3 hash. -/
def vhashAlg (msg : List Nat) : List Nat :=
  positionToBytes (chainPre (pad msg) ((pad msg).length / 28))

theorem injPos_dmBlock (h : Position) (blk : List Nat) (hh : InjPos h) : InjPos (dmBlock h blk) :=
  dmStep_inj h hh _

theorem injPos_foldl_dmBlock (l : List (List Nat)) : ∀ h, InjPos h →
    InjPos (l.foldl dmBlock h) := by
  induction l with
  | nil => intro h hh; exact hh
  | cons b bs ih => intro h hh; exact ih _ (injPos_dmBlock h _ hh)

theorem injPos_chainPre (xs : List Nat) (k : Nat) : InjPos (chainPre xs k) :=
  injPos_foldl_dmBlock _ _ injPos_ivCook12'

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
  rw [show Megadreifach.pad_block = Int.ofNat 28 from rfl, MegaDreifach.Link2.modI_ofNat _ (by decide), ok_bind]
  unfold SudoRt.sudoAssertEq
  rw [sEq_ofNat_zero, decide_eq_true hmod, if_pos rfl, ok_bind]
  rw [iv_cook12_refines, ok_bind, MegaDreifach.Link2.divI_ofNat _ (by decide), ok_bind,
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
      dm_step_refines _ (injPos_chainPre _ _) _
        (by rw [phiUnrank_length_of_wf _ hwf]; exact Nat.le_refl _) (phiUnrank_cards _ hwf), ok_bind]
    rw [show MegaDreifachV3.Em.dmStep (chainPre (pad msg) b)
        (phiUnrank (fromBE (blockAt (pad msg) b))) = chainPre (pad msg) (b + 1) from
      (chainPre_succ _ _).symm, pure_bind]
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

end MegaDreifachV3.Link2
