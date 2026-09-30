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

namespace MegaDreifach.Link2

open MegaDreifach

/-- Emitted 28-byte chunk-copy stepper (`chunk.append(padded[i + j])`). -/
def chunkStep (padded : Array Int) (i : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let j := σ.1
  let chunk := σ.2
  do
    if j > (27 : Int) then
      pure (SudoRt.Flow.brk (ρ := Array Int) (j, chunk))
    else
      match ← ((do
        let _t890 ← SudoRt.addI i j
        let _t891 ← SudoRt.atL padded _t890
        let _mb892 := SudoRt.appendL chunk _t891
        let ⟨_nr893, _⟩ := _mb892
        let chunk := _nr893
        let _hm876 := ()
        let _u894 := _hm876
        pure (SudoRt.Flow.cont (ρ := Array Int) chunk)) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array Int) (j, _fs))
      | .cont _fs => do
          if j == (27 : Int) then
            pure (SudoRt.Flow.brk (ρ := Array Int) (j, _fs))
          else do
            let i' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', _fs))

/-- The `b`-th 28-byte block of `xs`. -/
def blockAt (xs : List Nat) (b : Nat) : List Nat := (xs.drop (28 * b)).take 28

theorem take_succ_drop (xs : List Nat) (i j : Nat) (h : i + j < xs.length) :
    (xs.drop i).take (j + 1) = (xs.drop i).take j ++ [xs[i + j]'h] := by
  rw [List.take_succ]
  congr 1
  have h' : j < (xs.drop i).length := by rw [List.length_drop]; omega
  rw [List.getElem?_eq_getElem h', List.getElem_drop]
  rfl

theorem embed_append_one (xs : List Nat) (x : Nat) :
    embed (xs ++ [x]) = (embed xs).push (Int.ofNat x) := by
  simp [embed, List.map_append, Array.push]

theorem chunkStep_hit (xs : List Nat) (i0 j : Nat) (hj : j ≤ 27)
    (hlen : i0 + 28 ≤ xs.length) (hfits : FitsLen xs.length) :
    chunkStep (embed xs) (Int.ofNat i0) (Int.ofNat j, embed ((xs.drop i0).take j)) =
      if j = 27 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, embed ((xs.drop i0).take (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed ((xs.drop i0).take (j + 1)))) := by
  unfold chunkStep
  rw [show (27 : Int) = Int.ofNat 27 from rfl, if_neg (ofNat_not_gt hj),
    addI_ofNat i0 j (FitsLen.of_le hfits (by omega)), ok_bind,
    atL_embed xs (i0 + j) (by omega), ok_bind]
  dsimp only [SudoRt.appendL]
  rw [take_succ_drop xs i0 j (by omega), embed_append_one]
  exact loopTailR j 27 hj (by decide) _

theorem chunk_loop {β : Type} (xs : List Nat) (i0 : Nat)
    (after : Int × Array Int → Except SudoRt.Trap β) (onRet : Array Int → Except SudoRt.Trap β)
    (hlen : i0 + 28 ≤ xs.length) (hfits : FitsLen xs.length) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) (fuelRange 0 27)
      (chunkStep (embed xs) (Int.ofNat i0)) after onRet =
      after (Int.ofNat 27, embed ((xs.drop i0).take 28)) := by
  have h0 : ((0 : Int), (#[] : Array Int)) =
      (Int.ofNat 0, embed ((xs.drop i0).take 0)) := rfl
  rw [h0]
  exact chain_loop _ after onRet (fun j => embed ((xs.drop i0).take j)) 0 27 (by decide)
    (fun j _ hj => chunkStep_hit xs i0 j hj hlen hfits) _ rfl

theorem toBE_mem_lt (w v : Nat) (hv : v < 256 ^ w) : ∀ x ∈ toBE w v, x < 256 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hb := mixDecode_bound (List.replicate w 256) v (by rw [product_replicate_256]; exact hv)
    (fun r hr => by rw [(List.mem_replicate.mp hr).2]; decide) i hi
  have hi' : i < w := by rw [toBE_length] at hi; exact hi
  have hi2 : i < (List.replicate w 256).length := by rw [List.length_replicate]; exact hi'
  rw [List.getElem?_eq_getElem (l := mixDecode (List.replicate w 256) v) hi,
    List.getElem?_eq_getElem hi2, Option.getD_some, Option.getD_some, List.getElem_replicate] at hb
  exact hb

theorem pad_bytes (msg : List Nat) (hp : PadWf msg) : ∀ b ∈ pad msg, b ≤ 255 := by
  intro b hb
  unfold pad at hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact hp.bytes b hb
  · omega
  · rw [(List.mem_replicate.mp hb).2]; decide
  · have hfit := hp.bitlen
    unfold FitsBitlen i64MaxNat at hfit
    have := toBE_mem_lt 8 (8 * msg.length) (by omega) b hb
    omega

theorem blockAt_wf (xs : List Nat) (b : Nat) (hlen : 28 * b + 28 ≤ xs.length)
    (hbytes : ∀ x ∈ xs, x ≤ 255) : PhiChunkWf (blockAt xs b) where
  len := by unfold blockAt; rw [List.length_take, List.length_drop]; omega
  byte := fun x hx => hbytes x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem phiUnrank_length_of_wf (bs : List Nat) (h : PhiChunkWf bs) :
    (phiUnrank (fromBE bs)).length = 52 := by
  have := (lehmerUnrank_perm 52 (fromBE bs) (phiChunk_rank_lt bs h)).length_eq
  rw [List.length_range] at this
  exact this

theorem loopTailN {α ρ : Type} (i toN : Nat) (hi : i ≤ toN) (hf : FitsLen (i + 1)) (st : α) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := ρ) (Int.ofNat i, st)) : Except SudoRt.Trap _)
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', st))) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  by_cases heq : i = toN
  · subst heq; simp [beq_int_iff]; rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    rw [ite_int_beq, if_neg hneI, addI_ofNat_one i hf, ok_bind, if_neg heq]
    rfl

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
