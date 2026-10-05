/-
  Version-neutral parts of `v_Hash` / `v_HashDeck` Link 2, shared by v2 (VHash, VHashDeck) and
  v3 (MegaDreifachV3.Link2.VHash, VHashDeck): the emitted 28-byte chunk-copy loop
  (`chunkStep`, `chunk_loop`), block and byte facts (`blockAt_wf`, `pad_bytes`, `toBE_mem_lt`,
  `phiUnrank_length_of_wf`), the 28-byte deck message (`padWf_toBE28`, `deckPadBlock`,
  `pad_len28`). `identity` is in Compose (`identity_refines`). Nothing here names a
  v2-only or v3-only emitted function. Zero sorry. No native_decide.
-/
import MegaDreifach.Link2.PadRef
import MegaDreifach.Link2.PhiChunk

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
  exact loopTailN j 27 hj (by unfold FitsLen i64MaxNat; omega) _

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

/-- The 28-byte message `toBE 28 r` (`r < 2^224`) is a well-formed `Hash` input. -/
theorem padWf_toBE28 (r : Nat) (hr : r < phiMax) : PadWf (toBE 28 r) where
  bytes := fun b hb => by
    have := toBE_mem_lt 28 r (by unfold phiMax at hr; omega) b hb
    unfold Byte; omega
  bitlen := by rw [toBE_length]; unfold FitsBitlen i64MaxNat; decide

/-- The second (last) padded block of every 28-byte message: `0x80`, 19 zero bytes,
    and the 8-byte bit length `224`. -/
def deckPadBlock : List Nat := [0x80] ++ List.replicate (padZ 28) 0 ++ toBE 8 (8 * 28)

theorem deckPadBlock_length : deckPadBlock.length = 28 := by decide

theorem pad_len28 (msg : List Nat) (hl : msg.length = 28) : pad msg = msg ++ deckPadBlock := by
  unfold pad deckPadBlock
  rw [hl]
  simp only [List.append_assoc]

end MegaDreifach.Link2
