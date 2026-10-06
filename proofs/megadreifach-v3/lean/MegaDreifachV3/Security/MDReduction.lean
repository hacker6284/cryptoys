/-
  SECURITY (reduction, not a security claim). Constructive Merkle–Damgård
  extractor for the MegaDreifach v3 model hash.

  Not collision resistance. Not a PRF claim. A green build of this file is
  not a security claim.

  `extract m₁ m₂` walks the two padded chains from the end (`findR` from
  `MegaDreifach.Security.MDGeneric`, imported, not copied) and returns the
  first compression step whose inputs differ. On a `PadWf` digest collision
  of distinct messages it returns `some (Break.comp c)` (`extract_collision_comp`).
  `CompValid` is the certificate: the inputs are distinct as φ-images, `dmStep`
  agrees, both blocks are `PhiChunkWf`, both φ-images are 52-card permutations
  accepted by `require_permutation`, both chaining values are `InjPos` and
  `isLegal`, and each side is `chainPre` of that message's pad (a `chR` from
  `ivCook12`).

  The input condition is `PadWf`, the same hypothesis as `v_Hash_refines`.
  `FitsLen` of the padded length is derived inside that refinement from
  `PadWf.bitlen`; it is not a separate assumption here.

  Suffix-freeness of `pad` is restated (`pad_suffix_free`, `blocks_suffix_free`).
  The v2 proofs live in `MegaDreifach.Security.MDReduction`, which imports the
  v2 hash and is not elaborated here. The pad lemmas they call (`pad_injective`,
  `pad_suffix`, `toBE_inj`) are imported unchanged.
  NOTE: a version-neutral home for these restated pad-suffix lemmas (and for
  `DigestInj`) is a follow-up. The v3 card-phase word in `FaceWord.lean` stays here.

  Block count on the two pads, not a count of `dmBlock` calls inside `extract`:
  `(pad m₁).length / 28 + (pad m₂).length / 28` (`chain_block_count`), at most
  `(pad m₁).length + (pad m₂).length` (`chain_block_count_le`). `findR`
  recomputes each tail with `chR`, so a run of `extract` can evaluate `dmBlock`
  more times than that.

  Zero sorry. No native_decide.
-/
import Megadreifach
import MegaDreifach.Security.MDGeneric
import MegaDreifach.Domain
import MegaDreifach.Factoradic
import MegaDreifach.Pad
import MegaDreifach.Link2.Embed
import MegaDreifach.Link2.PhiChunk
import MegaDreifach.Link2.VHashCommon
import MegaDreifachV3.Link2.Codec
import MegaDreifachV3.Link2.VHash
import MegaDreifachV3.Security.DigestInj
import MegaDreifachV3.Security.FaceWord
import MegaDreifachV3.Security.DmStepSameH

namespace MegaDreifachV3.Security

open MegaDreifach MegaDreifach.Security MegaDreifachV3.Link2 MegaDreifachV3.Em
open MegaDreifach.Link2 (PhiChunkWf phiChunk_rank_lt blockAt blockAt_wf pad_bytes
  pow256_28_eq_phiMax FitsBitlen i64MaxNat PadWf embed decode_embed InjPos)

/-! ## Blocks and chains -/

/-- The 28-byte blocks of `pad msg`. -/
def blocksMsg (msg : List Nat) : List (List Nat) :=
  blocksOf (pad msg) ((pad msg).length / 28)

/-- Final chaining value of `msg`, from `ivCook12`. -/
def chainMsg (msg : List Nat) : Position :=
  chainPre (pad msg) ((pad msg).length / 28)

theorem vhashAlg_eq_chainMsg (msg : List Nat) :
    vhashAlg msg = positionToBytes (chainMsg msg) := rfl

theorem chainMsg_foldl (msg : List Nat) :
    chainMsg msg = (blocksMsg msg).foldl dmBlock Em.ivCook12 := rfl

/-- `chainPre xs k` is the reversed-list chain of its blocks, from `ivCook12`. -/
theorem chainPre_eq_chR (xs : List Nat) (k : Nat) :
    chainPre xs k = chR dmBlock Em.ivCook12 (blocksOf xs k).reverse := by
  unfold chainPre
  rw [foldl_eq_chR]

theorem blocksOf_succ (xs : List Nat) (k : Nat) :
    blocksOf xs (k + 1) = blocksOf xs k ++ [blockAt xs k] := by
  unfold blocksOf
  rw [List.range_succ, List.map_append]
  rfl

theorem blocksMsg_length (msg : List Nat) :
    (blocksMsg msg).length = (pad msg).length / 28 := by
  simp [blocksMsg, blocksOf]

/-- Block count on the two pads: one 28-byte block per `dmBlock` input on each chain.
    This is not a claim that `extract` evaluates `dmBlock` that many times.
    `findR` recomputes tails. -/
theorem chain_block_count (m1 m2 : List Nat) :
    (blocksMsg m1).length + (blocksMsg m2).length =
      (pad m1).length / 28 + (pad m2).length / 28 := by
  simp [blocksMsg_length]

/-- Block count on the two pads is at most the padded byte lengths.
    Not a count of `dmBlock` evaluations inside `extract`. -/
theorem chain_block_count_le (m1 m2 : List Nat) :
    (blocksMsg m1).length + (blocksMsg m2).length ≤
      (pad m1).length + (pad m2).length := by
  rw [chain_block_count]
  exact Nat.add_le_add (Nat.div_le_self _ _) (Nat.div_le_self _ _)

theorem flatten_blocksOf (xs : List Nat) (k : Nat) :
    (blocksOf xs k).flatten = xs.take (28 * k) := by
  induction k with
  | zero => simp [blocksOf]
  | succ k ih =>
      rw [blocksOf_succ, List.flatten_append, ih, Nat.mul_succ, List.take_add]
      simp [blockAt]

theorem flatten_blocksMsg (msg : List Nat) : (blocksMsg msg).flatten = pad msg := by
  unfold blocksMsg
  rw [flatten_blocksOf]
  have hmod : (pad msg).length % 28 = 0 := pad_length_mod msg
  have : 28 * ((pad msg).length / 28) = (pad msg).length := by omega
  rw [this, List.take_length]

theorem mem_blocksMsg (msg : List Nat) (hp : PadWf msg) (b : List Nat)
    (hb : b ∈ blocksMsg msg) : PhiChunkWf b := by
  unfold blocksMsg blocksOf at hb
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
  have hk' := List.mem_range.mp hk
  have hmod : (pad msg).length % 28 = 0 := pad_length_mod msg
  exact blockAt_wf (pad msg) k (by omega) (pad_bytes msg hp)

/-! ## Reachable chaining values are legal -/

theorem word_dmBlock (h : Position) (blk : List Nat) (hh : Word h) :
    Word (dmBlock h blk) := by
  unfold dmBlock
  exact word_dmStep h _ hh

theorem word_foldl_dmBlock (bs : List (List Nat)) (h : Position) (hh : Word h) :
    Word (bs.foldl dmBlock h) := by
  induction bs generalizing h with
  | nil => exact hh
  | cons b bs ih =>
      simp only [List.foldl_cons]
      exact ih _ (word_dmBlock h b hh)

/-- Every `chainPre xs k` is a face-move word from `ivCook12`. -/
theorem word_chainPre (xs : List Nat) (k : Nat) : Word (chainPre xs k) := by
  induction k with
  | zero =>
      rw [chainPre_zero]
      exact word_ivCook12
  | succ k ih =>
      rw [chainPre_succ]
      exact word_dmBlock _ _ ih

/-- Every v3 MD chaining value is a legal position (`isLegal`: even permutations
    and orientation parities). This is the class on which `positionToBytes` is
    injective. `InjPos` is the weaker bijective-tables class Link 2 already uses. -/
theorem isLegal_chainPre (xs : List Nat) (k : Nat) : isLegal (chainPre xs k) :=
  word_isLegal (word_chainPre xs k)

theorem isLegal_chR (r : List (List Nat)) :
    isLegal (chR dmBlock Em.ivCook12 r) := by
  rw [chR_eq_foldl]
  exact word_isLegal (word_foldl_dmBlock r.reverse _ word_ivCook12)

theorem injPos_of_isLegal {p : Position} (h : isLegal p) : InjPos p :=
  ⟨h.1, h.2.1⟩

/-- A digest collision of two chaining values is a position collision. -/
theorem positionToBytes_inj_chainPre (xs ys : List Nat) (k j : Nat)
    (h : positionToBytes (chainPre xs k) = positionToBytes (chainPre ys j)) :
    chainPre xs k = chainPre ys j :=
  positionToBytes_inj_legal _ _ (isLegal_chainPre xs k) (isLegal_chainPre ys j) h

/-- Equal model digests are equal final chaining values, and conversely.
    Holds for every message, not only `PadWf`: every chain is `isLegal`. -/
theorem vhashAlg_eq_iff (m1 m2 : List Nat) :
    vhashAlg m1 = vhashAlg m2 ↔ chainMsg m1 = chainMsg m2 := by
  constructor
  · intro h
    have h' : positionToBytes (chainMsg m1) = positionToBytes (chainMsg m2) := by
      simpa [vhashAlg_eq_chainMsg] using h
    exact positionToBytes_inj_chainPre _ _ _ _ h'
  · intro h
    simpa [vhashAlg_eq_chainMsg] using congrArg positionToBytes h

/-! ## MD strengthening: the pad is suffix-free

  Restated from v2. `pad_injective`, `pad_suffix` and `toBE_inj` are imported. -/

theorem padWf_fit (msg : List Nat) (hp : PadWf msg) : 8 * msg.length < 256 ^ 8 := by
  have h := hp.bitlen
  unfold FitsBitlen i64MaxNat at h
  have : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  omega

/-- If `pad m₁` is a suffix of `pad m₂` then `m₁ = m₂`. The length field is
    the last 8 bytes. -/
theorem pad_suffix_free (m1 m2 : List Nat)
    (h1 : 8 * m1.length < 256 ^ 8) (h2 : 8 * m2.length < 256 ^ 8)
    (hs : pad m1 <:+ pad m2) : m1 = m2 := by
  obtain ⟨t, ht⟩ := hs
  have hl1 := pad_length m1
  have hl2 := pad_length m2
  have hlen : (pad m2).length = t.length + (pad m1).length := by
    rw [← ht, List.length_append]
  have hd : (pad m2).drop ((pad m2).length - 8) = (pad m1).drop ((pad m1).length - 8) := by
    have e1 : (pad m2).drop ((pad m2).length - 8) = (t ++ pad m1).drop ((pad m2).length - 8) := by
      rw [ht]
    rw [e1, List.drop_append_eq_append_drop]
    have : (pad m2).length - 8 - t.length = (pad m1).length - 8 := by omega
    rw [this, List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [pad_suffix, pad_suffix] at hd
  have hbits := toBE_inj 8 _ _ h2 h1 hd
  have hml : m1.length = m2.length := by omega
  have hpl : (pad m1).length = (pad m2).length := by rw [hl1, hl2, hml]
  have hpe : pad m1 = pad m2 := List.IsSuffix.eq_of_length ⟨t, ht⟩ hpl
  exact pad_injective m1 m2 h1 h2 hpe

theorem flatten_suffix {γ : Type} {l1 l2 : List (List γ)} (h : l1 <:+ l2) :
    l1.flatten <:+ l2.flatten := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t.flatten, by rw [← List.flatten_append, ht]⟩

/-- Block-level suffix-freeness on `PadWf` (the length field rules out an
    IV-preimage branch of `findR`). -/
theorem blocks_suffix_free (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hs : blocksMsg m1 <:+ blocksMsg m2) : m1 = m2 := by
  have := flatten_suffix hs
  rw [flatten_blocksMsg, flatten_blocksMsg] at this
  exact pad_suffix_free m1 m2 (padWf_fit m1 hp1) (padWf_fit m2 hp2) this

/-! ## φ-images of pad blocks are permutations -/

theorem fromBE_lt_28 (bs : List Nat) (h : PhiChunkWf bs) : fromBE bs < phiMax := by
  have hb : ∀ i, i < bs.length → bs[i]?.getD 0 < (List.replicate bs.length 256)[i]?.getD 0 := by
    intro i hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_replicate, if_pos hi]
    simp only [Option.getD_some]
    have := h.byte _ (List.getElem_mem hi); omega
  have := mixEncode_lt (List.replicate bs.length 256) bs (by simp) hb
  unfold fromBE
  rw [product_replicate_256] at this
  rw [h.len] at this ⊢
  rw [pow256_28_eq_phiMax] at this
  exact this

theorem fromBE_inj_28 (b1 b2 : List Nat) (h1 : PhiChunkWf b1) (h2 : PhiChunkWf b2)
    (heq : fromBE b1 = fromBE b2) : b1 = b2 := by
  have bnd : ∀ bs : List Nat, PhiChunkWf bs → ∀ i, i < bs.length →
      bs[i]?.getD 0 < (List.replicate 28 256)[i]?.getD 0 := by
    intro bs h i hi
    have hi' : i < 28 := by rw [h.len] at hi; exact hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_replicate, if_pos hi']
    simp only [Option.getD_some]
    have := h.byte _ (List.getElem_mem hi); omega
  unfold fromBE at heq
  rw [h1.len, h2.len] at heq
  exact mixEncode_inj _ _ _ (by rw [h1.len]; simp) (by rw [h2.len]; simp)
    (bnd b1 h1) (bnd b2 h2) heq

theorem isPermutation52_phiChunk (bs : List Nat) (h : PhiChunkWf bs) :
    isPermutation52 (phiUnrank (fromBE bs)) := by
  have hp := lehmerUnrank_perm 52 (fromBE bs) (phiChunk_rank_lt bs h)
  have hlen := hp.length_eq
  rw [List.length_range] at hlen
  refine ⟨hlen, hp.nodup_iff.mpr (List.nodup_range 52), ?_⟩
  intro x hx
  exact List.mem_range.mp (hp.mem_iff.mp hx)

theorem require_permutation_phiChunk (bs : List Nat) (h : PhiChunkWf bs) :
    Megadreifach.require_permutation (embed (phiUnrank (fromBE bs))) =
      .ok (embed (phiUnrank (fromBE bs))) :=
  (require_permutation_refines _ (isPermutation52_phiChunk bs h)).1

/-- A `dmBlock` collision on 28-byte blocks is a `dmStep` collision on the
    φ-images, and the inputs differ as `(chaining value, deal)`. -/
theorem comp_collision_deals (c : CompPair Position (List Nat))
    (hc : c.IsCollision dmBlock) (h1 : PhiChunkWf c.b1) (h2 : PhiChunkWf c.b2) :
    (c.h1 ≠ c.h2 ∨ phiUnrank (fromBE c.b1) ≠ phiUnrank (fromBE c.b2)) ∧
      dmStep c.h1 (phiUnrank (fromBE c.b1)) =
        dmStep c.h2 (phiUnrank (fromBE c.b2)) := by
  refine ⟨?_, ?_⟩
  · rcases hc.1 with h | h
    · exact Or.inl h
    · right
      intro he
      exact h (fromBE_inj_28 _ _ h1 h2
        (phiUnrank_inj _ _ (fromBE_lt_28 _ h1) (fromBE_lt_28 _ h2) he))
  · simpa [dmBlock] using hc.2

/-! ## The extractor -/

/-- What `extract` returns. `comp` is a compression collision. `out` is the
    branch where the final chaining values differ; a `PadWf` digest collision
    does not take it (`vhashAlg_eq_iff`). -/
inductive Break where
  | comp (c : CompPair Position (List Nat))
  | out (p q : Position)

/-- Certificate for a compression collision extracted from messages `m₁, m₂`.

    * distinct φ-images (or distinct chaining values) and equal `dmStep`
    * both blocks `PhiChunkWf`; both φ-images permutations, so the emitted
      `require_permutation` returns them
    * both chaining values `InjPos` and `isLegal`
    * each side is block `i` of that message: `chainPre (pad m) i`, which is
      `chR` from `ivCook12` of the reversed prefix -/
def CompValid (m1 m2 : List Nat) (c : CompPair Position (List Nat)) : Prop :=
  (c.h1 ≠ c.h2 ∨ phiUnrank (fromBE c.b1) ≠ phiUnrank (fromBE c.b2)) ∧
  dmStep c.h1 (phiUnrank (fromBE c.b1)) =
    dmStep c.h2 (phiUnrank (fromBE c.b2)) ∧
  PhiChunkWf c.b1 ∧ PhiChunkWf c.b2 ∧
  isPermutation52 (phiUnrank (fromBE c.b1)) ∧
  isPermutation52 (phiUnrank (fromBE c.b2)) ∧
  Megadreifach.require_permutation (embed (phiUnrank (fromBE c.b1))) =
    .ok (embed (phiUnrank (fromBE c.b1))) ∧
  Megadreifach.require_permutation (embed (phiUnrank (fromBE c.b2))) =
    .ok (embed (phiUnrank (fromBE c.b2))) ∧
  InjPos c.h1 ∧ InjPos c.h2 ∧
  isLegal c.h1 ∧ isLegal c.h2 ∧
  (∃ i, i < (blocksMsg m1).length ∧
    c.h1 = chainPre (pad m1) i ∧
    c.h1 = chR dmBlock Em.ivCook12 (blocksOf (pad m1) i).reverse ∧
    c.b1 = blockAt (pad m1) i) ∧
  (∃ j, j < (blocksMsg m2).length ∧
    c.h2 = chainPre (pad m2) j ∧
    c.h2 = chR dmBlock Em.ivCook12 (blocksOf (pad m2) j).reverse ∧
    c.b2 = blockAt (pad m2) j)

/-- The MD extractor. If the final chaining values agree, walk both reversed
    block lists (`findR`) and return the first step whose compression inputs
    differ. Otherwise return the two final positions (`Break.out`).

    Block count on the two pads: `chain_block_count` / `chain_block_count_le`
    (`(pad m1).length / 28 + (pad m2).length / 28`, at most the padded byte
    lengths). That is not how many times this `def` evaluates `dmBlock`:
    `findR` recomputes each tail. Not collision resistance. Not a PRF claim. -/
def extract (m1 m2 : List Nat) : Option Break :=
  if chainMsg m1 = chainMsg m2 then
    (findR dmBlock Em.ivCook12 (blocksMsg m1).reverse (blocksMsg m2).reverse).map Break.comp
  else some (Break.out (chainMsg m1) (chainMsg m2))

private theorem pairsR_forward (m : List Nat) (h : Position) (b : List Nat)
    (hm : (h, b) ∈ pairsR dmBlock Em.ivCook12 (blocksMsg m).reverse) :
    ∃ i, i < (blocksMsg m).length ∧ h = chainPre (pad m) i ∧ b = blockAt (pad m) i := by
  have key : ∀ k, k ≤ (pad m).length / 28 → ∀ h b,
      (h, b) ∈ pairsR dmBlock Em.ivCook12 (blocksOf (pad m) k).reverse →
      ∃ i, i < k ∧ h = chainPre (pad m) i ∧ b = blockAt (pad m) i := by
    intro k
    induction k with
    | zero => intro _ h b hm; simp [blocksOf, pairsR] at hm
    | succ k ih =>
        intro hk h b hm
        have hrev : (blocksOf (pad m) (k + 1)).reverse =
            blockAt (pad m) k :: (blocksOf (pad m) k).reverse := by
          rw [blocksOf_succ, List.reverse_append]; rfl
        rw [hrev] at hm
        simp only [pairsR, List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨h1, h2⟩ | hm
        · refine ⟨k, Nat.lt_succ_self k, ?_, h2⟩
          rw [h1, chR_eq_foldl, List.reverse_reverse]; rfl
        · obtain ⟨i, hi, e1, e2⟩ := ih (by omega) h b hm
          exact ⟨i, by omega, e1, e2⟩
  have hlen : (blocksMsg m).length = (pad m).length / 28 := blocksMsg_length m
  rw [hlen]
  exact key _ (Nat.le_refl _) h b hm

private theorem extract_comp_inputs (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2) (hd : vhashAlg m1 = vhashAlg m2) :
    ∃ c, extract m1 m2 = some (Break.comp c) ∧
      c.IsCollision dmBlock ∧
      (c.h1, c.b1) ∈ pairsR dmBlock Em.ivCook12 (blocksMsg m1).reverse ∧
      (c.h2, c.b2) ∈ pairsR dmBlock Em.ivCook12 (blocksMsg m2).reverse ∧
      PhiChunkWf c.b1 ∧ PhiChunkWf c.b2 := by
  have hchain : chainMsg m1 = chainMsg m2 := (vhashAlg_eq_iff m1 m2).mp hd
  unfold extract
  rw [if_pos hchain]
  have hxy : ¬ blocksMsg m1 <:+ blocksMsg m2 :=
    fun hs => hne (blocks_suffix_free m1 m2 hp1 hp2 hs)
  have hyx : ¬ blocksMsg m2 <:+ blocksMsg m1 :=
    fun hs => hne (blocks_suffix_free m2 m1 hp2 hp1 hs).symm
  obtain ⟨c, hf, hcoll, hm1, hm2⟩ :=
    md_collision dmBlock Em.ivCook12 (blocksMsg m1) (blocksMsg m2) hchain hxy hyx
  refine ⟨c, ?_, hcoll, hm1, hm2, ?_, ?_⟩
  · rw [hf]; rfl
  · obtain ⟨hb, _⟩ := mem_pairsR dmBlock Em.ivCook12 _ _ _ hm1
    exact mem_blocksMsg m1 hp1 _ (List.mem_reverse.mp hb)
  · obtain ⟨hb, _⟩ := mem_pairsR dmBlock Em.ivCook12 _ _ _ hm2
    exact mem_blocksMsg m2 hp2 _ (List.mem_reverse.mp hb)

/-- **MD collision reduction for the v3 model hash.**

    Two distinct `PadWf` messages with equal `vhashAlg` digests make `extract`
    return `some (Break.comp c)` with `CompValid m1 m2 c`. That is a `dmStep`
    collision on distinct φ-images, at compression inputs of the two chains
    from `ivCook12`, on blocks `require_permutation` accepts.

    Not collision resistance: a hash collision is reduced to a compression
    collision. Nothing is claimed about whether either exists. Not a PRF claim.
    A green build is not a security claim. -/
theorem extract_collision_comp (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2) (hd : vhashAlg m1 = vhashAlg m2) :
    ∃ c, extract m1 m2 = some (Break.comp c) ∧ CompValid m1 m2 c := by
  obtain ⟨c, hf, hcoll, hm1, hm2, hb1, hb2⟩ :=
    extract_comp_inputs m1 m2 hp1 hp2 hne hd
  obtain ⟨i, hi, hhi, hbi⟩ := pairsR_forward m1 c.h1 c.b1 hm1
  obtain ⟨j, hj, hhj, hbj⟩ := pairsR_forward m2 c.h2 c.b2 hm2
  have hdeals := comp_collision_deals c hcoll hb1 hb2
  refine ⟨c, hf, ?_⟩
  unfold CompValid
  refine ⟨hdeals.1, hdeals.2, hb1, hb2,
    isPermutation52_phiChunk _ hb1, isPermutation52_phiChunk _ hb2,
    require_permutation_phiChunk _ hb1, require_permutation_phiChunk _ hb2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hhi]; exact injPos_chainPre (pad m1) i
  · rw [hhj]; exact injPos_chainPre (pad m2) j
  · rw [hhi]; exact isLegal_chainPre (pad m1) i
  · rw [hhj]; exact isLegal_chainPre (pad m2) j
  · refine ⟨i, hi, hhi, ?_, hbi⟩
    rw [hhi, chainPre_eq_chR]
  · refine ⟨j, hj, hhj, ?_, hbj⟩
    rw [hhj, chainPre_eq_chR]

/-- Same reduction for the emitted `v_Hash`, via `v_Hash_refines` on `PadWf`. -/
theorem vhashAlg_eq_of_v_Hash (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hd : Megadreifach.v_Hash (embed m1) = Megadreifach.v_Hash (embed m2)) :
    vhashAlg m1 = vhashAlg m2 := by
  rw [v_Hash_refines m1 hp1, v_Hash_refines m2 hp2] at hd
  have hd' : embed (vhashAlg m1) = embed (vhashAlg m2) := Except.ok.inj hd
  have l1 := decode_embed (vhashAlg m1)
  have l2 := decode_embed (vhashAlg m2)
  rw [← l1, ← l2, hd']

/-- **MD collision reduction for emitted `v_Hash`.**

    Hypotheses are exactly those of `v_Hash_refines`: `PadWf` on each message,
    the messages distinct, and the emitted digests equal. Conclusion is the
    same `CompValid` certificate as `extract_collision_comp`.

    Not collision resistance. Not a PRF claim. A green build is not a security claim. -/
theorem v_Hash_collision_comp (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2)
    (hd : Megadreifach.v_Hash (embed m1) = Megadreifach.v_Hash (embed m2)) :
    ∃ c, extract m1 m2 = some (Break.comp c) ∧ CompValid m1 m2 c :=
  extract_collision_comp m1 m2 hp1 hp2 hne (vhashAlg_eq_of_v_Hash m1 m2 hp1 hp2 hd)

/-- **MD second-preimage reduction.** If `m' ≠ m` hits the model digest of the
    target `m`, `extract m m'` returns a compression collision whose first side
    is one of `m`'s own compression inputs (`CompValid`'s index for `m`).
    Not a second-preimage resistance claim. Not a PRF claim. -/
theorem extract_second_preimage_comp (m m' : List Nat) (hp : PadWf m) (hp' : PadWf m')
    (hne : m' ≠ m) (hd : vhashAlg m' = vhashAlg m) :
    ∃ c, extract m m' = some (Break.comp c) ∧ CompValid m m' c :=
  extract_collision_comp m m' hp hp' (Ne.symm hne) hd.symm

/-- `extract_second_preimage_comp` for emitted `v_Hash`. Same `PadWf` hypotheses
    as `v_Hash_refines`. Not a second-preimage resistance claim. -/
theorem v_Hash_second_preimage_comp (m m' : List Nat) (hp : PadWf m) (hp' : PadWf m')
    (hne : m' ≠ m)
    (hd : Megadreifach.v_Hash (embed m') = Megadreifach.v_Hash (embed m)) :
    ∃ c, extract m m' = some (Break.comp c) ∧ CompValid m m' c :=
  extract_second_preimage_comp m m' hp hp' hne (vhashAlg_eq_of_v_Hash m' m hp' hp hd)

/-- When `c.h1 = c.h2`, A(b) (`dmStep_same_h_iff`) turns the `CompValid` `dmStep`
    collision into an `emBlock` collision on that same chaining value. The deals
    differ because `CompValid` already says the inputs differ. Nothing is said
    when the chaining values differ (free-start). Not collision resistance.
    Not a PRF claim. A green build is not a security claim. -/
theorem compValid_emBlock_of_same_h (m1 m2 : List Nat) (c : CompPair Position (List Nat))
    (hv : CompValid m1 m2 c) (hh : c.h1 = c.h2) :
    phiUnrank (fromBE c.b1) ≠ phiUnrank (fromBE c.b2) ∧
      emBlock c.h1 (phiUnrank (fromBE c.b1)) =
        emBlock c.h2 (phiUnrank (fromBE c.b2)) := by
  unfold CompValid at hv
  obtain ⟨hdist, hstep, _, _, _, _, _, _, hinj, _, _, _, _, _⟩ := hv
  refine ⟨?_, ?_⟩
  · rcases hdist with h | h
    · exact absurd hh h
    · exact h
  · -- Rewrite only the chaining-value argument. `rw` would open `emBlock`.
    have hstep' : dmStep c.h1 (phiUnrank (fromBE c.b1)) =
        dmStep c.h1 (phiUnrank (fromBE c.b2)) :=
      hstep.trans ((congrArg (fun h => dmStep h (phiUnrank (fromBE c.b2))) hh).symm)
    have hW : emBlock c.h1 (phiUnrank (fromBE c.b1)) =
        emBlock c.h1 (phiUnrank (fromBE c.b2)) :=
      (dmStep_same_h_iff c.h1 hinj _ _).mp hstep'
    exact hW.trans (congrArg (fun h => emBlock h (phiUnrank (fromBE c.b2))) hh)

end MegaDreifachV3.Security
