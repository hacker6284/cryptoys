/-
  SECURITY (reduction, not a security claim).  Merkle–Damgård reduction for
  the MegaDreifach model hash `Link2.vhashAlg` (= `Generated.v_Hash` on
  `PadWf`, by `Link2.v_Hash_refines`).

  * The pad is MD-strengthened: the last 8 bytes of `pad msg` are the bit
    length (`pad_suffix`).  We prove the padded encoding is suffix-free on
    `PadWf` messages (`pad_suffix_free`, `blocks_suffix_free`).
  * `extract m₁ m₂` is a computable function returning either
      - `comp c`: a compression collision `dmBlock h₁ b₁ = dmBlock h₂ b₂`
        with `(h₁, b₁) ≠ (h₂, b₂)`, both sides genuine compression inputs of
        the two messages (28-byte blocks, reachable chaining values), or
      - `out p q`: two distinct reachable final chaining values with the same
        29-byte digest (a collision of the output encoding `positionToBytes`).
    The `out` branch is ruled out in `DigestInj.lean` (digest injectivity on
    reachable chaining values); see `extract_collision_comp`.
  * Second preimage: the `comp` collision has its first side at one of the
    target message's own compression inputs.

  Grip-rule status: INDEPENDENT of the grip rule.  The pad lemmas
  (`pad_suffix_free`, `blocks_suffix_free`) and the fromBE lemmas do not
  involve E_m at all.  `extract_collision` / `extract_second_preimage` treat
  `dmBlock` as a black box.  If E_m changes, only `injPos_chR_from` (and so `injPos_chR`) needs repair:
  it uses `Link2.injPos_dmStep` (`Link2/InjInv.lean`), which unfolds the
  v2 `Em` definitions.  The link to `Generated.v_Hash`
  (`Link2.v_Hash_refines`, `Link2.em_block_refines`) is for the v2 sudo and
  would have to be redone for a new sudo E_m.

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Link2.VHash
import MegaDreifach.Security.MDGeneric

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-! ## Decidable equality of positions (computable, via the table lists) -/

theorem position_eq_iff (p q : Position) :
    p = q ↔ (listOf p.cp = listOf q.cp ∧ listOfOri p.co = listOfOri q.co ∧
      listOf p.ep = listOf q.ep ∧ listOfOri p.eo = listOfOri q.eo) := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro ⟨h1, h2, h3, h4⟩
    exact Position.ext (listOf_inj _ _ h1) (listOfOri_inj _ _ h2)
      (listOf_inj _ _ h3) (listOfOri_inj _ _ h4)

instance : DecidableEq Position := fun p q =>
  decidable_of_iff _ (position_eq_iff p q).symm

/-! ## Blocks of a padded message -/

/-- The 28-byte blocks of `pad msg`. -/
def blocksMsg (msg : List Nat) : List (List Nat) :=
  blocksOf (pad msg) ((pad msg).length / 28)

/-- Final chaining value of `msg`. -/
def chainMsg (msg : List Nat) : Position :=
  (blocksMsg msg).foldl dmBlock Em.ivCook12

theorem vhashAlg_eq_chainMsg (msg : List Nat) :
    vhashAlg msg = positionToBytes (chainMsg msg) := rfl

theorem blocksOf_succ (xs : List Nat) (k : Nat) :
    blocksOf xs (k + 1) = blocksOf xs k ++ [blockAt xs k] := by
  unfold blocksOf; rw [List.range_succ, List.map_append]; rfl

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

/-! ## MD strengthening: the padded encoding is suffix-free -/

theorem padWf_fit (msg : List Nat) (hp : PadWf msg) : 8 * msg.length < 256 ^ 8 := by
  have h := hp.bitlen
  unfold FitsBitlen i64MaxNat at h
  have : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  omega

/-- If `pad m₁` is a suffix of `pad m₂` then `m₁ = m₂` (the length field is
    the last 8 bytes, so the lengths agree, so the pads agree). -/
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

/-- Block-level suffix-freeness of the MegaDreifach pad (MD strengthening). -/
theorem blocks_suffix_free (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hs : blocksMsg m1 <:+ blocksMsg m2) : m1 = m2 := by
  have := flatten_suffix hs
  rw [flatten_blocksMsg, flatten_blocksMsg] at this
  exact pad_suffix_free m1 m2 (padWf_fit m1 hp1) (padWf_fit m2 hp2) this

/-! ## Reachable chaining values -/

/-- Chaining from any injective position stays injective. -/
theorem injPos_chR_from (h : Position) (hh : InjPos h) :
    ∀ r : List (List Nat), InjPos (chR dmBlock h r)
  | [] => hh
  | _ :: r => by
      simp only [chR]; unfold dmBlock
      exact injPos_dmStep _ _ (injPos_chR_from h hh r)

/-- Reachable chaining values are injective (the IV case of `injPos_chR_from`). -/
theorem injPos_chR (r : List (List Nat)) : InjPos (chR dmBlock Em.ivCook12 r) :=
  injPos_chR_from _ injPos_ivCook12 r

/-! ## The extractor -/

/-- What the reduction extracts from a Hash collision. -/
inductive Break where
  /-- A compression collision on `dmBlock`. -/
  | comp (c : CompPair Position (List Nat))
  /-- Two distinct final chaining values with the same digest. -/
  | out (p q : Position)

/-- Correctness predicate for an extracted break, relative to messages `m₁, m₂`. -/
def Break.Valid (m1 m2 : List Nat) : Break → Prop
  | .comp c =>
      c.IsCollision dmBlock ∧
      (c.h1, c.b1) ∈ pairsR dmBlock Em.ivCook12 (blocksMsg m1).reverse ∧
      (c.h2, c.b2) ∈ pairsR dmBlock Em.ivCook12 (blocksMsg m2).reverse ∧
      PhiChunkWf c.b1 ∧ PhiChunkWf c.b2 ∧ InjPos c.h1 ∧ InjPos c.h2
  | .out p q =>
      p ≠ q ∧ positionToBytes p = positionToBytes q ∧ InjPos p ∧ InjPos q ∧
      p = chainMsg m1 ∧ q = chainMsg m2

/-- The MD extractor (computable). -/
def extract (m1 m2 : List Nat) : Option Break :=
  if chainMsg m1 = chainMsg m2 then
    (findR dmBlock Em.ivCook12 (blocksMsg m1).reverse (blocksMsg m2).reverse).map Break.comp
  else some (Break.out (chainMsg m1) (chainMsg m2))

/-- **MD collision reduction.**  From two distinct well-formed messages with
    equal MegaDreifach digests, `extract` returns a valid break: a compression
    collision between compression inputs of the two messages, or an output
    encoding collision between the two final chaining values. -/
theorem extract_collision (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2) (hd : vhashAlg m1 = vhashAlg m2) :
    ∃ w, extract m1 m2 = some w ∧ w.Valid m1 m2 := by
  unfold extract
  by_cases hc : chainMsg m1 = chainMsg m2
  · rw [if_pos hc]
    have hxy : ¬ blocksMsg m1 <:+ blocksMsg m2 :=
      fun h => hne (blocks_suffix_free m1 m2 hp1 hp2 h)
    have hyx : ¬ blocksMsg m2 <:+ blocksMsg m1 :=
      fun h => hne (blocks_suffix_free m2 m1 hp2 hp1 h).symm
    obtain ⟨c, hf, hcoll, hm1, hm2⟩ :=
      md_collision dmBlock Em.ivCook12 (blocksMsg m1) (blocksMsg m2) hc hxy hyx
    refine ⟨Break.comp c, by rw [hf]; rfl, hcoll, hm1, hm2, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hb, _⟩ := mem_pairsR _ _ _ _ _ hm1
      exact mem_blocksMsg m1 hp1 _ (List.mem_reverse.mp hb)
    · obtain ⟨hb, _⟩ := mem_pairsR _ _ _ _ _ hm2
      exact mem_blocksMsg m2 hp2 _ (List.mem_reverse.mp hb)
    · obtain ⟨_, s, hs, _⟩ := mem_pairsR _ _ _ _ _ hm1
      rw [hs]; exact injPos_chR s
    · obtain ⟨_, s, hs, _⟩ := mem_pairsR _ _ _ _ _ hm2
      rw [hs]; exact injPos_chR s
  · rw [if_neg hc]
    refine ⟨_, rfl, hc, hd, ?_, ?_, rfl, rfl⟩
    · unfold chainMsg; rw [foldl_eq_chR]; exact injPos_chR _
    · unfold chainMsg; rw [foldl_eq_chR]; exact injPos_chR _

/-- **MD second-preimage reduction.**  If `m' ≠ m` hits the digest of the
    target `m`, the extractor returns either an output-encoding collision or a
    compression collision whose *first* side is one of the target's own
    compression inputs `(hᵢ₋₁(m), mᵢ)` — a compression second preimage for one
    of the at most `|pad m| / 28` targets. -/
theorem extract_second_preimage (m m' : List Nat) (hp : PadWf m) (hp' : PadWf m')
    (hne : m' ≠ m) (hd : vhashAlg m' = vhashAlg m) :
    ∃ w, extract m m' = some w ∧ w.Valid m m' ∧
      ∀ c, w = Break.comp c →
        ∃ i, i < (blocksMsg m).length ∧
          c.h1 = chainPre (pad m) i ∧ c.b1 = blockAt (pad m) i := by
  obtain ⟨w, hw, hv⟩ := extract_collision m m' hp hp' (Ne.symm hne) hd.symm
  refine ⟨w, hw, hv, ?_⟩
  intro c hc
  subst hc
  have hm := hv.2.1
  -- the pairs of the reversed block list are the forward compression inputs
  exact pairsR_forward m _ _ hm
where
  pairsR_forward (m : List Nat) (h : Position) (b : List Nat)
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
    have hlen : (blocksMsg m).length = (pad m).length / 28 := by
      simp [blocksMsg, blocksOf]
    rw [hlen]
    exact key _ (Nat.le_refl _) h b hm

/-! ## Deal-level form of the compression collision -/

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
  have e : (256 : Nat) ^ 28 = phiMax := by unfold phiMax; decide
  omega

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

/-- A `dmBlock` collision on 28-byte blocks is a collision of the deal-level DM
    step `Em.dmStep h deal` on two φ-images, with distinct (chaining value, deal). -/
theorem comp_collision_deals (c : CompPair Position (List Nat))
    (hc : c.IsCollision dmBlock) (h1 : PhiChunkWf c.b1) (h2 : PhiChunkWf c.b2) :
    (c.h1 ≠ c.h2 ∨ phiUnrank (fromBE c.b1) ≠ phiUnrank (fromBE c.b2)) ∧
      Em.dmStep c.h1 (phiUnrank (fromBE c.b1)) = Em.dmStep c.h2 (phiUnrank (fromBE c.b2)) := by
  refine ⟨?_, hc.2⟩
  rcases hc.1 with h | h
  · exact Or.inl h
  · right; intro he
    exact h (fromBE_inj_28 _ _ h1 h2
      (phiUnrank_inj _ _ (fromBE_lt_28 _ h1) (fromBE_lt_28 _ h2) he))

/-! ## Without MD strengthening (for comparison)

  For a general block list the generic extractor can also end in an
  "IV preimage": `findR_collision_or_iv`.  The pad's length field is exactly
  what excludes that branch here (`blocks_suffix_free`). -/

end MegaDreifach.Security
