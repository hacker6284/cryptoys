/-
  LINK 2 (private copy). `Generated.position_to_bytes` refines algebraic
  `positionToBytes` on every position whose corner and edge permutations
  are injective (`InjPos`). No legality / parity / orientation-sum
  hypothesis is needed: the emitted rank only reads the first `n-2`
  Lehmer digits, and `Fin`-typed orientations are automatically in range.

  CLOSED: `big_to_be_gen`, `position_to_bytes_refines_gen`,
  `rankPosition_lt_digest`.
-/
import MegaDreifachV1.Link2.EvenRankGen
import MegaDreifachV1.Link2.PosBytes

namespace MegaDreifachV1.Link2

set_option maxHeartbeats 4000000

/-! ## `big_to_be` for multi-limb values -/

theorem divmod256_gen (v : Nat) (hv : v < limbBase ^ 8) :
    Megadreifach.big_divmod_small (bigOf (natLimbs v)) (256 : Int) =
      .ok (bigOf (natLimbs (v / 256)), ((v % 256 : Nat) : Int)) := by
  have hl := natLimbs_length_le v 8 hv
  have h := big_divmod_nat 256 v (by decide) (by unfold limbBase; decide)
    (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 8) hl)
  exact h

def beAccN (v i : Nat) : Megadreifach.BigInt × Array Int :=
  (bigOf (natLimbs (v / 256 ^ (i - 1))), embed (leBytes (i - 1) v))

theorem beStepN_width (w v i : Nat) (hv : v < limbBase ^ 8) (hwf : FitsLen w)
    (hi1 : 1 ≤ i) (hiw : i ≤ w) :
    beStep (Int.ofNat w) (Int.ofNat i, beAccN v i) =
      if i = w then
        .ok (SudoRt.Flow.brk (Int.ofNat i, beAccN v (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), beAccN v (i + 1))) := by
  unfold beStep beAccN
  dsimp only
  rw [if_neg (ofNat_not_gt hiw)]
  have hv' : v / 256 ^ (i - 1) < limbBase ^ 8 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  rw [divmod256_gen _ hv', ok_bind, appendL_spec]
  have hdiv : (v / 256 ^ (i - 1)) / 256 = v / 256 ^ i := by
    have hi : (i - 1) + 1 = i := by omega
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow256_succ, hi]
  rw [← ofNat_eq_natCast ((v / 256 ^ (i - 1)) % 256),
    push_embed (leBytes (i - 1) v) ((v / 256 ^ (i - 1)) % 256), hdiv]
  have hle :
      leBytes (i - 1) v ++ [(v / 256 ^ (i - 1)) % 256] = leBytes ((i - 1) + 1) v :=
    (leBytes_succ_append (i - 1) v).symm
  have hidx : (i - 1) + 1 = i := by omega
  rw [hle, hidx]
  have hnext : (i + 1) - 1 = i := by omega
  by_cases hi : i = w
  · simp [hi, hnext, beq_int_iff]
    rfl
  · have hne : ¬ (Int.ofNat i = Int.ofNat w) := fun h => hi (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (FitsLen.of_le hwf (by omega))
    simp only [hi, if_false, beq_iff_eq, hne, hadd, ok_bind, hnext]
    rfl

theorem big_to_be_gen (w v : Nat) (hw : 0 < w) (hwf : FitsLen w) (hvB : v < limbBase ^ 8)
    (hbyte : v < 256 ^ w) :
    Megadreifach.big_to_be (bigOf (natLimbs v)) (Int.ofNat w) =
      .ok (embed (toBE w v)) := by
  unfold Megadreifach.big_to_be
  dsimp only
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := beStep (Int.ofNat w))
    intro σ
    unfold beStep
    rfl
  rw [fuelRange_eq (1 : Int) (Int.ofNat w)]
  rw [show (1 : Int) = Int.ofNat 1 from rfl,
    show (#[] : Array Int) = embed ([] : List Nat) from rfl,
    show (bigOf (natLimbs v), embed ([] : List Nat)) = beAccN v 1 by
      simp [beAccN, leBytes, Nat.pow_zero, Nat.div_one]]
  apply chain_loop (beStep (Int.ofNat w))
    (f := beAccN v) (fromN := 1) (toN := w) (hle := by omega)
    (hstep := fun i hi1 hiw => beStepN_width w v i hvB hwf hi1 hiw)
    (goal := .ok (embed (toBE w v)))
    (hafter := by
      dsimp [beAccN]
      rw [listLen_embed, leBytes_length, subI_ofNat_one w hw hwf, ok_bind]
      rw [fuelDown_eq (Int.ofNat (w - 1)) 0]
      have hdrop : (leBytes w v).drop w = [] := by
        have h := List.drop_length (leBytes w v)
        rwa [leBytes_length w v] at h
      rw [show (embed [] : Array Int) =
          embed ((leBytes w v).drop w).reverse by rw [hdrop]; rfl]
      rw [except_bind_pure]
      apply Eq.trans
      · apply runLoopOn_step_pointwise (step' := downCopyStep (embed (leBytes w v)))
        intro σ
        unfold downCopyStep
        rfl
      exact be_down_width w v hw hwf hbyte)


/-! ## Position well-formedness: injective permutations -/

/-- The only well-formedness `position_to_bytes` needs. -/
def InjPos (p : Position) : Prop := Injective p.cp ∧ Injective p.ep

theorem mem_listOf {n : Nat} (f : Fin n → Fin n) (x : Nat) (hx : x ∈ listOf f) :
    ∃ i : Fin n, x = (f i).val := by
  unfold listOf at hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < n := List.mem_range.mp hi
  exact ⟨⟨i, hi'⟩, by simp [hi']⟩

theorem permNWf_listOf {n : Nat} (f : Fin n → Fin n) (hf : Injective f) :
    PermNWf n (listOf f) where
  len := listOf_length f
  bound := by
    intro a ha
    obtain ⟨i, rfl⟩ := mem_listOf f a ha
    exact (f i).isLt
  nodup := by
    unfold listOf
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range n)
    intro x y hx hy hne hxy
    apply hne
    have hx' : x < n := List.mem_range.mp hx
    have hy' : y < n := List.mem_range.mp hy
    simp only [hx', hy', dite_true] at hxy
    have := hf (Fin.ext hxy)
    exact congrArg Fin.val this

theorem oriWf_listOfOri {n m : Nat} (f : Fin n → Fin m) :
    (listOfOri f).length = n ∧ ∀ o ∈ listOfOri f, o < m := by
  refine ⟨listOfOri_length f, ?_⟩
  intro o ho
  unfold listOfOri at ho
  rw [List.mem_map] at ho
  obtain ⟨i, hi, rfl⟩ := ho
  have hi' : i < n := List.mem_range.mp hi
  simp only [hi', dite_true]
  exact (f ⟨i, hi'⟩).isLt

theorem ori3Wf_listOfOri (f : Fin 20 → Fin 3) : Ori3Wf (listOfOri f) :=
  ⟨(oriWf_listOfOri f).1, (oriWf_listOfOri f).2⟩

theorem ori2Wf_listOfOri (f : Fin 30 → Fin 2) : Ori2Wf (listOfOri f) :=
  ⟨(oriWf_listOfOri f).1, (oriWf_listOfOri f).2⟩

theorem packOri3_lt' (co : List Nat) (h : Ori3Wf co) : packOri3 co < 3 ^ 19 := by
  rw [← oriAcc_pack3 co (by rw [h.len]; omega)]
  exact oriAcc_lt co h.bound 19 (by rw [h.len]; omega)

/-! ## Canonical limbs of the constants -/

theorem limbsOfNat_eq_natLimbs3 (v : Nat) (hv : v < limbBase ^ 3) :
    limbsOfNat v = natLimbs v := by
  have h := trimmed_eq_natLimbs (limbsOfNat v) (limbsOfNat_digits v hv) (limbsOfNat_trimmed v hv)
  rwa [limbsOfNat_val v hv] at h

theorem bigNat_eq3 (v : Nat) (hv : v < limbBase ^ 3) : bigNat v = bigOf (natLimbs v) := by
  unfold bigNat; rw [limbsOfNat_eq_natLimbs3 v hv]

theorem even30Limbs_eq : even30Limbs = natLimbs (evenPermCount 30) := by
  have h := trimmed_eq_natLimbs even30Limbs (by unfold even30Limbs limbBase; decide)
    (by unfold even30Limbs; decide)
  rwa [even30Limbs_val] at h

/-! ## Rank arithmetic -/

theorem mix_lt (a b X Y : Nat) (ha : a < X) (hb : b < Y) : a * Y + b < X * Y := by
  have h1 : (a + 1) * Y ≤ X * Y := Nat.mul_le_mul_right Y ha
  rw [Nat.succ_mul] at h1
  omega

theorem rankLists_horner (cp co ep eo : List Nat) :
    rankLists cp co ep eo =
      ((evenRank cp * 3 ^ 19 + packOri3 co) * evenPermCount 30 + evenRank ep) * 2 ^ 29 +
        packOri2 eo := by
  unfold rankLists rankRadices
  simp only [mixEncode, product, Nat.mul_one, Nat.add_zero, Nat.add_mul, Nat.mul_assoc,
    Nat.add_assoc]

theorem groupOrder_lt_limb8 : groupOrder < limbBase ^ 8 := by
  unfold groupOrder evenPermCount limbBase; decide

theorem rankPosition_lt_group (p : Position) (h : InjPos p) : rankPosition p < groupOrder := by
  unfold rankPosition
  rw [rankLists_horner]
  have h1 := evenRank_lt_countN 20 _ (permNWf_listOf p.cp h.1) (by decide)
  have h2 := packOri3_lt' _ (ori3Wf_listOfOri p.co)
  have h3 := evenRank_lt_countN 30 _ (permNWf_listOf p.ep h.2) (by decide)
  have h4 := packOri2_lt _ (ori2Wf_listOfOri p.eo)
  unfold groupOrder
  exact mix_lt _ _ _ _ (mix_lt _ _ _ _ (mix_lt _ _ _ _ h1 h2) h3) h4

theorem rankPosition_lt_digest (p : Position) (h : InjPos p) :
    rankPosition p < 256 ^ digestLen :=
  Nat.lt_trans (rankPosition_lt_group p h) groupOrder_lt_digest

/-! ## Glue -/

private theorem fits16 (k : Nat) (hk : k ≤ 16) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 16) hk

private theorem len8 (v : Nat) (hv : v < limbBase ^ 8) : (natLimbs v).length ≤ 8 :=
  natLimbs_length_le v 8 hv

private theorem fitsPair (a b : Nat) (ha : a < limbBase ^ 8) (hb : b < limbBase ^ 8) :
    FitsLen ((natLimbs a).length + (natLimbs b).length) :=
  fits16 _ (by have := len8 a ha; have := len8 b hb; omega)

private theorem fitsMax (a b : Nat) (ha : a < limbBase ^ 8) (hb : b < limbBase ^ 8) :
    FitsLen (max (natLimbs a).length (natLimbs b).length + 1) :=
  fits16 _ (by have := len8 a ha; have := len8 b hb; omega)

theorem position_to_bytes_refines_gen (p : Position) (h : InjPos p) :
    Megadreifach.position_to_bytes (embedPos p) = .ok (embed (positionToBytes p)) := by
  have hcp := permNWf_listOf p.cp h.1
  have hep := permNWf_listOf p.ep h.2
  have hco := ori3Wf_listOfOri p.co
  have heo := ori2Wf_listOfOri p.eo
  let rc := evenRank (listOf p.cp)
  let co := packOri3 (listOfOri p.co)
  let re := evenRank (listOf p.ep)
  let eo := packOri2 (listOfOri p.eo)
  let E := evenPermCount 30
  let A1 := rc * 3 ^ 19 + co
  let A2 := A1 * E + re
  let V := A2 * 2 ^ 29 + eo
  have hV : V = rankPosition p := by
    show _ = rankLists _ _ _ _; rw [rankLists_horner]
  have hVlt : V < limbBase ^ 8 := by rw [hV]; exact Nat.lt_trans (rankPosition_lt_group p h) groupOrder_lt_limb8
  have hE1 : 1 ≤ E := by show 1 ≤ evenPermCount 30; unfold evenPermCount; decide
  have hA1 : A1 ≤ V := by
    have : A1 ≤ A1 * E := Nat.le_mul_of_pos_right _ hE1
    have : A2 ≤ A2 * 2 ^ 29 := Nat.le_mul_of_pos_right _ (by decide)
    show A1 ≤ A2 * 2 ^ 29 + eo; omega
  have hA2 : A2 ≤ V := by
    have : A2 ≤ A2 * 2 ^ 29 := Nat.le_mul_of_pos_right _ (by decide)
    show A2 ≤ A2 * 2 ^ 29 + eo; omega
  have hrc : rc * 3 ^ 19 ≤ V := by show rc * 3 ^ 19 ≤ V; have := hA1; omega
  have hrc' : rc ≤ V := Nat.le_trans (Nat.le_mul_of_pos_right _ (by decide)) hrc
  have hco' : co ≤ V := by have := hA1; show co ≤ V; omega
  have hA1E : A1 * E ≤ V := by have := hA2; show A1 * E ≤ V; omega
  have hre : re ≤ V := by have := hA2; show re ≤ V; omega
  have hA22 : A2 * 2 ^ 29 ≤ V := Nat.le_add_right _ _
  have heo' : eo ≤ V := Nat.le_add_left _ _
  have lt8 : ∀ x, x ≤ V → x < limbBase ^ 8 := fun x hx => by omega
  have hc1 : (natLimbs (3 ^ 19)).length ≤ 8 := len8 _ (by unfold limbBase; decide)
  have hc2 : (natLimbs E).length ≤ 8 := len8 _ (by show evenPermCount 30 < _; unfold evenPermCount limbBase; decide)
  have hc3 : (natLimbs (2 ^ 29)).length ≤ 8 := len8 _ (by unfold limbBase; decide)
  unfold Megadreifach.position_to_bytes
  dsimp only [embedPos]
  rw [even_perm_rank_big_refines_gen 20 _ hcp (by decide) (by decide) evenPermCount20_lt, ok_bind]
  rw [ori3_span_eq, big_from_int_refines (3 ^ 19) three_pow19_fits, ok_bind,
    limbsOfNat_eq_natLimbs3 _ (by unfold limbBase; decide)]
  rw [big_mul_nat_gen _ _ (fitsPair rc (3 ^ 19) (lt8 rc hrc') (by unfold limbBase; decide)), ok_bind]
  rw [pack_ori3_refines _ hco, ok_bind,
    bigNat_eq3 _ (Nat.lt_trans (packOri3_lt' _ hco) (by unfold limbBase; decide))]
  rw [big_add_nat _ _ (fitsMax (rc * 3 ^ 19) co (lt8 _ hrc) (lt8 co hco')), ok_bind]
  rw [even30_refines, ok_bind, even30Limbs_eq]
  rw [big_mul_nat_gen _ _ (fitsPair A1 E (lt8 A1 hA1) (by show evenPermCount 30 < _; unfold evenPermCount limbBase; decide)), ok_bind]
  rw [even_perm_rank_big_refines_gen 30 _ hep (by decide) (by decide) evenPermCount30_lt, ok_bind]
  rw [big_add_nat _ _ (fitsMax (A1 * E) re (lt8 _ hA1E) (lt8 re hre)), ok_bind]
  rw [ori2_span_eq, big_from_int_refines (2 ^ 29) two_pow29_fits, ok_bind,
    limbsOfNat_eq_natLimbs3 _ (by unfold limbBase; decide)]
  rw [big_mul_nat_gen _ _ (fitsPair A2 (2 ^ 29) (lt8 A2 hA2) (by unfold limbBase; decide)), ok_bind]
  rw [pack_ori2_refines _ heo, ok_bind,
    bigNat_eq3 _ (Nat.lt_trans (packOri2_lt _ heo) (by unfold limbBase; decide))]
  rw [big_add_nat _ _ (fitsMax (A2 * 2 ^ 29) eo (lt8 _ hA22) (lt8 eo heo')), ok_bind]
  rw [digest_len_eq, except_bind_pure]
  unfold positionToBytes
  rw [← hV]
  exact big_to_be_gen digestLen V (by decide) (by unfold FitsLen i64MaxNat digestLen; decide)
    hVlt (by rw [hV]; exact rankPosition_lt_digest p h)

/-- General `even_perm_rank_big` for corner tables (any injective length-20 perm). -/
theorem even_perm_rank_big_refines_20 (perm : List Nat) (h : PermNWf 20 perm) :
    Megadreifach.even_perm_rank_big (embed perm) = .ok (bigOf (natLimbs (evenRank perm))) :=
  even_perm_rank_big_refines_gen 20 perm h (by decide) (by decide) evenPermCount20_lt

/-- General `even_perm_rank_big` for edge tables (any injective length-30 perm). -/
theorem even_perm_rank_big_refines_30 (perm : List Nat) (h : PermNWf 30 perm) :
    Megadreifach.even_perm_rank_big (embed perm) = .ok (bigOf (natLimbs (evenRank perm))) :=
  even_perm_rank_big_refines_gen 30 perm h (by decide) (by decide) evenPermCount30_lt

end MegaDreifachV1.Link2
