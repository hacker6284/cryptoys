/-
  SECURITY support (closes M3 on reachable positions).

  * `evenRank_inj`: `evenRank` is injective on EVEN permutations of `0..n-1`
    (Lehmer prefix of length `n-2` + even completion of the last two).
  * `positionToBytes_inj_legal`: the 29-byte digest is injective on legal
    positions.
  * `positionToBytes_inj_reachable`: hence on every chaining value reachable
    from IV-COOK12 (via `Parity.isLegal_chR`).
  * `extract_collision_comp`: the MD reduction of `MDReduction.lean` never
    takes the `out` branch — every Hash collision on `PadWf` messages yields
    a compression (`dmBlock`) collision.  Same for second preimages.

  Grip-rule status: INDEPENDENT of the grip rule.  `evenRank_inj` and
  `positionToBytes_inj_legal` are about the digest encoding only and need no
  repair if E_m changes.  `positionToBytes_inj_reachable` and the
  `extract_*_comp` / `v_Hash_collision_comp` / `v_Hash_second_preimage_comp` corollaries use
  `Parity.isLegal_chR` and `MDReduction.injPos_chR`; they need repair only
  through those (see the grip-rule notes in `Parity.lean` and
  `MDReduction.lean`).

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.Parity

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-! ## `evenRank` injectivity on even permutations -/

theorem evenRank_eq_mix (n : Nat) (perm : List Nat) (h : PermNWf n perm) :
    evenRank perm = mixEncode (evenRadices n) (evenDigits perm) := by
  unfold evenRank evenDigits; rw [h.len]

theorem evenDigits_bound (n : Nat) (hn : 2 ≤ n) (perm : List Nat) (h : PermNWf n perm) :
    ∀ i, i < (evenDigits perm).length →
      (evenDigits perm)[i]?.getD 0 < (evenRadices n)[i]?.getD 0 := by
  intro i hi
  have hn' : 2 ≤ perm.length := by rw [h.len]; exact hn
  have hi' : i < n - 2 := by rw [evenDigits_length perm hn', h.len] at hi; exact hi
  have hdg := evenDigit_eqN n perm h i hi'
  have hrad := evenRadix_get n i hn hi'
  rw [List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by rw [evenRadices_length n hn]; exact hi')]
  simp only [Option.getD_some, hrad, hdg.1]
  exact hdg.2

theorem evenRank_digits (n : Nat) (hn : 2 ≤ n) (p q : List Nat) (hp : PermNWf n p)
    (hq : PermNWf n q) (h : evenRank p = evenRank q) : evenDigits p = evenDigits q := by
  rw [evenRank_eq_mix n p hp, evenRank_eq_mix n q hq] at h
  have lp : (evenDigits p).length = (evenRadices n).length := by
    rw [evenDigits_length p (by rw [hp.len]; exact hn), hp.len, evenRadices_length n hn]
  have lq : (evenDigits q).length = (evenRadices n).length := by
    rw [evenDigits_length q (by rw [hq.len]; exact hn), hq.len, evenRadices_length n hn]
  exact mixEncode_inj _ _ _ lp lq (evenDigits_bound n hn p hp) (evenDigits_bound n hn q hq) h

theorem availAt_congr (p q : List Nat) (k : Nat) (hl : p.length = q.length)
    (ht : p.take k = q.take k) : availAt p k = availAt q k := by
  unfold availAt; rw [hl, ht]

theorem findIdx_inj (xs : List Nat) {a b : Nat} (ha : a ∈ xs) (hb : b ∈ xs)
    (h : xs.findIdx (· == a) = xs.findIdx (· == b)) : a = b := by
  have ga := get_findIdx xs ha
  have gb := get_findIdx xs hb
  have e : xs[xs.findIdx (· == a)]? = xs[xs.findIdx (· == b)]? := by rw [h]
  rw [List.getElem?_eq_getElem (findIdx_lt_mem xs ha),
    List.getElem?_eq_getElem (findIdx_lt_mem xs hb), ga, gb] at e
  exact Option.some.inj e

/-- Equal even digits ⇒ equal first `n-2` entries. -/
theorem take_eq_of_evenDigits (n : Nat) (hn : 2 ≤ n) (p q : List Nat) (hp : PermNWf n p)
    (hq : PermNWf n q) (hd : evenDigits p = evenDigits q) :
    ∀ k, k ≤ n - 2 → p.take k = q.take k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : k < n - 2 := by omega
      have ht := ih (by omega)
      have hkp : k < p.length := by rw [hp.len]; omega
      have hkq : k < q.length := by rw [hq.len]; omega
      have hA : availAt q k = availAt p k :=
        (availAt_congr p q k (by rw [hp.len, hq.len]) ht).symm
      have dp := (evenDigit_eqN n p hp k hk').1
      have dq := (evenDigit_eqN n q hq k hk').1
      have hdl : k < (evenDigits p).length := by
        rw [evenDigits_length p (by rw [hp.len]; exact hn), hp.len]; exact hk'
      have hdl' : k < (evenDigits q).length := by
        rw [evenDigits_length q (by rw [hq.len]; exact hn), hq.len]; exact hk'
      have hfind : (availAt p k).findIdx (· == p[k]) = (availAt p k).findIdx (· == q[k]) := by
        have e : (evenDigits p)[k]? = (evenDigits q)[k]? := by rw [hd]
        rw [List.getElem?_eq_getElem hdl, List.getElem?_eq_getElem hdl'] at e
        have e' := Option.some.inj e
        rw [dp, dq, hA] at e'
        exact e'
      have mp := mem_availAtN n p hp k (by omega)
      have mq := mem_availAtN n q hq k (by omega)
      rw [hA] at mq
      have hpq : p[k] = q[k] := findIdx_inj _ mp mq hfind
      rw [take_succ_get p k hkp, take_succ_get q k hkq, ht, hpq]

theorem split_last_two (p : List Nat) (n : Nat) (hn : 2 ≤ n) (hl : p.length = n) :
    p = p.take (n - 2) ++ [p[n - 2]'(by omega), p[n - 1]'(by omega)] := by
  have h1 : p.drop (n - 2) = p[n - 2]'(by omega) :: p.drop (n - 2 + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have h2 : p.drop (n - 2 + 1) = p[n - 1]'(by omega) :: p.drop (n - 1 + 1) := by
    have e : n - 2 + 1 = n - 1 := by omega
    rw [e]; exact List.drop_eq_getElem_cons (by omega)
  have h3 : p.drop (n - 1 + 1) = [] := List.drop_eq_nil_of_le (by omega)
  conv => lhs; rw [← List.take_append_drop (n - 2) p]
  rw [h1, h2, h3]

/-- The last two entries of a permutation with a fixed prefix are the two
    leftover symbols, in one of the two orders. -/
theorem last_two_cases (n : Nat) (hn : 2 ≤ n) (p : List Nat) (hp : PermNWf n p)
    (u v : Nat) (hA : availAt p (n - 2) = [u, v]) :
    p = p.take (n - 2) ++ [u, v] ∨ p = p.take (n - 2) ++ [v, u] := by
  have spec := availAt_specN n p hp (n - 2) (by omega)
  have hsplit := split_last_two p n hn hp.len
  have hsplit' := hsplit
  have hnd := hp.nodup
  rw [hsplit] at hnd
  have hnot : ∀ x, x ∈ [p[n - 2]'(by rw [hp.len]; omega), p[n - 1]'(by rw [hp.len]; omega)] →
      x ∈ availAt p (n - 2) := by
    intro x hx
    rw [spec.2.2]
    refine ⟨hp.bound x ?_, ?_⟩
    · rw [hsplit]; exact List.mem_append_right _ hx
    · intro hin
      exact (List.pairwise_append.mp hnd).2.2 x hin x hx rfl
  have ha := hnot _ (List.mem_cons_self _ _)
  have hb := hnot _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
  have hab : p[n - 2]'(by rw [hp.len]; omega) ≠ p[n - 1]'(by rw [hp.len]; omega) := by
    have := (List.pairwise_append.mp hnd).2.1
    intro h; rw [h] at this; simp at this
  rw [hA] at ha hb
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · left; rw [ha, hb] at hsplit'; exact hsplit'
  · right; rw [ha, hb] at hsplit'; exact hsplit'
  · exact absurd (ha.trans hb.symm) hab

/-- **`evenRank` is injective on even permutations of `0..n-1`.** -/
theorem evenRank_inj (n : Nat) (hn : 2 ≤ n) (p q : List Nat) (hp : PermNWf n p)
    (hq : PermNWf n q) (ep : permParity p = 0) (eq : permParity q = 0)
    (h : evenRank p = evenRank q) : p = q := by
  have hd := evenRank_digits n hn p q hp hq h
  have ht := take_eq_of_evenDigits n hn p q hp hq hd (n - 2) (Nat.le_refl _)
  have hA : availAt q (n - 2) = availAt p (n - 2) :=
    (availAt_congr p q _ (by rw [hp.len, hq.len]) ht).symm
  have spec := availAt_specN n p hp (n - 2) (by omega)
  obtain ⟨hnd, hlen, _⟩ := spec
  have h2 : n - (n - 2) = 2 := by omega
  rw [h2] at hlen
  have hex : ∃ u v, availAt p (n - 2) = [u, v] := by
    match hA2 : availAt p (n - 2) with
    | [u, v] => exact ⟨u, v, rfl⟩
    | [] => rw [hA2] at hlen; simp at hlen
    | [_] => rw [hA2] at hlen; simp at hlen
    | _ :: _ :: _ :: _ => rw [hA2] at hlen; simp at hlen
  obtain ⟨u, v, hAv⟩ := hex
  have huv : u ≠ v := by
    intro e; rw [hAv, e] at hnd; simp at hnd
  have cp := last_two_cases n hn p hp u v hAv
  have cq := last_two_cases n hn q hq u v (by rw [hA, hAv])
  rw [← ht] at cq
  have e1 := evenComplete_unique (p.take (n - 2)) u v huv p cp ep
  have e2 := evenComplete_unique (p.take (n - 2)) u v huv q cq eq
  rw [e1, e2]

/-! ## Orientation lists: the last entry is fixed by the sum -/

theorem last_unique_mod (m k : Nat) (hm : m = 2 ∨ m = 3) (L1 L2 : List Nat) (h1 : L1.length = k + 1)
    (h2 : L2.length = k + 1) (b1 : ∀ o ∈ L1, o < m) (b2 : ∀ o ∈ L2, o < m)
    (s1 : sumNats L1 % m = 0) (s2 : sumNats L2 % m = 0) (ht : L1.take k = L2.take k) :
    L1 = L2 := by
  have d1 : L1.drop k = [L1[k]'(by omega)] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  have d2 : L2.drop k = [L2[k]'(by omega)] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  have e1 : L1 = L1.take k ++ [L1[k]'(by omega)] := by
    conv => lhs; rw [← List.take_append_drop k L1]
    rw [d1]
  have e2 : L2 = L2.take k ++ [L2[k]'(by omega)] := by
    conv => lhs; rw [← List.take_append_drop k L2]
    rw [d2]
  have x1 := b1 _ (List.getElem_mem (show k < L1.length by omega))
  have x2 := b2 _ (List.getElem_mem (show k < L2.length by omega))
  have hs1 : (sumNats (L1.take k) + L1[k]'(by omega)) % m = 0 := by
    have := s1; rw [e1, sumNats_append] at this
    simpa [sumNats_cons, sumNats] using this
  have hs2 : (sumNats (L1.take k) + L2[k]'(by omega)) % m = 0 := by
    have := s2; rw [e2, sumNats_append, ← ht] at this
    simpa [sumNats_cons, sumNats] using this
  have hlast : L1[k]'(by omega) = L2[k]'(by omega) := by
    rcases hm with hm | hm <;> subst hm <;> omega
  rw [e1, e2, ht, hlast]

/-! ## Digest injectivity -/

theorem permNWf20 (p : Position) (h : isLegal p) : PermNWf 20 (listOf p.cp) :=
  permNWf_listOf p.cp h.1
theorem permNWf30 (p : Position) (h : isLegal p) : PermNWf 30 (listOf p.ep) :=
  permNWf_listOf p.ep h.2.1

/-- **The 29-byte digest is injective on legal positions.** -/
theorem positionToBytes_inj_legal (p q : Position) (hp : isLegal p) (hq : isLegal q)
    (h : positionToBytes p = positionToBytes q) : p = q := by
  have ip : InjPos p := ⟨hp.1, hp.2.1⟩
  have iq : InjPos q := ⟨hq.1, hq.2.1⟩
  have hr := positionToBytes_rank_inj p q (rankPosition_lt_group p ip)
    (rankPosition_lt_group q iq) h
  obtain ⟨c1, c2, c3, c4⟩ := rankLists_components_eq _ _ _ _ _ _ _ _
    (evenRank_lt_countN 20 _ (permNWf20 p hp) (by decide))
    (evenRank_lt_countN 20 _ (permNWf20 q hq) (by decide))
    (packOri3_lt' _ (ori3Wf_listOfOri p.co)) (packOri3_lt' _ (ori3Wf_listOfOri q.co))
    (evenRank_lt_countN 30 _ (permNWf30 p hp) (by decide))
    (evenRank_lt_countN 30 _ (permNWf30 q hq) (by decide))
    (packOri2_lt _ (ori2Wf_listOfOri p.eo)) (packOri2_lt _ (ori2Wf_listOfOri q.eo)) hr
  have hcp := evenRank_inj 20 (by decide) _ _ (permNWf20 p hp) (permNWf20 q hq)
    (legal_even_cp hp) (legal_even_cp hq) c1
  have hep := evenRank_inj 30 (by decide) _ _ (permNWf30 p hp) (permNWf30 q hq)
    (legal_even_ep hp) (legal_even_ep hq) c3
  have o3p := ori3Wf_listOfOri p.co
  have o3q := ori3Wf_listOfOri q.co
  have o2p := ori2Wf_listOfOri p.eo
  have o2q := ori2Wf_listOfOri q.eo
  have t3 := packOri3_inj _ _ o3p.len o3q.len o3p.bound o3q.bound
    (legal_co_parity hp) (legal_co_parity hq) c2
  have t2 := packOri2_inj _ _ o2p.len o2q.len o2p.bound o2q.bound c4
  have hco := last_unique_mod 3 19 (Or.inr rfl) _ _ o3p.len o3q.len o3p.bound o3q.bound
    (legal_co_parity hp) (legal_co_parity hq) t3
  have heo := last_unique_mod 2 29 (Or.inl rfl) _ _ o2p.len o2q.len o2p.bound o2q.bound
    (legal_eo_parity hp) (legal_eo_parity hq) t2
  exact (position_eq_iff p q).mpr ⟨hcp, hco, hep, heo⟩

/-- Digest injectivity on every reachable chaining value. -/
theorem positionToBytes_inj_reachable (r s : List (List Nat))
    (h : positionToBytes (chR dmBlock Em.ivCook12 r) = positionToBytes (chR dmBlock Em.ivCook12 s)) :
    chR dmBlock Em.ivCook12 r = chR dmBlock Em.ivCook12 s :=
  positionToBytes_inj_legal _ _ (isLegal_chR r) (isLegal_chR s) h

/-- Equal digests of well-formed messages ⇔ equal final chaining values. -/
theorem vhashAlg_eq_iff (m1 m2 : List Nat) :
    vhashAlg m1 = vhashAlg m2 ↔ chainMsg m1 = chainMsg m2 := by
  constructor
  · intro h
    exact positionToBytes_inj_legal _ _ (isLegal_chainMsg m1) (isLegal_chainMsg m2) h
  · intro h; rw [vhashAlg_eq_chainMsg, vhashAlg_eq_chainMsg, h]

/-! ## The MD reduction, final form -/

/-- **MD collision reduction (final).**  Any two distinct `PadWf` messages
    with equal MegaDreifach digests yield, via the computable `extract`, a
    compression collision `dmBlock h₁ b₁ = dmBlock h₂ b₂`, `(h₁,b₁) ≠ (h₂,b₂)`,
    between compression inputs of the two messages (28-byte blocks, legal
    reachable chaining values).  No output-encoding branch remains. -/
theorem extract_collision_comp (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2) (hd : vhashAlg m1 = vhashAlg m2) :
    ∃ c, extract m1 m2 = some (Break.comp c) ∧ (Break.comp c).Valid m1 m2 := by
  obtain ⟨w, hw, hv⟩ := extract_collision m1 m2 hp1 hp2 hne hd
  cases w with
  | comp c => exact ⟨c, hw, hv⟩
  | out p q =>
      exfalso
      obtain ⟨hpq, _, _, _, rfl, rfl⟩ := hv
      exact hpq ((vhashAlg_eq_iff m1 m2).mp hd)

/-- **MD second-preimage reduction (final).**  A second preimage `m' ≠ m` of
    the digest of `m` yields a compression collision whose first side is one of
    `m`'s own compression inputs `(chainPre (pad m) i, blockAt (pad m) i)`. -/
theorem extract_second_preimage_comp (m m' : List Nat) (hp : PadWf m) (hp' : PadWf m')
    (hne : m' ≠ m) (hd : vhashAlg m' = vhashAlg m) :
    ∃ c, extract m m' = some (Break.comp c) ∧ (Break.comp c).Valid m m' ∧
      ∃ i, i < (blocksMsg m).length ∧
        c.h1 = chainPre (pad m) i ∧ c.b1 = blockAt (pad m) i := by
  obtain ⟨c, hc, hv⟩ := extract_collision_comp m m' hp hp' (Ne.symm hne) hd.symm
  obtain ⟨w, hw, _, hi⟩ := extract_second_preimage m m' hp hp' hne hd
  rw [hc] at hw
  cases hw
  exact ⟨c, hc, hv, hi c rfl⟩

/-- Equal generated digests are equal algebraic digests (Link 2). -/
theorem vhashAlg_eq_of_v_Hash (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hd : Megadreifach.v_Hash (embed m1) = Megadreifach.v_Hash (embed m2)) :
    vhashAlg m1 = vhashAlg m2 := by
  rw [v_Hash_refines m1 hp1, v_Hash_refines m2 hp2] at hd
  have hd' : embed (vhashAlg m1) = embed (vhashAlg m2) := Except.ok.inj hd
  have l1 := decode_embed (vhashAlg m1)
  have l2 := decode_embed (vhashAlg m2)
  rw [← l1, ← l2, hd']

/-- `extract_collision_comp` for the generated code `Generated.v_Hash`. -/
theorem v_Hash_collision_comp (m1 m2 : List Nat) (hp1 : PadWf m1) (hp2 : PadWf m2)
    (hne : m1 ≠ m2) (hd : Megadreifach.v_Hash (embed m1) = Megadreifach.v_Hash (embed m2)) :
    ∃ c, extract m1 m2 = some (Break.comp c) ∧ (Break.comp c).Valid m1 m2 :=
  extract_collision_comp m1 m2 hp1 hp2 hne (vhashAlg_eq_of_v_Hash m1 m2 hp1 hp2 hd)

/-- `extract_second_preimage_comp` for the generated code `Generated.v_Hash`. -/
theorem v_Hash_second_preimage_comp (m m' : List Nat) (hp : PadWf m) (hp' : PadWf m')
    (hne : m' ≠ m) (hd : Megadreifach.v_Hash (embed m') = Megadreifach.v_Hash (embed m)) :
    ∃ c, extract m m' = some (Break.comp c) ∧ (Break.comp c).Valid m m' ∧
      ∃ i, i < (blocksMsg m).length ∧
        c.h1 = chainPre (pad m) i ∧ c.b1 = blockAt (pad m) i :=
  extract_second_preimage_comp m m' hp hp' hne (vhashAlg_eq_of_v_Hash m' m hp' hp hd)

end MegaDreifach.Security
