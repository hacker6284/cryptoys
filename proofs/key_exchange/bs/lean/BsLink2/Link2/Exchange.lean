/-
  BS Link 2: B9 the exchange. Given the key reader's cells for both keys (`read_key` itself
  is NOT covered), the emitted `exchange` publishes `3^a mod p` and `3^b mod p` and both
  players end with the model's `K = 3^(2ab) mod p`. Proof-only; not a security claim.
-/
import BsLink2.Link2.Check

namespace BsLink2.Link2

open MegaDreifach.Link2

theorem value_toReg (n v : Nat) (h : v < 3 ^ n) : Spec.value (Spec.toReg n v) = v := by
  induction n generalizing v with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    simp only [Spec.toReg, Spec.value]
    rw [ih (v / 3) (by rw [Nat.pow_succ] at h; omega)]
    omega

theorem p_pos (F : Spec.Field) (hF : F.Wf) : 0 < F.p := by
  have := value_lt F.toll hF.toll_trits
  have := Nat.pow_le_pow_right (show 0 < 3 by decide) (show F.toll.length ≤ F.n - 1 by
    have := hF.toll_lt; omega)
  have h3 : 3 ^ F.n = 3 * 3 ^ (F.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := hF.toll_lt; omega
  unfold Spec.Field.p Spec.Field.c
  have := Nat.pos_pow_of_pos (F.n - 1) (show 0 < 3 by decide)
  omega

theorem p_le (F : Spec.Field) : F.p ≤ 3 ^ F.n := Nat.sub_le _ _

/-- The model of a received public value checks to the square of what was sent. -/
theorem checkReceived_public (F : Spec.Field) (hF : F.Wf) (e : Nat)
    (h0 : 3 ^ (2 * e) % F.p ≠ 0) (h1 : 3 ^ (2 * e) % F.p ≠ 1) :
    Spec.checkReceived F (Spec.toReg F.n (3 ^ e % F.p)) =
      some (Spec.toReg F.n (3 ^ (2 * e) % F.p)) := by
  have hp := p_pos F hF
  have hlt : 3 ^ e % F.p < 3 ^ F.n := Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (p_le F)
  have hsq : Spec.value (Spec.toReg F.n (3 ^ e % F.p)) *
      Spec.value (Spec.toReg F.n (3 ^ e % F.p)) % F.p = 3 ^ (2 * e) % F.p := by
    rw [value_toReg _ _ hlt, ← Nat.mul_mod, ← Nat.pow_add, show e + e = 2 * e by omega]
  have hreg := isReg_toReg F.n (3 ^ e % F.p)
  unfold Spec.checkReceived
  rw [if_pos ⟨hreg.1, hreg.2⟩, hsq, if_neg (by omega)]

/-- The public walk (read the key, walk with g = 3) given the key reader's cells. -/
theorem public_walk_spec (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (key : Array Bs.KeyGrid) (cells : List Nat)
    (hread : Bs.read_key key = .ok (embed cells)) (hcells : ∀ c ∈ cells, c ≤ 2)
    (hfc : FitsLen cells.length) (hstart : 0 < Spec.expOf cells)
    (y : Array Int) (hy : Reg F.n y) :
    ∃ y', Bs.public_walk (emb F) key y = .ok (embed (Spec.publicValue F cells), y') ∧
      Reg F.n y' := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  obtain ⟨r, hw, hr1, hr2, hv⟩ := walk_public_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn
    h3 hfit cells hcells hfc hstart y hy
  refine ⟨r.2, ?_, hr2⟩
  unfold Bs.public_walk
  rw [hread, ok_bind, hw]
  show Except.ok (r.1, r.2) = _
  congr 2
  apply eq_embed_toReg hr1.trits hr1.size
  rw [hv, ← p_cast F hF, pw_natCast]
  rfl

/-- The shared walk (read the key, walk over the base C) given the key reader's cells. -/
theorem shared_walk_spec (F : Spec.Field) (hF : F.Wf)
    (hfit : FitsLen (2 * F.n + 2)) (key : Array Bs.KeyGrid) (base : List Nat)
    (hbase : Spec.IsReg F.n base) (cells : List Nat)
    (hread : Bs.read_key key = .ok (embed cells)) (hcells : ∀ c ∈ cells, c ≤ 2)
    (hfc : FitsLen cells.length) (hstart : 0 < Spec.expOf cells)
    (y : Array Int) (hy : Reg F.n y) :
    ∃ y', Bs.shared_walk (emb F) key (embed base) y =
      .ok (embed (Spec.sharedSecret F base cells), y') ∧ Reg F.n y' := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  have hbs : (embed base).size = F.n := by rw [size_embed]; exact hbase.1
  obtain ⟨r, hw, hr1, hr2, hv⟩ := walk_shared_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn
    hfit cells hcells hfc hstart (embed base) ⟨hbs, trits_embed hbase.2⟩ y hy
  refine ⟨r.2, ?_, hr2⟩
  unfold Bs.shared_walk
  rw [show SudoRt.sudoAssertEq (SudoRt.listLen (embed base)) (emb F).sudo_5Field_1n 707 = .ok () by
    simp only [listLen_eq, hbs]
    simp [SudoRt.sudoAssertEq, sEq_int, emb], ok_bind, hread, ok_bind, hw]
  show Except.ok (r.1, r.2) = _
  congr 2
  apply eq_embed_toReg hr1.trits hr1.size
  rw [hv, ← p_cast F hF, val_embed, powI_natCast]
  rfl

theorem pow_mod_base (a p k : Nat) : (a % p) ^ k % p = a ^ k % p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]

theorem sharedSecret_square (F : Spec.Field) (hF : F.Wf) (e : Nat) (cells : List Nat) :
    Spec.sharedSecret F (Spec.toReg F.n (3 ^ (2 * e) % F.p)) cells =
      Spec.toReg F.n (3 ^ (2 * e * Spec.expOf cells) % F.p) := by
  have hp := p_pos F hF
  have hlt : 3 ^ (2 * e) % F.p < 3 ^ F.n := Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (p_le F)
  unfold Spec.sharedSecret
  rw [value_toReg _ _ hlt, pow_mod_base, ← Nat.pow_mul]

/-- B9 in the emitted code, **given what the key reader returned for both keys**: if
    `read_key` returns Alice's cells `ca` and Bob's cells `cb` (trits, each with a hit),
    and neither received square is rejected by B8 (`3^(2a) mod p` and `3^(2b) mod p` are
    neither 0 nor 1), then `exchange` succeeds, the published values are the model's
    `3^a mod p` and `3^b mod p`, and both secrets are the model's `K = 3^(2ab) mod p`. -/
theorem exchange_agree_of_accepted (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : Array Bs.KeyGrid) (ca cb : List Nat)
    (hra : Bs.read_key keyA = .ok (embed ca)) (hrb : Bs.read_key keyB = .ok (embed cb))
    (hca : ∀ c ∈ ca, c ≤ 2) (hcb : ∀ c ∈ cb, c ≤ 2)
    (hfa : FitsLen ca.length) (hfb : FitsLen cb.length)
    (hsa : 0 < Spec.expOf ca) (hsb : 0 < Spec.expOf cb)
    (hA0 : 3 ^ (2 * Spec.expOf ca) % F.p ≠ 0) (hA1 : 3 ^ (2 * Spec.expOf ca) % F.p ≠ 1)
    (hB0 : 3 ^ (2 * Spec.expOf cb) % F.p ≠ 0) (hB1 : 3 ^ (2 * Spec.expOf cb) % F.p ≠ 1) :
    ∃ ex, Bs.exchange (emb F) keyA keyB = .ok (.ok ex) ∧
      ex.sudo_8Exchange_8public_a = embed (Spec.publicValue F ca) ∧
      ex.sudo_8Exchange_8public_b = embed (Spec.publicValue F cb) ∧
      ex.sudo_8Exchange_8secret_a = embed (Spec.exchangeKey F ca cb) ∧
      ex.sudo_8Exchange_8secret_b = embed (Spec.exchangeKey F ca cb) := by
  have hfn : FitsLen F.n := FitsLen.of_le hfit (by omega)
  have hn1 : 1 ≤ F.n := by omega
  have hy0 : Reg F.n (Array.mkArray F.n 0) := ⟨by simp, trits_mkArray_zero _⟩
  obtain ⟨ya, hwa, hya⟩ := public_walk_spec F hF h3 hfit keyA ca hra hca hfa hsa _ hy0
  obtain ⟨yb, hwb, hyb⟩ := public_walk_spec F hF h3 hfit keyB cb hrb hcb hfb hsb _ hy0
  have hcsa := call_the_shots_spec (emb F) F.n rfl hn1 hfn (Spec.publicValue F ca)
    (isReg_toReg _ _) yb hyb.size
  have hcsb := call_the_shots_spec (emb F) F.n rfl hn1 hfn (Spec.publicValue F cb)
    (isReg_toReg _ _) ya hya.size
  have hchkb : Bs.check_received (emb F) (embed (Spec.publicValue F cb)) =
      .ok (some (embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf cb) % F.p)))) := by
    rw [check_received_refines F hF hfit,
      show Spec.publicValue F cb = Spec.toReg F.n (3 ^ Spec.expOf cb % F.p) from rfl,
      checkReceived_public F hF _ hB0 hB1]; rfl
  have hchka : Bs.check_received (emb F) (embed (Spec.publicValue F ca)) =
      .ok (some (embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf ca) % F.p)))) := by
    rw [check_received_refines F hF hfit,
      show Spec.publicValue F ca = Spec.toReg F.n (3 ^ Spec.expOf ca % F.p) from rfl,
      checkReceived_public F hF _ hA0 hA1]; rfl
  have hya' : Reg F.n (embed (Spec.publicValue F cb)) :=
    ⟨by rw [size_embed]; exact (isReg_toReg _ _).1, trits_embed (isReg_toReg _ _).2⟩
  have hyb' : Reg F.n (embed (Spec.publicValue F ca)) :=
    ⟨by rw [size_embed]; exact (isReg_toReg _ _).1, trits_embed (isReg_toReg _ _).2⟩
  obtain ⟨ya2, hswa, _⟩ := shared_walk_spec F hF hfit keyA
    (Spec.toReg F.n (3 ^ (2 * Spec.expOf cb) % F.p)) (isReg_toReg _ _) ca hra hca hfa hsa
    _ hya'
  obtain ⟨yb2, hswb, _⟩ := shared_walk_spec F hF hfit keyB
    (Spec.toReg F.n (3 ^ (2 * Spec.expOf ca) % F.p)) (isReg_toReg _ _) cb hrb hcb hfb hsb
    _ hyb'
  rw [sharedSecret_square F hF] at hswa hswb
  refine ⟨{ sudo_8Exchange_8public_a := embed (Spec.publicValue F ca),
             sudo_8Exchange_8public_b := embed (Spec.publicValue F cb),
             sudo_8Exchange_7shots_a := ((Spec.publicValue F ca).map Spec.answer |>.map embShot).toArray,
             sudo_8Exchange_10received_a := embed (Spec.publicValue F ca),
             sudo_8Exchange_7shots_b := ((Spec.publicValue F cb).map Spec.answer |>.map embShot).toArray,
             sudo_8Exchange_10received_b := embed (Spec.publicValue F cb),
             sudo_8Exchange_6base_a := embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf cb) % F.p)),
             sudo_8Exchange_6base_b := embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf ca) % F.p)),
             sudo_8Exchange_8secret_a :=
               embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf cb * Spec.expOf ca) % F.p)),
             sudo_8Exchange_8secret_b :=
               embed (Spec.toReg F.n (3 ^ (2 * Spec.expOf ca * Spec.expOf cb) % F.p)) },
    ?_, rfl, rfl, ?_, rfl⟩
  · unfold Bs.exchange
    rw [empty_register_spec (emb F) F.n rfl, ok_bind, ok_bind]
    dsimp only
    rw [hwa, ok_bind]
    dsimp only
    rw [hwb, ok_bind]
    dsimp only
    rw [hcsa, ok_bind]
    dsimp only
    rw [hcsb, ok_bind]
    dsimp only
    rw [hchkb, ok_bind, hchka, ok_bind]
    simp only [SudoRt.optIsNone, Bool.false_eq_true, if_false, SudoRt.optUnwrap, ok_bind]
    rw [hswa, ok_bind]
    dsimp only
    rw [hswb, ok_bind]
    rfl
  · show embed _ = embed _
    unfold Spec.exchangeKey
    rw [Nat.mul_right_comm]

end BsLink2.Link2
