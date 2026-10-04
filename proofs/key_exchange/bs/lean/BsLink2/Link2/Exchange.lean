/-
  BS Link 2: B7 from a key, and B9 the exchange. For keys of well-formed pages (`Spec.KeyWf`),
  the emitted `public_value`, `shared_secret` and `exchange` refine the model, with the key
  reader (`read_key_spec`, `Key.lean`) proved rather than assumed. `exchange_refines` covers
  all three outcomes of B9: both reject branches and the agreed one. Proof-only; not a
  security claim.
-/
import BsLink2.Link2.Key

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
  rw [sudoAssertEq_int (a := SudoRt.listLen (embed base)) (b := (emb F).sudo_5Field_1n)
    (by simp only [listLen_eq, hbs]; simp [emb]), ok_bind, hread, ok_bind, hw]
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

theorem checkReceived_some_isReg (F : Spec.Field) {r b : List Nat}
    (h : Spec.checkReceived F r = some b) : Spec.IsReg F.n b := by
  unfold Spec.checkReceived at h
  split at h
  · split at h
    · cases h
    · cases h; exact isReg_toReg _ _
  · cases h

/-- B8 on a public value: the check rejects exactly when the square is 0 or 1 mod `p`. -/
theorem checkReceived_public_none (F : Spec.Field) (hF : F.Wf) (e : Nat)
    (h : 3 ^ (2 * e) % F.p = 0 ∨ 3 ^ (2 * e) % F.p = 1) :
    Spec.checkReceived F (Spec.toReg F.n (3 ^ e % F.p)) = none := by
  have hp := p_pos F hF
  have hlt : 3 ^ e % F.p < 3 ^ F.n := Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (p_le F)
  have hsq : Spec.value (Spec.toReg F.n (3 ^ e % F.p)) *
      Spec.value (Spec.toReg F.n (3 ^ e % F.p)) % F.p = 3 ^ (2 * e) % F.p := by
    rw [value_toReg _ _ hlt, ← Nat.mul_mod, ← Nat.pow_add, show e + e = 2 * e by omega]
  have hreg := isReg_toReg F.n (3 ^ e % F.p)
  unfold Spec.checkReceived
  rw [if_pos ⟨hreg.1, hreg.2⟩, hsq, if_pos h]

/-- A model string as the emitted ASCII array. -/
def embStr (s : String) : Array Int := (s.toList.map (fun c => Int.ofNat c.toNat)).toArray

/-- A model exchange record as the emitted `Exchange`. -/
def embRecord (e : Spec.ExchangeRecord) : Bs.Exchange :=
  { sudo_8Exchange_8public_a := embed e.publicA,
    sudo_8Exchange_8public_b := embed e.publicB,
    sudo_8Exchange_7shots_a := (e.shotsA.map embShot).toArray,
    sudo_8Exchange_10received_a := embed e.receivedA,
    sudo_8Exchange_7shots_b := (e.shotsB.map embShot).toArray,
    sudo_8Exchange_10received_b := embed e.receivedB,
    sudo_8Exchange_6base_a := embed e.baseA,
    sudo_8Exchange_6base_b := embed e.baseB,
    sudo_8Exchange_8secret_a := embed e.secretA,
    sudo_8Exchange_8secret_b := embed e.secretB }

/-- A model outcome as the emitted `Result<List<Int>, Exchange>`. -/
def embOutcome : Except String Spec.ExchangeRecord → SudoRt.SResult (Array Int) Bs.Exchange
  | .error s => .err (embStr s)
  | .ok e => .ok (embRecord e)

theorem embStr_aliceRejects : embStr Spec.aliceRejects = #[66, 56, 58, 32, 65, 108, 105, 99,
    101, 32, 114, 101, 106, 101, 99, 116, 115, 32, 66, 111, 98, 39, 115, 32, 118, 97, 108, 117,
    101] := by decide

theorem embStr_bobRejects : embStr Spec.bobRejects = #[66, 56, 58, 32, 66, 111, 98, 32, 114,
    101, 106, 101, 99, 116, 115, 32, 65, 108, 105, 99, 101, 39, 115, 32, 118, 97, 108, 117,
    101] := by decide

/-- B9 in the emitted code, **given what the key reader returned for both keys**: the
    emitted `exchange` returns the model's outcome on the two cell strings, whichever of its
    three branches that is. `exchange_refines` discharges the reader hypotheses. -/
theorem exchange_cells_refines (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : Array Bs.KeyGrid) (ca cb : List Nat)
    (hra : Bs.read_key keyA = .ok (embed ca)) (hrb : Bs.read_key keyB = .ok (embed cb))
    (hca : ∀ c ∈ ca, c ≤ 2) (hcb : ∀ c ∈ cb, c ≤ 2)
    (hfa : FitsLen ca.length) (hfb : FitsLen cb.length)
    (hsa : 0 < Spec.expOf ca) (hsb : 0 < Spec.expOf cb) :
    Bs.exchange (emb F) keyA keyB = .ok (embOutcome (Spec.exchangeCells F ca cb)) := by
  have hfn : FitsLen F.n := FitsLen.of_le hfit (by omega)
  have hn1 : 1 ≤ F.n := by omega
  have hy0 : Reg F.n (Array.mkArray F.n 0) := ⟨by simp, trits_mkArray_zero _⟩
  obtain ⟨ya, hwa, hya⟩ := public_walk_spec F hF h3 hfit keyA ca hra hca hfa hsa _ hy0
  obtain ⟨yb, hwb, hyb⟩ := public_walk_spec F hF h3 hfit keyB cb hrb hcb hfb hsb _ hy0
  have hcsa := call_the_shots_spec (emb F) F.n rfl hn1 hfn (Spec.publicValue F ca)
    (isReg_toReg _ _) yb hyb.size
  have hcsb := call_the_shots_spec (emb F) F.n rfl hn1 hfn (Spec.publicValue F cb)
    (isReg_toReg _ _) ya hya.size
  have hya' : Reg F.n (embed (Spec.publicValue F cb)) :=
    ⟨by rw [size_embed]; exact (isReg_toReg _ _).1, trits_embed (isReg_toReg _ _).2⟩
  have hyb' : Reg F.n (embed (Spec.publicValue F ca)) :=
    ⟨by rw [size_embed]; exact (isReg_toReg _ _).1, trits_embed (isReg_toReg _ _).2⟩
  unfold Bs.exchange
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
  rw [check_received_refines F hF hfit, ok_bind, check_received_refines F hF hfit, ok_bind]
  unfold Spec.exchangeCells
  dsimp only
  cases hB : Spec.checkReceived F (Spec.publicValue F cb) with
  | none =>
    simp only [Option.map, SudoRt.optIsNone, if_true, embOutcome, embStr_aliceRejects]; rfl
  | some ba =>
    cases hA : Spec.checkReceived F (Spec.publicValue F ca) with
    | none =>
      simp only [Option.map, SudoRt.optIsNone, Bool.false_eq_true, if_false, if_true,
        embOutcome, embStr_bobRejects]; rfl
    | some bb =>
      simp only [Option.map, SudoRt.optIsNone, Bool.false_eq_true, if_false,
        SudoRt.optUnwrap, ok_bind]
      obtain ⟨ya2, hswa, _⟩ := shared_walk_spec F hF hfit keyA ba
        (checkReceived_some_isReg F hB) ca hra hca hfa hsa _ hya'
      obtain ⟨yb2, hswb, _⟩ := shared_walk_spec F hF hfit keyB bb
        (checkReceived_some_isReg F hA) cb hrb hcb hfb hsb _ hyb'
      rw [hswa, ok_bind]
      dsimp only
      rw [hswb, ok_bind]
      rfl

/-! ### The headline theorems: from keys of well-formed pages -/

/-- What the walk lemmas need about a key's cells, from `read_key_spec` and the `readKey`
    lemmas: `read_key` returns them, they are trits, their count fits `i64`, and the
    exponent is non-zero. -/
theorem key_facts (pages : List Spec.Grid) (hk : Spec.KeyWf pages)
    (hkf : FitsLen (300 * pages.length + 1)) :
    Bs.read_key (embKey pages) = .ok (embed (Spec.readKey pages)) ∧
      (∀ c ∈ Spec.readKey pages, c ≤ 2) ∧ FitsLen (Spec.readKey pages).length ∧
      0 < Spec.expOf (Spec.readKey pages) :=
  ⟨read_key_spec pages hk (FitsLen.of_le hkf (by omega)), readKey_trits pages hk.2,
    FitsLen.of_le hkf (length_readKey_le pages hk.2), expOf_readKey_pos pages⟩

/-- B7, public phase, from a key. For a key of one or more well-formed pages, the emitted
    `public_value` is the register holding `3^e mod p`, where `e` is the key read by §4.3
    (start marker, then each page's ship pass and peg pass) as a base-3 number. -/
theorem public_value_refines (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (pages : List Spec.Grid) (hk : Spec.KeyWf pages)
    (hkf : FitsLen (300 * pages.length + 1)) :
    Bs.public_value (emb F) (embKey pages) =
      .ok (embed (Spec.publicValue F (Spec.readKey pages))) := by
  obtain ⟨hr, ht, hf, hs⟩ := key_facts pages hk hkf
  exact public_value_refines_of_read F hF h3 hfit _ _ hr ht hf hs

/-- B7, shared phase, from a key. For a key of one or more well-formed pages and a base
    register `C` of `n` trits, the emitted `shared_secret` is the register holding
    `C^e mod p`, `e` as in `public_value_refines`. -/
theorem shared_secret_refines (F : Spec.Field) (hF : F.Wf)
    (hfit : FitsLen (2 * F.n + 2)) (pages : List Spec.Grid) (hk : Spec.KeyWf pages)
    (hkf : FitsLen (300 * pages.length + 1)) (base : List Nat) (hbase : Spec.IsReg F.n base) :
    Bs.shared_secret (emb F) (embKey pages) (embed base) =
      .ok (embed (Spec.sharedSecret F base (Spec.readKey pages))) := by
  obtain ⟨hr, ht, hf, hs⟩ := key_facts pages hk hkf
  exact shared_secret_refines_of_read F hF hfit _ base hbase _ hr ht hf hs

/-- B9 from two keys of well-formed pages: the emitted `exchange` returns exactly the
    model's outcome, in all three branches (Alice rejects Bob's value; Bob rejects Alice's
    value; both accept and the record of publics, shots, bases and secrets). -/
theorem exchange_refines (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : List Spec.Grid)
    (hka : Spec.KeyWf keyA) (hkb : Spec.KeyWf keyB)
    (hfa : FitsLen (300 * keyA.length + 1)) (hfb : FitsLen (300 * keyB.length + 1)) :
    Bs.exchange (emb F) (embKey keyA) (embKey keyB) =
      .ok (embOutcome (Spec.exchange F keyA keyB)) := by
  obtain ⟨hra, hta, hfa', hsa⟩ := key_facts keyA hka hfa
  obtain ⟨hrb, htb, hfb', hsb⟩ := key_facts keyB hkb hfb
  exact exchange_cells_refines F hF h3 hfit _ _ _ _ hra hrb hta htb hfa' hfb' hsa hsb

/-- B8/B9 reject branch 1. If the square of Bob's public value is 0 or 1 mod `p`
    (`3^(2b) mod p ∈ {0, 1}`), the emitted `exchange` returns the error
    "B8: Alice rejects Bob's value", whatever Alice's value is. -/
theorem exchange_alice_rejects (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : List Spec.Grid)
    (hka : Spec.KeyWf keyA) (hkb : Spec.KeyWf keyB)
    (hfa : FitsLen (300 * keyA.length + 1)) (hfb : FitsLen (300 * keyB.length + 1))
    (hB : 3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p = 0 ∨
      3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p = 1) :
    Bs.exchange (emb F) (embKey keyA) (embKey keyB) =
      .ok (.err (embStr Spec.aliceRejects)) := by
  rw [exchange_refines F hF h3 hfit keyA keyB hka hkb hfa hfb]
  unfold Spec.exchange Spec.exchangeCells
  dsimp only
  rw [show Spec.publicValue F (Spec.readKey keyB) =
      Spec.toReg F.n (3 ^ Spec.expOf (Spec.readKey keyB) % F.p) from rfl,
    checkReceived_public_none F hF _ hB]
  rfl

/-- B8/B9 reject branch 2. If Alice accepts Bob's value (the square of his public value is
    neither 0 nor 1 mod `p`) but the square of Alice's public value is 0 or 1 mod `p`, the
    emitted `exchange` returns the error "B8: Bob rejects Alice's value". -/
theorem exchange_bob_rejects (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : List Spec.Grid)
    (hka : Spec.KeyWf keyA) (hkb : Spec.KeyWf keyB)
    (hfa : FitsLen (300 * keyA.length + 1)) (hfb : FitsLen (300 * keyB.length + 1))
    (hB0 : 3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p ≠ 0)
    (hB1 : 3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p ≠ 1)
    (hA : 3 ^ (2 * Spec.expOf (Spec.readKey keyA)) % F.p = 0 ∨
      3 ^ (2 * Spec.expOf (Spec.readKey keyA)) % F.p = 1) :
    Bs.exchange (emb F) (embKey keyA) (embKey keyB) =
      .ok (.err (embStr Spec.bobRejects)) := by
  rw [exchange_refines F hF h3 hfit keyA keyB hka hkb hfa hfb]
  unfold Spec.exchange Spec.exchangeCells
  dsimp only
  rw [show Spec.publicValue F (Spec.readKey keyB) =
      Spec.toReg F.n (3 ^ Spec.expOf (Spec.readKey keyB) % F.p) from rfl,
    show Spec.publicValue F (Spec.readKey keyA) =
      Spec.toReg F.n (3 ^ Spec.expOf (Spec.readKey keyA) % F.p) from rfl,
    checkReceived_public F hF _ hB0 hB1, checkReceived_public_none F hF _ hA]
  rfl

/-- B9, the agreed branch, from two keys of well-formed pages: if neither received square
    is rejected by B8 (`3^(2a) mod p` and `3^(2b) mod p` are neither 0 nor 1), `exchange`
    succeeds, the published values are the model's `3^a mod p` and `3^b mod p`, and both
    secrets are the model's `K = 3^(2ab) mod p`, where `a` and `b` are the two keys read by
    §4.3. -/
theorem exchange_agree_of_accepted (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (keyA keyB : List Spec.Grid)
    (hka : Spec.KeyWf keyA) (hkb : Spec.KeyWf keyB)
    (hfa : FitsLen (300 * keyA.length + 1)) (hfb : FitsLen (300 * keyB.length + 1))
    (hA0 : 3 ^ (2 * Spec.expOf (Spec.readKey keyA)) % F.p ≠ 0)
    (hA1 : 3 ^ (2 * Spec.expOf (Spec.readKey keyA)) % F.p ≠ 1)
    (hB0 : 3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p ≠ 0)
    (hB1 : 3 ^ (2 * Spec.expOf (Spec.readKey keyB)) % F.p ≠ 1) :
    ∃ ex, Bs.exchange (emb F) (embKey keyA) (embKey keyB) = .ok (.ok ex) ∧
      ex.sudo_8Exchange_8public_a = embed (Spec.publicValue F (Spec.readKey keyA)) ∧
      ex.sudo_8Exchange_8public_b = embed (Spec.publicValue F (Spec.readKey keyB)) ∧
      ex.sudo_8Exchange_8secret_a =
        embed (Spec.exchangeKey F (Spec.readKey keyA) (Spec.readKey keyB)) ∧
      ex.sudo_8Exchange_8secret_b =
        embed (Spec.exchangeKey F (Spec.readKey keyA) (Spec.readKey keyB)) := by
  rw [exchange_refines F hF h3 hfit keyA keyB hka hkb hfa hfb]
  unfold Spec.exchange Spec.exchangeCells
  dsimp only
  rw [show Spec.publicValue F (Spec.readKey keyB) =
      Spec.toReg F.n (3 ^ Spec.expOf (Spec.readKey keyB) % F.p) from rfl,
    show Spec.publicValue F (Spec.readKey keyA) =
      Spec.toReg F.n (3 ^ Spec.expOf (Spec.readKey keyA) % F.p) from rfl,
    checkReceived_public F hF _ hB0 hB1, checkReceived_public F hF _ hA0 hA1]
  refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
  · show embed (Spec.sharedSecret F _ (Spec.readKey keyA)) = _
    rw [sharedSecret_square F hF]
    unfold Spec.exchangeKey
    rw [Nat.mul_right_comm]
  · show embed (Spec.sharedSecret F _ (Spec.readKey keyB)) = _
    rw [sharedSecret_square F hF]
    rfl

end BsLink2.Link2
