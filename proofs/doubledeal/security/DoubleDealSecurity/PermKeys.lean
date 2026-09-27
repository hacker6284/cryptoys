/-
  T1: encrypt with PERMUTATION round keys (the key maps DoubleDeal actually
  uses). Proof-only, about the algebraic model `encrypt6`.

  Decks are exactly the permutations of the 52 card values, a relabelling σ
  acts on the left (on values) and a round key acts on the right (on
  positions), so the two always commute. Varying the first mixing round key
  over all permutations, while the rest of `encrypt6` stays an injective map,
  shows: if σ commutes with `encrypt6` for all permutation keys, then the
  unkeyed round body is σ-covariant (`F(σ·m) = τ·F(m)` for one fixed τ). The
  output relabelling τ need not equal σ, which is why the open conjecture is
  stated in covariant form (`roundBody_covariant_iff_id`).

  Scope: keys are independent `Equiv.Perm (Fin 52)` per round. That is a
  superset of the round keys a real key schedule (`expand_keys` of one master
  key) produces; the argument uses the identity for all rounds but the first
  mixing round, which a real schedule need not reach.
-/
import DoubleDealSecurity.Relabel

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- A round key: a permutation of the 52 positions. -/
abbrev Key := Equiv.Perm (Fin 52)

/-- `encrypt6` with permutation round keys. -/
def encrypt6P (m : Fin 52 → Nat) (k0 : Key) (kMix : Nat → Key) (kF : Key) : Fin 52 → Nat :=
  encrypt6 m k0 (fun n => kMix n) kF

/-! ## Decks as permutations -/

noncomputable def deckPerm (d : Fin 52 → Nat) (hd : IsDeck d) : Equiv.Perm (Fin 52) :=
  Equiv.ofBijective (fun i => ⟨d i, hd.1 i⟩)
    (Finite.injective_iff_bijective.1 (fun i j h => hd.2 i j (congrArg Fin.val h)))

@[simp] theorem deckPerm_val (d : Fin 52 → Nat) (hd : IsDeck d) (i : Fin 52) :
    (deckPerm d hd i).val = d i := rfl

theorem isDeck_rel (σ : Relabel) {m : Fin 52 → Nat} (hm : IsDeck m) : IsDeck (rel σ m) :=
  ⟨fun i => σ.app_lt (hm.1 i), fun i j h => hm.2 i j (σ.app_inj h)⟩

theorem isDeck_compose {m : Fin 52 → Nat} (hm : IsDeck m) (p : Key) :
    IsDeck (composeVec 52 Nat m p) :=
  ⟨fun _ => hm.1 _, fun _ _ h => p.injective (hm.2 _ _ h)⟩

/-! ## Inverse rotations only move cells -/

theorem rowRotateInv_bound (P : α → Prop) (g : Grid α) (t : Fin 4 → Nat)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (rowRotateInv g t r c) := by
  intro r c
  unfold rowRotateInv ofList13
  have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
  have hget := getElem_rotR (toList13 (g r)) (t r) c.val hne c.isLt
  rw [hget]
  have hj : (c.val + (13 - t r % 13)) % 13 < 13 := Nat.mod_lt _ (by decide)
  have hcell := getElem_toList13 (g r) ⟨(c.val + (13 - t r % 13)) % 13, hj⟩
  simpa [length_toList13, hcell] using hb r ⟨(c.val + (13 - t r % 13)) % 13, hj⟩

theorem colRotateInv_bound (P : α → Prop) (g : Grid α) (s : Fin 13 → Nat)
    (hb : ∀ r c, P (g r c)) : ∀ r c, P (colRotateInv g s r c) := by
  intro r c
  unfold colRotateInv ofList4
  have hne : (toList4 (fun r' => g r' c)).length ≠ 0 := by simp [length_toList4]
  have hget := rotL_get_eq (toList4 (fun r' => g r' c)) (s c) r.val hne r.isLt
  rw [hget]
  have hj : (r.val + s c % 4) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcell := getElem_toList4 (fun r' => g r' c) ⟨(r.val + s c % 4) % 4, hj⟩
  simp only [length_toList4]
  rw [hcell]
  exact hb _ c

theorem invUnkeyedNoMix_cells (x : Fin 52 → Nat) (i : Fin 52) :
    ∃ k, invUnkeyedNoMix x i = x k := by
  have h1 : ∀ r c, (fun v => ∃ k, v = x k) (invShiftRows (layColumnMajor x) r c) :=
    fun r c => ⟨_, rfl⟩
  have h2 := colRotateInv_bound (fun v => ∃ k, v = x k) (invShiftRows (layColumnMajor x))
    (fun c => colWeightSum cardColumnWeight (invShiftRows (layColumnMajor x)) c) h1
  have h3 := rowRotateInv_bound (fun v => ∃ k, v = x k) (applyColRotatesInv cardColumnWeight (invShiftRows (layColumnMajor x)))
    (fun r => rowWeightSum cardRank
      (applyColRotatesInv cardColumnWeight (invShiftRows (layColumnMajor x))) r) h2
  obtain ⟨k, hk⟩ := h3 (cmRow i) (cmCol i)
  exact ⟨k, hk⟩

/-- (PROVED) The stem maps decks to decks. -/
theorem isDeck_unkeyedNoMix {m : Fin 52 → Nat} (hm : IsDeck m) : IsDeck (unkeyedNoMix m) := by
  classical
  set x := unkeyedNoMix m
  have hinv : invUnkeyedNoMix x = m := invUnkeyedNoMix_unkeyedNoMix m
  choose ρ hρ using invUnkeyedNoMix_cells x
  have hρ' : ∀ i, m i = x (ρ i) := fun i => hinv ▸ hρ i
  have hinj : Function.Injective ρ := fun i i' h => hm.2 _ _ (by rw [hρ' i, hρ' i', h])
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨fun k => ?_, fun k k' h => ?_⟩
  · obtain ⟨i, rfl⟩ := hsurj k
    rw [← hρ' i]; exact hm.1 i
  · obtain ⟨i, rfl⟩ := hsurj k
    obtain ⟨i', rfl⟩ := hsurj k'
    rw [← hρ' i, ← hρ' i'] at h
    rw [hm.2 _ _ h]

/-- (PROVED) GridCycle maps decks to decks. -/
theorem isDeck_mixColumns {h : Fin 52 → Nat} (hh : IsDeck h) : IsDeck (mixColumns h) := by
  have cell : ∀ r c, ∃ k, gridW chooseSeat! h r c = h k ∧ seatW chooseSeat! h k.val = (r, c) := by
    intro r c
    obtain ⟨k, hk⟩ := seatW_surj _ freeChooser_v9 h (r, c)
    refine ⟨k, ?_, hk⟩
    have := gridW_at_seat _ freeChooser_v9 h k
    rw [hk] at this; exact this
  rw [mixColumns_eq]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨k, hk, _⟩ := cell (rmRow i) (rmCol i)
    show gridW chooseSeat! h (rmRow i) (rmCol i) < 52
    rw [hk]; exact hh.1 k
  · obtain ⟨k, hk, hs⟩ := cell (rmRow i) (rmCol i)
    obtain ⟨k', hk', hs'⟩ := cell (rmRow j) (rmCol j)
    have hij' : gridW chooseSeat! h (rmRow i) (rmCol i) =
        gridW chooseSeat! h (rmRow j) (rmCol j) := hij
    rw [hk, hk'] at hij'
    have hkk := hh.2 _ _ hij'
    subst hkk
    rw [hs] at hs'
    have e1 := congrArg Prod.fst hs'
    have e2 := congrArg Prod.snd hs'
    simp only at e1 e2
    rw [← rmFlat_rm i, ← rmFlat_rm j, e1, e2]

theorem isDeck_unkeyedWithMix {m : Fin 52 → Nat} (hm : IsDeck m) : IsDeck (unkeyedWithMix m) :=
  isDeck_mixColumns (isDeck_unkeyedNoMix hm)

/-! ## The tail of encrypt is injective -/

theorem applyFullRounds_succ' (pos : Nat → Fin 52 → Fin 52) :
    ∀ n (x : Fin 52 → Nat), applyFullRounds (n + 1) x pos =
      applyFullRounds n (fullRound x (pos 0)) (fun k => pos (k + 1))
  | 0, _ => rfl
  | n + 1, x => by
      rw [applyFullRounds, applyFullRounds_succ' pos n x]
      rfl

theorem fullRound_id_injective : Function.Injective (fun x => fullRound x id) := by
  intro x y h
  have h' : mixColumns (unkeyedNoMix x) = mixColumns (unkeyedNoMix y) := h
  have := congrArg (fun z => invUnkeyedNoMix (invMixColumns z)) h'
  simpa only [invMixColumns_mixColumns, invUnkeyedNoMix_unkeyedNoMix] using this

theorem applyFullRounds_id_injective :
    ∀ n, Function.Injective (fun x => applyFullRounds n x (fun _ => id))
  | 0 => fun _ _ h => h
  | n + 1 => fun _ _ h => applyFullRounds_id_injective n (fullRound_id_injective h)

/-- The rest of `encrypt6` after the first mixing round's key, with all later
    keys the identity. -/
def tail (y : Fin 52 → Nat) : Fin 52 → Nat :=
  fullRoundNoMix (applyFullRounds 4 y (fun _ => id)) id

theorem tail_injective : Function.Injective tail := by
  intro x y h
  have h' : unkeyedNoMix (applyFullRounds 4 x (fun _ => id)) =
      unkeyedNoMix (applyFullRounds 4 y (fun _ => id)) := h
  have := congrArg invUnkeyedNoMix h'
  simp only [invUnkeyedNoMix_unkeyedNoMix] at this
  exact applyFullRounds_id_injective 4 this

/-- Keys: identity everywhere except the first mixing round, which is `p`. -/
def keysAt0 (p : Key) : Nat → Key := fun n => if n = 0 then p else 1

theorem encrypt6P_keysAt0 (m : Fin 52 → Nat) (p : Key) :
    encrypt6P m 1 (keysAt0 p) 1 = tail (composeVec 52 Nat (unkeyedWithMix m) p) := by
  simp only [encrypt6P, encrypt6, encryptN, tail]
  rw [applyFullRounds_succ']
  have hk : (fun k => ⇑(keysAt0 p (k + 1))) = fun _ => (id : Fin 52 → Fin 52) := by
    funext k; simp [keysAt0]
  rw [hk]
  rfl

/-! ## Main reduction -/

/-- (PROVED) If σ commutes with `encrypt6` for all permutation round keys, the
    unkeyed round body is σ-covariant. -/
theorem round_covariant_of_encrypt6 (σ : Relabel)
    (h : ∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF)) :
    Covariant σ unkeyedWithMix := by
  -- for every first-round key p: tail(F(σm)·p) = σ·tail(F(m)·p)
  have hF : ∀ (p : Key) m, IsDeck m →
      tail (composeVec 52 Nat (unkeyedWithMix (rel σ m)) p) =
        rel σ (tail (composeVec 52 Nat (unkeyedWithMix m) p)) := by
    intro p m hm
    have := h 1 (keysAt0 p) 1 m hm
    simpa only [encrypt6P_keysAt0] using this
  -- κ m: the relabelling taking F(m) to F(σm) (both decks)
  let κ : ∀ m, IsDeck m → Relabel := fun m hm =>
    (deckPerm _ (isDeck_unkeyedWithMix hm)).symm.trans
      (deckPerm _ (isDeck_unkeyedWithMix (isDeck_rel σ hm)))
  have hκ : ∀ m (hm : IsDeck m) (i : Fin 52),
      (κ m hm).app (unkeyedWithMix m i) = unkeyedWithMix (rel σ m) i := by
    intro m hm i
    have hz := isDeck_unkeyedWithMix hm
    show (κ m hm).app (⟨unkeyedWithMix m i, hz.1 i⟩ : Fin 52).val = _
    rw [app_fin]
    have : (⟨unkeyedWithMix m i, hz.1 i⟩ : Fin 52) = deckPerm _ hz i := rfl
    simp only [κ, Equiv.trans_apply, this, Equiv.symm_apply_apply, deckPerm_val]
  -- A: tail(κ·u) = σ·tail(u) for every deck u
  have hA : ∀ m (hm : IsDeck m) u, IsDeck u → tail (rel (κ m hm) u) = rel σ (tail u) := by
    intro m hm u hu
    have hz := isDeck_unkeyedWithMix hm
    let p : Key := (deckPerm u hu).trans (deckPerm _ hz).symm
    have hzp : composeVec 52 Nat (unkeyedWithMix m) p = u := by
      funext i
      exact congrArg Fin.val (Equiv.apply_symm_apply (deckPerm _ hz) (deckPerm u hu i))
    have hxp : composeVec 52 Nat (unkeyedWithMix (rel σ m)) p = rel (κ m hm) u := by
      funext i
      show unkeyedWithMix (rel σ m) (p i) = (κ m hm).app (u i)
      rw [← hκ m hm (p i)]
      congr 1
      exact congrFun hzp i
    rw [← hxp, hF p m hm, hzp]
  -- κ does not depend on the deck
  let idD : Fin 52 → Nat := fun i => i.val
  have hidD : IsDeck idD := ⟨fun i => i.isLt, fun i j h => Fin.ext h⟩
  have hconst : ∀ m (hm : IsDeck m), κ m hm = κ idD hidD := by
    intro m hm
    have e : rel (κ m hm) idD = rel (κ idD hidD) idD :=
      tail_injective (by rw [hA m hm idD hidD, hA idD hidD idD hidD])
    apply Equiv.ext; intro c
    have := congrFun e c
    simp only [rel, idD, app_fin] at this
    exact Fin.ext this
  refine ⟨κ idD hidD, fun m hm => ?_⟩
  funext i
  rw [← hconst m hm]
  exact (hκ m hm i).symm

/-- (PROVED modulo the covariant round conjecture) No nontrivial σ gives
    `E_K(σM) = σ E_K(M)` for all permutation round keys and decks. -/
theorem encrypt6_commutes_iff_id (σ : Relabel) :
    (∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF)) ↔ σ.IsId := by
  constructor
  · intro h; exact (roundBody_covariant_iff_id σ).1 (round_covariant_of_encrypt6 σ h)
  · intro hid _ _ _ m _
    unfold IsId at hid; subst hid
    simp only [rel_one]

/-- (PROVED, no conjecture) No nontrivial σ that commutes with the v9 stem
    (i.e. no nontrivial `v9Sym a b`) gives `E_K(σM) = σ E_K(M)` for all
    permutation round keys. -/
theorem encrypt6_not_commutes_of_stem (σ : Relabel) (hid : ¬ σ.IsId)
    (hs : CommutesG σ sumRanksV9) :
    ¬ ∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF) :=
  fun h => roundBody_not_covariant_of_stem σ hid hs (round_covariant_of_encrypt6 σ h)

/-- (PROVED) The 51 nontrivial `v9Sym a b` (e.g. the suit rotation `v9Sym 0 1`):
    for each there are permutation round keys and a deck with
    `E_K(σM) ≠ σ E_K(M)`. -/
theorem encrypt6_not_commutes_v9Sym (a : Fin 13) (b : Fin 4) (hab : (a, b) ≠ (0, 0)) :
    ¬ ∀ k0 kMix kF, CommutesOnDecks (v9Sym a b) (fun m => encrypt6P m k0 kMix kF) := by
  obtain ⟨hr, hc⟩ := (v9_shift_iff (v9Sym a b)).2 ⟨a, b, fun _ => rfl⟩
  refine encrypt6_not_commutes_of_stem _ ?_ (sumRanks_commutes_of_shift _ _ _ hr hc)
  intro hid
  rw [isId_iff] at hid
  obtain ⟨rfl, rfl⟩ := v9SymFn_fixed a b ⟨0, by decide⟩ (hid _)
  exact hab rfl

end DoubleDeal.Security
