/-
  T1: encrypt with PERMUTATION round keys (the key maps DoubleDeal actually
  uses). Proof-only, about the algebraic model `encrypt6`.

  Decks are exactly the permutations of the 52 card values, a relabelling σ
  acts on the left (on values) and a round key acts on the right (on
  positions), so the two always commute. Varying the first mixing round key
  over all permutations, while the rest of `encrypt6` stays an injective map,
  shows: if σ commutes with `encrypt6` for all permutation keys, then the
  unkeyed round body is σ-covariant (`F(σ·m) = τ·F(m)` for one fixed τ). The
  output relabelling τ need not equal σ, which is why the round statement is
  in covariant form (`roundBody_covariant_iff_id`, proved in the heavy library). The
  default library states the consequence as the reduction
  `encrypt6_commutes_iff_id_of_covariant` (hard direction of the round statement as the
  hypothesis `hconj`); the unconditional `encrypt6_commutes_iff_id` is in the heavy library
  (`DoubleDealSecurityHeavy/V10Sym.lean`).

  Scope: keys are independent `Equiv.Perm (Fin 52)` per round. That is a
  superset of the round keys a real key schedule (`expand_keys` of one master
  key) produces; the argument uses the identity for all rounds but the first
  mixing round, which a real schedule need not reach.
-/
import DoubleDealSecurity.Rounds

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- A round key: a permutation of the 52 positions. -/
abbrev Key := Equiv.Perm (Fin 52)

/-- `encrypt6` with permutation round keys. -/
def encrypt6P (m : Fin 52 → Nat) (k0 : Key) (kMix : Nat → Key) (kF : Key) : Fin 52 → Nat :=
  encrypt6 m k0 (fun n => kMix n) kF

/-! ## Decks as permutations -/

theorem isDeck_rel (σ : Relabel) {m : Fin 52 → Nat} (hm : IsDeck m) : IsDeck (rel σ m) :=
  ⟨fun i => σ.app_lt (hm.1 i), fun _ _ h => hm.2 (σ.app_inj h)⟩

theorem isDeck_compose {m : Fin 52 → Nat} (hm : IsDeck m) (p : Key) :
    IsDeck (composeVec 52 Nat m p) :=
  ⟨fun _ => hm.1 _, fun _ _ h => p.injective (hm.2 h)⟩

theorem invUnkeyedNoMix_cells (x : Fin 52 → Nat) (i : Fin 52) :
    ∃ k, invUnkeyedNoMix x i = x k := by
  have h1 : ∀ r c, (fun v => ∃ k, v = x k) (invShiftRows (layColumnMajor x) r c) :=
    fun r c => ⟨_, rfl⟩
  have h3 := invSumRanksV10_bound (fun v => ∃ k, v = x k) (invShiftRows (layColumnMajor x)) h1
  obtain ⟨k, hk⟩ := h3 (cmRow i) (cmCol i)
  exact ⟨k, hk⟩

/-- (PROVED) The stem maps decks to decks. -/
theorem isDeck_unkeyedNoMix {m : Fin 52 → Nat} (hm : IsDeck m) : IsDeck (unkeyedNoMix m) := by
  refine isDeck_of_cells hm (fun i => ?_)
  obtain ⟨k, hk⟩ := invUnkeyedNoMix_cells (unkeyedNoMix m) i
  exact ⟨k, by rw [← hk, invUnkeyedNoMix_unkeyedNoMix]⟩

/-- (PROVED) GridCycle maps decks to decks. -/
theorem isDeck_mixColumns {h : Fin 52 → Nat} (hh : IsDeck h) : IsDeck (mixColumns h) := by
  simpa only [mixColumns_eq] using isDeck_scoop_gridW chooseSeat! freeChooser hh

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

/-- (PROVED, a reduction; GIVEN `hconj`, the hard direction of the covariant round
    statement, proved in the heavy library as `roundBody_covariant_iff_id`) No nontrivial σ
    gives `E_K(σM) = σ E_K(M)` for all permutation round keys and decks. Unconditional
    form: heavy library, `encrypt6_commutes_iff_id`. -/
theorem encrypt6_commutes_iff_id_of_covariant
    (hconj : ∀ σ : Relabel, Covariant σ unkeyedWithMix → σ = 1) (σ : Relabel) :
    (∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF)) ↔ σ = 1 := by
  constructor
  · intro h; exact hconj σ (round_covariant_of_encrypt6 σ h)
  · rintro rfl _ _ _; exact commutesOnDecks_one _

/-- (PROVED, no conjecture) No nontrivial σ that commutes with v10 SumRanks
    (e.g. no nontrivial `v10Sym a x`) gives `E_K(σM) = σ E_K(M)` for all
    permutation round keys. -/
theorem encrypt6_not_commutes_of_stem (σ : Relabel) (hid : σ ≠ 1)
    (hs : CommutesG σ sumRanksV10) :
    ¬ ∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF) :=
  fun h => roundBody_not_covariant_of_stem σ hid hs (round_covariant_of_encrypt6 σ h)

/-- (PROVED) The 51 nontrivial `v10Sym a x` (e.g. the label shift `v10Sym 0 1`,
    ♣↔♦ and ♥↔♠ within each rank): for each there are permutation round keys
    and a deck with `E_K(σM) ≠ σ E_K(M)`. -/
theorem encrypt6_not_commutes_v10Sym (a : Fin 13) (x : Fin 4) (hax : (a, x) ≠ (0, 0)) :
    ¬ ∀ k0 kMix kF, CommutesOnDecks (v10Sym a x) (fun m => encrypt6P m k0 kMix kF) := by
  refine encrypt6_not_commutes_of_stem _ ?_ (sumRanksV10_commutes_v10Sym a x)
  intro hid
  obtain ⟨rfl, rfl⟩ := v10SymFn_fixed a x ⟨0, by decide⟩ (Equiv.congr_fun hid _)
  exact hax rfl

end DoubleDeal.Security
