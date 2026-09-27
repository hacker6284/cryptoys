/-
  T1 — Link 2 transfer for relabellings.

  Generic lemmas take a cell map `f : Nat → Nat` (`CardMap f`); the headline
  statements are about `σ : Equiv.Perm (Fin 52)` acting through `σ.app`.
  Link 1 (sudo = Generated) stays open: these are facts about the emitted Lean.
-/
import DoubleDeal.Concrete
import DoubleDeal.Link2.Encrypt
import DoubleDealSecurity.Relabel

namespace DoubleDeal.Security

open DoubleDeal

/-! ## Relabelling the key moves positions -/

theorem indexOf_map_inj (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b)
    (xs : List Nat) (x : Nat) : indexOf (xs.map f) (f x) = indexOf xs x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map, indexOf]
    by_cases h : y = x
    · simp [h]
    · have h' : f y ≠ f x := fun e => h (hf _ _ e)
      simp [h, h', ih]

/-- (PROVED) Relabelling the key by an injective card map `f` moves positions:
    `keyPos (f·K) (f x) = keyPos K x`, i.e. seat `j` of `Compose(M, σK)` holds
    what seat `σ⁻¹ j` of `Compose(M, K)` held. The output is permuted
    positionally, not relabelled. -/
theorem keyPos_map_key (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b)
    (key : List Nat) (x : Nat) (hx : x < 52) (hfx : f x < 52) :
    keyPos (key.map f) ⟨f x, hfx⟩ = keyPos key ⟨x, hx⟩ := by
  unfold keyPos
  simp only
  rw [indexOf_map_inj f hf]

/-! ## Transfer to the emitted `Doubledeal.encrypt` -/

theorem cardBound_of_lt {n : Nat} (h : n < 52) : Link2.CardBound n := by
  unfold Link2.CardBound Link2.i64MaxNat; omega

theorem ofDeck_map (f : Nat → Nat) (xs : List Nat) (h : xs.length = 52)
    (h' : (xs.map f).length = 52) :
    ofDeck (xs.map f) h' = fun i => f (ofDeck xs h i) := by
  funext i; simp [ofDeck]

theorem toDeck_map (f : Nat → Nat) (g : Fin 52 → Nat) :
    toDeck (fun i => f (g i)) = (toDeck g).map f := by
  apply List.ext_getElem
  · simp [length_toDeck]
  · intro i h1 h2
    simp [toDeck, Array.getElem_toList, Array.getElem_ofFn]

theorem map_ofNat_inj : ∀ {xs ys : List Nat}, xs.map Int.ofNat = ys.map Int.ofNat → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Int.ofNat.inj h.1, map_ofNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem embed_inj {xs ys : List Nat} (h : Link2.embed xs = Link2.embed ys) : xs = ys := by
  have := congrArg Array.toList h
  simp only [Link2.toList_embed] at this
  exact map_ofNat_inj this

theorem ofDeck_congr {a b : List Nat} (e : a = b) {ha : a.length = 52} {hb : b.length = 52} :
    ofDeck a ha = ofDeck b hb := by subst e; rfl

theorem toDeck_inj {f g : Fin 52 → Nat} (h : toDeck f = toDeck g) : f = g := by
  rw [← Link2.ofDeck_toDeck f, ← Link2.ofDeck_toDeck g]
  exact ofDeck_congr h

/-- (PROVED) The emitted cipher satisfies `E_K(σM) = σ E_K(M)` exactly when the
    algebraic model does (52-card message of card values, Perm52 key). -/
theorem generated_encrypt_map_iff (f : Nat → Nat) (hf : CardMap f) (message key : List Nat)
    (hm : message.length = 52) (hk : Perm52 key) (hc : ∀ x ∈ message, x < 52) :
    Doubledeal.encrypt (Link2.embed (message.map f)) (Link2.embed key) =
        .ok (Link2.embed ((encryptDeck message key).map f)) ↔
      encryptDeckFn (fun i => f (ofDeck message hm i)) key =
        fun i => f (encryptDeckFn (ofDeck message hm) key i) := by
  have hm' : (message.map f).length = 52 := by simp [hm]
  have hcσ : ∀ i : Fin 52, Link2.CardBound ((ofDeck (message.map f) hm') i) := by
    intro i
    apply cardBound_of_lt
    simp only [ofDeck, List.getElem_map]
    exact hf.lt _ (hc _ (List.getElem_mem _))
  rw [Link2.encrypt_refines _ key hm' hk hcσ]
  rw [encryptDeck_eq_encryptDeckFn _ key hm', encryptDeck_eq_encryptDeckFn _ key hm,
    ofDeck_map f message hm hm', ← toDeck_map]
  constructor
  · intro h
    exact toDeck_inj (embed_inj (Except.ok.inj h))
  · intro h; rw [h]

/-- (PROVED, kernel `decide!`, ~80 s) Model-level K♣↔K♦ counterexample for the
    full v9 encrypt (message `K♦, A♣, 2♣, …`, identity key). -/
theorem encryptDeck_KC_KD_not_equivariant :
    encryptDeck (toDeck (fun i => swapNat 12 51 (firstDeck 51 i))) (List.range 52) ≠
      (encryptDeck (toDeck (firstDeck 51)) (List.range 52)).map (swapNat 12 51) := by
  decide!

theorem swapNat_cardMap : CardMap (swapNat 12 51) :=
  ⟨fun n h => by unfold swapNat; split <;> (try split) <;> omega⟩

/-- (PROVED) The emitted v9 `encrypt` is not K♣↔K♦-equivariant: on message
    `K♦, A♣, 2♣, …` with the identity key, `E_K(σM) ≠ σ E_K(M)`. -/
theorem generated_encrypt_KC_KD_not_equivariant :
    Doubledeal.encrypt (Link2.embed ((toDeck (firstDeck 51)).map (swapNat 12 51)))
        (Link2.embed (List.range 52)) ≠
      .ok (Link2.embed ((encryptDeck (toDeck (firstDeck 51)) (List.range 52)).map
        (swapNat 12 51))) := by
  intro h
  have hm' : ((toDeck (firstDeck 51)).map (swapNat 12 51)).length = 52 := by
    simp [length_toDeck]
  have hc : ∀ i : Fin 52, Link2.CardBound
      ((ofDeck ((toDeck (firstDeck 51)).map (swapNat 12 51)) hm') i) := by
    intro i
    apply cardBound_of_lt
    rw [ofDeck_map _ _ (length_toDeck _), Link2.ofDeck_toDeck]
    exact swapNat_cardMap.lt _ (firstDeck_lt i)
  rw [Link2.encrypt_refines _ _ hm' perm52_range hc, ← toDeck_map] at h
  exact encryptDeck_KC_KD_not_equivariant (embed_inj (Except.ok.inj h))

/-! ## Headline statements for `σ : Equiv.Perm (Fin 52)` -/

theorem ofDeck_map_rel (σ : Relabel) (xs : List Nat) (h : xs.length = 52)
    (h' : (xs.map σ.app).length = 52) :
    ofDeck (xs.map σ.app) h' = rel σ (ofDeck xs h) := ofDeck_map σ.app xs h h'

/-- (PROVED) Relabelling the key moves positions: seat `j` of `Compose(M, σK)`
    holds what seat `σ⁻¹ j` of `Compose(M, K)` held. -/
theorem keyPos_relabel_key (σ : Relabel) (key : List Nat) (j : Fin 52) :
    keyPos (key.map σ.app) j = keyPos key (σ.symm j) := by
  have h := keyPos_map_key σ.app (fun _ _ e => σ.app_inj e) key (σ.symm j).val (σ.symm j).isLt
    (σ.app_lt (σ.symm j).isLt)
  have hj : (⟨σ.app (σ.symm j).val, σ.app_lt (σ.symm j).isLt⟩ : Fin 52) = j := by
    apply Fin.ext; simp [σ.app_fin]
  rw [hj] at h
  exact h

/-- (PROVED) For `σ : Equiv.Perm (Fin 52)`, the emitted `Doubledeal.encrypt`
    satisfies `E_K(σM) = σ E_K(M)` exactly when the algebraic model does. -/
theorem generated_encrypt_relabel_iff (σ : Relabel) (message key : List Nat)
    (hm : message.length = 52) (hk : Perm52 key) (hc : ∀ x ∈ message, x < 52) :
    Doubledeal.encrypt (Link2.embed (message.map σ.app)) (Link2.embed key) =
        .ok (Link2.embed ((encryptDeck message key).map σ.app)) ↔
      encryptDeckFn (rel σ (ofDeck message hm)) key =
        rel σ (encryptDeckFn (ofDeck message hm) key) :=
  generated_encrypt_map_iff σ.app (app_cardMap σ) message key hm hk hc

/-- (PROVED) Headline: there is a relabelling `σ : Equiv.Perm (Fin 52)` — the
    transposition K♣↔K♦ — such that the emitted v9 `encrypt` does not commute
    with it: on message `K♦, A♣, 2♣, …` and the identity key,
    `E_K(σM) ≠ σ E_K(M)`. -/
theorem generated_encrypt_not_relabel_equivariant :
    ∃ (σ : Equiv.Perm (Fin 52)) (message key : List Nat),
      Perm52 key ∧ message.length = 52 ∧
      Doubledeal.encrypt (Link2.embed (message.map (Relabel.app σ))) (Link2.embed key) ≠
        .ok (Link2.embed ((encryptDeck message key).map (Relabel.app σ))) := by
  have h := generated_encrypt_KC_KD_not_equivariant
  rw [← swap_KC_KD_app] at h
  exact ⟨Equiv.swap KC KD, toDeck (firstDeck 51), List.range 52, perm52_range,
    length_toDeck _, h⟩

end DoubleDeal.Security
