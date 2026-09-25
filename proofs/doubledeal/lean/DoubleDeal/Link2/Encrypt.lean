/-
  LINK 2. `encrypt` refines algebraic `encryptDeck` / `encrypt6` on a
  length-52 message whose card ids fit in i64, and a Perm52 key.
  Proof-only. Not bit-security.
-/
import Doubledeal
import DoubleDeal.Basic
import DoubleDeal.Concrete
import DoubleDeal.Round
import DoubleDeal.Grid
import DoubleDeal.GridCycle
import DoubleDeal.SumRanks
import DoubleDeal.ShiftRows
import DoubleDeal.Compose
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Expand
import DoubleDeal.Link2.Compose
import DoubleDeal.Link2.GridLay
import DoubleDeal.Link2.SumLink
import DoubleDeal.Link2.Shift
import DoubleDeal.Link2.Scoop
import DoubleDeal.Link2.Mix

namespace DoubleDeal.Link2

theorem ofDeck_toDeck (f : Fin 52 → Nat) :
    ofDeck (toDeck f) (length_toDeck f) = f := by
  funext i
  simp [ofDeck, toDeck, Array.getElem_toList, Array.getElem_ofFn]

theorem toDeck_ofDeck (d : List Nat) (h : d.length = 52) :
    toDeck (ofDeck d h) = d := by
  apply List.ext_getElem
  · simp [toDeck, length_toDeck, h]
  · intro i hi hi'
    simp [toDeck, ofDeck, Array.getElem_toList, Array.getElem_ofFn]

theorem cardBound_zero : CardBound 0 := by
  unfold CardBound i64MaxNat
  decide

theorem rotL_get_eq {α : Type} (xs : List α) (k i : Nat)
    (hne : xs.length ≠ 0) (hi : i < xs.length) :
    (rotL xs k)[i]'(by rw [length_rotL]; exact hi) =
      xs[(i + k % xs.length) % xs.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero hne)) := by
  unfold rotL
  simp only [hne, ↓reduceIte]
  have hk : k % xs.length < xs.length := Nat.mod_lt _ (Nat.pos_of_ne_zero hne)
  have hdrop : (xs.drop (k % xs.length)).length = xs.length - k % xs.length := by
    rw [List.length_drop]
  by_cases hi' : i < xs.length - k % xs.length
  · have hidx : i < (xs.drop (k % xs.length)).length := by rw [hdrop]; exact hi'
    rw [List.getElem_append_left hidx, List.getElem_drop]
    have hlt : i + k % xs.length < xs.length := by omega
    simp [Nat.mod_eq_of_lt hlt, Nat.add_comm]
  · have hge : (xs.drop (k % xs.length)).length ≤ i := by rw [hdrop]; omega
    rw [List.getElem_append_right hge]
    simp only [hdrop]
    rw [List.getElem_take]
    have hmod : (i + k % xs.length) % xs.length = i - (xs.length - k % xs.length) := by
      have : i + k % xs.length = xs.length + (i - (xs.length - k % xs.length)) := by omega
      rw [this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    simp [hmod]

theorem rowRotate_bound (g : Grid Nat) (t : Fin 4 → Nat)
    (hb : ∀ r c, CardBound (g r c)) (r : Fin 4) (c : Fin 13) :
    CardBound (rowRotate g t r c) := by
  unfold rowRotate ofList13
  have hne : (toList13 (g r)).length ≠ 0 := by simp [length_toList13]
  have hget := rotL_get_eq (toList13 (g r)) (t r) c.val hne c.isLt
  rw [hget]
  simp only [length_toList13]
  have hj : (c.val + t r % 13) % 13 < 13 := Nat.mod_lt _ (by decide)
  rw [getElem_toList13 (g r) ⟨(c.val + t r % 13) % 13, hj⟩]
  exact hb r ⟨(c.val + t r % 13) % 13, hj⟩

theorem colRotate_bound (g : Grid Nat) (s : Fin 13 → Nat)
    (hb : ∀ r c, CardBound (g r c)) (r : Fin 4) (c : Fin 13) :
    CardBound (colRotate g s r c) := by
  unfold colRotate ofList4
  have hne : (toList4 (fun r' => g r' c)).length ≠ 0 := by simp [length_toList4]
  have hget := getElem_rotR (toList4 (fun r' => g r' c)) (s c) r.val hne r.isLt
  rw [hget]
  have hj : (r.val + (4 - s c % 4)) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcell := getElem_toList4 (fun r' => g r' c) ⟨(r.val + (4 - s c % 4)) % 4, hj⟩
  simpa [length_toList4, hcell] using hb ⟨(r.val + (4 - s c % 4)) % 4, hj⟩ c

theorem sumRanks_bound (g : Grid Nat) (hb : ∀ r c, CardBound (g r c)) :
    ∀ r c, CardBound (sumRanks cardRank g r c) := by
  intro r c
  unfold sumRanks applyColRotates applyRowRotates
  exact colRotate_bound _ _ (fun r' c' => rowRotate_bound g _ hb r' c') r c

theorem shiftRows_bound (g : Grid Nat) (hb : ∀ r c, CardBound (g r c)) :
    ∀ r c, CardBound (shiftRows g r c) := by
  intro r c
  simp [shiftRows]
  exact hb r _

theorem lay_bound (m : Fin 52 → Nat) (hb : ∀ i, CardBound (m i)) :
    ∀ r c, CardBound (layColumnMajor m r c) := by
  intro r c
  simp [layColumnMajor]
  exact hb _

theorem unkeyed_bound (m : Fin 52 → Nat) (hb : ∀ i, CardBound (m i)) :
    ∀ i, CardBound (unkeyedNoMix m i) := by
  intro i
  simp [unkeyedNoMix, scoopColumnMajor]
  exact shiftRows_bound _ (sumRanks_bound _ (lay_bound m hb)) _ _

theorem placeN_cell_bound (hand : Fin 52 → Nat) (hb : ∀ i, CardBound (hand i)) :
    ∀ n, n ≤ 52 → ∀ r c, CardBound ((placeN hand n).1 r c)
  | 0, _, r, c => by
      simp [placeN]
      exact cardBound_zero
  | n + 1, hn, r, c => by
      have hlt : n < 52 := by omega
      have ih := placeN_cell_bound hand hb n (Nat.le_of_lt hlt) r c
      simp only [placeN, hlt, ↓reduceDIte, setGrid]
      by_cases hcell :
          r = (chooseSeat! (placeN hand n).2).1.1 ∧
            c = (chooseSeat! (placeN hand n).2).1.2
      · simp [hcell, hb]
      · simpa [setGrid, hcell] using ih

theorem mix_bound (hand : Fin 52 → Nat) (hb : ∀ i, CardBound (hand i)) :
    ∀ i, CardBound (mixColumns hand i) := by
  intro i
  simp [mixColumns, placedGrid, scoopRowMajor]
  exact placeN_cell_bound hand hb 52 (Nat.le_refl _) _ _

theorem compose_bound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52)
    (hb : ∀ i, CardBound (m i)) : ∀ i, CardBound (DoubleDeal.composeVec 52 Nat m pos i) := by
  intro i
  simp [DoubleDeal.composeVec]
  exact hb _

theorem full_bound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52)
    (hb : ∀ i, CardBound (m i)) : ∀ i, CardBound (fullRound m pos i) := by
  intro i
  simp [fullRound, unkeyedWithMix]
  exact compose_bound _ _ (mix_bound _ (unkeyed_bound m hb)) i

theorem fullNoMix_bound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52)
    (hb : ∀ i, CardBound (m i)) : ∀ i, CardBound (fullRoundNoMix m pos i) := by
  intro i
  simp [fullRoundNoMix]
  exact compose_bound _ _ (unkeyed_bound m hb) i

/-- Whitening, then `n` mixed rounds on PassKey iterates `1 .. n`. -/
def encAt (m : Fin 52 → Nat) (key : List Nat) : Nat → Fin 52 → Nat
  | 0 => DoubleDeal.composeVec 52 Nat m (keyPos key)
  | n + 1 => fullRound (encAt m key n) (keyPos (passKeyIter (n + 1) key))

theorem encAt_bound (m : Fin 52 → Nat) (key : List Nat) (hb : ∀ i, CardBound (m i)) :
    ∀ n i, CardBound (encAt m key n i)
  | 0, i => by
      simp [encAt]
      exact compose_bound m _ hb i
  | n + 1, i => by
      simp [encAt]
      exact full_bound _ _ (fun j => encAt_bound m key hb n j) i

theorem encAt_rounds (m : Fin 52 → Nat) (key : List Nat) :
    ∀ n, encAt m key n =
      applyFullRounds n (DoubleDeal.composeVec 52 Nat m (keyPos key))
        (fun r => keyPos (passKeyIter (r + 1) key))
  | 0 => by simp [encAt, applyFullRounds]
  | n + 1 => by
      simp [encAt, applyFullRounds, encAt_rounds m key n]

theorem stem_refines (m : Fin 52 → Nat) :
    (do
      let g ← Doubledeal.lay_cm (embed (toDeck m))
      let g ← Doubledeal.sum_ranks g
      let g ← Doubledeal.shift_rows g
      Doubledeal.scoop_cm g) =
    .ok (embed (toDeck (unkeyedNoMix m))) := by
  rw [lay_cm_refines (toDeck m) (length_toDeck m)]
  simp only [ok_bind, ofDeck_toDeck]
  rw [sum_ranks_refines]
  simp only [ok_bind]
  rw [shift_rows_refines]
  simp only [ok_bind]
  rw [scoop_cm_refines]
  simp [unkeyedNoMix]

theorem compose_toDeck (m : Fin 52 → Nat) (key : List Nat) :
    composeDeck (toDeck m) key =
      toDeck (DoubleDeal.composeVec 52 Nat m (keyPos key)) := by
  have hm : (toDeck m).length = 52 := length_toDeck m
  simp only [composeDeck, hm, ↓reduceDIte]
  rw [composeOnce_toList, ofDeck_toDeck]

set_option maxHeartbeats 800000 in
theorem final_round_refines (m : Fin 52 → Nat) (key : List Nat) (hk : Perm52 key) :
    Doubledeal.final_round (embed (toDeck m)) (embed key) =
      .ok (embed (toDeck (fullRoundNoMix m (keyPos key)))) := by
  unfold Doubledeal.final_round
  rw [lay_cm_refines (toDeck m) (length_toDeck m)]
  simp only [ok_bind, ofDeck_toDeck]
  rw [sum_ranks_refines]
  simp only [ok_bind]
  rw [shift_rows_refines]
  simp only [ok_bind]
  rw [scoop_cm_refines]
  simp only [ok_bind]
  rw [show scoopColumnMajor (shiftRows (sumRanks cardRank (layColumnMajor m))) = unkeyedNoMix m from rfl]
  rw [compose_refines (toDeck (unkeyedNoMix m)) key (length_toDeck _) hk]
  rw [compose_toDeck, except_bind_pure]
  simp [fullRoundNoMix]

theorem unkeyed_full_refines (m : Fin 52 → Nat) (hb : ∀ i, CardBound (m i)) :
    Doubledeal.unkeyed_full (embed (toDeck m)) =
      .ok (embed (toDeck (unkeyedWithMix m))) := by
  unfold Doubledeal.unkeyed_full
  rw [lay_cm_refines (toDeck m) (length_toDeck m)]
  simp only [ok_bind, ofDeck_toDeck]
  rw [sum_ranks_refines]
  simp only [ok_bind]
  rw [shift_rows_refines]
  simp only [ok_bind]
  rw [scoop_cm_refines]
  simp only [ok_bind]
  rw [show scoopColumnMajor (shiftRows (sumRanks cardRank (layColumnMajor m))) = unkeyedNoMix m from rfl]
  rw [mix_columns_refines (unkeyedNoMix m) (unkeyed_bound m hb)]
  rw [except_bind_pure]
  simp [unkeyedWithMix]

theorem full_round_refines (m : Fin 52 → Nat) (key : List Nat) (hk : Perm52 key)
    (hb : ∀ i, CardBound (m i)) :
    Doubledeal.full_round (embed (toDeck m)) (embed key) =
      .ok (embed (toDeck (fullRound m (keyPos key)))) := by
  unfold Doubledeal.full_round
  rw [unkeyed_full_refines m hb]
  simp only [ok_bind]
  rw [compose_refines (toDeck (unkeyedWithMix m)) key (length_toDeck _) hk]
  simp only [ok_bind, compose_toDeck, fullRound, except_bind_pure]

/-- One emitted encrypt round: `atL` the round key, then `full_round`. -/
def roundStep (keys : Array (Array Int)) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let r := σ.1
  let m := σ.2
  do
    if r > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (r, m))
    else
      match ← ((do
        let kr ← SudoRt.atL keys r
        let m ← Doubledeal.full_round m kr
        pure (SudoRt.Flow.cont (ρ := Array Int) m)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (r, fs))
      | .cont fs =>
          if (r == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (r, fs))
          else do
            let r' ← SudoRt.addI r 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (r', fs))

theorem encrypt_as_loop (message key : Array Int) :
    Doubledeal.encrypt message key =
      (do
        let keys ← Doubledeal.expand_keys key
        let k0 ← SudoRt.atL keys (0 : Int)
        let m ← Doubledeal.compose message k0
        let _fromV := (1 : Int)
        let _toV := (5 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array Int) (_fromV, m) fuel
          (roundStep keys _toV)
          (fun σ =>
            let m := σ.2
            do
              let kr ← SudoRt.atL keys (6 : Int)
              let out ← Doubledeal.final_round m kr
              pure out)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.encrypt
  rfl

theorem roundStep_hit (m0 : Fin 52 → Nat) (key : List Nat) (hk : Perm52 key)
    (hb : ∀ i, CardBound (m0 i)) (r : Nat) (hr1 : 1 ≤ r) (hr5 : r ≤ 5) :
    roundStep (embedDecks (expandKeys key)) 5
        (Int.ofNat r, embed (toDeck (encAt m0 key (r - 1)))) =
      if r = 5 then
        .ok (SudoRt.Flow.brk (Int.ofNat r, embed (toDeck (encAt m0 key r))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (r + 1), embed (toDeck (encAt m0 key r)))) := by
  unfold roundStep
  rw [if_neg (show ¬ Int.ofNat r > (5 : Int) from ofNat_not_gt hr5)]
  have hlen : r < (expandKeys key).length := by simp [expandKeys]; omega
  have hat := atL_ofNat (embedDecks (expandKeys key)) r (by rw [size_embedDecks]; exact hlen)
  rw [get_embedDecks (expandKeys key) r hlen] at hat
  have hkey : (expandKeys key)[r]'hlen = passKeyIter r key := by
    have hr' : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp [expandKeys, passKeyIter]
  rw [hkey] at hat
  simp only [hat, ok_bind]
  have hb' : ∀ i, CardBound (encAt m0 key (r - 1) i) :=
    fun i => encAt_bound m0 key hb (r - 1) i
  have hpk : Perm52 (passKeyIter r key) := passKeyIter_perm52 key hk r
  rw [full_round_refines (encAt m0 key (r - 1)) (passKeyIter r key) hpk hb']
  simp only [ok_bind, Pure.pure, Except.pure]
  have hnext : fullRound (encAt m0 key (r - 1)) (keyPos (passKeyIter r key)) =
      encAt m0 key r := by
    cases r with
    | zero => omega
    | succ r =>
      simp [encAt, Nat.succ_sub_one]
  rw [hnext]
  by_cases heq : r = 5
  · subst heq
    have hbq : ((5 : Int) == (5 : Int)) = true := by decide
    simp [hbq]
  · have hbq : ((Int.ofNat r) == (5 : Int)) = false := by
      cases hbv : (Int.ofNat r) == (5 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv)) heq
    simp only [hbq, ↓reduceIte]
    rw [addI_ofNat_one r (fits_succ_lt (by omega : r < 5) (by decide : 5 ≤ 52))]
    simp [ok_bind, heq]

set_option maxHeartbeats 800000 in
theorem encrypt_refines (message key : List Nat)
    (hm : message.length = 52) (hk : Perm52 key)
    (hc : ∀ i : Fin 52, CardBound ((ofDeck message hm) i)) :
    Doubledeal.encrypt (embed message) (embed key) =
      .ok (embed (encryptDeck message key)) := by
  let m : Fin 52 → Nat := ofDeck message hm
  have hembed : embed message = embed (toDeck m) := by
    simp [m, toDeck_ofDeck]
  rw [hembed, encrypt_as_loop, expand_keys_refines key hk]
  simp only [ok_bind]
  have hat0 := atL_ofNat (embedDecks (expandKeys key)) 0
    (by rw [size_embedDecks]; simp [expandKeys])
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [get_embedDecks (expandKeys key) 0 (by simp [expandKeys])] at hat0
  have h0 : (expandKeys key)[0]'(by simp [expandKeys]) = key := by
    simp [expandKeys, passKeyIter]
  rw [h0] at hat0
  rw [hat0]
  simp only [ok_bind]
  rw [compose_refines (toDeck m) key (length_toDeck m) hk]
  simp only [ok_bind, compose_toDeck]
  have hfuel : (if (1 : Int) > (5 : Int) then 1 else ((5 : Int) - 1).natAbs + 1) =
      fuelRange (Int.ofNat 1) (Int.ofNat 5) := by
    rw [fuelRange_le (by decide : 1 ≤ 5)]
    decide
  rw [hfuel, except_bind_pure]
  have hstart : embed (toDeck (DoubleDeal.composeVec 52 Nat m (keyPos key))) =
      embed (toDeck (encAt m key 0)) := by simp [encAt]
  rw [hstart]
  have hb0 : ∀ i, CardBound (encAt m key 0 i) := fun i => encAt_bound m key hc 0 i
  have hstep : ∀ i, 1 ≤ i → i ≤ 5 →
      roundStep (embedDecks (expandKeys key)) 5
          (Int.ofNat i, embed (toDeck (encAt m key (i - 1)))) =
        if i = 5 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed (toDeck (encAt m key i))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (toDeck (encAt m key i)))) :=
    fun i hi1 hi2 => roundStep_hit m key hk hc i hi1 hi2
  have hgoal :
      toDeck (fullRoundNoMix (encAt m key 5) (keyPos (passKeyIter 6 key))) =
        encryptDeck message key := by
    rw [encryptDeck_eq_encryptDeckFn message key hm]
    simp [m, encryptDeckFn, encrypt6, encryptN, encAt_rounds m key 5, fullRoundNoMix]
  have hrun := chain_loop (roundStep (embedDecks (expandKeys key)) 5)
    (fun σ =>
      let msg := σ.2
      do
        let kr ← SudoRt.atL (embedDecks (expandKeys key)) (6 : Int)
        let out ← Doubledeal.final_round msg kr
        pure out)
    (fun r => pure r)
    (fun i => embed (toDeck (encAt m key (i - 1)))) 1 5 (by decide) hstep
    (.ok (embed (encryptDeck message key))) (by
      have hat6 := atL_ofNat (embedDecks (expandKeys key)) 6
        (by rw [size_embedDecks]; simp [expandKeys])
      rw [get_embedDecks (expandKeys key) 6 (by simp [expandKeys])] at hat6
      have hk6 : (expandKeys key)[6]'(by simp [expandKeys]) = passKeyIter 6 key := by
        simp [expandKeys, passKeyIter]
      rw [hk6] at hat6
      dsimp only
      rw [show (6 : Int) = Int.ofNat 6 from rfl, hat6]
      simp only [ok_bind]
      rw [show (5 + 1) - 1 = 5 by decide]
      rw [final_round_refines (encAt m key 5) (passKeyIter 6 key)
        (passKeyIter_perm52 key hk 6)]
      rw [except_bind_pure, hgoal])
  rw [show (1 : Int) = Int.ofNat 1 from rfl]
  have hf1 : (fun i => embed (toDeck (encAt m key (i - 1)))) 1 =
      embed (toDeck (encAt m key 0)) := by simp
  simpa [hf1] using hrun

end DoubleDeal.Link2
