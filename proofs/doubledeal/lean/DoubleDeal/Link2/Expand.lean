/-
  LINK 2. `expand_keys` refines algebraic `expandKeys` on a Perm52 key.
-/
import Doubledeal
import DoubleDeal.Concrete
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.PassKey

namespace DoubleDeal.Link2

def embedDecks (ks : List (List Nat)) : Array (Array Int) :=
  Array.mk (ks.map embed)

theorem size_embedDecks (ks : List (List Nat)) : (embedDecks ks).size = ks.length := by
  simp [embedDecks]

theorem get_embedDecks (ks : List (List Nat)) (i : Nat) (h : i < ks.length) :
    (embedDecks ks)[i]'(by rw [size_embedDecks]; exact h) = embed (ks[i]'h) := by
  simp [embedDecks]

theorem embedDecks_append (ks : List (List Nat)) (k : List Nat) :
    (embedDecks ks).push (embed k) = embedDecks (ks ++ [k]) := by
  simp [embedDecks, Array.push]

def keyPrefix (key : List Nat) : Nat → List (List Nat)
  | 0 => []
  | n + 1 => keyPrefix key n ++ [passKeyIter n key]

theorem keyPrefix_length (key : List Nat) (n : Nat) :
    (keyPrefix key n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keyPrefix, ih]

theorem length_passKeyIter (key : List Nat) (hk : Perm52 key) (n : Nat) :
    (passKeyIter n key).length = 52 :=
  (passKeyIter_perm52 key hk n).length

theorem keyPrefix_get (key : List Nat) (n i : Nat) (hi : i < n) :
    (keyPrefix key n)[i]'(by rw [keyPrefix_length]; exact hi) = passKeyIter i key := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hlast : i = n
    · simp [keyPrefix, hlast, keyPrefix_length, List.getElem_append_right]
    · have hi' : i < n := by omega
      have hlt : i < (keyPrefix key n).length := by rw [keyPrefix_length]; exact hi'
      simp [keyPrefix, List.getElem_append_left hlt, ih i hi']

theorem passKeyIter_succ_prev (key : List Nat) (r : Nat) (hr : 0 < r) :
    passKeyIter r key = passToKeyCutFallback (passKeyIter (r - 1) key) := by
  cases r with
  | zero => omega
  | succ n => simp [passKeyIter]

theorem keyPrefix_expand (key : List Nat) :
    keyPrefix key 7 = expandKeys key := by
  simp [keyPrefix, expandKeys, List.range_succ, List.map_append, List.map]

def expandKeysStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let r := σ.1
  let keys := σ.2
  do
    if r > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, keys))
    else
      match ← ((do
        let _t501 ← SudoRt.subI r (1 : Int)
        let _t502 ← SudoRt.atL keys _t501
        let _t503 ← Doubledeal.passkey _t502
        let _mb504 := SudoRt.appendL keys _t503
        let ⟨_nr505, _⟩ := _mb504
        let keys := _nr505
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) keys)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, _fs))
      | .cont _fs =>
          if (r == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, _fs))
          else do
            let i' ← SudoRt.addI r (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', _fs))

theorem expand_keys_as_loop (k0 : Array Int) :
    Doubledeal.expand_keys k0 =
      (do
        let keys := (#[] : Array (Array Int))
        let _mb := SudoRt.appendL keys k0
        let ⟨keys, _⟩ := _mb
        let _fromV := (1 : Int)
        let _toV := (6 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _init := (_fromV, keys)
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) _init fuel
          (expandKeysStep _toV)
          (fun σ =>
            let keys := σ.2
            pure keys)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.expand_keys
  rfl

theorem expandKeysStep_hit (key : List Nat) (hk : Perm52 key) (r : Nat)
    (hr : 1 ≤ r) (hrh : r ≤ 6) :
    expandKeysStep (6 : Int) (Int.ofNat r, embedDecks (keyPrefix key r)) =
      if r = 6 then
        .ok (SudoRt.Flow.brk (Int.ofNat r, embedDecks (keyPrefix key (r + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (r + 1), embedDecks (keyPrefix key (r + 1)))) := by
  unfold expandKeysStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat r > (6 : Int) from ofNat_not_gt hrh)]
  have hpos : 0 < r := by omega
  rw [subI_ofNat_one r hpos (fits52 (by omega))]
  have hidx : r - 1 < (keyPrefix key r).length := by rw [keyPrefix_length]; omega
  have hat := atL_ofNat (embedDecks (keyPrefix key r)) (r - 1)
    (by rw [size_embedDecks]; exact hidx)
  have hget := get_embedDecks (keyPrefix key r) (r - 1) hidx
  rw [hget] at hat
  simp only [hat, ok_bind]
  have hprev : (keyPrefix key r)[r - 1]'hidx = passKeyIter (r - 1) key :=
    keyPrefix_get key r (r - 1) (by omega)
  rw [hprev]
  have hlen := length_passKeyIter key hk (r - 1)
  rw [passkey_refines (passKeyIter (r - 1) key) (by rw [hlen]; exact fits_52)]
  simp only [ok_bind, appendL_spec]
  have happ := embedDecks_append (keyPrefix key r) (passToKeyCutFallback (passKeyIter (r - 1) key))
  have hnext : keyPrefix key r ++ [passToKeyCutFallback (passKeyIter (r - 1) key)] =
      keyPrefix key (r + 1) := by
    rw [← passKeyIter_succ_prev key r hpos, keyPrefix]
  rw [happ, hnext]
  by_cases heq : r = 6
  · subst heq
    simp only [ok_bind]
    have hbeq : ((6 : Int) == (6 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat r) == (6 : Int)) = false := by
      cases hb : (Int.ofNat r) == (6 : Int) with
      | false => rfl
      | true =>
        have heqI : Int.ofNat r = (6 : Int) := (beq_int_iff _ _).mp hb
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using heqI)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one r (fits_succ_lt (by omega : r < 7) (by decide : 7 ≤ 52))]
    simp [ok_bind, heq]

theorem expand_keys_refines (key : List Nat) (hk : Perm52 key) :
    Doubledeal.expand_keys (embed key) =
      .ok (embedDecks (expandKeys key)) := by
  rw [expand_keys_as_loop]
  have hpush : ((#[] : Array (Array Int)).push (embed key)) = embedDecks [key] := by
    simp [embedDecks, embed_nil, Array.push]
  simp only [appendL_spec, hpush]
  have h0 : [key] = keyPrefix key 1 := by simp [keyPrefix, passKeyIter]
  rw [h0]
  have hfuel : (if (1 : Int) > (6 : Int) then 1 else ((6 : Int) - 1).natAbs + 1) =
      fuelRange (Int.ofNat 1) (Int.ofNat 6) := by
    rw [fuelRange_le (by decide : 1 ≤ 6)]
    decide
  simp only [hfuel, except_bind_pure]
  have hstep : ∀ i, 1 ≤ i → i ≤ 6 →
      expandKeysStep (6 : Int) (Int.ofNat i, embedDecks (keyPrefix key i)) =
        if i = 6 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embedDecks (keyPrefix key (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedDecks (keyPrefix key (i + 1)))) :=
    fun i hi1 hi2 => expandKeysStep_hit key hk i hi1 hi2
  have hrun := chain_loop (expandKeysStep (6 : Int))
    (fun σ => let keys := σ.2; pure keys)
    (fun r => pure r)
    (fun i => embedDecks (keyPrefix key i)) 1 6 (by decide) hstep
    (pure (embedDecks (keyPrefix key 7)))
    (by simp [keyPrefix_expand])
  simpa [Pure.pure, Except.pure, keyPrefix_expand] using hrun

end DoubleDeal.Link2
