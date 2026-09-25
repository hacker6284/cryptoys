/-
  LINK 2. `index_of` / `compose` refine `indexOf` / `composeDeck`
  on a Perm52 key and a length-52 message.
-/
import Doubledeal
import DoubleDeal.Concrete
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck

namespace DoubleDeal.Link2

theorem ne_of_lt_indexOf (l : List Nat) (c i : Nat)
    (hlen : i < l.length) (hi : i < indexOf l c) : l.get ⟨i, hlen⟩ ≠ c := by
  induction l generalizing i with
  | nil => simp at hlen
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [indexOf, List.get] at hi ⊢
      split at hi
      · omega
      · next hne => exact hne
    | succ i =>
      simp only [List.get]
      by_cases hx : x = c
      · simp [indexOf, hx] at hi
      · have hdef : indexOf (x :: xs) c = indexOf xs c + 1 := by
          show (if x = c then 0 else indexOf xs c + 1) = _
          simp [hx]
        have hi' : i < indexOf xs c := by
          rw [hdef] at hi
          omega
        have hlen' : i < xs.length := by
          simp [List.length_cons] at hlen
          omega
        exact ih i hlen' hi'

def indexOfStep (deck : Array Int) (card toV : Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Int) :=
  do
    if i > toV then
      pure (SudoRt.Flow.brk i)
    else
      match ← ((do
        let _t338 ← SudoRt.atL deck i
        if (SudoRt.SEq.beq _t338 card) then
          pure (SudoRt.Flow.ret (ρ := Int) i)
        else
          pure (SudoRt.Flow.cont (ρ := Int) ())
      ) : Except SudoRt.Trap (SudoRt.Flow _ Int)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Int) i)
      | .cont _fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int) i)
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Int) i')

theorem index_of_as_loop (deck : Array Int) (card : Int) :
    Doubledeal.index_of deck card =
      (do
        let _fromV := (0 : Int)
        let _toV := (51 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Int) _fromV fuel
          (indexOfStep deck card _toV)
          (fun _σ => do
            let _as ← SudoRt.sudoAssert false 219
            pure (0 : Int))
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.index_of
  rfl

theorem index_of_found (key : List Nat) (hk : Perm52 key) (j : Nat) (hj : j < 52)
    (i : Nat) (hi : i ≤ indexOf key j) (hidx : indexOf key j ≤ 51) :
    SudoRt.runLoopOn (Int.ofNat i)
      (fuelRange (Int.ofNat i) (Int.ofNat 51))
      (indexOfStep (embed key) (Int.ofNat j) 51)
      (fun _σ => do
        let _as ← SudoRt.sudoAssert false 219
        pure (0 : Int))
      (fun r => pure r) =
      .ok (Int.ofNat (indexOf key j)) := by
  generalize hdelta : indexOf key j - i = delta
  induction delta generalizing i with
  | zero =>
    have heq : i = indexOf key j := by omega
    subst heq
    rw [fuelRange_le (by omega : indexOf key j ≤ 51), runLoopOn_succ]
    unfold indexOfStep
    rw [if_neg (show ¬ Int.ofNat (indexOf key j) > (51 : Int) from ofNat_not_gt hidx)]
    have hmem : j ∈ key := hk.complete ⟨j, hj⟩
    have hlt := indexOf_lt_of_mem key j hmem
    have hat := atL_embed key (indexOf key j) (by omega)
    have hget := get_indexOf key j hmem
    simp only [hat, hget, ok_bind, SudoRt.SEq.beq, beq_int_iff]
    simp [Pure.pure, Except.pure]
  | succ delta ih =>
    have hlt : i < indexOf key j := by omega
    have hi51 : i < 51 := by omega
    have hfuel :
        fuelRange (Int.ofNat i) (Int.ofNat 51) =
          fuelRange (Int.ofNat (i + 1)) (Int.ofNat 51) + 1 := by
      rw [fuelRange_le (by omega), fuelRange_le (by omega : i + 1 ≤ 51)]
      omega
    rw [hfuel, runLoopOn_succ]
    unfold indexOfStep
    rw [if_neg (show ¬ Int.ofNat i > (51 : Int) from ofNat_not_gt (Nat.le_of_lt hi51))]
    have hat := atL_embed key i (by rw [hk.length]; omega)
    have hne : key[i]'(by rw [hk.length]; omega) ≠ j :=
      ne_of_lt_indexOf key j i (by rw [hk.length]; omega) hlt
    have hdec : decide (Int.ofNat (key[i]'(by rw [hk.length]; omega)) = Int.ofNat j) = false := by
      simp [hne, ofNat_eq_natCast, Int.ofNat_inj]
    simp only [hat, hdec, ok_bind, SudoRt.SEq.beq, Pure.pure, Except.pure]
    have hneI : ¬ Int.ofNat i = (51 : Int) := by
      intro h
      exact (Nat.ne_of_lt hi51) (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h))
    have hbb : ((Int.ofNat i) == (51 : Int)) = false := by
      cases hb : (Int.ofNat i) == (51 : Int) with
      | false => rfl
      | true => exact absurd ((beq_int_iff _ _).mp hb) hneI
    simp only [hbb, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt hi51 (by decide))]
    simp only [ok_bind]
    exact ih (i + 1) (by omega) (by omega)

theorem index_of_refines (key : List Nat) (hk : Perm52 key) (j : Nat) (hj : j < 52) :
    Doubledeal.index_of (embed key) (Int.ofNat j) =
      .ok (Int.ofNat (indexOf key j)) := by
  rw [index_of_as_loop]
  have hmem : j ∈ key := hk.complete ⟨j, hj⟩
  have hlt := indexOf_lt_of_mem key j hmem
  have h52 : indexOf key j ≤ 51 := by rw [hk.length] at hlt; omega
  have hfuel : (if (0 : Int) > (51 : Int) then 1 else ((51 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 51) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [hfuel, except_bind_pure]
  exact index_of_found key hk j hj 0 (Nat.zero_le _) h52

def seat (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k)
    (j : Nat) (hj : j < 52) : Nat :=
  m[indexOf k j]'(by
    have hmem : j ∈ k := hk.complete ⟨j, hj⟩
    have hlt := indexOf_lt_of_mem k j hmem
    rw [hk.length] at hlt
    omega)

def composePrefix (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      composePrefix m k hm hk n ++
        [if h : n < 52 then seat m k hm hk n h else 0]

theorem composePrefix_succ_lt (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k)
    (n : Nat) (hn : n < 52) :
    composePrefix m k hm hk (n + 1) =
      composePrefix m k hm hk n ++ [seat m k hm hk n hn] := by
  simp [composePrefix, hn]

theorem push_embed (xs : List Nat) (x : Nat) :
    (embed xs).push (Int.ofNat x) = embed (xs ++ [x]) := by
  simp [embed, Array.push]

theorem seat_keyPos (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k)
    (j : Fin 52) :
    seat m k hm hk j.val j.isLt = ofDeck m hm (keyPos k j) := by
  have hmem : j.val ∈ k := hk.complete j
  have hlt := indexOf_lt_of_mem k j.val hmem
  have h52 : indexOf k j.val < 52 := by rw [hk.length] at hlt; omega
  simp [seat, ofDeck, keyPos, clampFin_of_lt _ h52]

theorem length_composePrefix (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k) :
    ∀ n, (composePrefix m k hm hk n).length = n
  | 0 => rfl
  | n + 1 => by simp [composePrefix, length_composePrefix m k hm hk n]

theorem get_composePrefix (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k)
    (n i : Nat) (hn : i < n) (hi : i < 52) :
    (composePrefix m k hm hk n)[i]'(by rw [length_composePrefix m k hm hk n]; exact hn) =
      seat m k hm hk i hi := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hlast : i = n
    · have hge : (composePrefix m k hm hk n).length ≤ i := by
        rw [length_composePrefix, hlast]
        exact Nat.le_refl _
      have hn52 : n < 52 := by rw [← hlast]; exact hi
      simp [composePrefix, hlast, hn52, List.getElem_append_right hge, length_composePrefix]
    · have hi' : i < n := by omega
      have hlt : i < (composePrefix m k hm hk n).length := by
        rw [length_composePrefix]; exact hi'
      simp [composePrefix, List.getElem_append_left hlt, ih i hi' hi]

theorem composePrefix_toDeck (m k : List Nat) (hm : m.length = 52) (hk : Perm52 k) :
    composePrefix m k hm hk 52 =
      toDeck (DoubleDeal.composeVec 52 Nat (ofDeck m hm) (keyPos k)) := by
  apply List.ext_getElem
  · simp [length_composePrefix, toDeck, Array.size_ofFn]
  · intro i hi hi'
    have hi52 : i < 52 := by rw [length_composePrefix] at hi; exact hi
    rw [get_composePrefix m k hm hk 52 i hi52 hi52]
    simp [toDeck, Array.getElem_ofFn, DoubleDeal.composeVec]
    exact seat_keyPos m k hm hk ⟨i, hi52⟩

def composeStep (m k0 : Array Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let j := σ.1
  let out := σ.2
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (j, out))
    else
      match ← ((do
        let _t344 ← Doubledeal.index_of k0 j
        let _t345 ← SudoRt.atL m _t344
        let _mb346 := SudoRt.appendL out _t345
        let ⟨_nr347, _⟩ := _mb346
        let out := _nr347
        pure (SudoRt.Flow.cont (ρ := Array Int) out)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array Int) (j, _fs))
      | .cont _fs =>
          if (j == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (j, _fs))
          else do
            let i' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', _fs))

theorem compose_as_loop (m k0 : Array Int) :
    Doubledeal.compose m k0 =
      (do
        let out := (#[] : Array Int)
        let _fromV := (0 : Int)
        let _toV := (51 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _init := (_fromV, out)
        let _out ← (SudoRt.runLoopOn (ρ := Array Int) _init fuel
          (composeStep m k0 _toV)
          (fun σ =>
            let out := σ.2
            pure out)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.compose
  rfl

theorem composeStep_hit (message key : List Nat) (hm : message.length = 52) (hk : Perm52 key)
    (j : Nat) (hj : j ≤ 51) :
    composeStep (embed message) (embed key) 51
      (Int.ofNat j, embed (composePrefix message key hm hk j)) =
      if j = 51 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, embed (composePrefix message key hm hk (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), embed (composePrefix message key hm hk (j + 1)))) := by
  unfold composeStep
  rw [if_neg (show ¬ Int.ofNat j > (51 : Int) from ofNat_not_gt hj)]
  have hj52 : j < 52 := by omega
  rw [index_of_refines key hk j hj52]
  simp only [ok_bind]
  have hmem : j ∈ key := hk.complete ⟨j, hj52⟩
  have hlt := indexOf_lt_of_mem key j hmem
  have hat := atL_embed message (indexOf key j) (by rw [hm, hk.length] at *; omega)
  have hcard : message[indexOf key j]'(by rw [hm, hk.length] at *; omega) =
      seat message key hm hk j hj52 := by
    simp [seat]
  rw [hat, hcard]
  simp only [ok_bind, appendL_spec, push_embed, composePrefix_succ_lt message key hm hk j hj52]
  by_cases heq : j = 51
  · subst heq
    simp only [ok_bind]
    have hbeq : ((51 : Int) == (51 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat j) == (51 : Int)) = false := by
      cases hb : (Int.ofNat j) == (51 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one j (fits_succ_lt (by omega : j < 51) (by decide : 51 ≤ 52))]
    simp [ok_bind, heq]

theorem compose_refines (message key : List Nat) (hm : message.length = 52) (hk : Perm52 key) :
    Doubledeal.compose (embed message) (embed key) =
      .ok (embed (composeDeck message key)) := by
  rw [compose_as_loop]
  have hfuel : (if (0 : Int) > (51 : Int) then 1 else ((51 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 51) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [embed_nil, hfuel, except_bind_pure]
  have hstep : ∀ i, 0 ≤ i → i ≤ 51 →
      composeStep (embed message) (embed key) 51
        (Int.ofNat i, embed (composePrefix message key hm hk i)) =
        if i = 51 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed (composePrefix message key hm hk (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (composePrefix message key hm hk (i + 1)))) :=
    fun i _ hi => composeStep_hit message key hm hk i hi
  have h0 : composePrefix message key hm hk 0 = [] := rfl
  have hrun := chain_loop (composeStep (embed message) (embed key) 51)
    (fun σ => let out := σ.2; pure out)
    (fun r => pure r)
    (fun i => embed (composePrefix message key hm hk i)) 0 51 (Nat.zero_le _) hstep
    (pure (embed (composePrefix message key hm hk 52)))
    rfl
  have hdeck : composePrefix message key hm hk 52 = composeDeck message key := by
    rw [composePrefix_toDeck]
    have hcd : composeDeck message key =
        (composeOnce (ofDeck message hm) (keyPos key)).toList := by
      simp [composeDeck, hm]
    rw [hcd, composeOnce_toList]
  simpa [h0, hdeck, Pure.pure, Except.pure] using hrun

end DoubleDeal.Link2
