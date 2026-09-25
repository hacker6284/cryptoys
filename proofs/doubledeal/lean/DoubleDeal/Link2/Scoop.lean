/-
  LINK 2. `scoop_cm` refines algebraic `scoopColumnMajor` on a 4×13 grid.
-/
import Doubledeal
import DoubleDeal.Concrete
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Shift
import DoubleDeal.Link2.Compose

namespace DoubleDeal.Link2

def scoopAt (g : Grid Nat) (n : Nat) : Nat :=
  if h : n / 4 < 13 then
    g ⟨n % 4, Nat.mod_lt _ (by decide)⟩ ⟨n / 4, h⟩
  else
    0

def scoopPrefix (g : Grid Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => scoopPrefix g n ++ [scoopAt g n]

theorem length_scoopPrefix (g : Grid Nat) : ∀ n, (scoopPrefix g n).length = n
  | 0 => rfl
  | n + 1 => by simp [scoopPrefix, length_scoopPrefix g n]

theorem scoopPrefix_get (g : Grid Nat) (n i : Nat) (hi : i < n) (hn : n ≤ 52) :
    (scoopPrefix g n)[i]'(by rw [length_scoopPrefix]; exact hi) =
      scoopAt g i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hlast : i = n
    · have hge : (scoopPrefix g n).length ≤ i := by
        rw [length_scoopPrefix, hlast]; exact Nat.le_refl _
      simp [scoopPrefix, hlast, List.getElem_append_right hge, length_scoopPrefix]
    · have hi' : i < n := by omega
      have hlt : i < (scoopPrefix g n).length := by rw [length_scoopPrefix]; exact hi'
      simp [scoopPrefix, List.getElem_append_left hlt, ih i hi' (by omega)]

theorem scoopPrefix_deck (g : Grid Nat) :
    scoopPrefix g 52 = toDeck (scoopColumnMajor g) := by
  apply List.ext_getElem
  · simp [length_scoopPrefix, toDeck, Array.size_ofFn]
  · intro i hi hi'
    have hi52 : i < 52 := by rw [length_scoopPrefix] at hi; exact hi
    rw [scoopPrefix_get g 52 i hi52 (Nat.le_refl _)]
    have hdiv : i / 4 < 13 := by omega
    simp [scoopAt, hdiv, toDeck, Array.getElem_ofFn, scoopColumnMajor, cmRow, cmCol]

def scoopInnerStep (grid : Array (Array Int)) (col toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let r := σ.1
  let out := σ.2
  do
    if r > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (r, out))
    else
      match ← ((do
        let row ← SudoRt.atL grid r
        let card ← SudoRt.atL row col
        let _mb := SudoRt.appendL out card
        let ⟨out, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array Int) out)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array Int) (r, _fs))
      | .cont _fs =>
          if (r == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (r, _fs))
          else do
            let i' ← SudoRt.addI r (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', _fs))

def scoopOuterStep (grid : Array (Array Int)) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let c := σ.1
  let out := σ.2
  do
    if c > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (c, out))
    else
      match ← ((do
        let fuel : Nat := if (0 : Int) > 3 then 1 else ((3 : Int) - 0).natAbs + 1
        let fl ← (SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), out) fuel
          (scoopInnerStep grid c 3)
          (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
          (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)))
        pure fl
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array Int) (c, _fs))
      | .cont _fs =>
          if (c == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (c, _fs))
          else do
            let i' ← SudoRt.addI c (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', _fs))

theorem scoop_cm_as_loop (g : Array (Array Int)) :
    Doubledeal.scoop_cm g =
      (do
        let out := (#[] : Array Int)
        let _fromV := (0 : Int)
        let _toV := (12 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array Int) (_fromV, out) fuel
          (scoopOuterStep g _toV)
          (fun σ =>
            let out := σ.2
            pure out)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.scoop_cm
  rfl

theorem scoopInner_hit (g : Grid Nat) (c r : Nat) (hc : c ≤ 12) (hr : r ≤ 3) :
    scoopInnerStep (embedGrid g) (Int.ofNat c) 3
      (Int.ofNat r, embed (scoopPrefix g (4 * c + r))) =
      if r = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat r, embed (scoopPrefix g (4 * c + r + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (r + 1), embed (scoopPrefix g (4 * c + r + 1)))) := by
  unfold scoopInnerStep
  rw [if_neg (show ¬ Int.ofNat r > (3 : Int) from ofNat_not_gt hr)]
  have hat := atL_ofNat (embedGrid g) r (by rw [embedGrid_size]; exact (by omega : r < 4))
  have hrow := embedGrid_get g ⟨r, by omega⟩
  have hat' :
      (embedGrid g)[r]'(by rw [embedGrid_size]; omega) = embed (toList13 (g ⟨r, by omega⟩)) := by
    simpa using hrow
  rw [hat'] at hat
  simp only [hat, ok_bind]
  have hget := getElem_toList13 (g ⟨r, by omega⟩) ⟨c, by omega⟩
  have hatC := atL_embed (toList13 (g ⟨r, by omega⟩)) c (by rw [length_toList13]; omega)
  rw [hatC]
  simp only [ok_bind, hget, appendL_spec, push_embed]
  have hnext : scoopPrefix g (4 * c + r) ++ [g ⟨r, by omega⟩ ⟨c, by omega⟩] =
      scoopPrefix g (4 * c + r + 1) := by
    have hlt : r < 4 := by omega
    have hidx : (4 * c + r) % 4 = r := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hdiv : (4 * c + r) / 4 = c := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right _ _ (by decide : 0 < 4),
        Nat.div_eq_of_lt hlt, Nat.zero_add]
    have h13 : (4 * c + r) / 4 < 13 := by rw [hdiv]; omega
    have hc13 : c < 13 := by omega
    simp [scoopPrefix, scoopAt, hidx, hdiv, h13, hc13]
  rw [hnext]
  by_cases heq : r = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat r) == (3 : Int)) = false := by
      cases hb : (Int.ofNat r) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one r (fits_succ_lt (by omega : r < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem scoopColumn_loop (g : Grid Nat) (c : Nat) (hc : c ≤ 12) :
    SudoRt.runLoopOn (Int.ofNat 0, embed (scoopPrefix g (4 * c)))
      (fuelRange (Int.ofNat 0) (Int.ofNat 3))
      (scoopInnerStep (embedGrid g) (Int.ofNat c) 3)
      (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
      (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)) =
      pure (SudoRt.Flow.cont (embed (scoopPrefix g (4 * (c + 1))))) := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      scoopInnerStep (embedGrid g) (Int.ofNat c) 3
        (Int.ofNat i, embed (scoopPrefix g (4 * c + i))) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed (scoopPrefix g (4 * c + i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (scoopPrefix g (4 * c + i + 1)))) :=
    fun i _ hi => scoopInner_hit g c i hc hi
  have h4 : 4 * c + 4 = 4 * (c + 1) := by omega
  have hrun := chain_loop
    (scoopInnerStep (embedGrid g) (Int.ofNat c) 3)
    (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
    (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r))
    (fun i => embed (scoopPrefix g (4 * c + i))) 0 3 (Nat.zero_le _) hstep
    (pure (SudoRt.Flow.cont (embed (scoopPrefix g (4 * (c + 1))))))
    (by simp [h4])
  simpa [Pure.pure] using hrun

theorem scoopOuter_hit (g : Grid Nat) (c : Nat) (hc : c ≤ 12) :
    scoopOuterStep (embedGrid g) 12
      (Int.ofNat c, embed (scoopPrefix g (4 * c))) =
      if c = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat c, embed (scoopPrefix g (4 * (c + 1)))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (c + 1), embed (scoopPrefix g (4 * (c + 1))))) := by
  unfold scoopOuterStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat c > (12 : Int) from ofNat_not_gt hc)]
  have hfuel : (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 3) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [hfuel]
  have hcol := scoopColumn_loop g c hc
  have hsame :
      SudoRt.runLoopOn ((0 : Int), embed (scoopPrefix g (4 * c)))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (scoopInnerStep (embedGrid g) (Int.ofNat c) 3)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
        (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)) =
      SudoRt.runLoopOn (Int.ofNat 0, embed (scoopPrefix g (4 * c)))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (scoopInnerStep (embedGrid g) (Int.ofNat c) 3)
        (fun σ => pure (SudoRt.Flow.cont (ρ := Array Int) σ.2))
        (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [hsame, hcol]
  simp only [Pure.pure, Except.pure, ok_bind]
  by_cases heq : c = 12
  · subst heq
    simp only [ok_bind]
    have hbeq : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · have hbeq : ((Int.ofNat c) == (12 : Int)) = false := by
      cases hb : (Int.ofNat c) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one c (fits_succ_lt (by omega : c < 12) (by decide : 12 ≤ 52))]
    simp [ok_bind, heq]

theorem scoop_cm_refines (g : Grid Nat) :
    Doubledeal.scoop_cm (embedGrid g) =
      .ok (embed (toDeck (scoopColumnMajor g))) := by
  rw [scoop_cm_as_loop]
  have hfuel : (if (0 : Int) > (12 : Int) then 1 else ((12 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 12) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [hfuel, except_bind_pure, embed_nil]
  have h0 : scoopPrefix g 0 = [] := rfl
  have hstep : ∀ i, 0 ≤ i → i ≤ 12 →
      scoopOuterStep (embedGrid g) 12
        (Int.ofNat i, embed (scoopPrefix g (4 * i))) =
        if i = 12 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed (scoopPrefix g (4 * (i + 1)))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (scoopPrefix g (4 * (i + 1))))) :=
    fun i _ hi => scoopOuter_hit g i hi
  have hrun := chain_loop (scoopOuterStep (embedGrid g) 12)
    (fun σ => let out := σ.2; pure out)
    (fun r => pure r)
    (fun i => embed (scoopPrefix g (4 * i))) 0 12 (Nat.zero_le _) hstep
    (pure (embed (scoopPrefix g (4 * 13))))
    rfl
  have h52 : 4 * 13 = 52 := by decide
  simpa [h0, h52, scoopPrefix_deck, Pure.pure, Except.pure] using hrun

end DoubleDeal.Link2
