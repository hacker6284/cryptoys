/-
  The root strip inside `base_point`. Even holes are red, odd holes stay
  empty, and hole `n - 2` is then painted white. That list is `rootDigits`
  with the unused last hole still empty. The emitted loop is the same list.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Loop
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def evenDigit (i : Nat) : Nat := if i % 2 = 0 then 2 else 0

/-- The strip after painting the first `m` holes, the rest still empty. -/
def paint (n m : Nat) : List Nat :=
  (List.range m).map evenDigit ++ List.replicate (n - m) 0

def rootStrip (n : Nat) : List Nat :=
  (paint n (n - 1)).set (n - 2) 1

private theorem set_join (xs ys : List Nat) (v : Nat) :
    (xs ++ ys).set xs.length v = xs ++ ys.set 0 v := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.set, ih]

private theorem paint_len (n m : Nat) (hm : m ≤ n) : (paint n m).length = n := by
  simp [paint, List.length_append, List.length_map, List.length_range,
    List.length_replicate]
  omega

private theorem paint_zero (n : Nat) : paint n 0 = List.replicate n 0 := by
  simp [paint]

private theorem paint_succ (n i : Nat) (hi : i < n) :
    paint n (i + 1) =
      if i % 2 = 0 then (paint n i).set i 2 else paint n i := by
  have hsplit : n - i = (n - (i + 1)) + 1 := by omega
  have hrep : List.replicate (n - i) 0 =
      0 :: List.replicate (n - (i + 1)) 0 := by
    rw [hsplit, List.replicate_succ]
  have hrange : List.range (i + 1) = List.range i ++ [i] := by
    rw [List.range_succ]
  by_cases he : i % 2 = 0
  · simp only [paint, hrange, List.map_append, List.map_singleton, he, evenDigit,
      if_true, hrep, List.append_assoc, List.singleton_append]
    have hidx : (List.range i).length = i := List.length_range i
    rw [← hidx]
    simpa [hidx] using
      (set_join ((List.range i).map evenDigit) (0 :: List.replicate (n - (i + 1)) 0) 2).symm
  · simp only [paint, hrange, List.map_append, List.map_singleton, he, evenDigit,
      if_false, hrep, List.append_assoc, List.singleton_append]

private theorem digit_early (n i : Nat) (hi : i + 2 < n) :
    rootDigit n i = evenDigit i := by
  unfold rootDigit evenDigit
  have hne : ¬ i + 2 = n := by omega
  simp [hne]

private theorem digit_last (n : Nat) (hn : 2 ≤ n) : rootDigit n (n - 2) = 1 := by
  unfold rootDigit
  have h : (n - 2) + 2 = n := by omega
  simp [h]

theorem rootStrip_eq (n : Nat) (hn : 2 ≤ n) :
    rootStrip n = rootDigits n ++ [0] := by
  have hm : n - 1 ≤ n := by omega
  have hlenL : (rootStrip n).length = n := by
    simp [rootStrip, List.length_set, paint_len n (n - 1) hm]
  have hlenR : (rootDigits n ++ [0]).length = n := by
    simp [rootDigits, List.length_append, List.length_map, List.length_range]
    omega
  apply List.ext_getElem (hlenL.trans hlenR.symm)
  intro i hi _
  have hiN : i < n := by simpa [hlenL] using hi
  let last := n - 1
  let white := n - 2
  by_cases hlast : i = last
  · have hgetL : (rootStrip n)[i] = 0 := by
      unfold rootStrip
      rw [List.getElem_set]
      have hdiff : white ≠ i := by omega
      simp only [white] at hdiff ⊢
      rw [if_neg hdiff]
      simp only [hlast, last]
      simp [paint, List.getElem_append, List.length_map, List.length_range,
        List.getElem_replicate]
    have hgetR : (rootDigits n ++ [0])[i] = 0 := by
      simp [rootDigits, hlast, last, List.getElem_append, List.length_map,
        List.length_range]
    rw [hgetL, hgetR]
  · have hiD : i < last := by omega
    by_cases hwhite : i = white
    · have hgetL : (rootStrip n)[i] = 1 := by
        unfold rootStrip
        rw [List.getElem_set]
        have hpos : n - 2 = i := by
          simpa [white] using hwhite.symm
        rw [if_pos hpos]
      have hgetR : (rootDigits n ++ [0])[i] = rootDigit n i := by
        simp [rootDigits, List.getElem_append, List.length_map, List.length_range, hiD,
          List.getElem_map]
      rw [hgetL, hgetR, hwhite]
      simpa [white] using (digit_last n hn).symm
    · have hearly : i + 2 < n := by omega
      have hgetL : (rootStrip n)[i] = evenDigit i := by
        unfold rootStrip
        rw [List.getElem_set]
        have hdiff : n - 2 ≠ i := by
          intro h
          exact hwhite (by simpa [white] using h.symm)
        rw [if_neg hdiff]
        simp [paint, List.getElem_append, List.length_map, List.length_range, hiD,
          List.getElem_map]
      have hgetR : (rootDigits n ++ [0])[i] = rootDigit n i := by
        simp [rootDigits, List.getElem_append, List.length_map, List.length_range, hiD,
          List.getElem_map]
      rw [hgetL, hgetR, digit_early n i hearly]

/-- One pass of the emitted strip loop. An even index is painted red. -/
def rootStripStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let i := σ.1
  let strip := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (i, strip))
    else
      match ← (do
        let t ← SudoRt.modI i (2 : Int)
        if SudoRt.SEq.beq t (0 : Int) then
          do
            let strip ← SudoRt.putL strip i (2 : Int)
            pure (SudoRt.Flow.cont strip)
        else
          pure (SudoRt.Flow.cont strip) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret r)
      | .brk fs => pure (SudoRt.Flow.brk (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (i, fs))
          else
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (i', fs))

private theorem embed_rep (n : Nat) :
    Array.mkArray n (0 : Int) = embed (List.replicate n 0) := by
  simp [embed, Array.mkArray, List.map_replicate]

private theorem embed_set (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    (embed xs).set ⟨i, by rw [size_embed]; exact h⟩ (Int.ofNat v) = embed (xs.set i v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro j hj hj'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem strip_body (n i : Nat) (hi : i < n) (strip : Array Int)
    (hp : strip = embed (paint n i)) :
    (do
        let t ← SudoRt.modI (Int.ofNat i) (2 : Int)
        if SudoRt.SEq.beq t (0 : Int) then
          do
            let strip ← SudoRt.putL strip (Int.ofNat i) (2 : Int)
            pure (SudoRt.Flow.cont strip)
        else
          pure (SudoRt.Flow.cont strip) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int))) =
      .ok (SudoRt.Flow.cont (embed (paint n (i + 1)))) := by
  have hmod := modI_ofNat i (by decide : (2 : Nat) ≠ 0)
  rw [show (2 : Int) = Int.ofNat 2 from rfl, hmod, ok_bind]
  by_cases he : i % 2 = 0
  · rw [sEq_ofNat_zero (i % 2), decide_eq_true he]
    simp only [cond_true]
    have hlt : i < (paint n i).length := by rw [paint_len n i (by omega)]; exact hi
    rw [hp, putL_ofNat _ i (Int.ofNat 2) (by rw [size_embed]; exact hlt), ok_bind, pure_eq_ok]
    have hset : (paint n i).set i 2 = paint n (i + 1) := by
      simpa [he] using (paint_succ n i hi).symm
    have hE := embed_set (paint n i) i 2 hlt
    have hfin : (embed (paint n i)).set ⟨i, by rw [size_embed]; exact hlt⟩ (Int.ofNat 2) =
        embed (paint n (i + 1)) := by
      rw [hE, hset]
    exact congrArg (fun a => Except.ok (SudoRt.Flow.cont a)) hfin
  · rw [sEq_ofNat_zero (i % 2), decide_eq_false he]
    simp only [cond_false, pure_eq_ok]
    have hset : paint n (i + 1) = paint n i := by
      simpa [he] using paint_succ n i hi
    simpa [hp, hset]

private theorem strip_step (n toN i : Nat) (strip : Array Int)
    (hn : 2 ≤ n) (hto : toN = n - 2) (hi : i ≤ toN)
    (hfit : FitsLen (i + 1))
    (hp : strip = embed (paint n i)) :
    rootStripStep (Int.ofNat toN) (Int.ofNat i, strip) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, embed (paint n (i + 1))))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (paint n (i + 1)))) := by
  unfold rootStripStep
  dsimp only
  have hlt : i < n := by omega
  have hng : ¬ Int.ofNat i > Int.ofNat toN := ofNat_not_gt hi
  rw [if_neg hng]
  rw [strip_body n i hlt strip hp, ok_bind]
  simp only [pure_eq_ok]
  exact asc_tail toN i hfit (embed (paint n (i + 1)))

private theorem strip_inv (n : Nat) (hn : 2 ≤ n) (hfit : FitsLen n) :
    SudoRt.runLoopOn (Int.ofNat 0, Array.mkArray n (0 : Int))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
        (rootStripStep (Int.ofNat (n - 2)))
        (fun σ =>
          SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
            SudoRt.putL σ.2 ix (1 : Int))
        (fun r => pure r) =
      .ok (embed (rootStrip n)) := by
  have hto : n - 2 ≤ n - 2 := Nat.le_refl _
  have h0 : Array.mkArray n (0 : Int) = embed (paint n 0) := by
    rw [embed_rep, paint_zero]
  refine asc_goal (fun i s => s = embed (paint n i)) (by omega : 0 ≤ n - 2) h0 ?_ ?_
  · intro i s hi hito hs
    have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    have hstep := strip_step n (n - 2) i s hn rfl hito hfiti hs
    refine ⟨embed (paint n (i + 1)), rfl, ?_⟩
    simpa using hstep
  · intro s hs
    have hsub := subI_ofNat n 2 hfit (by omega)
    rw [show (2 : Int) = Int.ofNat 2 from rfl, hsub, ok_bind]
    have hlt : n - 2 < (paint n (n - 1)).length := by
      rw [paint_len n (n - 1) (by omega)]
      omega
    simp only [Prod.snd]
    have hidx : n - 2 + 1 = n - 1 := by omega
    rw [hs, hidx]
    rw [show (1 : Int) = Int.ofNat 1 from rfl]
    rw [putL_ofNat _ (n - 2) (Int.ofNat 1) (by rw [size_embed]; exact hlt)]
    exact congrArg Except.ok (embed_set (paint n (n - 1)) (n - 2) 1 hlt)

/-- The emitted strip, including the final white peg in hole `n - 2`. -/
theorem root_strip_loop (n : Nat) (hn : 2 ≤ n) (hfit : FitsLen n) :
    SudoRt.runLoopOn (Int.ofNat 0, Array.mkArray n (0 : Int))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
        (rootStripStep (Int.ofNat (n - 2)))
        (fun σ =>
          SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
            SudoRt.putL σ.2 ix (1 : Int))
        (fun r => pure r) =
      .ok (embed (rootDigits n ++ [0])) := by
  rw [strip_inv n hn hfit, rootStrip_eq n hn]

end EcbsLink2.Link2
