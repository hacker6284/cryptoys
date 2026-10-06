/-
  BS Link 2: §3.1 sending a public value (`answer`, `copy_shot`, `call_the_shots`,
  `send_public_value`) against the model `Spec.sendPublicValue`. Proof-only.
-/
import BsLink2.Link2.Refines

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- The emitted `Shot` of a model shot. -/
def embShot : Spec.Shot → Bs.Shot
  | .hit => .Sudo_4Shot_3Hit
  | .miss => .Sudo_4Shot_4Miss
  | .misfire => .Sudo_4Shot_7Misfire

theorem getD_lt (xs : List Nat) (j : Nat) (h : j < xs.length) : xs.getD j 0 = xs[j] := by
  simp [List.getD, h]

theorem answer_spec (value : Array Int) (i : Nat) (hi : i < value.size) (hd : 0 ≤ value[i] ∧ value[i] ≤ 2) :
    Bs.answer value (Int.ofNat i) = .ok (embShot (Spec.answer value[i].toNat)) := by
  unfold Bs.answer
  rw [atL_ofNat value i hi]
  rcases (by omega : value[i] = 0 ∨ value[i] = 1 ∨ value[i] = 2) with e | e | e <;>
    simp [e, sEq_int, Spec.answer, embShot] <;> rfl

theorem copy_shot_spec (y : Array Int) (i : Nat) (hi : i < y.size) (t : Nat) (ht : t ≤ 2) :
    Bs.copy_shot y (Int.ofNat i) (embShot (Spec.answer t)) =
      .ok (if t = 0 then y else y.set ⟨i, hi⟩ (Int.ofNat t)) := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
    simp [Bs.copy_shot, Spec.answer, embShot, putL_cast y i _ hi] <;> rfl

theorem call_the_shots_spec (f : Bs.Field) (n : Nat) (hn : f.sudo_5Field_1n = Int.ofNat n)
    (hn1 : 1 ≤ n) (hfit : FitsLen n) (x : List Nat) (hx : Spec.IsReg n x)
    (y : Array Int) (hy : y.size = n) :
    Bs.call_the_shots f (embed x) y =
      .ok (((x.map Spec.answer).map embShot).toArray, embed x) := by
  obtain ⟨hxl, hxt⟩ := hx
  have hxs : (embed x).size = n := by rw [size_embed, hxl]
  have htx := trits_embed hxt
  unfold Bs.call_the_shots
  simp only [listLen_eq, hn, hxs, hy, sEq_int, decide_True, pure_eq_ok, if_true, ok_bind,
    sudoAssert_true, subI_ofNat_one n hn1 hfit]
  rw [bind_ok_right, fuelRange_eq]
  refine asc_goal (fromN := 0) (toN := n - 1) (fun i (o : Array Int) => o.size = n ∧
      ∀ j (hj : j < o.size), j < i → o[j] = 0)
    (Nat.zero_le _) ⟨hy, fun j _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · intro i o _ hi hI
    obtain ⟨hI, hz⟩ := hI
    have hio : i < o.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    refine ⟨o.set ⟨i, hio⟩ 0, ⟨by simp [hI], ?_⟩, ?_⟩
    · intro j hj hji
      by_cases e : j = i
      · subst e; simp
      · simp only [Array.size_set] at hj
        rw [Array.getElem_set_ne _ _ _ _ (Ne.symm e)]; exact hz j hj (by omega)
    dsimp only
    rw [if_neg (ofNat_not_gt hi), putL_ofNat o i _ hio, ok_bind]
    exact asc_tail _ i hfi _
  · intro o hI
    obtain ⟨hI, hz⟩ := hI
    dsimp only
    rw [bind_ok_right]
    refine asc_goal (fromN := 0) (toN := n - 1) (fun i (st : Array Bs.Shot × Array Int) =>
        st.1.toList = ((x.take i).map Spec.answer).map embShot ∧ st.2.size = n ∧
        ∀ j (hj : j < st.2.size), (j < i → st.2[j] = Int.ofNat (x.getD j 0)) ∧
          (i ≤ j → st.2[j] = 0))
      (Nat.zero_le _) ⟨by simp, hI, fun j _ => ⟨fun h => absurd h (Nat.not_lt_zero _),
        fun _ => hz j (by simpa using ‹j < (#[], o).2.size›)
          (by have : j < o.size := ‹j < (#[], o).2.size›; omega)⟩⟩ ?_ ?_
    · intro i st _ hi hI
      obtain ⟨sh, o⟩ := st
      obtain ⟨hsh, hosz, hoj⟩ := hI
      dsimp only at hsh hosz hoj
      have hio : i < o.size := by omega
      have hix : i < (embed x).size := by omega
      have hixl : i < x.length := by omega
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      have hxi : (embed x)[i] = Int.ofNat x[i] := get_embed x i hix
      have hti : x[i] ≤ 2 := hxt _ (List.getElem_mem _)
      have hd := trits_get htx i hix
      have hans := answer_spec (embed x) i hix hd
      rw [hxi] at hans
      rw [show (Int.ofNat x[i]).toNat = x[i] from rfl] at hans
      have hcopy := copy_shot_spec o i hio x[i] hti
      refine ⟨((SudoRt.appendL sh (embShot (Spec.answer x[i]))).fst,
        if x[i] = 0 then o else o.set ⟨i, hio⟩ (Int.ofNat x[i])), ⟨?_, ?_, ?_⟩, ?_⟩
      · simp [SudoRt.appendL, hsh, List.take_succ, hixl]
      · split <;> simp [hosz]
      · intro j hj
        have hj' : j < o.size := by split at hj <;> simp_all
        have hjx : j < x.length := by omega
        by_cases e : j = i
        · subst e
          refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
          rw [getD_lt _ _ hjx]
          split
          · next h0 => rw [(hoj j hj').2 (Nat.le_refl _), h0]; rfl
          · simp
        · have hoj' := hoj j hj'
          have hget : (if x[i] = 0 then o else o.set ⟨i, hio⟩ (Int.ofNat x[i]))[j]'hj = o[j] := by
            split
            · rfl
            · exact Array.getElem_set_ne _ _ _ _ (Ne.symm e)
          rw [hget]
          exact ⟨fun h => hoj'.1 (by omega), fun h => hoj'.2 (by omega)⟩
      · dsimp only
        rw [if_neg (ofNat_not_gt hi), hans, ok_bind, hcopy, ok_bind]
        exact asc_tail _ i hfi _
    · intro st hI
      obtain ⟨sh, o⟩ := st
      obtain ⟨hsh, hosz, hoj⟩ := hI
      dsimp only at hsh hosz hoj ⊢
      rw [show n - 1 + 1 = x.length by omega, List.take_length] at hsh
      show Except.ok (sh, o) = _
      congr 2
      · apply Array.ext'; rw [hsh]
      · apply Array.ext _ _ (by rw [hosz, hxs])
        intro j h1 h2
        rw [(hoj j h1).1 (by omega), get_embed x j h2, getD_lt _ _ (by omega)]

/-- §3.1 refines the model: sending a register `x` of `n` trits yields the answers
    `x.map answer` (in call order, hole 0 first) and a Y holding exactly `x`. -/
theorem send_public_value_refines (F : Spec.Field) (hF : F.Wf) (hfit : FitsLen F.n)
    (x : List Nat) (hx : Spec.IsReg F.n x) :
    Bs.send_public_value (emb F) (embed x) =
      .ok { sudo_6Called_5shots := ((Spec.sendPublicValue x).1.map embShot).toArray,
            sudo_6Called_1y := embed (Spec.sendPublicValue x).2 } := by
  unfold Bs.send_public_value
  rw [show Bs.empty_register (emb F) = .ok (Array.mkArray F.n 0) by
    unfold Bs.empty_register; rw [show (emb F).sudo_5Field_1n = Int.ofNat F.n from rfl,
      filledL_ofNat]; rfl, ok_bind]
  dsimp only
  rw [call_the_shots_spec (emb F) F.n rfl (by have := hF.toll_pos; have := hF.toll_lt; omega)
      hfit x hx _ (by simp)]
  simp [Spec.sendPublicValue]

end BsLink2.Link2
