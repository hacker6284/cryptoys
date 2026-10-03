/-
  Link 2 for the v3 piece searches `edge_face_of` and `corner_face_of`. Symbolic in the
  position: for every position `g` and colours with `edge_slot` / `corner_slot` defined, when the
  model search `edgeFaceOf?` / `cornerFaceOf?` returns `some y`, the emitted function returns
  `y` (the slot scans are driven by `chain_loop`; the asserts pass). When the model
  returns `some` is the found-invariant (proved separately). No sorry. No native_decide.
-/
import MegaDreifachV3.Link2.CardTables
import MegaDreifachV3.Link2.CardFacts
import MegaDreifach.Link2.EvenRank

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifachV3.Em

theorem lastIdx_succ (i : Nat) (p : Nat → Bool) :
    lastIdx (i + 1) p = if p i then some i else lastIdx i p := by
  unfold lastIdx
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The emitted scan's `slot` after the indices `< i`: the last hit, or `-1`. -/
def scanAcc (i : Nat) (p : Nat → Bool) : Int :=
  match lastIdx i p with
  | none => -1
  | some s => Int.ofNat s

theorem sEq_ofNatV3 (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int, decide_eq_decide]
  exact ⟨fun e => Int.ofNat.inj e, fun e => e ▸ rfl⟩

theorem atL_listOf30' (f : Fin 30 → Fin 30) (i : Nat) (hi : i < 30) :
    SudoRt.atL (embed (listOf f)) (Int.ofNat i) = .ok (Int.ofNat (f ⟨i % 30, Nat.mod_lt _ (by decide)⟩).val) := by
  have hlen : i < (listOf f).length := by rw [listOf_length]; exact hi
  rw [atL_embed (listOf f) i hlen]
  simp [listOf, List.getElem_map, List.getElem_range, Nat.mod_eq_of_lt hi, hi]

theorem lastIdx_lt (n : Nat) (p : Nat → Bool) (t : Nat) (h : lastIdx n p = some t) : t < n := by
  induction n with
  | zero => simp [lastIdx] at h
  | succ k ih =>
    rw [lastIdx_succ] at h
    by_cases hp : p k = true
    · rw [if_pos hp] at h; cases h; omega
    · rw [if_neg hp] at h; have := ih h; omega

theorem lastIdx_spec (n : Nat) (p : Nat → Bool) (t : Nat) (h : lastIdx n p = some t) : p t = true := by
  induction n with
  | zero => simp [lastIdx] at h
  | succ k ih =>
    rw [lastIdx_succ] at h
    by_cases hp : p k = true
    · rw [if_pos hp] at h; cases h; exact hp
    · rw [if_neg hp] at h; exact ih h

theorem sudoAssertEq_self (x : Int) (line : Nat) : SudoRt.sudoAssertEq x x line = .ok () := by
  have hb : SudoRt.SEq.beq x x = true := by simp [sEq_int]
  unfold SudoRt.sudoAssertEq
  rw [hb]
  rfl

theorem edge_face_of_refines (g : Position) (a b x : Fin 12) (s : Fin 30)
    (hs : edgeSlot? a b = some s) (y : Fin 12) (hy : edgeFaceOf? g a b x = some y) :
    Megadreifach.edge_face_of (embedPos g) (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat x.val) =
      .ok (Int.ofNat y.val) := by
  have hpc : edgeSlot a b = s := by simp [edgeSlot, hs]
  unfold Megadreifach.edge_face_of
  rw [edge_slot_refines a b s hs, ok_bind, negI_one, ok_bind]
  dsimp only
  rw [except_bind_pure]
  refine chain_loop _ _ _
    (fun i => scanAcc i (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s))) 0 29
    (by decide) ?_ _ ?_
  · intro i _ hi
    have hi30 : i < 30 := by omega
    have hgt : ¬ (Int.ofNat i > (29 : Int)) := by rw [Int.ofNat_eq_coe]; omega
    dsimp only
    rw [if_neg hgt, show (embedPos g).sudo_8Position_2ep = embed (listOf g.ep) from rfl,
      atL_listOf30' g.ep i hi30, ok_bind, sEq_ofNatV3]
    have hfit : FitsLen (i + 1) := by unfold FitsLen i64MaxNat; omega
    have hadd : SudoRt.addI (Int.ofNat i) 1 = .ok (Int.ofNat (i + 1)) := addI_ofNat i 1 hfit
    have hbeq : (Int.ofNat i == 29) = decide (i = 29) := by
      rw [Int.ofNat_eq_coe]
      by_cases h : i = 29 <;> simp [h] <;> omega
    by_cases hp : g.ep ⟨i % 30, Nat.mod_lt _ (by decide)⟩ = s
    · have hd : decide ((g.ep ⟨i % 30, Nat.mod_lt _ (by decide)⟩).val = s.val) = true := by
        simp [hp]
      have hn : scanAcc (i + 1) (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) =
          Int.ofNat i := by simp [scanAcc, lastIdx_succ, hp]
      rw [if_pos hd, hn]
      simp only [pure_bind, hbeq, hadd, ok_bind]
      by_cases h29 : i = 29 <;> simp [h29] <;> rfl
    · have hd : decide ((g.ep ⟨i % 30, Nat.mod_lt _ (by decide)⟩).val = s.val) = false := by
        simp [Fin.val_inj, hp]
      have hn : scanAcc (i + 1) (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) =
          scanAcc i (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) := by
        simp [scanAcc, lastIdx_succ, hp]
      rw [if_neg (by rw [hd]; decide), hn]
      simp only [pure_bind, hbeq, hadd, ok_bind]
      by_cases h29 : i = 29 <;> simp [h29] <;> rfl
  · dsimp only
    unfold edgeFaceOf? at hy
    rw [hpc] at hy
    dsimp only at hy
    cases hl : lastIdx 30 (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) with
    | none => rw [hl] at hy; cases hy
    | some sl =>
      rw [hl] at hy
      dsimp only at hy
      have hacc : scanAcc (29 + 1) (fun t => decide (g.ep ⟨t % 30, Nat.mod_lt _ (by decide)⟩ = s)) =
          Int.ofNat sl := by simp [scanAcc, hl]
      rw [hacc]
      have hsl : sl < 30 := lastIdx_lt 30 _ sl hl
      have hge : decide (Int.ofNat sl ≥ 0) = true := by simp; omega
      rw [hge, sudoAssert_true, ok_bind, edge_faces_refines ⟨sl, hsl⟩, ok_bind]
      dsimp only
      rw [edge_colours_at_refines g _ _ ⟨sl, hsl⟩ (edgeSlot?_faces ⟨sl, hsl⟩), ok_bind]
      dsimp only
      rw [sEq_ofNatV3]
      by_cases h0 : (edgeColoursAt g (edgeFace sl 0) (edgeFace sl 1)).1 = x
      · rw [if_pos h0] at hy
        cases hy
        rw [if_pos (by simp [h0])]
        rfl
      · rw [if_neg h0] at hy
        by_cases h1 : (edgeColoursAt g (edgeFace sl 0) (edgeFace sl 1)).2 = x
        · rw [if_pos h1] at hy
          cases hy
          rw [if_neg (by simp [Fin.val_inj, h0]), ← h1, sudoAssertEq_self, ok_bind]
          rfl
        · rw [if_neg h1] at hy
          cases hy

theorem atL_listOf20' (f : Fin 20 → Fin 20) (i : Nat) (hi : i < 20) :
    SudoRt.atL (embed (listOf f)) (Int.ofNat i) = .ok (Int.ofNat (f ⟨i % 20, Nat.mod_lt _ (by decide)⟩).val) := by
  have hlen : i < (listOf f).length := by rw [listOf_length]; exact hi
  rw [atL_embed (listOf f) i hlen]
  simp [listOf, List.getElem_map, List.getElem_range, Nat.mod_eq_of_lt hi, hi]

theorem atL_listOfOri20' (f : Fin 20 → Fin 3) (i : Nat) (hi : i < 20) :
    SudoRt.atL (embed (listOfOri f)) (Int.ofNat i) = .ok (Int.ofNat (f ⟨i % 20, Nat.mod_lt _ (by decide)⟩).val) := by
  have hlen : i < (listOfOri f).length := by rw [listOfOri_length]; exact hi
  rw [atL_embed (listOfOri f) i hlen]
  simp [listOfOri, List.getElem_map, List.getElem_range, Nat.mod_eq_of_lt hi, hi]

theorem corner_face_of_refines (g : Position) (a b c x : Fin 12) (t : Fin 20)
    (ht : cornerSlot? a b c = some t) (y : Fin 12) (hy : cornerFaceOf? g a b c x = some y) :
    Megadreifach.corner_face_of (embedPos g) (Int.ofNat a.val) (Int.ofNat b.val)
        (Int.ofNat c.val) (Int.ofNat x.val) = .ok (Int.ofNat y.val) := by
  have hpc : cornerSlot a b c = t := by simp [cornerSlot, ht]
  unfold Megadreifach.corner_face_of
  rw [corner_slot_refines a b c t ht, ok_bind, negI_one, ok_bind]
  dsimp only
  rw [except_bind_pure]
  refine chain_loop _ _ _
    (fun i => scanAcc i (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t))) 0 19
    (by decide) ?_ _ ?_
  · intro i _ hi
    have hi20 : i < 20 := by omega
    have hgt : ¬ (Int.ofNat i > (19 : Int)) := by rw [Int.ofNat_eq_coe]; omega
    dsimp only
    rw [if_neg hgt, show (embedPos g).sudo_8Position_2cp = embed (listOf g.cp) from rfl,
      atL_listOf20' g.cp i hi20, ok_bind, sEq_ofNatV3]
    have hfit : FitsLen (i + 1) := by unfold FitsLen i64MaxNat; omega
    have hadd : SudoRt.addI (Int.ofNat i) 1 = .ok (Int.ofNat (i + 1)) := addI_ofNat i 1 hfit
    have hbeq : (Int.ofNat i == 19) = decide (i = 19) := by
      rw [Int.ofNat_eq_coe]
      by_cases h : i = 19 <;> simp [h] <;> omega
    by_cases hp : g.cp ⟨i % 20, Nat.mod_lt _ (by decide)⟩ = t
    · have hd : decide ((g.cp ⟨i % 20, Nat.mod_lt _ (by decide)⟩).val = t.val) = true := by
        simp [hp]
      have hn : scanAcc (i + 1) (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) =
          Int.ofNat i := by simp [scanAcc, lastIdx_succ, hp]
      rw [if_pos hd, hn]
      simp only [pure_bind, hbeq, hadd, ok_bind]
      by_cases h19 : i = 19 <;> simp [h19] <;> rfl
    · have hd : decide ((g.cp ⟨i % 20, Nat.mod_lt _ (by decide)⟩).val = t.val) = false := by
        simp [Fin.val_inj, hp]
      have hn : scanAcc (i + 1) (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) =
          scanAcc i (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) := by
        simp [scanAcc, lastIdx_succ, hp]
      rw [if_neg (by rw [hd]; decide), hn]
      simp only [pure_bind, hbeq, hadd, ok_bind]
      by_cases h19 : i = 19 <;> simp [h19] <;> rfl
  · dsimp only
    unfold cornerFaceOf? at hy
    rw [hpc] at hy
    dsimp only at hy
    cases hl : lastIdx 20 (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) with
    | none => rw [hl] at hy; cases hy
    | some sl =>
      rw [hl] at hy
      dsimp only at hy
      have hacc : scanAcc (19 + 1) (fun u => decide (g.cp ⟨u % 20, Nat.mod_lt _ (by decide)⟩ = t)) =
          Int.ofNat sl := by simp [scanAcc, hl]
      rw [hacc]
      have hsl : sl < 20 := lastIdx_lt 20 _ sl hl
      have hge : decide (Int.ofNat sl ≥ 0) = true := by simp; omega
      rw [hge, sudoAssert_true, ok_bind, corner_faces_refines ⟨sl, hsl⟩, ok_bind]
      dsimp only
      rw [corner_faces_refines t, ok_bind]
      dsimp only
      rw [show (embedPos g).sudo_8Position_2co = embed (listOfOri g.co) from rfl,
        atL_listOfOri20' g.co sl hsl, ok_bind, ok_bind]
      simp only [colour_on_refines, ok_bind, sEq_ofNatV3]
      by_cases h2 : colourOn (cornerFace sl 2) (cornerFace sl 1) (cornerFace sl 2) (cornerFace t.val 0)
          (cornerFace t.val 1) (cornerFace t.val 2) (g.co ⟨sl % 20, Nat.mod_lt _ (by decide)⟩) = x <;>
      by_cases h1 : colourOn (cornerFace sl 1) (cornerFace sl 1) (cornerFace sl 2) (cornerFace t.val 0)
          (cornerFace t.val 1) (cornerFace t.val 2) (g.co ⟨sl % 20, Nat.mod_lt _ (by decide)⟩) = x <;>
      by_cases h0 : colourOn (cornerFace sl 0) (cornerFace sl 1) (cornerFace sl 2) (cornerFace t.val 0)
          (cornerFace t.val 1) (cornerFace t.val 2) (g.co ⟨sl % 20, Nat.mod_lt _ (by decide)⟩) = x <;>
      simp only [h0, h1, h2, if_true, if_false, Option.some.injEq, reduceCtorEq] at hy <;>
      subst hy <;>
      simp [h0, h1, h2, Fin.val_inj, sudoAssert_true] <;> rfl

end MegaDreifachV3.Link2
