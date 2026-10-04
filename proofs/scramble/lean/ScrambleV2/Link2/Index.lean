/-
  LINK 2. The emitted `index_bytes` against the model's `digestOf`: whenever the model's
  digest is defined, the emitted corner loop (slot lookup, three stickers, piece id,
  W/Y orientation, base-3 pack), edge loop (two stickers, piece id, orientation bit,
  base-2 pack), `rank_perm` and `digest_bytes` return exactly those 9 bytes. On a
  reachable cube the digest is always defined (`Reach.index_bytes`). Proof-only.
-/
import ScrambleV2.Link2.Digest
import ScrambleV2.Link2.Lookup

namespace ScrambleV2.Link2
open MegaDreifach.Link2

def v0 : V3 := ⟨0, 0, 0⟩

/-- The sudo's code for a unit axis (`axisCode` read backwards). -/
def axc (a : V3) : Int := ((axisCode.find? (·.2 = a)).map (·.1)).getD 0

def csl (i : Nat) : V3 × List V3 := cornerSlots.getD i (v0, [])
def esl (i : Nat) : V3 × List V3 := edgeSlots.getD i (v0, [])

theorem corner_tables_all : ∀ i ∈ List.range 8,
    SudoRt.atL Scramble.cx (Int.ofNat i) = .ok (csl i).1.x ∧
    SudoRt.atL Scramble.cy (Int.ofNat i) = .ok (csl i).1.y ∧
    SudoRt.atL Scramble.cz (Int.ofNat i) = .ok (csl i).1.z ∧
    (csl i).2 = [(csl i).2.getD 0 v0, (csl i).2.getD 1 v0, (csl i).2.getD 2 v0] ∧
    SudoRt.atL Scramble.cax (Int.ofNat (i * 3)) = .ok (axc ((csl i).2.getD 0 v0)) ∧
    SudoRt.atL Scramble.cax (Int.ofNat (i * 3 + 1)) = .ok (axc ((csl i).2.getD 1 v0)) ∧
    SudoRt.atL Scramble.cax (Int.ofNat (i * 3 + 2)) = .ok (axc ((csl i).2.getD 2 v0)) ∧
    (axc ((csl i).2.getD 0 v0), (csl i).2.getD 0 v0) ∈ axisCode ∧
    (axc ((csl i).2.getD 1 v0), (csl i).2.getD 1 v0) ∈ axisCode ∧
    (axc ((csl i).2.getD 2 v0), (csl i).2.getD 2 v0) ∈ axisCode := by decide

theorem edge_tables_all : ∀ i ∈ List.range 12,
    SudoRt.atL Scramble.ex (Int.ofNat i) = .ok (esl i).1.x ∧
    SudoRt.atL Scramble.ey (Int.ofNat i) = .ok (esl i).1.y ∧
    SudoRt.atL Scramble.ez (Int.ofNat i) = .ok (esl i).1.z ∧
    (esl i).2 = [(esl i).2.getD 0 v0, (esl i).2.getD 1 v0] ∧
    SudoRt.atL Scramble.eax (Int.ofNat (i * 2)) = .ok (axc ((esl i).2.getD 0 v0)) ∧
    SudoRt.atL Scramble.eax (Int.ofNat (i * 2 + 1)) = .ok (axc ((esl i).2.getD 1 v0)) ∧
    (axc ((esl i).2.getD 0 v0), (esl i).2.getD 0 v0) ∈ axisCode ∧
    (axc ((esl i).2.getD 1 v0), (esl i).2.getD 1 v0) ∈ axisCode := by decide

/-- On a corner piece, the first W/Y sticker (model) is where the emitted if-chain
    puts it: the piece has exactly one. -/
def cornerOriOK (u v w : Color) : Bool :=
  match pieceId cornerTable [u, v, w] with
  | some _ => decide (cornerOri [u, v, w] = some (if isUD w then 2 else if isUD v then 1 else 0))
  | none => true

theorem cornerOriOK_all : ∀ u ∈ allColors, ∀ v ∈ allColors, ∀ w ∈ allColors,
    cornerOriOK u v w = true := by decide

theorem cornerOri_piece (u v w : Color) (n : Nat) (h : pieceId cornerTable [u, v, w] = some n) :
    cornerOri [u, v, w] = some (if isUD w then 2 else if isUD v then 1 else 0) := by
  have hk := cornerOriOK_all u (mem_allColors u) v (mem_allColors v) w (mem_allColors w)
  unfold cornerOriOK at hk
  rw [h] at hk
  exact of_decide_eq_true hk


theorem mapM_getElem {α β} (f : α → Option β) : ∀ (l : List α) (ys : List β),
    l.mapM f = some ys → ys.length = l.length ∧
      ∀ i (h1 : i < l.length) (h2 : i < ys.length), f l[i] = some ys[i]
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun i h1 => absurd h1 (by simp)⟩
  | x :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some zs =>
        simp only [hx, hl, Option.bind_eq_bind, Option.some_bind, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hget⟩ := mapM_getElem f l zs hl
        refine ⟨by simp [hlen], fun i h1 h2 => ?_⟩
        cases i with
        | zero => simpa using hx
        | succ i => simpa using hget i (by simpa using h1) (by simpa using h2)

theorem packLE_append (b : Nat) : ∀ (l : List Nat) (d : Nat),
    packLE b (l ++ [d]) = packLE b l + d * b ^ l.length
  | [], d => by simp [packLE]
  | x :: l, d => by
    show packLE b (x :: (l ++ [d])) = _
    rw [packLE, packLE, packLE_append b l d, List.length_cons, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem packLE_lt (b : Nat) : ∀ (l : List Nat), (∀ d ∈ l, d < b) → packLE b l < b ^ l.length
  | [], _ => by simp [packLE]
  | x :: l, h => by
    have hx := h x (List.mem_cons_self _ _)
    have ih := packLE_lt b l (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [packLE, List.length_cons, Nat.pow_succ]
    have : b * packLE b l + b ≤ b * b ^ l.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (b ^ l.length) b]; omega

theorem take_succ_of_lt {α} (l : List α) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]; rfl

/-- A slot read that succeeds: the emitted `cubie_at` finds the model's cubie. -/
theorem slot_read (cube : Cube) (hfit : FitsLen cube.length) (sl : V3 × List V3)
    (cols : List Color) (hr : readSlot cube sl = some cols) :
    ∃ j, ∃ hj : j < cube.length,
      Scramble.cubie_at (embedCube cube) sl.1.x sl.1.y sl.1.z = .ok (Int.ofNat j) ∧
      sl.2.mapM (colorFacing cube[j]) = some cols := by
  unfold readSlot at hr
  cases hc : cubieAt cube sl.1 with
  | none => simp [hc] at hr
  | some c =>
    simp only [hc, Option.bind_eq_bind, Option.some_bind] at hr
    obtain ⟨j, hj, hjc, hfirst⟩ := find?_index _ _ _ hc
    refine ⟨j, hj, cubie_at_refines cube sl.1 j hj ?_ ?_ hfit, by rw [hjc]; exact hr⟩
    · have := List.find?_some hc; rw [← hjc] at this; simpa using this
    · intro i hi; have := hfirst i hi; simpa using this

theorem slot_of_facing (c : Cubie) (a : V3) (col : Color) (h : colorFacing c a = some col) :
    slot c a = col.code := by unfold slot; rw [h]


theorem mapM2 {α β} (f : α → Option β) (a b : α) (ys : List β) (h : [a, b].mapM f = some ys) :
    ∃ u v, f a = some u ∧ f b = some v ∧ ys = [u, v] := by
  cases ha : f a <;> cases hb : f b <;> simp_all [List.mapM_cons]

theorem mapM3 {α β} (f : α → Option β) (a b c : α) (ys : List β) (h : [a, b, c].mapM f = some ys) :
    ∃ u v w, f a = some u ∧ f b = some v ∧ f c = some w ∧ ys = [u, v, w] := by
  cases ha : f a <;> cases hb : f b <;> cases hc : f c <;> simp_all [List.mapM_cons]

theorem corner_slot (cube : Cube) (hfit : FitsLen cube.length) (i : Nat) (hi : i < 8)
    (cols : List Color) (hr : readSlot cube (csl i) = some cols) :
    ∃ j, ∃ hj : j < cube.length, ∃ u v w, cols = [u, v, w] ∧
      Scramble.cubie_at (embedCube cube) (csl i).1.x (csl i).1.y (csl i).1.z = .ok (Int.ofNat j) ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((csl i).2.getD 0 v0)) = .ok u.code ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((csl i).2.getD 1 v0)) = .ok v.code ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((csl i).2.getD 2 v0)) = .ok w.code := by
  obtain ⟨j, hj, hcub, hm⟩ := slot_read cube hfit _ cols hr
  obtain ⟨_, _, _, hl, _, _, _, m0, m1, m2⟩ := corner_tables_all i (List.mem_range.mpr hi)
  rw [hl] at hm
  obtain ⟨u, v, w, hu, hv, hw, rfl⟩ := mapM3 _ _ _ _ _ hm
  refine ⟨j, hj, u, v, w, rfl, hcub, ?_, ?_, ?_⟩
  · rw [sticker_on_refines _ _ m0, slot_of_facing _ _ _ hu]
  · rw [sticker_on_refines _ _ m1, slot_of_facing _ _ _ hv]
  · rw [sticker_on_refines _ _ m2, slot_of_facing _ _ _ hw]

theorem edge_slot (cube : Cube) (hfit : FitsLen cube.length) (i : Nat) (hi : i < 12)
    (cols : List Color) (hr : readSlot cube (esl i) = some cols) :
    ∃ j, ∃ hj : j < cube.length, ∃ u v, cols = [u, v] ∧
      Scramble.cubie_at (embedCube cube) (esl i).1.x (esl i).1.y (esl i).1.z = .ok (Int.ofNat j) ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((esl i).2.getD 0 v0)) = .ok u.code ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((esl i).2.getD 1 v0)) = .ok v.code := by
  obtain ⟨j, hj, hcub, hm⟩ := slot_read cube hfit _ cols hr
  obtain ⟨_, _, _, hl, _, _, m0, m1⟩ := edge_tables_all i (List.mem_range.mpr hi)
  rw [hl] at hm
  obtain ⟨u, v, hu, hv, rfl⟩ := mapM2 _ _ _ _ hm
  refine ⟨j, hj, u, v, rfl, hcub, ?_, ?_⟩
  · rw [sticker_on_refines _ _ m0, slot_of_facing _ _ _ hu]
  · rw [sticker_on_refines _ _ m1, slot_of_facing _ _ _ hv]


theorem mulI_3 (n : Nat) (h : FitsLen (n * 3)) : SudoRt.mulI (Int.ofNat n) (3 : Int) = .ok (Int.ofNat (n * 3)) :=
  mulI_ofNat n 3 h
theorem addI_2 (n : Nat) (h : FitsLen (n + 2)) : SudoRt.addI (Int.ofNat n) (2 : Int) = .ok (Int.ofNat (n + 2)) :=
  addI_ofNat n 2 h
theorem mulI_l0 (p : Nat) : SudoRt.mulI (0 : Int) (Int.ofNat p) = .ok (Int.ofNat (0 * p)) :=
  mulI_ofNat 0 p (by simp [FitsLen])
theorem mulI_l1 (p : Nat) (h : FitsLen (1 * p)) : SudoRt.mulI (1 : Int) (Int.ofNat p) = .ok (Int.ofNat (1 * p)) :=
  mulI_ofNat 1 p h
theorem mulI_l2 (p : Nat) (h : FitsLen (2 * p)) : SudoRt.mulI (2 : Int) (Int.ofNat p) = .ok (Int.ofNat (2 * p)) :=
  mulI_ofNat 2 p h

theorem csl_eq (i : Nat) (h : i < cornerSlots.length) : csl i = cornerSlots[i] := by
  simp [csl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem esl_eq (i : Nat) (h : i < edgeSlots.length) : esl i = edgeSlots[i] := by
  simp [esl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The corner-loop body at slot `i`. -/
theorem corner_body (cube : Cube) (hfit : FitsLen cube.length) (cs : List (List Color))
    (hcs : cornerSlots.mapM (readSlot cube) = some cs) (cp : List Nat)
    (hcp : cs.mapM (pieceId cornerTable) = some cp) (co : List Nat)
    (hco : (cs.take 7).mapM cornerOri = some co) (hdig : ∀ d ∈ co, d < 3) (i : Nat) (hi : i ≤ 7) :
    (do
      let _t1156 ← SudoRt.atL Scramble.cx (Int.ofNat i)
      let _t1157 ← SudoRt.atL Scramble.cy (Int.ofNat i)
      let _t1158 ← SudoRt.atL Scramble.cz (Int.ofNat i)
      let _t1159 ← Scramble.cubie_at (embedCube cube) _t1156 _t1157 _t1158
      let _t1160 ← SudoRt.atL (embedCube cube) _t1159
      let _t1161 ← SudoRt.mulI (Int.ofNat i) 3
      let _t1162 ← SudoRt.atL Scramble.cax _t1161
      let _t1163 ← Scramble.sticker_on _t1160 _t1162
      let _t1164 ← SudoRt.mulI (Int.ofNat i) 3
      let _t1165 ← SudoRt.addI _t1164 1
      let _t1166 ← SudoRt.atL Scramble.cax _t1165
      let _t1167 ← Scramble.sticker_on _t1160 _t1166
      let _t1168 ← SudoRt.mulI (Int.ofNat i) 3
      let _t1169 ← SudoRt.addI _t1168 2
      let _t1170 ← SudoRt.atL Scramble.cax _t1169
      let _t1171 ← Scramble.sticker_on _t1160 _t1170
      let _t1172 ← Scramble.corner_piece _t1163 _t1167 _t1171
      let _t1176 ← Scramble.is_ud _t1167
      if _t1176 = true then do
          let _t1177 ← Scramble.is_ud _t1171
          if _t1177 = true then
              if decide (Int.ofNat i < 7) = true then do
                let _t1179 ← SudoRt.mulI 2 (Int.ofNat (3 ^ min i 7))
                let _t1180 ← SudoRt.addI (Int.ofNat (packLE 3 (co.take i))) _t1179
                let _t1181 ← SudoRt.mulI (Int.ofNat (3 ^ min i 7)) 3
                pure (SudoRt.Flow.cont (ρ := Array Int) ((SudoRt.appendL (embed (cp.take i)) _t1172).fst, _t1180, _t1181))
              else pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst,
                Int.ofNat (packLE 3 (co.take i)), Int.ofNat (3 ^ min i 7)))
            else
              if decide (Int.ofNat i < 7) = true then do
                let _t1179 ← SudoRt.mulI 1 (Int.ofNat (3 ^ min i 7))
                let _t1180 ← SudoRt.addI (Int.ofNat (packLE 3 (co.take i))) _t1179
                let _t1181 ← SudoRt.mulI (Int.ofNat (3 ^ min i 7)) 3
                pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst, _t1180, _t1181))
              else pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst,
                Int.ofNat (packLE 3 (co.take i)), Int.ofNat (3 ^ min i 7)))
        else do
          let _t1186 ← Scramble.is_ud _t1171
          if _t1186 = true then
              if decide (Int.ofNat i < 7) = true then do
                let _t1179 ← SudoRt.mulI 2 (Int.ofNat (3 ^ min i 7))
                let _t1180 ← SudoRt.addI (Int.ofNat (packLE 3 (co.take i))) _t1179
                let _t1181 ← SudoRt.mulI (Int.ofNat (3 ^ min i 7)) 3
                pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst, _t1180, _t1181))
              else pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst,
                Int.ofNat (packLE 3 (co.take i)), Int.ofNat (3 ^ min i 7)))
            else
              if decide (Int.ofNat i < 7) = true then do
                let _t1179 ← SudoRt.mulI 0 (Int.ofNat (3 ^ min i 7))
                let _t1180 ← SudoRt.addI (Int.ofNat (packLE 3 (co.take i))) _t1179
                let _t1181 ← SudoRt.mulI (Int.ofNat (3 ^ min i 7)) 3
                pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst, _t1180, _t1181))
              else pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (cp.take i)) _t1172).fst,
                Int.ofNat (packLE 3 (co.take i)), Int.ofNat (3 ^ min i 7)))) =
    .ok (SudoRt.Flow.cont (embed (cp.take (i + 1)), Int.ofNat (packLE 3 (co.take (i + 1))),
      Int.ofNat (3 ^ min (i + 1) 7))) := by
  have hi8 : i < 8 := by omega
  obtain ⟨hlcs, gcs⟩ := mapM_getElem _ _ _ hcs
  obtain ⟨hlcp, gcp⟩ := mapM_getElem _ _ _ hcp
  obtain ⟨hlco, gco⟩ := mapM_getElem _ _ _ hco
  have hl8 : cornerSlots.length = 8 := rfl
  have hics : i < cs.length := by omega
  have hlt7 : (cs.take 7).length = 7 := by simp; omega
  have hr : readSlot cube (csl i) = some cs[i] := by
    rw [csl_eq i (by omega)]; exact gcs i (by omega) hics
  obtain ⟨hx, hy, hz, _, a0, a1, a2, _, _, _⟩ := corner_tables_all i (List.mem_range.mpr hi8)
  obtain ⟨j, hj, u, v, w, hcols, hcub, s0, s1, s2⟩ := corner_slot cube hfit i hi8 _ hr
  have hn : pieceId cornerTable [u, v, w] = some cp[i] := by
    rw [← hcols]; exact gcp i hics (by omega)
  have hori := cornerOri_piece u v w _ hn
  simp only [hx, hy, hz, ok_bind, hcub, atL_embedCube cube j hj, mulI_3 i (fits_small (by omega)),
    a0, s0, addI_ofNat_one (i * 3) (fits_small (by omega)), a1, s1,
    addI_2 (i * 3) (fits_small (by omega)), a2, s2, corner_piece_refines u v w _ hn, is_ud_refines,
    appendL_spec, push_embed', ← take_succ_of_lt cp i (by omega)]
  by_cases h7 : i < 7
  · have hco7 : co[i]'(by omega) = if isUD w then 2 else if isUD v then 1 else 0 := by
      have := gco i (by simp; omega) (by omega)
      simp only [List.getElem_take, hcols, hori, Option.some.injEq] at this
      exact this.symm
    have hmin : min i 7 = i := by omega
    have hmin' : min (i + 1) 7 = i + 1 := by omega
    have hdec : decide (Int.ofNat i < 7) = true := by
      simp only [decide_eq_true_eq]; exact (ofNat_lt_iff i 7).mpr h7
    have hp : 3 ^ i ≤ 729 := by
      have := Nat.pow_le_pow_right (show 0 < 3 by decide) (show i ≤ 6 by omega); simpa using this
    have hlen : (co.take i).length = i := by simp; omega
    have hpk : packLE 3 (co.take i) < 3 ^ i := by
      have := packLE_lt 3 (co.take i) (fun d hd => hdig d (List.mem_of_mem_take hd))
      rwa [hlen] at this
    rw [hmin, hmin', take_succ_of_lt co i (by omega), packLE_append]
    simp only [hlen, hco7, hdec]
    have hpk3 := hpk
    cases isUD v <;> cases isUD w <;>
      simp only [if_true, if_false, Bool.false_eq_true, mulI_l0, mulI_l1 (3 ^ i) (fits_small (by omega)),
        mulI_l2 (3 ^ i) (fits_small (by omega)), ok_bind, pure_eq_ok,
        addI_ofNat (packLE 3 (co.take i)) (0 * 3 ^ i) (fits_small (by omega)),
        addI_ofNat (packLE 3 (co.take i)) (1 * 3 ^ i) (fits_small (by omega)),
        addI_ofNat (packLE 3 (co.take i)) (2 * 3 ^ i) (fits_small (by omega)),
        mulI_3 (3 ^ i) (fits_small (by omega)), Nat.pow_succ]
  · obtain rfl : i = 7 := by omega
    have hdec : decide (Int.ofNat 7 < 7) = false := by decide
    rw [List.take_of_length_le (show co.length ≤ 7 + 1 by omega),
      List.take_of_length_le (show co.length ≤ 7 by omega)]
    simp only [hdec, Bool.false_eq_true, if_false, ite_self, pure_eq_ok]
    rfl


theorem edgeBit_le (c : Color) : edgeBit c ≤ 1 := by unfold edgeBit; split <;> omega

theorem firstBit_le (l : List Color) : firstBit l ≤ 1 := by
  cases l with
  | nil => simp [firstBit]
  | cons c _ => exact edgeBit_le c

/-- The edge-loop body at slot `i`. -/
theorem edge_body (cube : Cube) (hfit : FitsLen cube.length) (es : List (List Color))
    (hes : edgeSlots.mapM (readSlot cube) = some es) (ep : List Nat)
    (hep : es.mapM (pieceId edgeTable) = some ep) (i : Nat) (hi : i ≤ 11) :
    (do
      let _t1199 ← SudoRt.atL Scramble.ex (Int.ofNat i)
      let _t1200 ← SudoRt.atL Scramble.ey (Int.ofNat i)
      let _t1201 ← SudoRt.atL Scramble.ez (Int.ofNat i)
      let _t1202 ← Scramble.cubie_at (embedCube cube) _t1199 _t1200 _t1201
      let _t1203 ← SudoRt.atL (embedCube cube) _t1202
      let _t1204 ← SudoRt.mulI (Int.ofNat i) 2
      let _t1205 ← SudoRt.atL Scramble.eax _t1204
      let _t1206 ← Scramble.sticker_on _t1203 _t1205
      let _t1207 ← SudoRt.mulI (Int.ofNat i) 2
      let _t1208 ← SudoRt.addI _t1207 1
      let _t1209 ← SudoRt.atL Scramble.eax _t1208
      let _t1210 ← Scramble.sticker_on _t1203 _t1209
      let _t1211 ← Scramble.edge_piece _t1206 _t1210
      if decide (Int.ofNat i < 11) = true then do
          let _t1216 ← Scramble.edge_bit _t1206
          let _t1217 ← SudoRt.mulI _t1216 (Int.ofNat (2 ^ min i 11))
          let _t1218 ← SudoRt.addI (Int.ofNat (packLE 2 (((es.take 11).map firstBit).take i))) _t1217
          let _t1219 ← SudoRt.mulI (Int.ofNat (2 ^ min i 11)) 2
          pure (SudoRt.Flow.cont (ρ := Array Int) ((SudoRt.appendL (embed (ep.take i)) _t1211).fst, _t1218, _t1219))
        else pure (SudoRt.Flow.cont ((SudoRt.appendL (embed (ep.take i)) _t1211).fst,
          Int.ofNat (packLE 2 (((es.take 11).map firstBit).take i)), Int.ofNat (2 ^ min i 11)))) =
    .ok (SudoRt.Flow.cont (embed (ep.take (i + 1)),
      Int.ofNat (packLE 2 (((es.take 11).map firstBit).take (i + 1))),
      Int.ofNat (2 ^ min (i + 1) 11))) := by
  have hi12 : i < 12 := by omega
  obtain ⟨hles, ges⟩ := mapM_getElem _ _ _ hes
  obtain ⟨hlep, gep⟩ := mapM_getElem _ _ _ hep
  have hl12 : edgeSlots.length = 12 := rfl
  have hies : i < es.length := by omega
  have hr : readSlot cube (esl i) = some es[i] := by
    rw [esl_eq i (by omega)]; exact ges i (by omega) hies
  obtain ⟨hx, hy, hz, _, a0, a1, _, _⟩ := edge_tables_all i (List.mem_range.mpr hi12)
  obtain ⟨j, hj, u, v, hcols, hcub, s0, s1⟩ := edge_slot cube hfit i hi12 _ hr
  have hn : pieceId edgeTable [u, v] = some ep[i] := by
    rw [← hcols]; exact gep i hies (by omega)
  simp only [hx, hy, hz, ok_bind, hcub, atL_embedCube cube j hj, mulI_2 i (fits_small (by omega)),
    a0, s0, addI_ofNat_one (i * 2) (fits_small (by omega)), a1, s1,
    edge_piece_refines u v _ hn, appendL_spec, push_embed', ← take_succ_of_lt ep i (by omega)]
  have hleo : ((es.take 11).map firstBit).length = 11 := by simp; omega
  by_cases h11 : i < 11
  · have heo : ((es.take 11).map firstBit)[i]'(by omega) = edgeBit u := by
      simp [List.getElem_map, List.getElem_take, hcols, firstBit]
    have hmin : min i 11 = i := by omega
    have hmin' : min (i + 1) 11 = i + 1 := by omega
    have hdec : decide (Int.ofNat i < 11) = true := by
      simp only [decide_eq_true_eq]; exact (ofNat_lt_iff i 11).mpr h11
    have hp : 2 ^ i ≤ 1024 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show i ≤ 10 by omega); simpa using this
    have hlen : (((es.take 11).map firstBit).take i).length = i := by simp; omega
    have hpk : packLE 2 (((es.take 11).map firstBit).take i) < 2 ^ i := by
      have := packLE_lt 2 (((es.take 11).map firstBit).take i) (fun d hd => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hd)
        have := firstBit_le l; omega)
      rwa [hlen] at this
    have hb := edgeBit_le u
    rw [hmin, hmin', take_succ_of_lt ((es.take 11).map firstBit) i (by omega), packLE_append]
    simp only [hlen, heo, hdec, if_true, edge_bit_refines, ok_bind, pure_eq_ok,
      mulI_ofNat (edgeBit u) (2 ^ i) (fits_small (by
        have := Nat.mul_le_mul_right (2 ^ i) hb; omega)),
      addI_ofNat (packLE 2 (((es.take 11).map firstBit).take i)) (edgeBit u * 2 ^ i) (fits_small (by
        have := Nat.mul_le_mul_right (2 ^ i) hb; omega)),
      mulI_2 (2 ^ i) (fits_small (by omega)), Nat.pow_succ]
  · obtain rfl : i = 11 := by omega
    have hdec : decide (Int.ofNat 11 < 11) = false := by decide
    rw [List.take_of_length_le (show ((es.take 11).map firstBit).length ≤ 11 + 1 by omega),
      List.take_of_length_le (show ((es.take 11).map firstBit).length ≤ 11 by omega)]
    simp only [hdec, Bool.false_eq_true, if_false, pure_eq_ok]
    rfl


theorem mulI_2187 (n : Nat) (h : FitsLen (n * 2187)) :
    SudoRt.mulI (Int.ofNat n) (2187 : Int) = .ok (Int.ofNat (n * 2187)) := mulI_ofNat n 2187 h
theorem mulI_239500800 (n : Nat) (h : FitsLen (n * 239500800)) :
    SudoRt.mulI (Int.ofNat n) (239500800 : Int) = .ok (Int.ofNat (n * 239500800)) :=
  mulI_ofNat n 239500800 h
theorem divI_2 (n : Nat) : SudoRt.divI (Int.ofNat n) (2 : Int) = .ok (Int.ofNat (n / 2)) :=
  divI_ofNat n (by decide)

theorem fits_i64 {n : Nat} (h : n < 2 ^ 62) : FitsLen n := by
  unfold FitsLen i64MaxNat
  have : (2 : Nat) ^ 62 = 4611686018427387904 := by decide
  omega

/-- LINK 2. `index_bytes` on the embedded cube is the model's digest, whenever the model's
    digest is defined (the slot reads, piece ids and orientations succeed). -/
theorem index_bytes_refines (cube : Cube) (hfit : FitsLen cube.length) (d : List Nat)
    (hd : digestOf cube = some d) : Scramble.index_bytes (embedCube cube) = .ok (embed d) := by
  unfold digestOf at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def, Option.some.injEq] at hd
  obtain ⟨cs, hcs, cp, hcp, co, hco, es, hes, ep, hep, rfl⟩ := hd
  obtain ⟨hlcs, gcs⟩ := mapM_getElem _ _ _ hcs
  obtain ⟨hlcp, gcp⟩ := mapM_getElem _ _ _ hcp
  obtain ⟨hlco, gco⟩ := mapM_getElem _ _ _ hco
  obtain ⟨hles, _⟩ := mapM_getElem _ _ _ hes
  obtain ⟨hlep, _⟩ := mapM_getElem _ _ _ hep
  have hl8 : cornerSlots.length = 8 := rfl
  have hl12 : edgeSlots.length = 12 := rfl
  have hlt7 : (cs.take 7).length = 7 := by simp; omega
  have hdig : ∀ x ∈ co, x < 3 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have htc : t < cs.length := by omega
    have hr : readSlot cube (csl t) = some cs[t] := by
      rw [csl_eq t (by omega)]; exact gcs t (by omega) htc
    obtain ⟨_, _, u, v, w, hcols, _⟩ := corner_slot cube hfit t (by omega) _ hr
    have hn : pieceId cornerTable [u, v, w] = some cp[t] := by
      rw [← hcols]; exact gcp t htc (by omega)
    have := gco t (by omega) ht
    simp only [List.getElem_take, hcols, cornerOri_piece u v w _ hn, Option.some.injEq] at this
    rw [← this]; split
    · omega
    · split <;> omega
  have hco_lt : packLE 3 co < 2187 := by
    have := packLE_lt 3 co hdig; rw [hlco, hlt7] at this; simpa using this
  have heo_lt : packLE 2 ((es.take 11).map firstBit) < 2048 := by
    have := packLE_lt 2 ((es.take 11).map firstBit) (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx; have := firstBit_le l; omega)
    have hlen : ((es.take 11).map firstBit).length = 11 := by simp; omega
    rw [hlen] at this; simpa using this
  have hcp_lt : rank cp < 40320 := by
    have := rank_lt_fact cp; rw [hlcp, hlcs, hl8] at this; simpa [fact] using this
  have hep_lt : rank ep < 479001600 := by
    have := rank_lt_fact ep; rw [hlep, hles, hl12] at this; simpa [fact] using this
  unfold Scramble.index_bytes
  simp only [fuelRange_eq, bind_pure_right]
  refine chain_eq _ _ _ (fun i => (embed (cp.take i), Int.ofNat (packLE 3 (co.take i)),
    Int.ofNat (3 ^ min i 7))) 0 7 (by omega) ?c1 _ ?c2 _ rfl
  case c1 =>
    intro i _ hi
    dsimp only
    rw [if_neg (show ¬ (Int.ofNat i > (7 : Int)) from ofNat_not_gt hi),
      bind_ok_of (corner_body cube hfit cs hcs cp hcp co hco hdig i hi)]
    dsimp only
    simp only [pure_eq_ok]
    rw [show (7 : Int) = Int.ofNat 7 from rfl, asc_tail 7 i (fits_small (by omega))]
  case c2 =>
    dsimp only
    rw [List.take_of_length_le (show cp.length ≤ 7 + 1 by omega),
      List.take_of_length_le (show co.length ≤ 7 + 1 by omega),
      rank_perm_refines cp (by omega), ok_bind, mulI_2187 _ (fits_i64 (by omega)), ok_bind,
      addI_ofNat _ _ (fits_i64 (by omega)), ok_bind]
    refine chain_eq _ _ _ (fun i => (embed (ep.take i),
      Int.ofNat (packLE 2 (((es.take 11).map firstBit).take i)), Int.ofNat (2 ^ min i 11)))
      0 11 (by omega) ?e1 _ ?e2 _ rfl
    case e1 =>
      intro i _ hi
      dsimp only
      rw [if_neg (show ¬ (Int.ofNat i > (11 : Int)) from ofNat_not_gt hi),
        bind_ok_of (edge_body cube hfit es hes ep hep i hi)]
      dsimp only
      simp only [pure_eq_ok]
      rw [show (11 : Int) = Int.ofNat 11 from rfl, asc_tail 11 i (fits_small (by omega))]
    case e2 =>
      dsimp only
      have hs3 : (rank cp * 2187 + packLE 3 co) * 239500800 + rank ep / 2 < 2 ^ 61 := by
        have : (2 : Nat) ^ 61 = 2305843009213693952 := by decide
        omega
      rw [List.take_of_length_le (show ep.length ≤ 11 + 1 by omega),
        List.take_of_length_le (show ((es.take 11).map firstBit).length ≤ 11 + 1 by simp; omega),
        mulI_239500800 _ (fits_i64 (by omega)), ok_bind, rank_perm_refines ep (by omega), ok_bind,
        divI_2, ok_bind, addI_ofNat _ _ (fits_i64 (by omega)), ok_bind,
        digest_bytes_refines _ _ hs3 heo_lt]


theorem Reach.length (cube : Cube) (h : Reach cube) : cube.length = 26 := by
  obtain ⟨_, _, _, hperm⟩ := h
  have := hperm.length_eq
  simpa using this

theorem Reach.fits (cube : Cube) (h : Reach cube) : FitsLen cube.length := by
  rw [Reach.length cube h]; exact fits_small (by decide)

/-- On every reachable cube, `index_bytes` returns the model's (defined) digest. -/
theorem Reach.index_bytes (cube : Cube) (h : Reach cube) :
    ∃ d, ScrambleV2.digestOf cube = some d ∧ Scramble.index_bytes (embedCube cube) = .ok (embed d) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (ScrambleV2.Link2.Reach.digestOf cube h)
  exact ⟨d, hd, index_bytes_refines cube (Reach.fits cube h) d hd⟩

end ScrambleV2.Link2
