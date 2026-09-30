/-
  Rotation covariance of the v2 card step, part 2: the reads and the step.

  * `readColours_cov`, `readGrip_cov`: the corner and edge reads of a conjugated
    position, at the rotated faces, are the rotated colours (so the new grip is the
    rotated grip);
  * `g2Mid_cov`, `g2Step_cov`: for `s < 60` and a `GripOk` grip `o`,
    `g2Step (conj s g, rotG s o) card pos = (conj s g', rotG s o')` where
    `(g', o') = g2Step (g, o) card pos`, for every card and deal position;
  * `net2_cov`: `net2 (rotAt s) card = conj s (net2 gripId card)`;
  * `unconj`, `conj_inj`, `injPos_unconj`: inverting the conjugation.

  Kernel `decide!` on finite tables (about 41 s).  Zero sorry, no native_decide.
-/
import MegaDreifach.G2Cov

namespace MegaDreifach.G2Cov

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2

/-! ## Conjugation, slot by slot -/

theorem rhoA_rhoB_cp (s : Nat) (hs : s < 60) (q : Fin 20) : (rhoA s).cp ((rhoB s).cp q) = q :=
  congrFun (congrArg Position.cp (rhoBA s hs)) q

theorem rhoA_rhoB_ep (s : Nat) (hs : s < 60) (q : Fin 30) : (rhoA s).ep ((rhoB s).ep q) = q :=
  congrFun (congrArg Position.ep (rhoBA s hs)) q

theorem rhoA_rhoB_co (s : Nat) (hs : s < 60) (q : Fin 20) :
    ((rhoA s).co ((rhoB s).cp q)).val = (3 - ((rhoB s).co q).val) % 3 := by
  have h := congrFun (congrArg Position.co (rhoBA s hs)) q
  have hv := congrArg Fin.val h
  simp only [compose, identity, fin_val_add] at hv
  have h1 := ((rhoA s).co ((rhoB s).cp q)).isLt
  have h2 := ((rhoB s).co q).isLt
  change (_ + _) % 3 = 0 at hv
  omega

theorem rhoA_rhoB_eo (s : Nat) (hs : s < 60) (q : Fin 30) :
    ((rhoA s).eo ((rhoB s).ep q)).val = ((rhoB s).eo q).val := by
  have h := congrFun (congrArg Position.eo (rhoBA s hs)) q
  have hv := congrArg Fin.val h
  simp only [compose, identity, fin_val_add] at hv
  have h1 := ((rhoA s).eo ((rhoB s).ep q)).isLt
  have h2 := ((rhoB s).eo q).isLt
  change (_ + _) % 2 = 0 at hv
  omega

theorem conj_cp (s : Nat) (hs : s < 60) (g : Position) (q : Fin 20) :
    (conj s g).cp ((rhoB s).cp q) = (rhoB s).cp (g.cp q) := by
  show (rhoB s).cp (g.cp ((rhoA s).cp ((rhoB s).cp q))) = _
  rw [rhoA_rhoB_cp s hs]

theorem conj_co (s : Nat) (hs : s < 60) (g : Position) (q : Fin 20) :
    ((conj s g).co ((rhoB s).cp q)).val =
      (((rhoB s).co (g.cp q)).val + (g.co q).val + (3 - ((rhoB s).co q).val) % 3) % 3 := by
  show ((rhoB s).co (g.cp ((rhoA s).cp ((rhoB s).cp q))) +
      (g.co ((rhoA s).cp ((rhoB s).cp q)) + (rhoA s).co ((rhoB s).cp q))).val = _
  rw [fin_val_add, fin_val_add, rhoA_rhoB_cp s hs, rhoA_rhoB_co s hs]
  omega

theorem conj_ep (s : Nat) (hs : s < 60) (g : Position) (q : Fin 30) :
    (conj s g).ep ((rhoB s).ep q) = (rhoB s).ep (g.ep q) := by
  show (rhoB s).ep (g.ep ((rhoA s).ep ((rhoB s).ep q))) = _
  rw [rhoA_rhoB_ep s hs]

theorem conj_eo (s : Nat) (hs : s < 60) (g : Position) (q : Fin 30) :
    ((conj s g).eo ((rhoB s).ep q)).val =
      (((rhoB s).eo (g.ep q)).val + (g.eo q).val + ((rhoB s).eo q).val) % 2 := by
  show ((rhoB s).eo (g.ep ((rhoA s).ep ((rhoB s).ep q))) +
      (g.eo ((rhoA s).ep ((rhoB s).ep q)) + (rhoA s).eo ((rhoB s).ep q))).val = _
  rw [fin_val_add, fin_val_add, rhoA_rhoB_ep s hs, rhoA_rhoB_eo s hs]
  omega

/-! ## Finite read tables -/

theorem cAN_cov_table :
    allN 60 (fun s => allF 12 (fun p => allF 12 (fun x => !decide (x ∈ nbrs p) ||
      (Nat.beq (cornerAfterNoon (rotN s p) (rotN s x)).val (rotN s (cornerAfterNoon p x)).val &&
       Nat.beq (cornerSlot (rotN s p) (rotN s x) (rotN s (cornerAfterNoon p x))).val
         ((rhoB s).cp (cornerSlot p x (cornerAfterNoon p x))).val &&
       Nat.beq (edgeSlot (rotN s p) (rotN s x)).val ((rhoB s).ep (edgeSlot p x)).val)))) = true := by
  decide!

theorem cf_cov_table :
    allN 60 (fun s => allF 20 (fun q => allN 3 (fun j =>
      Nat.beq (cornerFace ((rhoB s).cp q).val ((j + (3 - ((rhoB s).co q).val) % 3) % 3)).val
        (rotN s (cornerFace q.val j)).val))) = true := by
  decide!

theorem ef_cov_table :
    allN 60 (fun s => allF 30 (fun q => allN 2 (fun j =>
      Nat.beq (edgeFace ((rhoB s).ep q).val ((j + ((rhoB s).eo q).val) % 2)).val
        (rotN s (edgeFace q.val j)).val))) = true := by
  decide!

theorem loc_cfg_table :
    (allF 20 (fun t => allN 3 (fun k =>
      Nat.beq (locOf (cornerFace t.val k) (cornerFace t.val 1) (cornerFace t.val 2)) k)) &&
    allF 30 (fun e => !Nat.beq (edgeFace e.val 0).val (edgeFace e.val 1).val) &&
    allF 12 (fun p => allF 12 (fun x => !decide (x ∈ nbrs p) ||
      (let t := (cornerSlot p x (cornerAfterNoon p x)).val
       Nat.beq (cornerFace t (locOf p (cornerFace t 1) (cornerFace t 2))).val p.val &&
       Nat.beq (cornerFace t (locOf x (cornerFace t 1) (cornerFace t 2))).val x.val &&
       (Nat.beq (edgeFace (edgeSlot p x).val 0).val p.val ||
        Nat.beq (edgeFace (edgeSlot p x).val 1).val p.val))))) = true := by
  decide!

/-! ## Unpacking the tables -/

theorem andB {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem cf_cov (s : Nat) (hs : s < 60) (q : Fin 20) (j : Nat) (hj : j < 3) :
    cornerFace ((rhoB s).cp q).val ((j + (3 - ((rhoB s).co q).val) % 3) % 3) =
      rotAt s (cornerFace q.val j) := by
  rw [rotAt_eq_rotN s hs]
  exact Fin.ext (Nat.eq_of_beq_eq_true (allN_spec (allF_spec (allN_spec cf_cov_table s hs) q) j hj))

theorem ef_cov (s : Nat) (hs : s < 60) (q : Fin 30) (j : Nat) (hj : j < 2) :
    edgeFace ((rhoB s).ep q).val ((j + ((rhoB s).eo q).val) % 2) = rotAt s (edgeFace q.val j) := by
  rw [rotAt_eq_rotN s hs]
  exact Fin.ext (Nat.eq_of_beq_eq_true (allN_spec (allF_spec (allN_spec ef_cov_table s hs) q) j hj))

theorem cfg_parts (s : Nat) (hs : s < 60) (p x : Fin 12) (hx : x ∈ nbrs p) :
    cornerAfterNoon (rotAt s p) (rotAt s x) = rotAt s (cornerAfterNoon p x) ∧
    cornerSlot (rotAt s p) (rotAt s x) (rotAt s (cornerAfterNoon p x)) =
      (rhoB s).cp (cornerSlot p x (cornerAfterNoon p x)) ∧
    edgeSlot (rotAt s p) (rotAt s x) = (rhoB s).ep (edgeSlot p x) := by
  have h := allF_spec (allF_spec (allN_spec cAN_cov_table s hs) p) x
  simp only [hx, decide_True, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  rw [rotAt_eq_rotN s hs]
  exact ⟨Fin.ext (Nat.eq_of_beq_eq_true h.1.1), Fin.ext (Nat.eq_of_beq_eq_true h.1.2),
    Fin.ext (Nat.eq_of_beq_eq_true h.2)⟩

theorem loc_self (t : Fin 20) (k : Nat) (hk : k < 3) :
    locOf (cornerFace t.val k) (cornerFace t.val 1) (cornerFace t.val 2) = k := by
  have h := loc_cfg_table
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true (allN_spec (allF_spec h.1.1 t) k hk)

theorem edge_faces_ne (e : Fin 30) : edgeFace e.val 0 ≠ edgeFace e.val 1 := by
  have h := loc_cfg_table
  simp only [Bool.and_eq_true] at h
  have := allF_spec h.1.2 e
  intro he
  rw [he, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem cfg_faces (p x : Fin 12) (hx : x ∈ nbrs p) :
    (let t := (cornerSlot p x (cornerAfterNoon p x)).val
     cornerFace t (locOf p (cornerFace t 1) (cornerFace t 2)) = p ∧
     cornerFace t (locOf x (cornerFace t 1) (cornerFace t 2)) = x) ∧
    (edgeFace (edgeSlot p x).val 0 = p ∨ edgeFace (edgeSlot p x).val 1 = p) := by
  have h2 := allF_spec (allF_spec (andB loc_cfg_table).2 p) x
  simp only [hx, decide_True, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h2
  refine ⟨⟨Fin.ext (Nat.eq_of_beq_eq_true h2.1.1), Fin.ext (Nat.eq_of_beq_eq_true h2.1.2)⟩, ?_⟩
  rcases h2.2 with h3 | h3
  · exact Or.inl (Fin.ext (Nat.eq_of_beq_eq_true h3))
  · exact Or.inr (Fin.ext (Nat.eq_of_beq_eq_true h3))

theorem locOf_lt (face f1 f2 : Fin 12) : locOf face f1 f2 < 3 := Nat.lt_succ_of_le (locOf_le _ _ _)

/-! ## The corner read -/

theorem coloursAt_eq (g : Position) (a b c : Fin 12) :
    coloursAt g a b c =
      (cornerFace (g.cp (cornerSlot a b c)).val
          ((locOf a (cornerFace (cornerSlot a b c).val 1) (cornerFace (cornerSlot a b c).val 2) + 3 -
            (g.co (cornerSlot a b c)).val) % 3),
       cornerFace (g.cp (cornerSlot a b c)).val
          ((locOf b (cornerFace (cornerSlot a b c).val 1) (cornerFace (cornerSlot a b c).val 2) + 3 -
            (g.co (cornerSlot a b c)).val) % 3)) := by
  unfold coloursAt
  dsimp only
  rw [colourOn_eq, colourOn_eq]

/-- One colour of the corner read, rotated: `a` is a face of the slot `t`. -/
theorem corner_colour_cov (s : Nat) (hs : s < 60) (g : Position) (t : Fin 20) (a : Fin 12)
    (ha : cornerFace t.val (locOf a (cornerFace t.val 1) (cornerFace t.val 2)) = a) :
    cornerFace ((conj s g).cp ((rhoB s).cp t)).val
        ((locOf (rotAt s a) (cornerFace ((rhoB s).cp t).val 1) (cornerFace ((rhoB s).cp t).val 2) + 3 -
          ((conj s g).co ((rhoB s).cp t)).val) % 3) =
      rotAt s (cornerFace (g.cp t).val
        ((locOf a (cornerFace t.val 1) (cornerFace t.val 2) + 3 - (g.co t).val) % 3)) := by
  have hL := locOf_lt a (cornerFace t.val 1) (cornerFace t.val 2)
  generalize hLd : locOf a (cornerFace t.val 1) (cornerFace t.val 2) = L at hL ha
  have hRa : rotAt s a = cornerFace ((rhoB s).cp t).val ((L + (3 - ((rhoB s).co t).val) % 3) % 3) := by
    rw [cf_cov s hs t L hL, ha]
  rw [hRa, loc_self _ _ (Nat.mod_lt _ (by decide)), conj_cp s hs, conj_co s hs,
    ← cf_cov s hs (g.cp t) _ (Nat.mod_lt _ (by decide))]
  congr 1
  have h1 := ((rhoB s).co (g.cp t)).isLt
  have h2 := (g.co t).isLt
  have h3 := ((rhoB s).co t).isLt
  omega

theorem coloursAt_cov (s : Nat) (hs : s < 60) (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p) :
    coloursAt (conj s g) (rotAt s p) (rotAt s x) (cornerAfterNoon (rotAt s p) (rotAt s x)) =
      (rotAt s (coloursAt g p x (cornerAfterNoon p x)).1,
       rotAt s (coloursAt g p x (cornerAfterNoon p x)).2) := by
  obtain ⟨h1, h2, -⟩ := cfg_parts s hs p x hx
  obtain ⟨⟨hp, hx'⟩, -⟩ := cfg_faces p x hx
  rw [coloursAt_eq, coloursAt_eq, h1, h2]
  simp only [Prod.mk.injEq]
  exact ⟨corner_colour_cov s hs g _ p hp, corner_colour_cov s hs g _ x hx'⟩

/-! ## The edge read -/

theorem edgeColoursAt_cov (s : Nat) (hs : s < 60) (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p) :
    edgeColoursAt (conj s g) (rotAt s p) (rotAt s x) =
      (rotAt s (edgeColoursAt g p x).1, rotAt s (edgeColoursAt g p x).2) := by
  obtain ⟨-, -, h3⟩ := cfg_parts s hs p x hx
  obtain ⟨-, hpe⟩ := cfg_faces p x hx
  unfold edgeColoursAt
  dsimp only
  rw [h3, conj_ep s hs]
  generalize he : edgeSlot p x = e at hpe
  have hne := edge_faces_ne ((rhoB s).ep e)
  have hne0 := edge_faces_ne e
  have hq0 := ef_cov s hs (g.ep e) 0 (by decide)
  have hq1 := ef_cov s hs (g.ep e) 1 (by decide)
  have he0 := ef_cov s hs e 0 (by decide)
  have he1 := ef_cov s hs e 1 (by decide)
  have hori := conj_eo s hs g e
  have hb := ((rhoB s).eo (g.ep e)).isLt
  have hbe := ((rhoB s).eo e).isLt
  have ho := (g.eo e).isLt
  generalize ((conj s g).eo ((rhoB s).ep e)).val = o' at hori ⊢
  generalize ((rhoB s).eo (g.ep e)).val = bq at hb hq0 hq1 hori
  generalize ((rhoB s).eo e).val = be at hbe he0 he1 hori
  generalize (g.eo e).val = o at ho hori ⊢
  -- locate `p` in the slot, before and after the rotation
  have hloc : (if rotAt s p = edgeFace ((rhoB s).ep e).val 0 then 0 else 1) =
      ((if p = edgeFace e.val 0 then 0 else 1) + be) % 2 := by
    rcases hpe with hp | hp
    · rw [if_pos hp.symm, ← hp]
      obtain rfl | rfl : be = 0 ∨ be = 1 := by omega
      · rw [show (0 + 0) % 2 = 0 from rfl] at he0; rw [← he0]; simp
      · rw [show (0 + 1) % 2 = 1 from rfl] at he0
        rw [← he0, if_neg (Ne.symm hne)]
    · have hp0 : p ≠ edgeFace e.val 0 := fun h => hne0 (h ▸ hp.symm ▸ rfl)
      rw [if_neg hp0, ← hp]
      obtain rfl | rfl : be = 0 ∨ be = 1 := by omega
      · rw [show (1 + 0) % 2 = 1 from rfl] at he1; rw [← he1, if_neg (Ne.symm hne)]
      · rw [show (1 + 1) % 2 = 0 from rfl] at he1; rw [← he1]; simp
  rw [hloc]
  generalize (if p = edgeFace e.val 0 then 0 else 1) = L
  obtain rfl | rfl : bq = 0 ∨ bq = 1 := by omega
  · rw [show (0 + 0) % 2 = 0 from rfl] at hq0
    rw [show (1 + 0) % 2 = 1 from rfl] at hq1
    rw [hq0, hq1]
    by_cases hc : (L + o) % 2 = 0
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]
  · rw [show (0 + 1) % 2 = 1 from rfl] at hq0
    rw [show (1 + 1) % 2 = 0 from rfl] at hq1
    rw [hq0, hq1]
    by_cases hc : (L + o) % 2 = 0
    · rw [if_pos hc, if_neg (by omega)]
    · rw [if_neg hc, if_pos (by omega)]

/-! ## The read and the card step -/

theorem readColours_cov (s : Nat) (hs : s < 60) (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p)
    (pos : Nat) :
    readColours (conj s g) (rotAt s p) (rotAt s x) pos =
      (rotAt s (readColours g p x pos).1, rotAt s (readColours g p x pos).2) := by
  unfold readColours
  split
  · rw [coloursAt_cov s hs g p x hx]
  · rw [edgeColoursAt_cov s hs g p x hx]

theorem readGrip_cov (s : Nat) (hs : s < 60) (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p)
    (pos : Nat) :
    readGrip (conj s g) (rotAt s p) (rotAt s x) pos = rotG s (readGrip g p x pos) := by
  rw [readGrip_eq, readGrip_eq, readColours_cov s hs g p x hx]
  exact absReorient_cov s hs _ _ (readColours_adj g p x pos hx)

theorem g2Mid_cov (s : Nat) (hs : s < 60) (g : Position) (o : Grip) (card : Nat) :
    g2Mid (conj s g, rotG s o) card =
      (conj s (g2Mid (g, o) card).1, rotG s (g2Mid (g, o) card).2.1, (g2Mid (g, o) card).2.2) := by
  unfold g2Mid
  by_cases hr : card / 4 < 12
  · simp only [dif_pos hr]
    rw [faceTurn_cov s hs]
    rfl
  · simp only [dif_neg hr]
    rw [faceTurn_cov s hs, spinAboutUp_cov s hs]
    rfl

/-- **Rotation covariance of the v2 card step.**  On a `GripOk` grip, rotating the
    whole puzzle (conjugating the position by rotation `s < 60` and relabelling the
    grip's faces) commutes with a card step, for every card and read position. -/
theorem g2Step_cov (s : Nat) (hs : s < 60) (g : Position) (o : Grip) (ho : GripOk o)
    (card pos : Nat) :
    g2Step (conj s g, rotG s o) card pos =
      (conj s (g2Step (g, o) card pos).1, rotG s (g2Step (g, o) card pos).2) := by
  rw [g2Step_eq, g2Step_eq, g2Mid_cov s hs]
  dsimp only
  have hW := gripOk_g2Mid (g, o) card ho
  generalize g2Mid (g, o) card = m at hW ⊢
  obtain ⟨gm, oW, held⟩ := m
  dsimp only at hW ⊢
  have hn := visualNoon_mem oW hW held
  rw [visualNoon_cov]
  show (faceTurn (faceTurn (conj s gm) (rotAt s (visualNoon held oW)) 1) (rotAt s (oW 1)) 1,
      readGrip (conj s gm) (rotAt s (oW held)) (rotAt s (visualNoon held oW)) pos) = _
  rw [← faceTurn_cov s hs, ← faceTurn_cov s hs, readGrip_cov s hs gm _ _ hn]

theorem rotG_gripId (s : Nat) : rotG s gripId = rotAt s := rfl

/-- The v2 nets on the 60 grips are the rotations of the 52 nets on the identity grip. -/
theorem net2_cov (s : Nat) (hs : s < 60) (card : Nat) :
    G2Nets.net2 (rotAt s) card = conj s (G2Nets.net2 gripId card) := by
  have h := g2Step_cov s hs identity gripId gripOk_id card 1
  rw [conj_identity s hs, rotG_gripId] at h
  unfold G2Nets.net2
  rw [h]

/-! ## Undoing a rotation -/

/-- The preimage of `g` under `conj s`. -/
def unconj (s : Nat) (g : Position) : Position := compose (compose (rhoB s) g) (rhoA s)

theorem conj_unconj (s : Nat) (hs : s < 60) (g : Position) : conj s (unconj s g) = g := by
  simp only [unconj, conj, compose_assoc]
  rw [← compose_assoc (rhoA s) (rhoB s), rhoAB s hs, compose_id_left, compose_id_right]

theorem unconj_conj (s : Nat) (hs : s < 60) (g : Position) : unconj s (conj s g) = g := by
  simp only [unconj, conj, compose_assoc]
  rw [← compose_assoc (rhoB s) (rhoA s), rhoBA s hs, compose_id_left, compose_id_right]

theorem conj_inj (s : Nat) (hs : s < 60) {g h : Position} (e : conj s g = conj s h) : g = h := by
  rw [← unconj_conj s hs g, e, unconj_conj s hs h]

theorem injective_comp {α β γ : Type} {f : β → γ} {g : α → β} (hf : Injective f) (hg : Injective g) :
    Injective (f ∘ g) := fun h => hg (hf h)

theorem injPos_unconj (s : Nat) (hs : s < 60) (g : Position) (hg : InjPos g) : InjPos (unconj s g) := by
  have hA : Injective (rhoA s).cp := fun {a b} h => by
    have := congrArg (rhoB s).cp h
    have e1 := congrFun (congrArg Position.cp (rhoAB s hs)) a
    have e2 := congrFun (congrArg Position.cp (rhoAB s hs)) b
    simp only [compose, identity, Function.comp] at e1 e2
    exact (e1.symm.trans (this.trans e2) : id a = id b)
  have hAe : Injective (rhoA s).ep := fun {a b} h => by
    have := congrArg (rhoB s).ep h
    have e1 := congrFun (congrArg Position.ep (rhoAB s hs)) a
    have e2 := congrFun (congrArg Position.ep (rhoAB s hs)) b
    simp only [compose, identity, Function.comp] at e1 e2
    exact (e1.symm.trans (this.trans e2) : id a = id b)
  have hB : Injective (rhoB s).cp := fun {a b} h => by
    have := congrArg (rhoA s).cp h
    rw [rhoA_rhoB_cp s hs, rhoA_rhoB_cp s hs] at this; exact this
  have hBe : Injective (rhoB s).ep := fun {a b} h => by
    have := congrArg (rhoA s).ep h
    rw [rhoA_rhoB_ep s hs, rhoA_rhoB_ep s hs] at this; exact this
  exact ⟨injective_comp hA (injective_comp hg.1 hB), injective_comp hAe (injective_comp hg.2 hBe)⟩

end MegaDreifach.G2Cov
