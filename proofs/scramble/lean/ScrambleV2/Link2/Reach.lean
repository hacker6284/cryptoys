/-
  LINK 2. The invariant `Reach` of every cube the v2 walk visits, on the model alone.

  * Each cubie is a rotation (`rots`) of the solved cubie that started in its list
    slot: `cube[i] = moveCubie g.app (solvedCubie lattice[i])`.
  * The positions are a permutation of the 26 lattice points.
  * One frame `F ∈ rots` places every face center: the center that started at axis `a`
    sits at `F.app a`.

  It holds for the solved cube and survives a quarter turn and any whole-cube rotation
  from `rots`; Rule B and the seat only ever build a matrix in `rots`. From it: every
  `cubieAt` / `centerOf` / `colorFacing` the model asks for is `some`, and every slot
  the digest reads holds a real piece, so `digestV2?` never answers `none`
  (`digestV2_isSome`). The finite facts are checked by `decide` over `rots` (24),
  `lattice` (26), the axes and the colors. Proof-only.
-/
import ScrambleV2.Link2.Rots
import ScrambleV2.Link2.Turn

namespace ScrambleV2.Link2

/-! ## Pairwise lists -/

/-- `R` holds between the two lists, position by position. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b l1 l2} : R a b → All2 R l1 l2 → All2 R (a :: l1) (b :: l2)

theorem All2.imp {α β} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l1 l2}, All2 R l1 l2 → All2 S l1 l2
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons (h _ _ hab) (All2.imp h t)

theorem All2.map_left {α β} {R S : α → β → Prop} (f : α → α) (h : ∀ a b, R a b → S (f a) b) :
    ∀ {l1 l2}, All2 R l1 l2 → All2 S (l1.map f) l2
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons (h _ _ hab) (All2.map_left f h t)

theorem All2.of_map {α β} {R : α → β → Prop} (f : β → α) (h : ∀ b, R (f b) b) :
    ∀ l : List β, All2 R (l.map f) l
  | [] => .nil
  | b :: l => .cons (h b) (All2.of_map f h l)

theorem All2.mem_left {α β} {R : α → β → Prop} :
    ∀ {l1 l2}, All2 R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self _ _, hab⟩
    · obtain ⟨b, hb, r⟩ := All2.mem_left t a h
      exact ⟨b, List.mem_cons_of_mem _ hb, r⟩

theorem All2.with_mem {α β} {R : α → β → Prop} (L : List β) :
    ∀ {l1 l2}, (∀ b ∈ l2, b ∈ L) → All2 R l1 l2 → All2 (fun a b => R a b ∧ b ∈ L) l1 l2
  | _, _, _, .nil => .nil
  | _, _, hL, .cons hab t =>
    .cons ⟨hab, hL _ (List.mem_cons_self _ _)⟩
      (All2.with_mem L (fun b hb => hL b (List.mem_cons_of_mem _ hb)) t)

/-- A `find?` on the left list tracks a `find?` on the right one when the two
    predicates agree on related entries. -/
theorem All2.find {α β} {R : α → β → Prop} (P : α → Bool) (Q : β → Bool)
    (hPQ : ∀ a b, R a b → P a = Q b) :
    ∀ {l1 l2}, All2 R l1 l2 → ∀ b, l2.find? Q = some b → ∃ a, l1.find? P = some a ∧ R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons (a := a) (b := b0) hab t, b, h => by
    by_cases hq : Q b0 = true
    · rw [List.find?_cons_of_pos _ hq] at h
      cases h
      exact ⟨a, by rw [List.find?_cons_of_pos _ (by rw [hPQ _ _ hab]; exact hq)], hab⟩
    · rw [List.find?_cons_of_neg _ hq] at h
      obtain ⟨a', h1, h2⟩ := All2.find P Q hPQ t b h
      refine ⟨a', ?_, h2⟩
      rw [List.find?_cons_of_neg _ (by rw [hPQ _ _ hab]; exact hq)]
      exact h1

/-! ## Model algebra -/

theorem moveCubie_comp (g h : V3 → V3) (c : Cubie) :
    moveCubie g (moveCubie h c) = moveCubie (fun v => g (h v)) c := by
  simp [moveCubie, List.map_map, Function.comp_def]

theorem moveCubie_mul (a b : Mat) (c : Cubie) :
    moveCubie a.app (moveCubie b.app c) = moveCubie (a.mul b).app c := by
  rw [moveCubie_comp]
  congr 1
  funext v
  rw [Mat.app_mul]

theorem moveCubie_id (c : Cubie) :
    moveCubie (Mat.app ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩) c = c := by
  obtain ⟨p, st⟩ := c
  simp only [moveCubie, Mat.app_id]
  congr 1
  conv => rhs; rw [← List.map_id st]
  rfl

theorem colorFacing_rot (g : Mat) (hg : g ∈ rots) (c : Cubie) (a : V3) :
    colorFacing (moveCubie g.app c) a = colorFacing c (g.transpose.app a) := by
  conv => lhs; rw [← rots_app_transpose g hg a]
  exact colorFacing_move g.app (rots_inj g hg) c _

/-- The matrix of each face map. -/
def faceMat : Face → Mat
  | .U => ⟨⟨0, 0, 1⟩, ⟨0, 1, 0⟩, ⟨-1, 0, 0⟩⟩
  | .D => ⟨⟨0, 0, 1⟩, ⟨0, 1, 0⟩, ⟨-1, 0, 0⟩⟩
  | .R => ⟨⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, -1, 0⟩⟩
  | .L => ⟨⟨1, 0, 0⟩, ⟨0, 0, -1⟩, ⟨0, 1, 0⟩⟩
  | .F => ⟨⟨0, 1, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, 1⟩⟩
  | .B => ⟨⟨0, -1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, 1⟩⟩

theorem faceMat_app (f : Face) (v : V3) : (faceMat f).app v = f.map v := by
  obtain ⟨x, y, z⟩ := v
  cases f <;> simp only [faceMat, Mat.app, V3.dot, Face.map, V3.mk.injEq] <;> omega

theorem faceMat_rots (f : Face) : faceMat f ∈ rots := by
  cases f <;> decide

/-! ## Finite facts -/

def allColors : List Color := [.W, .Y, .R, .O, .B, .G]

theorem mem_allColors (c : Color) : c ∈ allColors := by cases c <;> decide

def allFaces : List Face := [.U, .D, .R, .L, .F, .B]

theorem mem_allFaces (f : Face) : f ∈ allFaces := by cases f <;> decide

/-- The axis whose solved color is `col`. -/
def homeAxis : Color → V3
  | .W => ⟨0, 1, 0⟩ | .Y => ⟨0, -1, 0⟩ | .R => ⟨1, 0, 0⟩
  | .O => ⟨-1, 0, 0⟩ | .G => ⟨0, 0, 1⟩ | .B => ⟨0, 0, -1⟩

theorem homeAxis_mem (col : Color) : homeAxis col ∈ axes := by cases col <;> decide

theorem isCenter_rot_all :
    ∀ g ∈ rots, ∀ p ∈ lattice, isCenter (g.app p) = isCenter p := by decide

theorem center_axes_all : ∀ p ∈ lattice, isCenter p = true → p ∈ axes := by decide

theorem axes_lattice_all : ∀ a ∈ axes, a ∈ lattice := by decide

theorem center_color_all : ∀ p ∈ lattice, ∀ col ∈ allColors,
    (isCenter p && (solvedCubie p).stickers.any (·.2 = col)) = decide (p = homeAxis col) := by
  decide

theorem lattice_find_home_all : ∀ col ∈ allColors,
    lattice.find? (fun p => decide (p = homeAxis col)) = some (homeAxis col) := by decide

theorem face_fixes_axis_all : ∀ f ∈ allFaces, ∀ a ∈ axes, f.onFace a = true → f.map a = a := by
  decide

theorem face_perm_all : ∀ f ∈ allFaces,
    (lattice.map fun p => if f.onFace p then f.map p else p).Perm lattice := by decide

theorem rots_perm_all : ∀ m ∈ rots, (lattice.map m.app).Perm lattice := by decide

/-- The two colors on the cubie a rotation `g` brings to `(1, 1, 1)`, facing `+Y` and `+Z`,
    are on perpendicular faces. -/
def cornerOK (g : Mat) : Bool :=
  match colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 1, 0⟩),
      colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 0, 1⟩) with
  | some u, some f => V3.dot (homeAxis u) (homeAxis f) = 0
  | _, _ => false

theorem cornerOK_all : ∀ g ∈ rots, cornerOK g = true := by decide

/-- Rule B's matrix `⟨e × t, e, t⟩` for two perpendicular axes moved by a rotation. -/
theorem ruleMat_all : ∀ F ∈ rots, ∀ a ∈ axes, ∀ b ∈ axes, V3.dot a b = 0 →
    (⟨V3.cross (F.app a) (F.app b), F.app a, F.app b⟩ : Mat) ∈ rots := by decide

/-- Every corner slot the digest reads, on the cubie a rotation `g` brings there, shows
    three colors that name a corner piece and carry W or Y on one of the axes. -/
def cornerSlotOK (g : Mat) (sl : V3 × List V3) : Bool :=
  match sl.2.mapM (fun a => colorFacing (solvedCubie (g.transpose.app sl.1)) (g.transpose.app a)) with
  | some cols => (pieceId cornerTable cols).isSome && (cornerOri cols).isSome
  | none => false

def edgeSlotOK (g : Mat) (sl : V3 × List V3) : Bool :=
  match sl.2.mapM (fun a => colorFacing (solvedCubie (g.transpose.app sl.1)) (g.transpose.app a)) with
  | some cols => (pieceId edgeTable cols).isSome
  | none => false

theorem cornerSlotOK_all : ∀ g ∈ rots, ∀ sl ∈ cornerSlots, cornerSlotOK g sl = true := by decide

theorem edgeSlotOK_all : ∀ g ∈ rots, ∀ sl ∈ edgeSlots, edgeSlotOK g sl = true := by decide

theorem cornerSlots_lattice : ∀ sl ∈ cornerSlots, sl.1 ∈ lattice := by decide

theorem edgeSlots_lattice : ∀ sl ∈ edgeSlots, sl.1 ∈ lattice := by decide

theorem id_rots : (⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ : Mat) ∈ rots := by decide

/-! ## The invariant -/

/-- Cubie `c` started as the solved cubie at `p` and is a rotation of it; if `p` is a
    face center, `c` sits where the frame `F` puts `p`. -/
def Posed (F : Mat) (c : Cubie) (p : V3) : Prop :=
  (∃ g ∈ rots, c = moveCubie g.app (solvedCubie p)) ∧ (isCenter p = true → c.pos = F.app p)

/-- The invariant with its frame. -/
def ReachF (F : Mat) (cube : Cube) : Prop :=
  F ∈ rots ∧ All2 (Posed F) cube lattice ∧ (cube.map Cubie.pos).Perm lattice

/-- The invariant of every cube the v2 walk visits. -/
def Reach (cube : Cube) : Prop := ∃ F, ReachF F cube

theorem reach_solved : ReachF ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ solvedCube := by
  refine ⟨id_rots, ?_, ?_⟩
  · refine All2.of_map solvedCubie (fun p => ⟨⟨_, id_rots, (moveCubie_id _).symm⟩, fun _ => ?_⟩) lattice
    rw [Mat.app_id]; rfl
  · rw [solvedCube, List.map_map]
    exact (List.Perm.of_eq (by rw [show (Cubie.pos ∘ solvedCubie) = id from rfl, List.map_id]))

theorem face_map_eq (f : Face) : f.map = (faceMat f).app := funext fun v => (faceMat_app f v).symm

theorem reach_quarter (F : Mat) (f : Face) (cube : Cube) (h : ReachF F cube) :
    ReachF F (quarter f cube) := by
  obtain ⟨hF, hall, hperm⟩ := h
  refine ⟨hF, ?_, ?_⟩
  · have hall' := All2.with_mem lattice (fun b hb => hb) hall
    refine All2.map_left _ ?_ hall'
    intro c p ⟨⟨⟨g, hg, hc⟩, hcen⟩, hp⟩
    by_cases hon : f.onFace c.pos = true
    · simp only [hon, if_true]
      refine ⟨⟨(faceMat f).mul g, rots_mul _ _ (faceMat_rots f) hg, ?_⟩, fun hcp => ?_⟩
      · rw [hc, face_map_eq, moveCubie_mul]
      · rw [moveCubie_pos, hcen hcp]
        have hax : F.app p ∈ axes := rots_axes F hF p (center_axes_all p hp hcp)
        rw [hcen hcp] at hon
        exact face_fixes_axis_all f (mem_allFaces f) _ hax hon
    · simp only [hon, Bool.false_eq_true, if_false]
      exact ⟨⟨g, hg, hc⟩, hcen⟩
  · have hmap : (quarter f cube).map Cubie.pos =
        (cube.map Cubie.pos).map (fun p => if f.onFace p then f.map p else p) := by
      simp only [quarter, List.map_map]
      congr 1
      funext c
      simp only [Function.comp]
      split <;> rfl
    rw [hmap]
    exact (hperm.map _).trans (face_perm_all f (mem_allFaces f))

theorem reach_rotate (F M : Mat) (hM : M ∈ rots) (cube : Cube) (h : ReachF F cube) :
    ReachF (M.mul F) (cube.map (moveCubie M.app)) := by
  obtain ⟨hF, hall, hperm⟩ := h
  refine ⟨rots_mul _ _ hM hF, ?_, ?_⟩
  · refine All2.map_left _ ?_ hall
    intro c p ⟨⟨g, hg, hc⟩, hcen⟩
    refine ⟨⟨M.mul g, rots_mul _ _ hM hg, ?_⟩, fun hcp => ?_⟩
    · rw [hc, moveCubie_mul]
    · rw [moveCubie_pos, hcen hcp, Mat.app_mul]
  · rw [List.map_map, show (Cubie.pos ∘ moveCubie M.app) = M.app ∘ Cubie.pos from rfl,
      ← List.map_map]
    exact (hperm.map _).trans (rots_perm_all M hM)

/-! ## What the invariant gives -/

theorem isCenter_homeAxis (col : Color) : isCenter (homeAxis col) = true := by
  cases col <;> decide

/-- Where each center is. -/
theorem centerOf_reach (F : Mat) (cube : Cube) (h : ReachF F cube) (col : Color) :
    centerOf cube col = some (F.app (homeAxis col)) := by
  obtain ⟨hF, hall, _⟩ := h
  have hall' := All2.with_mem lattice (fun b hb => hb) hall
  obtain ⟨a, ha, ⟨_, hcen⟩, _⟩ := All2.find
    (fun c => isCenter c.pos && c.stickers.any (·.2 = col))
    (fun p => decide (p = homeAxis col))
    (fun c p ⟨⟨⟨g, hg, hc⟩, _⟩, hp⟩ => by
      show (isCenter c.pos && c.stickers.any (·.2 = col)) = decide (p = homeAxis col)
      rw [← center_color_all p hp col (mem_allColors col), hc]
      simp only [moveCubie, List.any_map, Function.comp_def]
      rw [show (solvedCubie p).pos = p from rfl, isCenter_rot_all g hg p hp])
    hall' (homeAxis col) (lattice_find_home_all col (mem_allColors col))
  unfold centerOf
  rw [ha, Option.map_some', hcen (isCenter_homeAxis col)]

/-- The cubie in each lattice slot. -/
theorem cubieAt_reach (F : Mat) (cube : Cube) (h : ReachF F cube) (q : V3) (hq : q ∈ lattice) :
    ∃ g ∈ rots, cubieAt cube q = some (moveCubie g.app (solvedCubie (g.transpose.app q))) ∧
      g.app (g.transpose.app q) = q := by
  obtain ⟨_, hall, hperm⟩ := h
  have hmem : q ∈ cube.map Cubie.pos := hperm.mem_iff.mpr hq
  obtain ⟨c0, hc0, hpos0⟩ := List.mem_map.mp hmem
  have hsome : (cube.find? fun c => c.pos = q).isSome := by
    rw [List.find?_isSome]; exact ⟨c0, hc0, by simp [hpos0]⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  have hcq : c.pos = q := by simpa using List.find?_some hc
  obtain ⟨p, hp, ⟨g, hg, hcg⟩, _⟩ := All2.mem_left hall c (List.mem_of_find?_eq_some hc)
  have hgp : g.app p = q := by rw [← hcq, hcg]; rfl
  have hpq : p = g.transpose.app q := by rw [← hgp, rots_transpose_app g hg]
  refine ⟨g, hg, ?_, by rw [← hpq, hgp]⟩
  unfold cubieAt
  rw [hc, hcg, hpq]

/-- Rule B's rotation of a reachable cube, when `up` and `front` are on perpendicular
    faces: the matrix is in `rots`, and the result is reachable. -/
theorem rotateTo_reach (F : Mat) (cube : Cube) (h : ReachF F cube) (up front : Color)
    (hperp : V3.dot (homeAxis up) (homeAxis front) = 0) :
    ∃ cube', rotateTo cube up front = some cube' ∧ Reach cube' := by
  have hF := h.1
  unfold rotateTo
  rw [centerOf_reach F cube h up, centerOf_reach F cube h front]
  simp only [Option.bind_eq_bind, Option.some_bind]
  split
  · exact ⟨cube, rfl, F, h⟩
  · refine ⟨_, rfl, _, reach_rotate F _ ?_ cube h⟩
    exact ruleMat_all F hF _ (homeAxis_mem up) _ (homeAxis_mem front) hperp

theorem mem_lattice_111 : (⟨1, 1, 1⟩ : V3) ∈ lattice := by decide

theorem ruleB_reach (F : Mat) (cube : Cube) (h : ReachF F cube) :
    ∃ cube', ruleB cube = some cube' ∧ Reach cube' := by
  obtain ⟨g, hg, hc, _⟩ := cubieAt_reach F cube h _ mem_lattice_111
  have hk := cornerOK_all g hg
  unfold cornerOK at hk
  unfold ruleB
  rw [hc]
  simp only [Option.bind_eq_bind, Option.some_bind, colorFacing_rot g hg]
  revert hk
  cases h1 : colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 1, 0⟩) with
  | none => simp
  | some u =>
    cases h2 : colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 0, 1⟩) with
    | none => simp
    | some f =>
      intro hk
      simp only [decide_eq_true_eq] at hk
      simp only [Option.some_bind]
      exact rotateTo_reach F cube h u f hk

theorem Reach.ruleB (cube : Cube) (h : Reach cube) :
    ∃ cube', ruleB cube = some cube' ∧ Reach cube' :=
  let ⟨F, hF⟩ := h; ruleB_reach F cube hF

theorem Reach.quarter_turn (f : Face) (cube : Cube) (h : Reach cube) : Reach (quarter f cube) :=
  let ⟨F, hF⟩ := h; ⟨F, reach_quarter F f cube hF⟩

theorem Reach.symbolV2 (cube : Cube) (h : Reach cube) (n : Nat) :
    ∃ cube', symbolV2 cube n = some cube' ∧ Reach cube' :=
  Reach.ruleB _ (Reach.quarter_turn _ _ (Reach.quarter_turn _ _ h))

theorem Reach.walkV2 (tape : List Nat) : ∀ (cube : Cube), Reach cube →
    ∃ cube', walkV2 cube tape = some cube' ∧ Reach cube' := by
  induction tape with
  | nil => intro cube h; exact ⟨cube, rfl, h⟩
  | cons n t ih =>
    intro cube h
    obtain ⟨c1, h1, r1⟩ := Reach.symbolV2 cube h n
    obtain ⟨c2, h2, r2⟩ := ih c1 r1
    refine ⟨c2, ?_, r2⟩
    unfold ScrambleV2.walkV2 at h2 ⊢
    rw [List.foldlM_cons, h1]
    exact h2

theorem Reach.seat (cube : Cube) (h : Reach cube) :
    ∃ cube', seat cube = some cube' ∧ Reach cube' := by
  obtain ⟨F, hF⟩ := Reach.quarter_turn _ _ (Reach.quarter_turn _ _ (Reach.quarter_turn _ _ (Reach.quarter_turn _ _ h)))
  exact rotateTo_reach F _ hF .W .G (by decide)

/-! ## The digest reads real pieces -/

theorem mapM_some {α β} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self _ _))
    obtain ⟨ys, hys⟩ := mapM_some f l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

theorem mem_of_mapM_some {α β} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ l, f x = some y
  | [], ys, h, y, hy => by
    simp only [List.mapM_nil] at h
    cases h; simp at hy
  | x :: l, ys, h, y, hy => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some bs =>
        simp only [hx, hl, Option.bind_eq_bind, Option.some_bind] at h
        cases h
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨x, List.mem_cons_self _ _, hx⟩
        · obtain ⟨z, hz, hfz⟩ := mem_of_mapM_some f l bs hl y hy
          exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

theorem readSlot_rot (F : Mat) (cube : Cube) (h : ReachF F cube) (sl : V3 × List V3)
    (hsl : sl.1 ∈ lattice) : ∃ g ∈ rots, readSlot cube sl =
      sl.2.mapM (fun a => colorFacing (solvedCubie (g.transpose.app sl.1)) (g.transpose.app a)) := by
  obtain ⟨g, hg, hc, _⟩ := cubieAt_reach F cube h sl.1 hsl
  refine ⟨g, hg, ?_⟩
  unfold readSlot
  rw [hc]
  simp only [Option.bind_eq_bind, Option.some_bind]
  congr 1
  funext a
  exact colorFacing_rot g hg _ a

theorem corner_read (F : Mat) (cube : Cube) (h : ReachF F cube) (sl : V3 × List V3)
    (hsl : sl ∈ cornerSlots) : ∃ cols, readSlot cube sl = some cols ∧
      (pieceId cornerTable cols).isSome ∧ (cornerOri cols).isSome := by
  obtain ⟨g, hg, hr⟩ := readSlot_rot F cube h sl (cornerSlots_lattice sl hsl)
  have hk := cornerSlotOK_all g hg sl hsl
  unfold cornerSlotOK at hk
  rw [hr]
  revert hk
  cases sl.2.mapM (fun a => colorFacing (solvedCubie (g.transpose.app sl.1)) (g.transpose.app a)) with
  | none => simp
  | some cols =>
    intro hk
    simp only [Bool.and_eq_true] at hk
    exact ⟨cols, rfl, hk.1, hk.2⟩

theorem edge_read (F : Mat) (cube : Cube) (h : ReachF F cube) (sl : V3 × List V3)
    (hsl : sl ∈ edgeSlots) : ∃ cols, readSlot cube sl = some cols ∧
      (pieceId edgeTable cols).isSome := by
  obtain ⟨g, hg, hr⟩ := readSlot_rot F cube h sl (edgeSlots_lattice sl hsl)
  have hk := edgeSlotOK_all g hg sl hsl
  unfold edgeSlotOK at hk
  rw [hr]
  revert hk
  cases sl.2.mapM (fun a => colorFacing (solvedCubie (g.transpose.app sl.1)) (g.transpose.app a)) with
  | none => simp
  | some cols => intro hk; exact ⟨cols, rfl, hk⟩

theorem Reach.digestOf (cube : Cube) (h : Reach cube) : (digestOf cube).isSome := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨cs, hcs⟩ := mapM_some (readSlot cube) cornerSlots (fun sl hsl => by
    obtain ⟨cols, hc, _⟩ := corner_read F cube hF sl hsl; simp [hc])
  have hcs' := mem_of_mapM_some _ _ _ hcs
  obtain ⟨cp, hcp⟩ := mapM_some (pieceId cornerTable) cs (fun cols hc => by
    obtain ⟨sl, hsl, hr⟩ := hcs' cols hc
    obtain ⟨cols', hr', hp, _⟩ := corner_read F cube hF sl hsl
    rw [hr] at hr'; cases hr'; exact hp)
  obtain ⟨co, hco⟩ := mapM_some cornerOri (cs.take 7) (fun cols hc => by
    obtain ⟨sl, hsl, hr⟩ := hcs' cols (List.mem_of_mem_take hc)
    obtain ⟨cols', hr', _, ho⟩ := corner_read F cube hF sl hsl
    rw [hr] at hr'; cases hr'; exact ho)
  obtain ⟨es, hes⟩ := mapM_some (readSlot cube) edgeSlots (fun sl hsl => by
    obtain ⟨cols, hc, _⟩ := edge_read F cube hF sl hsl; simp [hc])
  have hes' := mem_of_mapM_some _ _ _ hes
  obtain ⟨ep, hep⟩ := mapM_some (pieceId edgeTable) es (fun cols hc => by
    obtain ⟨sl, hsl, hr⟩ := hes' cols hc
    obtain ⟨cols', hr', hp⟩ := edge_read F cube hF sl hsl
    rw [hr] at hr'; cases hr'; exact hp)
  unfold ScrambleV2.digestOf
  simp [hcs, hcp, hco, hes, hep]

/-- The model never answers `none`: every message has a v2 digest. -/
theorem digestV2_isSome (msg : List Nat) : (digestV2? msg).isSome := by
  obtain ⟨c1, h1, r1⟩ := Reach.walkV2 (padV2 (nybbles msg)) solvedCube ⟨_, reach_solved⟩
  obtain ⟨c2, h2, r2⟩ := Reach.seat c1 r1
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Reach.digestOf c2 r2)
  unfold digestV2?
  simp [h1, h2, hd]

end ScrambleV2.Link2
