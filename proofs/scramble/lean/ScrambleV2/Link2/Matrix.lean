/-
  LINK 2. The emitted `cross`, `dot`, `mul_vec`, `paint_cubie` and `apply_matrix`
  against the model's `V3.cross`, `V3.dot`, `Mat.app` and `moveCubie`, for a matrix in
  `rots` (the only matrices Rule B and the seat build on the walk; `Reach.lean`).

  Rows are the tuple shape from the streaming-state regeneration: a triple of
  `(Int × Int × Int)`, not `List<List<int>>`. Proof-only.
-/
import ScrambleV2.Link2.Rots
import ScrambleV2.Link2.TurnRaw
import ScrambleV2.Link2.Turn

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-! ## Small integer arithmetic -/

theorem narrowI_small (n : Int) (h1 : -1000 ≤ n) (h2 : n ≤ 1000) :
    SudoRt.narrowI n = .ok n := by
  unfold SudoRt.narrowI
  have : ¬ ((n < SudoRt.i64Min || n > SudoRt.i64Max) = true) := by
    simp [SudoRt.i64Min, SudoRt.i64Max]; omega
  rw [if_neg this]

theorem mulI_small (a b : Int) (h1 : -1000 ≤ a * b) (h2 : a * b ≤ 1000) :
    SudoRt.mulI a b = .ok (a * b) := narrowI_small _ h1 h2

theorem addI_small (a b : Int) (h1 : -1000 ≤ a + b) (h2 : a + b ≤ 1000) :
    SudoRt.addI a b = .ok (a + b) := narrowI_small _ h1 h2

theorem subI_small (a b : Int) (h1 : -1000 ≤ a - b) (h2 : a - b ≤ 1000) :
    SudoRt.subI a b = .ok (a - b) := narrowI_small _ h1 h2

theorem mul_unit (a b : Int) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb1 : -1 ≤ b) (hb2 : b ≤ 1) :
    -1 ≤ a * b ∧ a * b ≤ 1 := by
  have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl | rfl <;> omega

/-! ## Matrices on the bridge -/

/-- One model row → the emitted `(Int × Int × Int)`. -/
def embedRow (v : V3) : Int × Int × Int := (v.x, v.y, v.z)

/-- Model matrix → the emitted triple of rows. -/
def embedMat (m : Mat) :
    (Int × Int × Int) × (Int × Int × Int) × (Int × Int × Int) :=
  (embedRow m.r0, embedRow m.r1, embedRow m.r2)

/-- The emitted `dot` on a row in `{-1, 0, 1}` and a vector in `{-1, 0, 1}` is `V3.dot`. -/
theorem dot_refines (r : V3) (hr : Unit3 r) (x y z : Int) (hv : Unit3 ⟨x, y, z⟩) :
    Scramble.dot (embedRow r) x y z = .ok (V3.dot r ⟨x, y, z⟩) := by
  obtain ⟨a, b, c⟩ := r
  obtain ⟨ha1, ha2, hb1, hb2, hc1, hc2⟩ := hr
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hv
  simp only at *
  have p1 := mul_unit a x ha1 ha2 hx1 hx2
  have p2 := mul_unit b y hb1 hb2 hy1 hy2
  have p3 := mul_unit c z hc1 hc2 hz1 hz2
  unfold Scramble.dot embedRow
  dsimp only
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind]
  rfl

theorem mul_vec_refines (m : Mat) (hm : SmallMat m) (x y z : Int) (hv : Unit3 ⟨x, y, z⟩) :
    Scramble.mul_vec (embedMat m) x y z =
      .ok ((m.app ⟨x, y, z⟩).x, (m.app ⟨x, y, z⟩).y, (m.app ⟨x, y, z⟩).z) := by
  obtain ⟨r0, r1, r2⟩ := m
  obtain ⟨h0, h1, h2⟩ := hm
  unfold Scramble.mul_vec embedMat Mat.app
  dsimp only
  rw [dot_refines r0 h0 x y z hv, ok_bind, dot_refines r1 h1 x y z hv, ok_bind,
    dot_refines r2 h2 x y z hv, ok_bind]
  rfl

theorem cross_refines (a b : V3) (ha : Unit3 a) (hb : Unit3 b) :
    Scramble.cross a.x a.y a.z b.x b.y b.z =
      .ok ((V3.cross a b).x, (V3.cross a b).y, (V3.cross a b).z) := by
  obtain ⟨x, y, z⟩ := a
  obtain ⟨u, v, w⟩ := b
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hb
  simp only at *
  have q1 := mul_unit y w h3 h4 k5 k6
  have q2 := mul_unit z v h5 h6 k3 k4
  have q3 := mul_unit z u h5 h6 k1 k2
  have q4 := mul_unit x w h1 h2 k5 k6
  have q5 := mul_unit x v h1 h2 k3 k4
  have q6 := mul_unit y u h3 h4 k1 k2
  unfold Scramble.cross
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    subI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    mulI_small _ _ (by omega) (by omega), ok_bind, subI_small _ _ (by omega) (by omega), ok_bind,
    mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    subI_small _ _ (by omega) (by omega), ok_bind]
  rfl

/-! ## `apply_matrix` -/

theorem embedC_move (M : Mat) (hM : M ∈ rots) (c : Cubie) :
    embedC (moveCubie M.app c) =
      ⟨(M.app c.pos).x, (M.app c.pos).y, (M.app c.pos).z,
       slot c (M.transpose.app ax_xp), slot c (M.transpose.app ax_xn),
       slot c (M.transpose.app ax_yp), slot c (M.transpose.app ax_yn),
       slot c (M.transpose.app ax_zp), slot c (M.transpose.app ax_zn)⟩ := by
  have sm := fun b => slot_move M.app (rots_inj M hM) c (M.transpose.app b) b
    (rots_app_transpose M hM b)
  simp only [embedC, moveCubie_pos, sm]

/-! ## Painting one cubie

The emitted `paint_cubie` writes a color onto `M.app` of its axis, and leaves the
stickers alone when the color is `0`. On a rotation the six axes land on the six
axes, each exactly once, so the six writes rebuild `slot` of the transposed axis:
the stickers of `moveCubie M.app`.
-/

abbrev Stick := Int × Int × Int × Int × Int × Int

def axisOf : Nat → V3
  | 0 => ax_xp | 1 => ax_xn | 2 => ax_yp | 3 => ax_yn | 4 => ax_zp | 5 => ax_zn
  | _ => ax_xp

/-- Which sticker slot a unit axis writes. Not an axis maps to the fall-through `zn`. -/
def axisIdx (a : V3) : Nat :=
  if a = ax_xp then 0 else if a = ax_xn then 1 else if a = ax_yp then 2
  else if a = ax_yn then 3 else if a = ax_zp then 4 else 5

def getS (s : Stick) : Nat → Int
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2.1
  | 3 => s.2.2.2.1
  | 4 => s.2.2.2.2.1
  | _ => s.2.2.2.2.2

def putAxis (xp xn yp yn zp zn : Int) (a : V3) (col : Int) : Stick :=
  if a = ax_xp then (col, xn, yp, yn, zp, zn)
  else if a = ax_xn then (xp, col, yp, yn, zp, zn)
  else if a = ax_yp then (xp, xn, col, yn, zp, zn)
  else if a = ax_yn then (xp, xn, yp, col, zp, zn)
  else if a = ax_zp then (xp, xn, yp, yn, col, zn)
  else (xp, xn, yp, yn, zp, col)

def putS (s : Stick) (a : V3) (col : Int) : Stick :=
  putAxis (getS s 0) (getS s 1) (getS s 2) (getS s 3) (getS s 4) (getS s 5) a col

theorem axes_cases (a : V3) (ha : a ∈ axes) :
    a = ax_yp ∨ a = ax_yn ∨ a = ax_xp ∨ a = ax_xn ∨ a = ax_zp ∨ a = ax_zn := by
  simpa [axes, ax_yp, ax_yn, ax_xp, ax_xn, ax_zp, ax_zn,
    List.mem_cons, List.mem_singleton, or_false] using ha

theorem axes_unit (a : V3) (ha : a ∈ axes) : Unit3 a := by
  rcases axes_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Unit3
    decide

theorem nat_of_lt_six (t : Nat) (ht : t < 6) :
    t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega

theorem axisOf_mem_all : ∀ k ∈ List.range 6, axisOf k ∈ axes := by decide

theorem axisOf_mem (k : Nat) (hk : k < 6) : axisOf k ∈ axes :=
  axisOf_mem_all k (List.mem_range.mpr hk)

theorem axisIdx_spec_all : ∀ a ∈ axes, axisOf (axisIdx a) = a ∧ axisIdx a < 6 := by decide

theorem axisIdx_lt (a : V3) (ha : a ∈ axes) : axisIdx a < 6 :=
  (axisIdx_spec_all a ha).2

theorem getS_zero (t : Nat) : getS (0, 0, 0, 0, 0, 0) t = 0 := by
  unfold getS
  split <;> rfl

theorem putAxis_get (xp xn yp yn zp zn col : Int) (a : V3) (ha : a ∈ axes) (t : Nat)
    (ht : t < 6) :
    getS (putAxis xp xn yp yn zp zn a col) t =
      if a = axisOf t then col else getS (xp, xn, yp, yn, zp, zn) t := by
  rcases axes_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases nat_of_lt_six t ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [putAxis, getS, axisOf, ax_xp, ax_xn, ax_yp, ax_yn, ax_zp, ax_zn]

theorem putS_get (s : Stick) (a : V3) (ha : a ∈ axes) (col : Int) (t : Nat) (ht : t < 6) :
    getS (putS s a col) t = if a = axisOf t then col else getS s t := by
  simpa [putS] using putAxis_get (getS s 0) (getS s 1) (getS s 2) (getS s 3) (getS s 4)
    (getS s 5) col a ha t ht

theorem putAxis_zero (xp xn yp yn zp zn : Int) (a : V3) (ha : a ∈ axes)
    (h0 : getS (xp, xn, yp, yn, zp, zn) (axisIdx a) = 0) :
    putAxis xp xn yp yn zp zn a 0 = (xp, xn, yp, yn, zp, zn) := by
  rcases axes_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl
  · have hi : axisIdx ax_yp = 2 := by decide
    simp only [hi, getS] at h0
    have n1 : ¬ ax_yp = ax_xp := by decide
    have n2 : ¬ ax_yp = ax_xn := by decide
    simp [putAxis, n1, n2, h0]
  · have hi : axisIdx ax_yn = 3 := by decide
    simp only [hi, getS] at h0
    have n1 : ¬ ax_yn = ax_xp := by decide
    have n2 : ¬ ax_yn = ax_xn := by decide
    have n3 : ¬ ax_yn = ax_yp := by decide
    simp [putAxis, n1, n2, n3, h0]
  · have hi : axisIdx ax_xp = 0 := by decide
    simp only [hi, getS] at h0
    simp [putAxis, h0]
  · have hi : axisIdx ax_xn = 1 := by decide
    simp only [hi, getS] at h0
    have n1 : ¬ ax_xn = ax_xp := by decide
    simp [putAxis, n1, h0]
  · have hi : axisIdx ax_zp = 4 := by decide
    simp only [hi, getS] at h0
    have n1 : ¬ ax_zp = ax_xp := by decide
    have n2 : ¬ ax_zp = ax_xn := by decide
    have n3 : ¬ ax_zp = ax_yp := by decide
    have n4 : ¬ ax_zp = ax_yn := by decide
    simp [putAxis, n1, n2, n3, n4, h0]
  · have hi : axisIdx ax_zn = 5 := by decide
    simp only [hi, getS] at h0
    have n1 : ¬ ax_zn = ax_xp := by decide
    have n2 : ¬ ax_zn = ax_xn := by decide
    have n3 : ¬ ax_zn = ax_yp := by decide
    have n4 : ¬ ax_zn = ax_yn := by decide
    have n5 : ¬ ax_zn = ax_zp := by decide
    simp [putAxis, n1, n2, n3, n4, n5, h0]

theorem write_axis_axes (a : V3) (ha : a ∈ axes) (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn a.x a.y a.z col =
      .ok (putAxis xp xn yp yn zp zn a col) := by
  rcases axes_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [putAxis, ax_xp, ax_xn, ax_yp, ax_yn, ax_zp, ax_zn]
    first
      | exact wxp xp xn yp yn zp zn col
      | exact wxn xp xn yp yn zp zn col
      | exact wyp xp xn yp yn zp zn col
      | exact wyn xp xn yp yn zp zn col
      | exact wzp xp xn yp yn zp zn col
      | exact wzn xp xn yp yn zp zn col

/-- `paint_cubie` along an axis, into a slot that is still `0`, writes `col` there
    (a `0` color leaves the zero slot unchanged). -/
theorem paint_put (M : Mat) (hM : M ∈ rots) (nx ny nz xp xn yp yn zp zn : Int) (a : V3)
    (ha : a ∈ axes) (col : Int)
    (hfresh : getS (xp, xn, yp, yn, zp, zn) (axisIdx (M.app a)) = 0) :
    Scramble.paint_cubie nx ny nz (embedMat M) xp xn yp yn zp zn a.x a.y a.z col =
      .ok (putAxis xp xn yp yn zp zn (M.app a) col) := by
  unfold Scramble.paint_cubie
  by_cases h0 : col = 0
  · subst h0
    have hb : SudoRt.SEq.beq (0 : Int) 0 = true := by simp [sEq_int]
    simp only [hb, if_true]
    rw [putAxis_zero xp xn yp yn zp zn (M.app a) (rots_axes M hM a ha) hfresh]
    rfl
  · have hb : SudoRt.SEq.beq col 0 = false := by simp [sEq_int, h0]
    simp only [hb, if_false]
    rw [mul_vec_refines M (rots_small M hM) a.x a.y a.z (axes_unit a ha), ok_bind]
    rw [write_axis_axes (M.app a) (rots_axes M hM a ha)]
    rfl

/-- Where the sticker now on axis `t` came from: `M⁻¹` applied to that axis. -/
def srcFor (M : Mat) (t : Nat) : Nat := axisIdx (M.transpose.app (axisOf t))

set_option maxHeartbeats 1000000 in
theorem route_idx_all : ∀ M ∈ rots, ∀ t ∈ List.range 6,
    srcFor M t < 6 ∧
    M.app (axisOf (srcFor M t)) = axisOf t ∧
    axisOf (srcFor M t) = M.transpose.app (axisOf t) := by
  decide

set_option maxHeartbeats 1000000 in
theorem route_unique_all : ∀ M ∈ rots, ∀ t ∈ List.range 6, ∀ k ∈ List.range 6,
    M.app (axisOf k) = axisOf t → k = srcFor M t := by
  decide

theorem route_unique (M : Mat) (hM : M ∈ rots) (t : Nat) (ht : t ∈ List.range 6)
    (k : Nat) (hk : k ∈ List.range 6) (happ : M.app (axisOf k) = axisOf t) :
    k = srcFor M t :=
  route_unique_all M hM t ht k hk happ

theorem src_of_image (M : Mat) (hM : M ∈ rots) (k : Nat) (hk : k < 6) :
    srcFor M (axisIdx (M.app (axisOf k))) = k := by
  have himg : M.app (axisOf k) ∈ axes := rots_axes M hM _ (axisOf_mem k hk)
  have hidx := axisIdx_spec_all _ himg
  exact (route_unique M hM _ (List.mem_range.mpr hidx.2) k (List.mem_range.mpr hk) hidx.1.symm).symm

def foldPaint (M : Mat) (col : Nat → Int) : Nat → Stick
  | 0 => (0, 0, 0, 0, 0, 0)
  | n + 1 => putS (foldPaint M col n) (M.app (axisOf n)) (col n)

theorem foldPaint_zero (M : Mat) (col : Nat → Int) : foldPaint M col 0 = (0, 0, 0, 0, 0, 0) := rfl

theorem foldPaint_succ (M : Mat) (col : Nat → Int) (n : Nat) :
    foldPaint M col (n + 1) = putS (foldPaint M col n) (M.app (axisOf n)) (col n) := rfl

theorem axisOf_0 : axisOf 0 = ax_xp := rfl

theorem get_paint (M : Mat) (hM : M ∈ rots) (col : Nat → Int) :
    ∀ n, n ≤ 6 → ∀ t, t < 6 →
      getS (foldPaint M col n) t = if srcFor M t < n then col (srcFor M t) else 0 := by
  intro n hn t ht
  induction n with
  | zero => simp [foldPaint, getS_zero]
  | succ n ih =>
    have hn' : n < 6 := by omega
    rw [foldPaint, putS_get _ _ (rots_axes M hM _ (axisOf_mem n hn')) _ t ht]
    by_cases hhit : M.app (axisOf n) = axisOf t
    · have hk : n = srcFor M t :=
        route_unique M hM t (List.mem_range.mpr ht) n (List.mem_range.mpr hn') hhit
      rw [if_pos hhit]
      have hlt : srcFor M t < n + 1 := by rw [← hk]; exact Nat.lt_succ_self n
      rw [if_pos hlt, hk]
    · have hne : srcFor M t ≠ n := by
        intro heq
        have hr := (route_idx_all M hM t (List.mem_range.mpr ht)).2.1
        rw [heq] at hr
        exact hhit hr
      rw [if_neg hhit, ih (Nat.le_of_lt hn')]
      by_cases hlt : srcFor M t < n
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · have hnot : ¬ srcFor M t < n + 1 := by omega
        rw [if_neg hlt, if_neg hnot]

theorem fresh_fold (M : Mat) (hM : M ∈ rots) (col : Nat → Int) (k : Nat) (hk : k < 6) :
    getS (foldPaint M col k) (axisIdx (M.app (axisOf k))) = 0 := by
  have himg : M.app (axisOf k) ∈ axes := rots_axes M hM _ (axisOf_mem k hk)
  rw [get_paint M hM col k (by omega) _ (axisIdx_lt _ himg), src_of_image M hM k hk]
  simp

def col6 (c0 c1 c2 c3 c4 c5 : Int) : Nat → Int
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | _ => 0

/-- One paint, then an arbitrary continuation of the resulting sticker tuple. -/
theorem paint_bind {α} (M : Mat) (hM : M ∈ rots) (nx ny nz : Int) (s : Stick) (k : Nat)
    (hk : k < 6) (col : Int) (hfresh : getS s (axisIdx (M.app (axisOf k))) = 0)
    (kont : Stick → Except SudoRt.Trap α) :
    (do
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS s 0) (getS s 1) (getS s 2)
        (getS s 3) (getS s 4) (getS s 5) (axisOf k).x (axisOf k).y (axisOf k).z col
      kont t) =
      kont (putS s (M.app (axisOf k)) col) := by
  rw [paint_put M hM nx ny nz (getS s 0) (getS s 1) (getS s 2) (getS s 3) (getS s 4) (getS s 5)
      (axisOf k) (axisOf_mem k hk) col hfresh, ok_bind]
  rfl

theorem paint_bind_ax {α} (M : Mat) (hM : M ∈ rots) (nx ny nz ax ay az : Int) (s : Stick)
    (k : Nat) (hk : k < 6) (hax : ax = (axisOf k).x) (hay : ay = (axisOf k).y)
    (haz : az = (axisOf k).z) (col : Int)
    (hfresh : getS s (axisIdx (M.app (axisOf k))) = 0) (kont : Stick → Except SudoRt.Trap α) :
    (do
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS s 0) (getS s 1) (getS s 2)
        (getS s 3) (getS s 4) (getS s 5) ax ay az col
      kont t) =
      kont (putS s (M.app (axisOf k)) col) := by
  subst hax; subst hay; subst haz
  exact paint_bind M hM nx ny nz s k hk col hfresh kont

/-- The first paint reads the six zero slots and the `+X` axis as literals. -/
theorem paint_bind_xp {α} (M : Mat) (hM : M ∈ rots) (nx ny nz c0 : Int)
    (hfresh : getS (0, 0, 0, 0, 0, 0) (axisIdx (M.app ax_xp)) = 0)
    (kont : Stick → Except SudoRt.Trap α) :
    (do
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) 0 0 0 0 0 0 (1 : Int) 0 0 c0
      kont t) =
      kont (putS (0, 0, 0, 0, 0, 0) (M.app ax_xp) c0) := by
  have hfresh' : getS (0, 0, 0, 0, 0, 0) (axisIdx (M.app (axisOf 0))) = 0 := by
    simpa [axisOf] using hfresh
  simpa [getS, axisOf, ax_xp] using
    paint_bind M hM nx ny nz (0, 0, 0, 0, 0, 0) 0 (by decide) c0 hfresh' kont

theorem fst_getS (t : Stick) : t.fst = getS t 0 := rfl
theorem snd1_getS (t : Stick) : t.2.fst = getS t 1 := rfl
theorem snd2_getS (t : Stick) : t.2.2.fst = getS t 2 := rfl
theorem snd3_getS (t : Stick) : t.2.2.2.fst = getS t 3 := rfl
theorem snd4_getS (t : Stick) : t.2.2.2.2.fst = getS t 4 := rfl
theorem snd5_getS (t : Stick) : t.2.2.2.2.snd = getS t 5 := rfl

theorem col6_0 (a b c d e f : Int) : col6 a b c d e f 0 = a := rfl
theorem col6_1 (a b c d e f : Int) : col6 a b c d e f 1 = b := rfl
theorem col6_2 (a b c d e f : Int) : col6 a b c d e f 2 = c := rfl
theorem col6_3 (a b c d e f : Int) : col6 a b c d e f 3 = d := rfl
theorem col6_4 (a b c d e f : Int) : col6 a b c d e f 4 = e := rfl
theorem col6_5 (a b c d e f : Int) : col6 a b c d e f 5 = f := rfl

/-- The six emitted paints, in axis order `+X -X +Y -Y +Z -Z`, build `foldPaint`. -/
theorem six_paints {α} (M : Mat) (hM : M ∈ rots) (nx ny nz c0 c1 c2 c3 c4 c5 : Int)
    (kont : Stick → Except SudoRt.Trap α) :
    (do
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) 0 0 0 0 0 0 (1 : Int) 0 0 c0
      let n1 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) t.fst t.2.fst t.2.2.fst t.2.2.2.fst
          t.2.2.2.2.fst t.2.2.2.2.snd n1 0 0 c1
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) t.fst t.2.fst t.2.2.fst t.2.2.2.fst
          t.2.2.2.2.fst t.2.2.2.2.snd 0 1 0 c2
      let n2 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) t.fst t.2.fst t.2.2.fst t.2.2.2.fst
          t.2.2.2.2.fst t.2.2.2.2.snd 0 n2 0 c3
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) t.fst t.2.fst t.2.2.fst t.2.2.2.fst
          t.2.2.2.2.fst t.2.2.2.2.snd 0 0 1 c4
      let n3 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) t.fst t.2.fst t.2.2.fst t.2.2.2.fst
          t.2.2.2.2.fst t.2.2.2.2.snd 0 0 n3 c5
      kont t) =
      kont (foldPaint M (col6 c0 c1 c2 c3 c4 c5) 6) := by
  let col := col6 c0 c1 c2 c3 c4 c5
  simp only [fst_getS, snd1_getS, snd2_getS, snd3_getS, snd4_getS, snd5_getS]
  have h0 : getS (0, 0, 0, 0, 0, 0) (axisIdx (M.app ax_xp)) = 0 := by
    simpa [axisOf, foldPaint] using fresh_fold M hM col 0 (by decide)
  rw [paint_bind_xp M hM nx ny nz c0 h0]
  rw [show putS (0, 0, 0, 0, 0, 0) (M.app ax_xp) c0 = foldPaint M col 1 by
    conv => rhs; rw [foldPaint_succ, foldPaint_zero, axisOf_0]
    rw [show col 0 = c0 from by unfold col; exact col6_0 c0 c1 c2 c3 c4 c5]]
  rw [negI_one, ok_bind]
  have h1 : getS (foldPaint M col 1) (axisIdx (M.app (axisOf 1))) = 0 :=
    fresh_fold M hM col 1 (by decide)
  rw [paint_bind_ax M hM nx ny nz (-1) 0 0 (foldPaint M col 1) 1 (by decide)
      (by simp [axisOf, ax_xn]) (by simp [axisOf, ax_xn]) (by simp [axisOf, ax_xn]) c1 h1]
  rw [show putS (foldPaint M col 1) (M.app (axisOf 1)) c1 = foldPaint M col 2 by
    conv => rhs; rw [foldPaint_succ]
    rw [show col 1 = c1 from by unfold col; exact col6_1 c0 c1 c2 c3 c4 c5]]
  have h2 : getS (foldPaint M col 2) (axisIdx (M.app (axisOf 2))) = 0 :=
    fresh_fold M hM col 2 (by decide)
  rw [paint_bind_ax M hM nx ny nz 0 1 0 (foldPaint M col 2) 2 (by decide)
      (by simp [axisOf, ax_yp]) (by simp [axisOf, ax_yp]) (by simp [axisOf, ax_yp]) c2 h2]
  rw [show putS (foldPaint M col 2) (M.app (axisOf 2)) c2 = foldPaint M col 3 by
    conv => rhs; rw [foldPaint_succ]
    rw [show col 2 = c2 from by unfold col; exact col6_2 c0 c1 c2 c3 c4 c5]]
  rw [ok_bind]
  have h3 : getS (foldPaint M col 3) (axisIdx (M.app (axisOf 3))) = 0 :=
    fresh_fold M hM col 3 (by decide)
  rw [paint_bind_ax M hM nx ny nz 0 (-1) 0 (foldPaint M col 3) 3 (by decide)
      (by simp [axisOf, ax_yn]) (by simp [axisOf, ax_yn]) (by simp [axisOf, ax_yn]) c3 h3]
  rw [show putS (foldPaint M col 3) (M.app (axisOf 3)) c3 = foldPaint M col 4 by
    conv => rhs; rw [foldPaint_succ]
    rw [show col 3 = c3 from by unfold col; exact col6_3 c0 c1 c2 c3 c4 c5]]
  have h4 : getS (foldPaint M col 4) (axisIdx (M.app (axisOf 4))) = 0 :=
    fresh_fold M hM col 4 (by decide)
  rw [paint_bind_ax M hM nx ny nz 0 0 1 (foldPaint M col 4) 4 (by decide)
      (by simp [axisOf, ax_zp]) (by simp [axisOf, ax_zp]) (by simp [axisOf, ax_zp]) c4 h4]
  rw [show putS (foldPaint M col 4) (M.app (axisOf 4)) c4 = foldPaint M col 5 by
    conv => rhs; rw [foldPaint_succ]
    rw [show col 4 = c4 from by unfold col; exact col6_4 c0 c1 c2 c3 c4 c5]]
  rw [ok_bind]
  have h5 : getS (foldPaint M col 5) (axisIdx (M.app (axisOf 5))) = 0 :=
    fresh_fold M hM col 5 (by decide)
  rw [paint_bind_ax M hM nx ny nz 0 0 (-1) (foldPaint M col 5) 5 (by decide)
      (by simp [axisOf, ax_zn]) (by simp [axisOf, ax_zn]) (by simp [axisOf, ax_zn]) c5 h5]
  rw [show putS (foldPaint M col 5) (M.app (axisOf 5)) c5 = foldPaint M col 6 by
    conv => rhs; rw [foldPaint_succ]
    rw [show col 5 = c5 from by unfold col; exact col6_5 c0 c1 c2 c3 c4 c5]]

/-- `six_paints` with sticker components written `getS`, the shape `apply_matrix` reduces to. -/
theorem six_paints_gs {α} (M : Mat) (hM : M ∈ rots) (nx ny nz c0 c1 c2 c3 c4 c5 : Int)
    (kont : Stick → Except SudoRt.Trap α) :
    (do
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) 0 0 0 0 0 0 (1 : Int) 0 0 c0
      let n1 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS t 0) (getS t 1) (getS t 2)
          (getS t 3) (getS t 4) (getS t 5) n1 0 0 c1
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS t 0) (getS t 1) (getS t 2)
          (getS t 3) (getS t 4) (getS t 5) 0 1 0 c2
      let n2 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS t 0) (getS t 1) (getS t 2)
          (getS t 3) (getS t 4) (getS t 5) 0 n2 0 c3
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS t 0) (getS t 1) (getS t 2)
          (getS t 3) (getS t 4) (getS t 5) 0 0 1 c4
      let n3 ← SudoRt.negI (1 : Int)
      let t ← Scramble.paint_cubie nx ny nz (embedMat M) (getS t 0) (getS t 1) (getS t 2)
          (getS t 3) (getS t 4) (getS t 5) 0 0 n3 c5
      kont t) =
      kont (foldPaint M (col6 c0 c1 c2 c3 c4 c5) 6) := by
  simp only [← fst_getS, ← snd1_getS, ← snd2_getS, ← snd3_getS, ← snd4_getS, ← snd5_getS]
  exact six_paints M hM nx ny nz c0 c1 c2 c3 c4 c5 kont

/-- The colors on `c`, in paint order. -/
def slotCol (c : Cubie) : Nat → Int
  | 0 => slot c ax_xp | 1 => slot c ax_xn | 2 => slot c ax_yp
  | 3 => slot c ax_yn | 4 => slot c ax_zp | 5 => slot c ax_zn | _ => 0

theorem col6_slot (c : Cubie) (k : Nat) (hk : k < 6) :
    col6 (slot c ax_xp) (slot c ax_xn) (slot c ax_yp) (slot c ax_yn) (slot c ax_zp)
        (slot c ax_zn) k = slotCol c k := by
  rcases nat_of_lt_six k hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem foldPaint_cong (M : Mat) (col col' : Nat → Int) :
    ∀ n, (∀ k, k < n → col k = col' k) → foldPaint M col n = foldPaint M col' n := by
  intro n h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldPaint, foldPaint, ih (fun k hk => h k (by omega)), h n (by omega)]

/-- Stickers of the moved cubie, as the six slots `slot c (M⁻¹ axis)`. -/
def movedStick (M : Mat) (c : Cubie) : Stick :=
  (slot c (M.transpose.app ax_xp), slot c (M.transpose.app ax_xn),
   slot c (M.transpose.app ax_yp), slot c (M.transpose.app ax_yn),
   slot c (M.transpose.app ax_zp), slot c (M.transpose.app ax_zn))

theorem getS_moved (M : Mat) (c : Cubie) (t : Nat) (ht : t < 6) :
    getS (movedStick M c) t = slot c (M.transpose.app (axisOf t)) := by
  rcases nat_of_lt_six t ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [getS, movedStick, axisOf]

theorem stick_ext (s1 s2 : Stick) (h : ∀ t, t < 6 → getS s1 t = getS s2 t) : s1 = s2 := by
  obtain ⟨a, b, c, d, e, f⟩ := s1
  obtain ⟨a', b', c', d', e', f'⟩ := s2
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  simp only [getS] at h0 h1 h2 h3 h4 h5
  subst h0; subst h1; subst h2; subst h3; subst h4; subst h5
  rfl

theorem fold_moved (M : Mat) (hM : M ∈ rots) (c : Cubie) :
    foldPaint M (slotCol c) 6 = movedStick M c := by
  apply stick_ext
  intro t ht
  rw [get_paint M hM _ 6 (Nat.le_refl _) t ht, getS_moved M c t ht]
  have ht' : t ∈ List.range 6 := List.mem_range.mpr ht
  have hsrc : srcFor M t < 6 := (route_idx_all M hM t ht').1
  simp only [hsrc, if_true]
  have hax : axisOf (srcFor M t) = M.transpose.app (axisOf t) := (route_idx_all M hM t ht').2.2
  have hcol : slotCol c (srcFor M t) = slot c (axisOf (srcFor M t)) := by
    have hk : srcFor M t < 6 := hsrc
    generalize hsk : srcFor M t = k at hk ⊢
    rcases nat_of_lt_six k hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hcol, hax]

theorem fold_col6 (M : Mat) (hM : M ∈ rots) (c : Cubie) :
    foldPaint M (col6 (slot c ax_xp) (slot c ax_xn) (slot c ax_yp) (slot c ax_yn)
      (slot c ax_zp) (slot c ax_zn)) 6 = movedStick M c := by
  rw [foldPaint_cong M _ (slotCol c) 6 (fun k hk => col6_slot c k hk), fold_moved M hM c]

/-- The emitted `apply_matrix` with a rotation from `rots` is the model's
    `map (moveCubie M.app)` on a lattice cube. -/
theorem apply_matrix_refines (M : Mat) (hM : M ∈ rots) (cube : Cube)
    (hu : ∀ c ∈ cube, Unit3 c.pos) (hfit : FitsLen cube.length) :
    Scramble.apply_matrix (embedCube cube) (embedMat M) =
      .ok (embedCube (cube.map (moveCubie M.app))) := by
  unfold Scramble.apply_matrix
  simp only [listLen_embedCube, fuelRange_eq, bind_pure_right]
  rcases Nat.eq_zero_or_pos cube.length with h0 | hpos
  · have hnil : cube = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rfl
  · rw [subI_ofNat_one _ hpos hfit, ok_bind]
    have hz : (0 : Int) = Int.ofNat 0 := rfl
    rw [hz]
    have hinit : (#[] : Array Scramble.Cubie) =
        embedCube ((cube.take 0).map (moveCubie M.app)) := by
      simp [embedCube]
    rw [hinit]
    refine chain_loop _ _ _ (fun i => embedCube ((cube.take i).map (moveCubie M.app))) 0
      (cube.length - 1) (Nat.zero_le _) ?_ _ ?_
    · intro i _ hi
      have hix : i < cube.length := by omega
      simp only
      rw [if_neg (ofNat_not_gt hi), atL_embedCube cube i hix, ok_bind]
      have hc := hu _ (List.getElem_mem hix)
      have htail : (embedCube ((cube.take (i + 1)).map (moveCubie M.app))) =
          (embedCube ((cube.take i).map (moveCubie M.app))).push
            (embedC (moveCubie M.app cube[i])) := by
        rw [take_succ_map _ _ _ hix, ← push_embedCube]
      rw [htail, embedC_move M hM]
      generalize embedCube ((cube.take i).map (moveCubie M.app)) = out
      generalize cube[i] = c at hc ⊢
      have hs := rots_small M hM
      simp only [embedC]
      rw [mul_vec_refines M hs c.pos.x c.pos.y c.pos.z hc, ok_bind]
      dsimp only
      rw [show (⟨c.pos.x, c.pos.y, c.pos.z⟩ : V3) = c.pos from rfl]
      conv =>
        lhs
        arg 1
        simp only [fst_getS, snd1_getS, snd2_getS, snd3_getS, snd4_getS, snd5_getS]
        rw [show Int.ofNat 0 = (0 : Int) from rfl]
        rw [six_paints_gs M hM (M.app c.pos).x (M.app c.pos).y (M.app c.pos).z
            (slot c ax_xp) (slot c ax_xn) (slot c ax_yp) (slot c ax_yn)
            (slot c ax_zp) (slot c ax_zn)]
      rw [fold_col6 M hM c]
      simp only [movedStick, appendL_spec, pure_eq_ok]
      dsimp only [getS]
      rw [ok_bind]
      dsimp only
      rw [asc_tail (cube.length - 1) i (FitsLen.succ_le hix hfit)]
    · simp only
      rw [show cube.length - 1 + 1 = cube.length by omega, List.take_length]
      rfl

end ScrambleV2.Link2
