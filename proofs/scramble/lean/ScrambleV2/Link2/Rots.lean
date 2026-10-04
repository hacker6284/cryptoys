/-
  LINK 2. The 24 rotations of the cube (signed permutation matrices with determinant
  1) and the finite facts about them that the refinement and the invariant use.
  Proof-only; not part of the model (the model's Rule B matrix is built from the
  centers, `Spec.rotateTo`).
-/
import ScrambleV2.Link2.Embed

namespace ScrambleV2.Link2

/-- The 24 signed permutation matrices with determinant 1, by rows. -/
def rots : List Mat :=
  [⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩,
   ⟨⟨1, 0, 0⟩, ⟨0, -1, 0⟩, ⟨0, 0, -1⟩⟩,
   ⟨⟨-1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, -1⟩⟩,
   ⟨⟨-1, 0, 0⟩, ⟨0, -1, 0⟩, ⟨0, 0, 1⟩⟩,
   ⟨⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, -1, 0⟩⟩,
   ⟨⟨1, 0, 0⟩, ⟨0, 0, -1⟩, ⟨0, 1, 0⟩⟩,
   ⟨⟨-1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, 1, 0⟩⟩,
   ⟨⟨-1, 0, 0⟩, ⟨0, 0, -1⟩, ⟨0, -1, 0⟩⟩,
   ⟨⟨0, 1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, -1⟩⟩,
   ⟨⟨0, 1, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, 1⟩⟩,
   ⟨⟨0, -1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, 1⟩⟩,
   ⟨⟨0, -1, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, -1⟩⟩,
   ⟨⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 0⟩⟩,
   ⟨⟨0, 1, 0⟩, ⟨0, 0, -1⟩, ⟨-1, 0, 0⟩⟩,
   ⟨⟨0, -1, 0⟩, ⟨0, 0, 1⟩, ⟨-1, 0, 0⟩⟩,
   ⟨⟨0, -1, 0⟩, ⟨0, 0, -1⟩, ⟨1, 0, 0⟩⟩,
   ⟨⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩,
   ⟨⟨0, 0, 1⟩, ⟨-1, 0, 0⟩, ⟨0, -1, 0⟩⟩,
   ⟨⟨0, 0, -1⟩, ⟨1, 0, 0⟩, ⟨0, -1, 0⟩⟩,
   ⟨⟨0, 0, -1⟩, ⟨-1, 0, 0⟩, ⟨0, 1, 0⟩⟩,
   ⟨⟨0, 0, 1⟩, ⟨0, 1, 0⟩, ⟨-1, 0, 0⟩⟩,
   ⟨⟨0, 0, 1⟩, ⟨0, -1, 0⟩, ⟨1, 0, 0⟩⟩,
   ⟨⟨0, 0, -1⟩, ⟨0, 1, 0⟩, ⟨1, 0, 0⟩⟩,
   ⟨⟨0, 0, -1⟩, ⟨0, -1, 0⟩, ⟨-1, 0, 0⟩⟩]

theorem rots_length : rots.length = 24 := rfl

/-- The 27 points of `{-1, 0, 1}³`. -/
def cube27 : List V3 :=
  trits.flatMap fun x => trits.flatMap fun y => trits.map fun z => ⟨x, y, z⟩

theorem mem_cube27 (v : V3) (h : Unit3 v) : v ∈ cube27 := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  have hx : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  have hy : y = -1 ∨ y = 0 ∨ y = 1 := by omega
  have hz : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> decide

theorem unit_of_mem_cube27 (v : V3) (h : v ∈ cube27) : Unit3 v := by
  unfold Unit3; revert v h; decide

def _root_.ScrambleV2.Mat.transpose (m : Mat) : Mat :=
  ⟨⟨m.r0.x, m.r1.x, m.r2.x⟩, ⟨m.r0.y, m.r1.y, m.r2.y⟩, ⟨m.r0.z, m.r1.z, m.r2.z⟩⟩

def _root_.ScrambleV2.Mat.mul (a b : Mat) : Mat :=
  ⟨⟨a.r0.dot ⟨b.r0.x, b.r1.x, b.r2.x⟩, a.r0.dot ⟨b.r0.y, b.r1.y, b.r2.y⟩,
     a.r0.dot ⟨b.r0.z, b.r1.z, b.r2.z⟩⟩,
   ⟨a.r1.dot ⟨b.r0.x, b.r1.x, b.r2.x⟩, a.r1.dot ⟨b.r0.y, b.r1.y, b.r2.y⟩,
     a.r1.dot ⟨b.r0.z, b.r1.z, b.r2.z⟩⟩,
   ⟨a.r2.dot ⟨b.r0.x, b.r1.x, b.r2.x⟩, a.r2.dot ⟨b.r0.y, b.r1.y, b.r2.y⟩,
     a.r2.dot ⟨b.r0.z, b.r1.z, b.r2.z⟩⟩⟩

theorem _root_.ScrambleV2.Mat.app_mul (a b : Mat) (v : V3) : (a.mul b).app v = a.app (b.app v) := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6⟩, ⟨a7, a8, a9⟩⟩ := a
  obtain ⟨⟨b1, b2, b3⟩, ⟨b4, b5, b6⟩, ⟨b7, b8, b9⟩⟩ := b
  obtain ⟨x, y, z⟩ := v
  simp only [Mat.mul, Mat.app, V3.dot, V3.mk.injEq, Int.add_mul, Int.mul_add, Int.mul_assoc]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem rots_mul_all : ∀ a ∈ rots, ∀ b ∈ rots, a.mul b ∈ rots := by decide

theorem rots_mul (a b : Mat) (ha : a ∈ rots) (hb : b ∈ rots) : a.mul b ∈ rots :=
  rots_mul_all a ha b hb

theorem rots_transpose_all : ∀ m ∈ rots, m.transpose ∈ rots := by decide

theorem rots_transpose (m : Mat) (hm : m ∈ rots) : m.transpose ∈ rots := rots_transpose_all m hm

theorem rots_transpose_mul_all :
    ∀ m ∈ rots, m.transpose.mul m = ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ := by decide

theorem rots_transpose_mul (m : Mat) (hm : m ∈ rots) :
    m.transpose.mul m = ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ := rots_transpose_mul_all m hm

theorem _root_.ScrambleV2.Mat.app_id (v : V3) : Mat.app ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ v = v := by
  obtain ⟨x, y, z⟩ := v
  simp only [Mat.app, V3.dot, V3.mk.injEq]; omega

/-- Every rotation is undone by its transpose. -/
theorem rots_transpose_app (m : Mat) (hm : m ∈ rots) (v : V3) :
    m.transpose.app (m.app v) = v := by
  rw [← Mat.app_mul, rots_transpose_mul m hm, Mat.app_id]

theorem rots_mul_transpose_all :
    ∀ m ∈ rots, m.mul m.transpose = ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ := by decide

theorem rots_app_transpose (m : Mat) (hm : m ∈ rots) (v : V3) :
    m.app (m.transpose.app v) = v := by
  rw [← Mat.app_mul, rots_mul_transpose_all m hm, Mat.app_id]

theorem rots_inj (m : Mat) (hm : m ∈ rots) (v w : V3) (h : m.app v = m.app w) : v = w := by
  rw [← rots_transpose_app m hm v, ← rots_transpose_app m hm w, h]

theorem rots_app_cube27_all : ∀ m ∈ rots, ∀ v ∈ cube27, m.app v ∈ cube27 := by decide

theorem rots_app_cube27 (m : Mat) (hm : m ∈ rots) (v : V3) (hv : v ∈ cube27) :
    m.app v ∈ cube27 := rots_app_cube27_all m hm v hv

theorem rots_unit (m : Mat) (hm : m ∈ rots) (v : V3) (hv : Unit3 v) : Unit3 (m.app v) :=
  unit_of_mem_cube27 _ (rots_app_cube27 m hm v (mem_cube27 v hv))

theorem rots_axes_all : ∀ m ∈ rots, ∀ a ∈ axes, m.app a ∈ axes := by decide

theorem rots_axes (m : Mat) (hm : m ∈ rots) (a : V3) (ha : a ∈ axes) : m.app a ∈ axes :=
  rots_axes_all m hm a ha

/-- Entries in `{-1, 0, 1}`. -/
def SmallMat (m : Mat) : Prop := Unit3 m.r0 ∧ Unit3 m.r1 ∧ Unit3 m.r2

theorem rots_small_all : ∀ m ∈ rots, SmallMat m := by
  unfold SmallMat Unit3; decide

theorem rots_small (m : Mat) (hm : m ∈ rots) : SmallMat m := rots_small_all m hm

end ScrambleV2.Link2
