/-
  4×13 grid lay/scoop (column-major and row-major) — correctness, zero sorry.
  Packet index conventions match TwoDeck SPEC §3.1–3.2.
-/
namespace TwoDeck

/-- A filled 4×13 grid. -/
abbrev Grid (α : Type _) := Fin 4 → Fin 13 → α

/-- Column-major: packet index `k` → `(row = k % 4, col = k / 4)`. -/
def cmRow (k : Fin 52) : Fin 4 := ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩
def cmCol (k : Fin 52) : Fin 13 := ⟨k.val / 4, by
  have : k.val < 52 := k.isLt; omega⟩

/-- Row-major: packet index `k` → `(row = k / 13, col = k % 13)`. -/
def rmRow (k : Fin 52) : Fin 4 := ⟨k.val / 13, by
  have : k.val < 52 := k.isLt; omega⟩
def rmCol (k : Fin 52) : Fin 13 := ⟨k.val % 13, Nat.mod_lt _ (by decide)⟩

theorem cm_index (k : Fin 52) : (cmRow k).val = k.val % 4 ∧ (cmCol k).val = k.val / 4 :=
  ⟨rfl, rfl⟩

theorem rm_index (k : Fin 52) : (rmRow k).val = k.val / 13 ∧ (rmCol k).val = k.val % 13 :=
  ⟨rfl, rfl⟩

/-- Flat index of seat `(r,c)` in column-major order. -/
def cmFlat (r : Fin 4) (c : Fin 13) : Fin 52 :=
  ⟨r.val + 4 * c.val, by have := r.isLt; have := c.isLt; omega⟩

/-- Flat index of seat `(r,c)` in row-major order. -/
def rmFlat (r : Fin 4) (c : Fin 13) : Fin 52 :=
  ⟨13 * r.val + c.val, by have := r.isLt; have := c.isLt; omega⟩

theorem cmFlat_cm (k : Fin 52) : cmFlat (cmRow k) (cmCol k) = k := by
  apply Fin.ext
  simp [cmFlat, cmRow, cmCol]
  exact Nat.mod_add_div k.val 4

theorem rmFlat_rm (k : Fin 52) : rmFlat (rmRow k) (rmCol k) = k := by
  apply Fin.ext
  simp [rmFlat, rmRow, rmCol]
  exact Nat.div_add_mod k.val 13

theorem cm_cmFlat (r : Fin 4) (c : Fin 13) :
    cmRow (cmFlat r c) = r ∧ cmCol (cmFlat r c) = c := by
  constructor <;> apply Fin.ext <;> simp [cmFlat, cmRow, cmCol]
  · exact Nat.mod_eq_of_lt r.isLt
  · -- simp reduced (r+4c)/4 via add_mul_div; finish r/4=0
    have hr : r.val < 4 := r.isLt
    -- Goal is likely r/4 + c = c or similar; use omega on vals
    omega

theorem rm_rmFlat (r : Fin 4) (c : Fin 13) :
    rmRow (rmFlat r c) = r ∧ rmCol (rmFlat r c) = c := by
  constructor <;> apply Fin.ext <;> simp [rmFlat, rmRow, rmCol]
  · have hc : c.val < 13 := c.isLt
    rw [Nat.mul_add_div (by decide : (0:Nat) < 13), Nat.div_eq_of_lt hc, Nat.add_zero]
  · have hc : c.val < 13 := c.isLt
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

/-- Lay packet column-major into a grid. -/
def layColumnMajor (deck : Fin 52 → α) : Grid α :=
  fun r c => deck (cmFlat r c)

/-- Scoop grid column-major into a packet. -/
def scoopColumnMajor (g : Grid α) : Fin 52 → α :=
  fun k => g (cmRow k) (cmCol k)

/-- Lay packet row-major into a grid. -/
def layRowMajor (deck : Fin 52 → α) : Grid α :=
  fun r c => deck (rmFlat r c)

/-- Scoop grid row-major into a packet. -/
def scoopRowMajor (g : Grid α) : Fin 52 → α :=
  fun k => g (rmRow k) (rmCol k)

theorem scoop_lay_columnMajor (deck : Fin 52 → α) :
    scoopColumnMajor (layColumnMajor deck) = deck := by
  funext k
  simp [scoopColumnMajor, layColumnMajor, cmFlat_cm]

theorem lay_scoop_columnMajor (g : Grid α) :
    layColumnMajor (scoopColumnMajor g) = g := by
  funext r c
  simp [scoopColumnMajor, layColumnMajor]
  have h := cm_cmFlat r c
  rw [h.1, h.2]

theorem scoop_lay_rowMajor (deck : Fin 52 → α) :
    scoopRowMajor (layRowMajor deck) = deck := by
  funext k
  simp [scoopRowMajor, layRowMajor, rmFlat_rm]

theorem lay_scoop_rowMajor (g : Grid α) :
    layRowMajor (scoopRowMajor g) = g := by
  funext r c
  simp [scoopRowMajor, layRowMajor]
  have h := rm_rmFlat r c
  rw [h.1, h.2]

end TwoDeck
