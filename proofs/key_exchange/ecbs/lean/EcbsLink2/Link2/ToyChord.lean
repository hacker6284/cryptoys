/-
  Field steps of the first Toy chord (red cell after the copy).
  Each product is one kernel evaluation. The inverse is `toy_run_inv`.
-/
import EcbsLink2.Link2.ToyInv

namespace EcbsLink2.Spec

def toyY : List Nat :=
  [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0]

def toyPx : List Nat :=
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def toyPy : List Nat :=
  [1, 0, 0, 1, 1, 2, 0, 0, 2, 2, 0, 2, 2, 1, 0, 1, 2, 2, 1, 1, 0, 1, 0]

def toyRun : List Nat :=
  [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def toyInvL : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0]

def toyRise : List Nat :=
  [0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 0, 0, 0, 2, 0, 2, 1, 0, 2, 0, 0, 0, 0]

def toySlope : List Nat :=
  [2, 2, 1, 0, 1, 1, 2, 1, 1, 1, 2, 0, 1, 0, 0, 2, 1, 0, 1, 2, 1, 0, 1]

def toySlope2 : List Nat :=
  [1, 1, 2, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 2, 1, 1, 1, 1, 1, 2, 1]

def toyX3 : List Nat :=
  [2, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 2, 1, 1, 1, 1, 1, 2, 1]

def toyY3 : List Nat :=
  [2, 2, 2, 2, 1, 0, 1, 1, 0, 0, 2, 1, 0, 2, 0, 1, 2, 0, 0, 1, 2, 2, 0]

theorem toy_cube_px : fieldCube 23 15 72 (basisPeg 23 2) = toyPx := by
  set_option maxRecDepth 8192 in decide

theorem toy_cube_py : fieldCube 23 15 72 toyY = toyPy := by
  set_option maxRecDepth 8192 in decide

theorem toy_run_sub : fieldSub 23 (basisPeg 23 2) toyPx = toyRun := by
  set_option maxRecDepth 8192 in decide

theorem toy_rise_sub : fieldSub 23 (mirrorTrits toyY) toyPy = toyRise := by
  set_option maxRecDepth 8192 in decide

theorem toy_slope_mul : fieldMul 23 15 72 toyRise toyInvL = toySlope := by
  set_option maxRecDepth 8192 in decide

theorem toy_slope2_mul : fieldMul 23 15 72 toySlope toySlope = toySlope2 := by
  set_option maxRecDepth 8192 in decide

theorem toy_x3_add :
    fieldAdd 23 (fieldAdd 23 (fieldAdd 23 toySlope2 (whiteHole0 23)) toyPx) (mirrorTrits toyRun) =
      toyX3 := by
  set_option maxRecDepth 8192 in decide

theorem toy_y3_sub :
    fieldSub 23 (fieldMul 23 15 72 toySlope (fieldSub 23 toyPx toyX3)) toyPy = toyY3 := by
  set_option maxRecDepth 8192 in decide

end EcbsLink2.Spec
