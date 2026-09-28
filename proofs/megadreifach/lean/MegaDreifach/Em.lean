/-
  E_m — algebraic model of the MegaDreifach block map (G2 body + F3 tail).

  Mirrors `primitives/hash/megadreifach/megadreifach.sudo` (normative):
  `face_move`, `face_turn`, `inverse`, `noon_phys`, `spin_about_up`,
  `abs_reorient`, `colour_on`, `corner_slot`, `colours_at`, `recipe_a`,
  `g2_step`, `f3_step`, `em_block`, and the Davies–Meyer step
  `h ↦ compose h (em_block h deal)`.

  Model choices:
  * positions are the M1 `Position` (Fin-valued cubie tables);
  * a grip `o` (the sudo `List<int>` of length 12, "which physical face is
    held where") is a `Grip := Fin 12 → Fin 12`, embedded with `listOf`;
  * tables are copied verbatim from the `.sudo` and read with `getD`, the
    entry reduced `mod n` so every lookup is a total `Fin n`.  On the shipped
    tables every entry is already `< n` (`tables_wf`, kernel `decide`), so
    the reduction is the identity there.

  Algebraic layer only; Link 2 refinements live in `Link2/FaceTurn.lean`
  and `Link2/EmHelpers.lean`.  Zero sorry.  No native_decide.
-/
import MegaDreifach.Group

namespace MegaDreifach.Em

open MegaDreifach

/-! ## Tables (verbatim from `megadreifach.sudo`) -/

def ftCp : List (List Nat) := [
  [4, 0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
  [7, 1, 2, 3, 0, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
  [1, 9, 2, 3, 4, 5, 6, 0, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
  [0, 2, 11, 3, 4, 5, 6, 7, 8, 1, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19],
  [0, 1, 3, 13, 4, 5, 6, 7, 8, 9, 10, 2, 11, 12, 14, 15, 16, 17, 18, 19],
  [0, 1, 2, 4, 5, 14, 6, 7, 8, 9, 10, 11, 12, 3, 13, 15, 16, 17, 18, 19],
  [0, 1, 2, 3, 4, 6, 16, 7, 8, 9, 10, 11, 12, 13, 5, 14, 15, 17, 18, 19],
  [0, 1, 2, 3, 4, 5, 7, 8, 17, 9, 10, 11, 12, 13, 14, 15, 6, 16, 18, 19],
  [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 18, 11, 12, 13, 14, 15, 16, 8, 17, 19],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 19, 13, 14, 15, 16, 17, 10, 18],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 19, 16, 17, 18, 12],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 15]]

def ftCo : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2]]

def ftEp : List (List Nat) := [
  [4, 0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [8, 1, 2, 3, 4, 0, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [0, 11, 2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [0, 1, 14, 3, 4, 5, 6, 7, 8, 9, 10, 2, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [0, 1, 2, 17, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 3, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 4, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
  [0, 1, 2, 3, 4, 5, 22, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 6, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29],
  [0, 1, 2, 3, 4, 5, 6, 9, 8, 24, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 7, 22, 23, 25, 26, 27, 28, 29],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 11, 26, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 10, 24, 25, 27, 28, 29],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 14, 28, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13, 26, 27, 29],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 17, 20, 19, 29, 21, 22, 23, 24, 25, 26, 27, 16, 28],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 22, 25, 24, 27, 26, 29, 28, 21]]

def ftEo : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def rots : List (List Nat) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  [0, 2, 3, 4, 5, 1, 7, 8, 9, 10, 6, 11],
  [0, 3, 4, 5, 1, 2, 8, 9, 10, 6, 7, 11],
  [0, 4, 5, 1, 2, 3, 9, 10, 6, 7, 8, 11],
  [0, 5, 1, 2, 3, 4, 10, 6, 7, 8, 9, 11],
  [1, 0, 5, 6, 7, 2, 3, 4, 10, 11, 8, 9],
  [1, 5, 6, 7, 2, 0, 4, 10, 11, 8, 3, 9],
  [1, 6, 7, 2, 0, 5, 10, 11, 8, 3, 4, 9],
  [1, 7, 2, 0, 5, 6, 11, 8, 3, 4, 10, 9],
  [1, 2, 0, 5, 6, 7, 8, 3, 4, 10, 11, 9],
  [2, 0, 1, 7, 8, 3, 4, 5, 6, 11, 9, 10],
  [2, 1, 7, 8, 3, 0, 5, 6, 11, 9, 4, 10],
  [2, 7, 8, 3, 0, 1, 6, 11, 9, 4, 5, 10],
  [2, 8, 3, 0, 1, 7, 11, 9, 4, 5, 6, 10],
  [2, 3, 0, 1, 7, 8, 9, 4, 5, 6, 11, 10],
  [3, 0, 2, 8, 9, 4, 5, 1, 7, 11, 10, 6],
  [3, 2, 8, 9, 4, 0, 1, 7, 11, 10, 5, 6],
  [3, 8, 9, 4, 0, 2, 7, 11, 10, 5, 1, 6],
  [3, 9, 4, 0, 2, 8, 11, 10, 5, 1, 7, 6],
  [3, 4, 0, 2, 8, 9, 10, 5, 1, 7, 11, 6],
  [4, 0, 3, 9, 10, 5, 1, 2, 8, 11, 6, 7],
  [4, 3, 9, 10, 5, 0, 2, 8, 11, 6, 1, 7],
  [4, 9, 10, 5, 0, 3, 8, 11, 6, 1, 2, 7],
  [4, 10, 5, 0, 3, 9, 11, 6, 1, 2, 8, 7],
  [4, 5, 0, 3, 9, 10, 6, 1, 2, 8, 11, 7],
  [5, 0, 4, 10, 6, 1, 2, 3, 9, 11, 7, 8],
  [5, 4, 10, 6, 1, 0, 3, 9, 11, 7, 2, 8],
  [5, 10, 6, 1, 0, 4, 9, 11, 7, 2, 3, 8],
  [5, 6, 1, 0, 4, 10, 11, 7, 2, 3, 9, 8],
  [5, 1, 0, 4, 10, 6, 7, 2, 3, 9, 11, 8],
  [6, 1, 5, 10, 11, 7, 2, 0, 4, 9, 8, 3],
  [6, 5, 10, 11, 7, 1, 0, 4, 9, 8, 2, 3],
  [6, 10, 11, 7, 1, 5, 4, 9, 8, 2, 0, 3],
  [6, 11, 7, 1, 5, 10, 9, 8, 2, 0, 4, 3],
  [6, 7, 1, 5, 10, 11, 8, 2, 0, 4, 9, 3],
  [7, 1, 6, 11, 8, 2, 0, 5, 10, 9, 3, 4],
  [7, 6, 11, 8, 2, 1, 5, 10, 9, 3, 0, 4],
  [7, 11, 8, 2, 1, 6, 10, 9, 3, 0, 5, 4],
  [7, 8, 2, 1, 6, 11, 9, 3, 0, 5, 10, 4],
  [7, 2, 1, 6, 11, 8, 3, 0, 5, 10, 9, 4],
  [8, 2, 7, 11, 9, 3, 0, 1, 6, 10, 4, 5],
  [8, 7, 11, 9, 3, 2, 1, 6, 10, 4, 0, 5],
  [8, 11, 9, 3, 2, 7, 6, 10, 4, 0, 1, 5],
  [8, 9, 3, 2, 7, 11, 10, 4, 0, 1, 6, 5],
  [8, 3, 2, 7, 11, 9, 4, 0, 1, 6, 10, 5],
  [9, 3, 8, 11, 10, 4, 0, 2, 7, 6, 5, 1],
  [9, 8, 11, 10, 4, 3, 2, 7, 6, 5, 0, 1],
  [9, 11, 10, 4, 3, 8, 7, 6, 5, 0, 2, 1],
  [9, 10, 4, 3, 8, 11, 6, 5, 0, 2, 7, 1],
  [9, 4, 3, 8, 11, 10, 5, 0, 2, 7, 6, 1],
  [10, 4, 9, 11, 6, 5, 0, 3, 8, 7, 1, 2],
  [10, 9, 11, 6, 5, 4, 3, 8, 7, 1, 0, 2],
  [10, 11, 6, 5, 4, 9, 8, 7, 1, 0, 3, 2],
  [10, 6, 5, 4, 9, 11, 7, 1, 0, 3, 8, 2],
  [10, 5, 4, 9, 11, 6, 1, 0, 3, 8, 7, 2],
  [11, 6, 10, 9, 8, 7, 1, 5, 4, 3, 2, 0],
  [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
  [11, 9, 8, 7, 6, 10, 4, 3, 2, 1, 5, 0],
  [11, 8, 7, 6, 10, 9, 3, 2, 1, 5, 4, 0],
  [11, 7, 6, 10, 9, 8, 2, 1, 5, 4, 3, 0]]

def nbrsTab : List (List Nat) := [
  [1, 2, 3, 4, 5],
  [0, 5, 6, 7, 2],
  [0, 1, 7, 8, 3],
  [0, 2, 8, 9, 4],
  [0, 3, 9, 10, 5],
  [0, 4, 10, 6, 1],
  [1, 5, 10, 11, 7],
  [1, 6, 11, 8, 2],
  [2, 7, 11, 9, 3],
  [3, 8, 11, 10, 4],
  [4, 9, 11, 6, 5],
  [6, 10, 9, 8, 7]]

def oppTab : List Nat := [11, 9, 10, 6, 7, 8, 3, 4, 5, 1, 2, 0]

def cornerFacesTab : List (List Nat) := [
  [0, 1, 2], [0, 2, 3], [0, 3, 4], [0, 4, 5], [0, 5, 1],
  [1, 5, 6], [1, 6, 7], [1, 7, 2], [2, 7, 8], [2, 8, 3],
  [3, 8, 9], [3, 9, 4], [4, 9, 10], [4, 10, 5], [5, 10, 6],
  [6, 10, 11], [6, 11, 7], [7, 11, 8], [8, 11, 9], [9, 11, 10]]

/-- Every table has the SPEC shape and every entry is in range. -/
theorem tables_wf :
    ftCp.length = 12 ∧ ftCo.length = 12 ∧ ftEp.length = 12 ∧ ftEo.length = 12 ∧
    (∀ r ∈ ftCp, r.length = 20 ∧ ∀ x ∈ r, x < 20) ∧
    (∀ r ∈ ftCo, r.length = 20 ∧ ∀ x ∈ r, x < 3) ∧
    (∀ r ∈ ftEp, r.length = 30 ∧ ∀ x ∈ r, x < 30) ∧
    (∀ r ∈ ftEo, r.length = 30 ∧ ∀ x ∈ r, x < 2) ∧
    rots.length = 60 ∧ (∀ r ∈ rots, r.length = 12 ∧ ∀ x ∈ r, x < 12) ∧
    nbrsTab.length = 12 ∧ (∀ r ∈ nbrsTab, r.length = 5 ∧ ∀ x ∈ r, x < 12) ∧
    oppTab.length = 12 ∧ (∀ x ∈ oppTab, x < 12) ∧
    cornerFacesTab.length = 20 ∧ (∀ r ∈ cornerFacesTab, r.length = 3 ∧ ∀ x ∈ r, x < 12) := by
  decide

/-! ## Total table reads -/

/-- `row[i]` reduced mod `n` (total; the identity on in-range tables). -/
def rd (row : List Nat) (n : Nat) (hn : 0 < n) (i : Nat) : Fin n :=
  ⟨row.getD i 0 % n, Nat.mod_lt _ hn⟩

/-- Position whose four cubie tables are the given lists. -/
def posOfLists (cp co ep eo : List Nat) : Position where
  cp := fun s => rd cp 20 (by decide) s.val
  co := fun s => rd co 3 (by decide) s.val
  ep := fun s => rd ep 30 (by decide) s.val
  eo := fun s => rd eo 2 (by decide) s.val

/-! ## Face turns -/

/-- `face_move f`: the clockwise quarter-fifth turn of face `f`. -/
def faceMove (f : Fin 12) : Position :=
  posOfLists (ftCp.getD f.val []) (ftCo.getD f.val []) (ftEp.getD f.val []) (ftEo.getD f.val [])

/-- `n`-fold left multiplication by `T` (the emitted `out = compose(t, out)` loop). -/
def leftIter (T : Position) : Nat → Position → Position
  | 0, g => g
  | n + 1, g => compose T (leftIter T n g)

/-- `face_turn g f amount`: turn face `f` by `amount mod 5` fifths. -/
def faceTurn (g : Position) (f : Fin 12) (amount : Nat) : Position :=
  leftIter (faceMove f) (amount % 5) g

/-! ## Inverse -/

/-- Emitted `inv[p[s]] = s` loop over `s = 0 .. n-1`, starting from zeros
    (last writer wins; on a permutation this is the inverse permutation). -/
def invList (p : List Nat) (n : Nat) : List Nat :=
  (List.range n).foldl (fun acc s => acc.set (p.getD s 0) s) (List.replicate n 0)

/-- Algebraic inverse permutation of a `Fin n` table, via `invList`. -/
def permInv {n : Nat} (hn : 0 < n) (p : Fin n → Fin n) : Fin n → Fin n :=
  fun t => rd (invList (listOf p) n) n hn t.val

/-- `inverse g` (SPEC): M2 `inverseWith` at the emitted inverse permutations. -/
def inverse (g : Position) : Position :=
  inverseWith g (permInv (by decide) g.cp) (permInv (by decide) g.ep)

/-! ## Faces, grips, reorientation -/

/-- A grip: `o h` is the physical face currently in the held slot `h`. -/
abbrev Grip := Fin 12 → Fin 12

def gripId : Grip := id

/-- `face_nbrs f` as a list (clockwise ring of 5 faces). -/
def nbrs (f : Fin 12) : List (Fin 12) :=
  (List.range 5).map (fun i => rd (nbrsTab.getD f.val []) 12 (by decide) i)

def nbr (f : Fin 12) (i : Nat) : Fin 12 := rd (nbrsTab.getD f.val []) 12 (by decide) i

def opp (f : Fin 12) : Fin 12 := rd oppTab 12 (by decide) f.val

/-- Core of `noon_phys`: only the Up and Front entries of the grip are read. -/
def noonCore (phys up front : Fin 12) : Fin 12 :=
  if phys = up then front
  else if up ∈ nbrs phys then up
  else ((nbrs phys).find? (fun x => decide (x ∈ nbrs up))).getD (nbr phys 0)

/-- `noon_phys phys o`: the physical face at "noon" when `phys` faces the solver. -/
def noonPhys (phys : Fin 12) (o : Grip) : Fin 12 := noonCore phys (o 0) (o 1)

/-- Index of `x` in a 5-ring (`5` if absent). -/
def ringIdx (ring : List (Fin 12)) (x : Fin 12) : Nat := ring.findIdx (· == x)

/-- Physical relabelling of `spin_about_up` (up ring `+k`, down ring `-k`). -/
def spinPhys (up : Fin 12) (k : Nat) : Fin 12 → Fin 12 := fun x =>
  let down := opp up
  if x = up then up
  else if x = down then down
  else if x ∈ nbrs up then nbr up ((ringIdx (nbrs up) x + k) % 5)
  else if x ∈ nbrs down then nbr down ((ringIdx (nbrs down) x + 5 - k) % 5)
  else x

/-- `spin_about_up o k`: rotate the grip about its Up face by `k` fifths. -/
def spinAboutUp (o : Grip) (k : Nat) : Grip :=
  if k % 5 = 0 then o else fun h => spinPhys (o 0) (k % 5) (o h)

/-- Row `s` of `rots_flat` as a grip. -/
def rotAt (s : Nat) : Grip := fun h => rd (rots.getD s []) 12 (by decide) h.val

/-- `abs_reorient c1 c2`: first rotation with `r[0] = c1`, `r[1] = c2`.
    `none` is the emitted `assert false`. -/
def absReorient? (c1 c2 : Fin 12) : Option Grip :=
  ((List.range 60).find? (fun s => decide (rotAt s 0 = c1 ∧ rotAt s 1 = c2))).map rotAt

/-- Total version (identity grip on the trap branch). -/
def absReorient (c1 c2 : Fin 12) : Grip := (absReorient? c1 c2).getD gripId

/-! ## Corner colours -/

def cornerFace (slot : Nat) (j : Nat) : Fin 12 :=
  rd (cornerFacesTab.getD slot []) 12 (by decide) j

/-- `colour_on`: colour seen on `face` of a corner at faces `(f0,f1,f2)`
    holding cubie colours `(c0,c1,c2)` with twist `ori`. -/
def colourOn (face f1 f2 c0 c1 c2 : Fin 12) (ori : Fin 3) : Fin 12 :=
  let loc : Nat := if face = f2 then 2 else if face = f1 then 1 else 0
  let k := (loc + 3 - ori.val) % 3
  if k = 0 then c0 else if k = 1 then c1 else c2

/-- `corner_slot a b c`: rotate the triple so the least face is first, then
    look it up in `corner_faces`. `none` is the emitted `assert false`. -/
def cornerSlot? (a b c : Fin 12) : Option (Fin 20) :=
  let t : Fin 12 × Fin 12 × Fin 12 :=
    if c < a ∧ c < b then (c, a, b)
    else if b < a ∧ b < c then (b, c, a) else (a, b, c)
  ((List.range 20).find? (fun s =>
      decide (cornerFace s 0 = t.1 ∧ cornerFace s 1 = t.2.1 ∧ cornerFace s 2 = t.2.2))).bind
    (fun s => if h : s < 20 then some ⟨s, h⟩ else none)

def cornerSlot (a b c : Fin 12) : Fin 20 := (cornerSlot? a b c).getD 0

/-- `colours_at g a b c`: colours on faces `a`, `b` of the corner `{a,b,c}`. -/
def coloursAt (g : Position) (a b c : Fin 12) : Fin 12 × Fin 12 :=
  let slot := cornerSlot a b c
  let cubie := g.cp slot
  let ori := g.co slot
  let f1 := cornerFace slot.val 1
  let f2 := cornerFace slot.val 2
  let c0 := cornerFace cubie.val 0
  let c1 := cornerFace cubie.val 1
  let c2 := cornerFace cubie.val 2
  (colourOn a f1 f2 c0 c1 c2 ori, colourOn b f1 f2 c0 c1 c2 ori)

/-- `recipe_a g phys o`: re-grip from the colours around `phys`'s noon corner. -/
def recipeA (g : Position) (phys : Fin 12) (o : Grip) : Grip :=
  let noon := noonPhys phys o
  let ni := (List.range 5).foldl (fun acc i => if nbr phys i = noon then i else acc) 0
  let nextCw := nbr phys ((ni + 1) % 5)
  let cc := coloursAt g phys noon nextCw
  absReorient cc.1 cc.2

/-! ## Block map -/

/-- `g2_step (g, o) card` for a card id. -/
def g2Step (st : Position × Grip) (card : Nat) : Position × Grip :=
  let g := st.1
  let o := st.2
  let rank := card / 4
  let amt := card % 4 + 1
  let (g1, oW, held) :=
    if h : rank < 12 then (faceTurn g (o ⟨rank, h⟩) amt, o, (⟨rank, h⟩ : Fin 12))
    else (faceTurn g (o 0) ((5 - amt) % 5), spinAboutUp o amt, (0 : Fin 12))
  let noon := noonPhys (oW held) oW
  let g2 := if noon ≠ oW held then faceTurn g1 noon 1 else g1
  let g3 := faceTurn g2 (oW 1) 1
  (g3, recipeA g3 (oW held) oW)

/-- `f3_step (g, o)`: blank round, turn Up then re-grip. -/
def f3Step (st : Position × Grip) : Position × Grip :=
  let g := faceTurn st.1 (st.2 0) 1
  (g, recipeA g (st.2 0) st.2)

def f3Iter : Nat → Position × Grip → Position × Grip
  | 0, st => st
  | n + 1, st => f3Iter n (f3Step st)

/-- `em_block h deal`: 52 G2 steps from the identity grip, then `f3_t = 12` F3 rounds. -/
def emBlock (h : Position) (deal : List Nat) : Position :=
  (f3Iter f3T ((deal.take 52).foldl g2Step (h, gripId))).1

/-- Davies–Meyer chaining step: `h' = compose h (E_m h deal)`. -/
def dmStep (h : Position) (deal : List Nat) : Position := compose h (emBlock h deal)

/-- `iv_cook12`: fold of `face_turn g f 1` over `f = 0..11` from identity. -/
def ivCook12 : Position :=
  (List.range 12).foldl (fun g f => if hf : f < 12 then faceTurn g ⟨f, hf⟩ 1 else g) identity

end MegaDreifach.Em
