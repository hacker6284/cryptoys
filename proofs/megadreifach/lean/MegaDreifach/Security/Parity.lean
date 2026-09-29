/-
  SECURITY support (closes part of M3).  Every reachable MegaDreifach
  chaining value is legal (`isLegal`: even corner/edge permutations, corner
  twist sum ≡ 0 mod 3, edge flip sum ≡ 0 mod 2).

  Method: adjacent transpositions flip inversion parity and keep sums
  (`swapAdj_*`); each concrete face move's corner/edge permutation is an
  explicit EVEN product of adjacent transpositions (`swC`, `swE`, checked by
  kernel `decide`); reachable positions are words in face moves (`Word`),
  closed under `compose`; so all of them are legal (`word_isLegal`,
  `isLegal_chR`).

  Grip-rule status: INDEPENDENT of the grip rule.  The statement holds for
  any block map that left-multiplies the position by face moves, whichever
  faces the grips pick; no proof uses the corner-only read.  If E_m changes,
  repair `word_g2Step`, `word_f3Iter`, `word_foldl_g2`, `word_emBlock` (and
  `CornerDriven.g2Step_fst`), which unfold the current `Em.g2Step` /
  `Em.f3Step` / `Em.emBlock`.  `word_dmStep` needs the DM feed-forward
  `dmStep h d = compose h (emBlock h d)`.  The swap tables `swC` / `swE` and
  `faceMove_*` need repair only if the face-move tables change.

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.CornerDriven

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-! ## Adjacent swaps -/

/-- Swap the entries at positions `i` and `i+1` (identity if out of range). -/
def swapAdj {α : Type} : List α → Nat → List α
  | a :: b :: r, 0 => b :: a :: r
  | a :: r, n + 1 => a :: swapAdj r n
  | l, _ => l

def applySwaps {α : Type} (l : List α) : List Nat → List α
  | [] => l
  | i :: is => applySwaps (swapAdj l i) is

theorem map_swapAdj {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (swapAdj l i).map f = swapAdj (l.map f) i
  | [], _ => rfl
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [swapAdj]
  | _ :: _ :: _, 0 => rfl
  | a :: b :: r, n + 1 => by
      show f a :: (swapAdj (b :: r) n).map f = f a :: swapAdj ((b :: r).map f) n
      rw [map_swapAdj f (b :: r) n]

theorem map_applySwaps {α β : Type} (f : α → β) :
    ∀ (sw : List Nat) (l : List α), (applySwaps l sw).map f = applySwaps (l.map f) sw
  | [], _ => rfl
  | i :: is, l => by
      simp only [applySwaps]
      rw [map_applySwaps f is, map_swapAdj]

theorem swapAdj_length {α : Type} : ∀ (l : List α) (i : Nat), (swapAdj l i).length = l.length
  | [], _ => rfl
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [swapAdj]
  | _ :: _ :: _, 0 => rfl
  | a :: b :: r, n + 1 => by
      show (a :: swapAdj (b :: r) n).length = _
      simp only [List.length_cons, swapAdj_length (b :: r) n]

theorem swapAdj_perm {α : Type} : ∀ (l : List α) (i : Nat), (swapAdj l i).Perm l
  | [], _ => List.Perm.refl _
  | [_], 0 => List.Perm.refl _
  | [_], _ + 1 => by simp [swapAdj]
  | a :: b :: r, 0 => List.Perm.swap a b r
  | a :: b :: r, n + 1 => by
      show (a :: swapAdj (b :: r) n).Perm (a :: b :: r)
      exact List.Perm.cons a (swapAdj_perm (b :: r) n)

theorem swapAdj_nodup {α : Type} (l : List α) (i : Nat) (h : l.Nodup) : (swapAdj l i).Nodup :=
  (swapAdj_perm l i).nodup_iff.mpr h

theorem countP_swapAdj {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat), (swapAdj l i).countP p = l.countP p
  | l, i => (swapAdj_perm l i).countP_eq p

theorem filter_length_swapAdj (p : Nat → Bool) (l : List Nat) (i : Nat) :
    ((swapAdj l i).filter p).length = (l.filter p).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, countP_swapAdj]

theorem sumNats_cons (x : Nat) (xs : List Nat) : sumNats (x :: xs) = x + sumNats xs := by
  have := sumNats_append [x] xs
  simp only [List.singleton_append] at this
  rw [this]; rfl

theorem sumNats_swapAdj : ∀ (l : List Nat) (i : Nat), sumNats (swapAdj l i) = sumNats l
  | [], _ => rfl
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [swapAdj]
  | a :: b :: r, 0 => by
      show sumNats (b :: a :: r) = sumNats (a :: b :: r)
      rw [sumNats_cons, sumNats_cons, sumNats_cons, sumNats_cons]; omega
  | a :: b :: r, n + 1 => by
      show sumNats (a :: swapAdj (b :: r) n) = _
      rw [sumNats_cons, sumNats_cons a, sumNats_swapAdj (b :: r) n]

/-- An adjacent swap of two distinct entries flips the inversion parity. -/
theorem inversions_swapAdj : ∀ (l : List Nat) (i : Nat), l.Nodup → i + 1 < l.length →
    (inversions (swapAdj l i) + 1) % 2 = inversions l % 2
  | [], _, _, hi => by simp at hi
  | [_], _, _, hi => by simp at hi
  | a :: b :: r, 0, hnd, _ => by
      have hab : a ≠ b := by
        intro h; subst h; simp at hnd
      show (inversions (b :: a :: r) + 1) % 2 = inversions (a :: b :: r) % 2
      simp only [inversions, List.filter_cons]
      by_cases h1 : a > b
      · have h2 : ¬ b > a := by omega
        simp [h1, h2]; omega
      · have h2 : b > a := by omega
        simp [h1, h2]; omega
  | a :: b :: r, n + 1, hnd, hi => by
      show (inversions (a :: swapAdj (b :: r) n) + 1) % 2 = inversions (a :: b :: r) % 2
      have hnd' : (b :: r).Nodup := (List.nodup_cons.mp hnd).2
      have ih := inversions_swapAdj (b :: r) n hnd' (by simp at hi ⊢; omega)
      have hf := filter_length_swapAdj (fun y => decide (a > y)) (b :: r) n
      rw [inversions, hf]
      show _ = ((List.filter (fun y => decide (a > y)) (b :: r)).length + inversions (b :: r)) % 2
      omega

theorem applySwaps_length {α : Type} : ∀ (sw : List Nat) (l : List α),
    (applySwaps l sw).length = l.length
  | [], _ => rfl
  | i :: is, l => by simp only [applySwaps]; rw [applySwaps_length is, swapAdj_length]

theorem applySwaps_nodup {α : Type} : ∀ (sw : List Nat) (l : List α), l.Nodup →
    (applySwaps l sw).Nodup
  | [], _, h => h
  | i :: is, l, h => applySwaps_nodup is _ (swapAdj_nodup l i h)

theorem sumNats_applySwaps : ∀ (sw : List Nat) (l : List Nat),
    sumNats (applySwaps l sw) = sumNats l
  | [], _ => rfl
  | i :: is, l => by simp only [applySwaps]; rw [sumNats_applySwaps is, sumNats_swapAdj]

theorem permParity_applySwaps : ∀ (sw : List Nat) (l : List Nat), l.Nodup →
    (∀ i ∈ sw, i + 1 < l.length) →
    permParity (applySwaps l sw) = (permParity l + sw.length) % 2
  | [], l, _, _ => by simp [applySwaps, permParity]
  | i :: is, l, hnd, hi => by
      simp only [applySwaps]
      have hi0 := hi i (List.mem_cons_self _ _)
      have hrest : ∀ j ∈ is, j + 1 < (swapAdj l i).length := by
        intro j hj; rw [swapAdj_length]; exact hi j (List.mem_cons_of_mem _ hj)
      rw [permParity_applySwaps is _ (swapAdj_nodup l i hnd) hrest]
      have hflip := inversions_swapAdj l i hnd hi0
      unfold permParity
      simp only [List.length_cons]
      omega

/-! ## `listOf` of a composition -/

theorem listOf_comp {n : Nat} (f σ : Fin n → Fin n) :
    listOf (f ∘ σ) = (listOf σ).map (fun j => (listOf f).getD j 0) := by
  apply List.ext_getElem
  · simp [listOf]
  · intro i h1 h2
    have hi : i < n := by simp [listOf] at h1; exact h1
    simp [listOf, hi]

theorem range_map_listOf {n : Nat} (f : Fin n → Fin n) :
    (List.range n).map (fun j => (listOf f).getD j 0) = listOf f := by
  apply List.ext_getElem
  · simp [listOf]
  · intro i h1 h2
    have hi : i < n := by simp at h1; exact h1
    simp [listOf, hi]

theorem range_map_listOfOri {n m : Nat} (f : Fin n → Fin m) :
    (List.range n).map (fun j => (listOfOri f).getD j 0) = listOfOri f := by
  apply List.ext_getElem
  · simp [listOfOri]
  · intro i h1 h2
    have hi : i < n := by simp at h1; exact h1
    simp [listOfOri, hi]

theorem listOf_nodup {n : Nat} (f : Fin n → Fin n) (hf : Injective f) : (listOf f).Nodup :=
  (permNWf_listOf f hf).nodup

/-- Orientation of a composition, as a list. -/
theorem listOfOri_compose {n m : Nat} (σ : Fin n → Fin n) (a b : Fin n → Fin m) :
    listOfOri (fun s => a (σ s) + b s) =
      List.zipWith (fun x y => (x + y) % m)
        ((listOf σ).map (fun j => (listOfOri a).getD j 0)) (listOfOri b) := by
  apply List.ext_getElem
  · simp [listOfOri, listOf]
  · intro i h1 h2
    have hi : i < n := by simp [listOfOri] at h1; exact h1
    simp [listOfOri, listOf, hi, Fin.val_add]

theorem sumNats_zipWith_mod (m : Nat) : ∀ (xs ys : List Nat), xs.length = ys.length →
    sumNats (List.zipWith (fun x y => (x + y) % m) xs ys) % m = (sumNats xs + sumNats ys) % m
  | [], [], _ => by simp [sumNats]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.zipWith_cons_cons]
      rw [sumNats_cons, sumNats_cons, sumNats_cons]
      have ih := sumNats_zipWith_mod m xs ys (by simpa using h)
      rw [Nat.add_mod, ih, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega

/-! ## Face moves are explicit even products of adjacent swaps -/

/-- Adjacent-swap words for the 12 corner face permutations. -/
def swC : List (List Nat) := [
  [3, 2, 1, 0],
  [6, 5, 4, 3, 2, 1, 0, 1, 2, 3],
  [0, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6],
  [1, 10, 9, 8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7, 8],
  [2, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 4, 5, 6, 7, 8, 9, 10],
  [3, 4, 13, 12, 11, 10, 9, 8, 7, 6, 5, 6, 7, 8, 9, 10, 11, 12],
  [5, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 7, 8, 9, 10, 11, 12, 13],
  [6, 7, 16, 15, 14, 13, 12, 11, 10, 9, 8, 9, 10, 11, 12, 13, 14, 15],
  [8, 9, 17, 16, 15, 14, 13, 12, 11, 10, 11, 12, 13, 14, 15, 16],
  [10, 11, 18, 17, 16, 15, 14, 13, 12, 13, 14, 15, 16, 17],
  [12, 13, 14, 18, 17, 16, 15, 16, 17, 18],
  [15, 16, 17, 18]]

/-- Adjacent-swap words for the 12 edge face permutations. -/
def swE : List (List Nat) := [
  [3, 2, 1, 0],
  [7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4],
  [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7],
  [13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  [16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
  [4, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
  [21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18],
  [8, 7, 8, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21],
  [11, 10, 11, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23],
  [14, 13, 14, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25],
  [17, 16, 17, 19, 18, 19, 28, 27, 26, 25, 24, 23, 22, 21, 20, 21, 22, 23, 24, 25, 26, 27],
  [22, 21, 22, 24, 23, 24, 26, 25, 26, 28, 27, 28]]

theorem faceMove_cp_swaps : ∀ f : Fin 12,
    listOf (Em.faceMove f).cp = applySwaps (List.range 20) (swC.getD f.val []) := by decide

theorem faceMove_ep_swaps : ∀ f : Fin 12,
    listOf (Em.faceMove f).ep = applySwaps (List.range 30) (swE.getD f.val []) := by decide

theorem swC_even : ∀ f : Fin 12, (swC.getD f.val []).length % 2 = 0 := by decide
theorem swE_even : ∀ f : Fin 12, (swE.getD f.val []).length % 2 = 0 := by decide
theorem swC_range : ∀ f : Fin 12, ∀ i ∈ swC.getD f.val [], i + 1 < 20 := by decide
theorem swE_range : ∀ f : Fin 12, ∀ i ∈ swE.getD f.val [], i + 1 < 30 := by decide

theorem faceMove_co_sum : ∀ f : Fin 12, sumNats (listOfOri (Em.faceMove f).co) % 3 = 0 := by
  decide
theorem faceMove_eo_sum : ∀ f : Fin 12, sumNats (listOfOri (Em.faceMove f).eo) % 2 = 0 := by
  decide

/-! ## Left multiplication by a face move preserves legality -/

theorem isLegal_faceMove_compose (f : Fin 12) (g : Position) (hg : isLegal g) :
    isLegal (compose (Em.faceMove f) g) := by
  obtain ⟨hcp, hep, pc, pe, sc, se⟩ := hg
  have hinj := injPos_compose _ _ (injPos_faceMove f) ⟨hcp, hep⟩
  refine ⟨hinj.1, hinj.2, ?_, ?_, ?_, ?_⟩
  · show permParity (listOf (g.cp ∘ (Em.faceMove f).cp)) = 0
    rw [listOf_comp, faceMove_cp_swaps, map_applySwaps, range_map_listOf,
      permParity_applySwaps _ _ (listOf_nodup _ hcp)
        (by intro i hi; rw [listOf_length]; exact swC_range f i hi), pc]
    have := swC_even f; omega
  · show permParity (listOf (g.ep ∘ (Em.faceMove f).ep)) = 0
    rw [listOf_comp, faceMove_ep_swaps, map_applySwaps, range_map_listOf,
      permParity_applySwaps _ _ (listOf_nodup _ hep)
        (by intro i hi; rw [listOf_length]; exact swE_range f i hi), pe]
    have := swE_even f; omega
  · show sumNats (listOfOri (fun s => g.co ((Em.faceMove f).cp s) + (Em.faceMove f).co s)) % 3 = 0
    rw [listOfOri_compose, sumNats_zipWith_mod]
    · rw [faceMove_cp_swaps, map_applySwaps, range_map_listOfOri, sumNats_applySwaps]
      have := faceMove_co_sum f; omega
    · simp [listOfOri, listOf]
  · show sumNats (listOfOri (fun s => g.eo ((Em.faceMove f).ep s) + (Em.faceMove f).eo s)) % 2 = 0
    rw [listOfOri_compose, sumNats_zipWith_mod]
    · rw [faceMove_ep_swaps, map_applySwaps, range_map_listOfOri, sumNats_applySwaps]
      have := faceMove_eo_sum f; omega
    · simp [listOfOri, listOf]

/-! ## Words in face moves -/

/-- Positions that are products of face moves. -/
inductive Word : Position → Prop
  | id : Word identity
  | step (f : Fin 12) (g : Position) : Word g → Word (compose (Em.faceMove f) g)

theorem word_isLegal {p : Position} (h : Word p) : isLegal p := by
  induction h with
  | id => exact identity_isLegal
  | step f g _ ih => exact isLegal_faceMove_compose f g ih

theorem word_compose {a b : Position} (ha : Word a) (hb : Word b) : Word (compose a b) := by
  induction ha with
  | id => rw [compose_id_left]; exact hb
  | step f g _ ih => rw [compose_assoc]; exact Word.step f _ ih

theorem word_leftIter (f : Fin 12) : ∀ (n : Nat) (g : Position), Word g →
    Word (Em.leftIter (Em.faceMove f) n g)
  | 0, _, h => h
  | n + 1, g, h => Word.step f _ (word_leftIter f n g h)

theorem word_faceTurn (g : Position) (f : Fin 12) (a : Nat) (h : Word g) :
    Word (Em.faceTurn g f a) := word_leftIter f _ _ h

theorem word_g2Step (st : Position × Em.Grip) (card : Nat) (h : Word st.1) :
    Word (Em.g2Step st card).1 := by
  obtain ⟨g, o⟩ := st
  rw [g2Step_fst]
  refine word_compose ?_ h
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    apply word_faceTurn
    split
    · exact word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id)
    · exact word_faceTurn _ _ _ Word.id
  · simp only [hr, dite_false]
    apply word_faceTurn
    split
    · exact word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id)
    · exact word_faceTurn _ _ _ Word.id

theorem word_f3Iter : ∀ (n : Nat) (st : Position × Em.Grip), Word st.1 → Word (Em.f3Iter n st).1
  | 0, _, h => h
  | n + 1, _, h => word_f3Iter n _ (word_faceTurn _ _ _ h)

theorem word_foldl_g2 : ∀ (cards : List Nat) (st : Position × Em.Grip), Word st.1 →
    Word (cards.foldl Em.g2Step st).1
  | [], _, h => h
  | c :: cs, st, h => word_foldl_g2 cs _ (word_g2Step st c h)

theorem word_emBlock (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.emBlock h deal) :=
  word_f3Iter _ _ (word_foldl_g2 _ (h, Em.gripId) hh)

theorem word_dmStep (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.dmStep h deal) :=
  word_compose hh (word_emBlock h deal hh)

theorem word_ivCook12 : Word Em.ivCook12 := by
  unfold Em.ivCook12
  have key : ∀ (l : List Nat) (g : Position), Word g →
      Word (l.foldl (fun g f => if hf : f < 12 then Em.faceTurn g ⟨f, hf⟩ 1 else g) g) := by
    intro l
    induction l with
    | nil => intro g h; exact h
    | cons f fs ih =>
        intro g h
        simp only [List.foldl_cons]
        apply ih
        split
        · exact word_faceTurn _ _ _ h
        · exact h
  exact key _ _ Word.id

theorem word_chR (r : List (List Nat)) : Word (chR dmBlock Em.ivCook12 r) := by
  induction r with
  | nil => simp only [chR]; exact word_ivCook12
  | cons b r ih => simp only [chR]; unfold dmBlock; exact word_dmStep _ _ ih

/-- Every chaining value reachable from IV-COOK12 is a legal megaminx position. -/
theorem isLegal_chR (r : List (List Nat)) : isLegal (chR dmBlock Em.ivCook12 r) :=
  word_isLegal (word_chR r)

theorem isLegal_chainMsg (msg : List Nat) : isLegal (chainMsg msg) := by
  unfold chainMsg; rw [foldl_eq_chR]; exact isLegal_chR _

end MegaDreifach.Security
