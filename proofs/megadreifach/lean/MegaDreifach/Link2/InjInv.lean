/-
  Invariant `InjPos` (injective corner / edge permutation tables) is preserved
  by `g2Step`, `f3Step`, `emBlock`, `dmStep`, and holds at `ivCook12`. The
  version-neutral part (`compose`, `faceMove`, `faceTurn`) is in `InjPos.lean`.  Zero sorry.  No native_decide.
-/
import MegaDreifach.Em
import MegaDreifach.Link2.PosBytesGen
import MegaDreifach.Link2.EmIv
import MegaDreifach.Link2.InjPos

namespace MegaDreifach.Link2

open MegaDreifach

theorem injPos_g2Step (st : Position × Em.Grip) (card pos : Nat) (h : InjPos st.1) :
    InjPos (Em.g2Step st card pos).1 := by
  unfold Em.g2Step
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    exact injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ h))
  · simp only [hr, dite_false]
    exact injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ h))

theorem injPos_f3Step (st : Position × Em.Grip) (rnd : Nat) (h : InjPos st.1) :
    InjPos (Em.f3Step st rnd).1 :=
  injPos_faceTurn _ _ _ h

theorem injPos_f3Run : ∀ n r (st : Position × Em.Grip), InjPos st.1 → InjPos (Em.f3Run r n st).1
  | 0, _, _, h => h
  | n + 1, r, st, h => injPos_f3Run n (r + 1) _ (injPos_f3Step st r h)

theorem injPos_g2Run : ∀ (cards : List Nat) (p : Nat) (st : Position × Em.Grip), InjPos st.1 →
    InjPos (Em.g2Run p cards st).1
  | [], _, _, h => h
  | c :: cs, p, st, h => injPos_g2Run cs (p + 1) _ (injPos_g2Step st c p h)

theorem injPos_emBlock (h : Position) (deal : List Nat) (hh : InjPos h) :
    InjPos (Em.emBlock h deal) :=
  injPos_f3Run _ _ _ (injPos_g2Run _ _ (h, Em.gripId) hh)

theorem injPos_dmStep (h : Position) (deal : List Nat) (hh : InjPos h) :
    InjPos (Em.dmStep h deal) :=
  injPos_compose _ _ hh (injPos_emBlock h deal hh)

theorem injPos_of_isLegal (p : Position) (h : isLegal p) : InjPos p := ⟨h.1, h.2.1⟩

theorem injPos_ivCook12 : InjPos Em.ivCook12 := injPos_of_isLegal _ ivCook12_isLegal

theorem injPos_foldl_dm (blocks : List (List Nat)) : ∀ h, InjPos h →
    InjPos (blocks.foldl Em.dmStep h) := by
  induction blocks with
  | nil => intro h hh; exact hh
  | cons b bs ih => intro h hh; exact ih _ (injPos_dmStep h b hh)

/-- Digest refinement for every Davies–Meyer output (no side condition beyond
    the chaining value being injective, which holds from the IV onward). -/
theorem position_to_bytes_dm_refines (h : Position) (deal : List Nat) (hh : InjPos h) :
    Megadreifach.position_to_bytes (embedPos (Em.dmStep h deal)) =
      .ok (embed (positionToBytes (Em.dmStep h deal))) :=
  position_to_bytes_refines_gen _ (injPos_dmStep h deal hh)

end MegaDreifach.Link2
