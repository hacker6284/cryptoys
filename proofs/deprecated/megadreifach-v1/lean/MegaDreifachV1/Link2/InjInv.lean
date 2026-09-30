/-
  Invariant `InjPos` (injective corner / edge permutation tables) is preserved
  by `compose`, `faceMove`, `faceTurn`, `g2Step`, `f3Step`, `emBlock`, `dmStep`,
  and holds at `ivCook12`.  Zero sorry.  No native_decide.
-/
import MegaDreifachV1.Em
import MegaDreifachV1.Link2.PosBytesGen
import MegaDreifachV1.Link2.EmIv

namespace MegaDreifachV1.Link2

open MegaDreifachV1

theorem injective_comp {α β γ : Type _} {f : β → γ} {g : α → β}
    (hf : Injective f) (hg : Injective g) : Injective (f ∘ g) :=
  fun h => hg (hf h)

theorem injPos_compose (g h : Position) (hg : InjPos g) (hh : InjPos h) :
    InjPos (compose g h) :=
  ⟨injective_comp hh.1 hg.1, injective_comp hh.2 hg.2⟩

theorem faceMove_cp_inj_dec :
    ∀ f : Fin 12, ∀ x y : Fin 20, (Em.faceMove f).cp x = (Em.faceMove f).cp y → x = y := by
  decide

theorem faceMove_ep_inj_dec :
    ∀ f : Fin 12, ∀ x y : Fin 30, (Em.faceMove f).ep x = (Em.faceMove f).ep y → x = y := by
  decide

theorem injPos_faceMove (f : Fin 12) : InjPos (Em.faceMove f) :=
  ⟨fun h => faceMove_cp_inj_dec f _ _ h, fun h => faceMove_ep_inj_dec f _ _ h⟩

theorem injPos_leftIter (T : Position) (hT : InjPos T) :
    ∀ n g, InjPos g → InjPos (Em.leftIter T n g)
  | 0, _, hg => hg
  | n + 1, g, hg => injPos_compose _ _ hT (injPos_leftIter T hT n g hg)

theorem injPos_faceTurn (g : Position) (f : Fin 12) (a : Nat) (hg : InjPos g) :
    InjPos (Em.faceTurn g f a) :=
  injPos_leftIter _ (injPos_faceMove f) _ _ hg

theorem injPos_g2Step (st : Position × Em.Grip) (card : Nat) (h : InjPos st.1) :
    InjPos (Em.g2Step st card).1 := by
  unfold Em.g2Step
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    apply injPos_faceTurn
    split
    · exact injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ h)
    · exact injPos_faceTurn _ _ _ h
  · simp only [hr, dite_false]
    apply injPos_faceTurn
    split
    · exact injPos_faceTurn _ _ _ (injPos_faceTurn _ _ _ h)
    · exact injPos_faceTurn _ _ _ h

theorem injPos_f3Step (st : Position × Em.Grip) (h : InjPos st.1) :
    InjPos (Em.f3Step st).1 :=
  injPos_faceTurn _ _ _ h

theorem injPos_f3Iter : ∀ n (st : Position × Em.Grip), InjPos st.1 → InjPos (Em.f3Iter n st).1
  | 0, _, h => h
  | n + 1, st, h => injPos_f3Iter n _ (injPos_f3Step st h)

theorem injPos_foldl_g2 : ∀ (cards : List Nat) (st : Position × Em.Grip), InjPos st.1 →
    InjPos (cards.foldl Em.g2Step st).1
  | [], _, h => h
  | c :: cs, st, h => injPos_foldl_g2 cs _ (injPos_g2Step st c h)

theorem injPos_emBlock (h : Position) (deal : List Nat) (hh : InjPos h) :
    InjPos (Em.emBlock h deal) :=
  injPos_f3Iter _ _ (injPos_foldl_g2 _ (h, Em.gripId) hh)

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

end MegaDreifachV1.Link2
