/-
  Link 2 layers shared with v2, stated for the v3 emit.

  The v2 lemmas used here (sources in ../../megadreifach/lean/MegaDreifach/Link2/, built in
  this package by the `MegaDreifachLink` lib) are re-elaborated against THIS package's
  Generated/ (emitted from primitives/hash/megadreifach/v3/megadreifach.sudo). So each
  theorem below is about the v3 emitted function of that name. These functions are textually
  unchanged from v2 in the sudo. The model side is the v2 algebra (`MegaDreifach.compose`,
  `MegaDreifach.Em.faceMove` / `faceTurn` / `inverse`), which v3 keeps (SPEC v3 §5).

  Not covered here: the v3 card phase (em_block / em_run), Hash, HashDeck, HashDeckBody, the
  digest encoding, pad and phi. No sorry. No native_decide.
-/
import MegaDreifach.Link2.Compose
import MegaDreifach.Link2.FaceTurn
import MegaDreifach.Link2.Inverse

namespace MegaDreifachV3.Link2

open MegaDreifach MegaDreifach.Link2

/-- v3 emitted `compose` is the group law of the position model. -/
theorem compose_refines (g h : Position) :
    Megadreifach.compose (embedPos g) (embedPos h) = .ok (embedPos (MegaDreifach.compose g h)) :=
  MegaDreifach.Link2.compose_refines g h

/-- v3 emitted `face_move` is the model's quarter-click face generator. -/
theorem face_move_refines (f : Fin 12) :
    Megadreifach.face_move (Int.ofNat f.val) = .ok (embedPos (Em.faceMove f)) :=
  MegaDreifach.Link2.face_move_refines f

/-- v3 emitted `face_turn` is the model's `faceTurn` (any click count). -/
theorem face_turn_refines (g : Position) (f : Fin 12) (amount : Nat) :
    Megadreifach.face_turn (embedPos g) (Int.ofNat f.val) (Int.ofNat amount) =
      .ok (embedPos (Em.faceTurn g f amount)) :=
  MegaDreifach.Link2.face_turn_refines g f amount

/-- v3 emitted `inverse` is the model's inverse. -/
theorem inverse_refines (g : Position) :
    Megadreifach.inverse (embedPos g) = .ok (embedPos (Em.inverse g)) :=
  MegaDreifach.Link2.inverse_refines g

end MegaDreifachV3.Link2
