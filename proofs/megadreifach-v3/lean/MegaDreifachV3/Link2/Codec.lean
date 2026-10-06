/-
  Link 2 for the v3 byte codecs: pad, the deal check, the digest encoding and phi.

  As in Shared.lean, the v2 lemmas used here (sources in
  ../../megadreifach/lean/MegaDreifach/Link2/, built in this package by the
  `MegaDreifachLink` lib) are re-elaborated against THIS package's Generated/, so each theorem
  below is about the v3 emitted function of that name. These functions are textually unchanged
  from v2 in the sudo; only the `.sudo` line numbers in their asserts moved, and the v2
  lemmas take those as a parameter. The model side is the v2 one (`pad`, `requirePermutation`,
  `positionToBytes`, `phiUnrank`, `lehmerRank`), which v3 keeps (SPEC v3 §5).

  Exactly: `pad_message` on `PadWf` (bytes `≤ 255`, bit length fits); `require_permutation`
  on permutations of `0..51` (it returns its input); `position_to_bytes` (the digest
  encoding) on positions with bijective cp and ep; `phi_chunk` on 28-byte blocks; `phi_inv` on
  permutations whose Lehmer rank is `< 2^224`. Not covered here: the v3 card phase, Hash,
  HashDeck, HashDeckBody. No sorry. No native_decide.
-/
import MegaDreifach.Link2.PadRef
import MegaDreifach.Link2.RequirePerm
import MegaDreifach.Link2.PosBytes
import MegaDreifach.Link2.PosBytesGen
import MegaDreifach.Link2.PhiChunk
import MegaDreifach.Link2.PhiInv

namespace MegaDreifachV3.Link2

open MegaDreifach MegaDreifach.Link2

/-- v3 `pad_message` is the model `pad` on well-formed messages. -/
theorem pad_message_refines (msg : List Nat) (hp : PadWf msg) :
    Megadreifach.pad_message (embed msg) = .ok (embed (pad msg)) :=
  MegaDreifach.Link2.pad_message_refines msg hp

/-- Same, on a `WellFormedPad` array. -/
theorem pad_message_refines_array (a : Array Int) (h : WellFormedPad a) :
    Megadreifach.pad_message a = .ok (embed (pad (decode a))) :=
  MegaDreifach.Link2.pad_message_refines_array a h

/-- v3 `require_permutation` returns a permutation of `0..51` unchanged, as the model does. -/
theorem require_permutation_refines (deal : List Nat) (h : isPermutation52 deal) :
    Megadreifach.require_permutation (embed deal) = .ok (embed deal) ∧
      requirePermutation deal = some deal :=
  MegaDreifach.Link2.require_permutation_refines deal h

/-- Same, on a `DealWf` array. -/
theorem require_permutation_refines_array (a : Array Int) (h : DealWf a) :
    Megadreifach.require_permutation a = .ok a ∧
      requirePermutation (decode a) = some (decode a) :=
  MegaDreifach.Link2.require_permutation_refines_array a h

/-- v3 `position_to_bytes` (the digest encoding) is the model `positionToBytes` under the
    v2 side conditions `PosBytesWf` (see `MegaDreifach.Link2.PosBytesWf`); the general form
    is `position_to_bytes_refines_gen` below. -/
theorem position_to_bytes_refines (p : Position) (h : PosBytesWf p) :
    Megadreifach.position_to_bytes (embedPos p) = .ok (embed (positionToBytes p)) :=
  MegaDreifach.Link2.position_to_bytes_refines p h

/-- v3 `position_to_bytes` (the digest encoding) is the model `positionToBytes` on every
    position whose corner and edge permutations are bijective (`InjPos`). -/
theorem position_to_bytes_refines_gen (p : Position) (h : InjPos p) :
    Megadreifach.position_to_bytes (embedPos p) = .ok (embed (positionToBytes p)) :=
  MegaDreifach.Link2.position_to_bytes_refines_gen p h

/-- v3 `phi_chunk` is the model `phiUnrank` of the big-endian value of a 28-byte block. -/
theorem phi_chunk_refines (bs : List Nat) (h : PhiChunkWf bs) :
    Megadreifach.phi_chunk (embed bs) = .ok (embed (phiUnrank (fromBE bs))) :=
  MegaDreifach.Link2.phi_chunk_refines bs h

/-- Same, on a `WellFormedPhiChunk` array. -/
theorem phi_chunk_refines_array (a : Array Int) (h : WellFormedPhiChunk a) :
    Megadreifach.phi_chunk a = .ok (embed (phiUnrank (fromBE (decode a)))) :=
  MegaDreifach.Link2.phi_chunk_refines_array a h

/-- v3 `phi_inv` is the 28-byte big-endian Lehmer rank. -/
theorem phi_inv_refines (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.phi_inv (embed deal) = .ok (embed (toBE 28 (lehmerRank deal))) :=
  MegaDreifach.Link2.phi_inv_refines deal h

/-- Same, on a `WellFormedPhiInv` array. -/
theorem phi_inv_refines_array (a : Array Int) (h : WellFormedPhiInv a) :
    Megadreifach.phi_inv a = .ok (embed (toBE 28 (lehmerRank (decode a)))) :=
  MegaDreifach.Link2.phi_inv_refines_array a h

end MegaDreifachV3.Link2
