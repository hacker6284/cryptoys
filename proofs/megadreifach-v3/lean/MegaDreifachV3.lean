/-
  MegaDreifach v3 (ZP26 card phase) Lean package: the KAT data, the compiled KAT runner over
  the emitted v3 code, and the Link 2 layers shared with v2 (Link2/Shared.lean: compose,
  face_move, face_turn, inverse; Link2/Codec.lean: pad_message, require_permutation,
  position_to_bytes, phi_chunk, phi_inv), via the v2 lemmas re-elaborated against the v3 emit.
  The card-phase model (Em.lean, a typed transliteration of the v3 sudo) and its Link 2
  layers: Link2/CardFacts.lean, Link2/CardTables.lean, Link2/FaceOf.lean,
  Link2/FaceOfFound.lean, Link2/RunStep.lean, Link2/EmRun.lean (em_run / em_block),
  Link2/VHash.lean (iv_cook12, Hash, MegaDreifach) and Link2/VHashDeck.lean (HashDeck,
  HashDeckBody, HashDeckBodyFrom and aliases). Every export has a Link 2 theorem; see
  ../README.md.
-/
import MegaDreifachV3.Vectors
import MegaDreifachV3.KatRun
import MegaDreifachV3.Link2.Shared
import MegaDreifachV3.Link2.Codec
import MegaDreifachV3.Em
import MegaDreifachV3.Link2.CardFacts
import MegaDreifachV3.Link2.CardTables
import MegaDreifachV3.Link2.FaceOf
import MegaDreifachV3.Link2.FaceOfFound
import MegaDreifachV3.Link2.RunStep
import MegaDreifachV3.Link2.EmRun
import MegaDreifachV3.Link2.VHash
import MegaDreifachV3.Link2.VHashDeck
