/-
  MegaDreifach v3 (ZP26 card phase) Lean package: the KAT data, the compiled KAT runner over
  the emitted v3 code, and the Link 2 layers shared with v2 (Link2/Shared.lean: compose,
  face_move, face_turn, inverse; Link2/Codec.lean: pad_message, require_permutation,
  position_to_bytes, phi_chunk, phi_inv), via the v2 lemmas re-elaborated against the v3 emit.
  The card-phase model (Em.lean, a typed transliteration of the v3 sudo) with its first
  Link 2 pieces (Link2/CardFacts.lean, Link2/CardTables.lean). em_run / em_block, Hash and the
  other exports are not linked yet; see ../README.md.
-/
import MegaDreifachV3.Vectors
import MegaDreifachV3.KatRun
import MegaDreifachV3.Link2.Shared
import MegaDreifachV3.Link2.Codec
import MegaDreifachV3.Em
import MegaDreifachV3.Link2.CardFacts
import MegaDreifachV3.Link2.CardTables
