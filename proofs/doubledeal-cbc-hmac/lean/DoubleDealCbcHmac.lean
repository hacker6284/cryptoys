/-
  PROOF-ONLY root of the DoubleDeal-CBC-HMAC Link 2 package. Imports the hand-written
  model (`DoubleDealCbcHmac.Spec`) and every Link 2 module; `Axioms.lean` audits every
  theorem under `DoubleDealCbcHmac.*` (`check_axioms.py cbc-hmac`).
-/
import DoubleDealCbcHmac.Spec
import DoubleDealCbcHmac.Link2.Loop
import DoubleDealCbcHmac.Link2.Bytes
import DoubleDealCbcHmac.Link2.Hmac
import DoubleDealCbcHmac.Link2.Pad
import DoubleDealCbcHmac.Link2.Unpad
