/-
  VULNERABILITY PROOF (deprecated DoubleDeal v9 only).
  Kernel `decide!` facts: each emitted stage of `encrypt` on `messageSigmaJson` (sigma M)
  with the witness key, from the hinted state to the next one. About 15 s and
  1.5 GB per full round on the build box.
-/
import DoubleDealV9.Glue
import DoubleDealV9.RunM  -- not needed for the proofs; serialises the build (peak memory)

namespace DoubleDealV9.Witness
open DoubleDealV9.Glue

set_option maxRecDepth 100000

theorem sig_whiten : Doubledeal_v9.compose (embed messageSigmaJson) (embed key) = .ok B0 := ok_of_toOption (by decide!)
theorem sig_round1 : Doubledeal_v9.full_round B0 K1 = .ok B1 := ok_of_toOption (by decide!)
theorem sig_round2 : Doubledeal_v9.full_round B1 K2 = .ok B2 := ok_of_toOption (by decide!)
theorem sig_round3 : Doubledeal_v9.full_round B2 K3 = .ok B3 := ok_of_toOption (by decide!)
theorem sig_round4 : Doubledeal_v9.full_round B3 K4 = .ok B4 := ok_of_toOption (by decide!)
theorem sig_round5 : Doubledeal_v9.full_round B4 K5 = .ok B5 := ok_of_toOption (by decide!)
theorem sig_final : Doubledeal_v9.final_round B5 K6 = .ok (embed cipherSigmaJson) := ok_of_toOption (by decide!)

end DoubleDealV9.Witness
