/-
  VULNERABILITY PROOF (deprecated DoubleDeal v9 only).
  Kernel `decide!` facts: each emitted stage of `encrypt` on `message`
  with the witness key, from the hinted state to the next one. About 15 s and
  1.5 GB per full round on the build box.
-/
import DoubleDealV9.Glue
import DoubleDealV9.Keys  -- not needed for the proofs; serialises the build (peak memory)

namespace DoubleDealV9.Witness
open DoubleDealV9.Glue

set_option maxRecDepth 100000

theorem msg_whiten : Doubledeal_v9.compose (embed message) (embed key) = .ok A0 := ok_of_toOption (by decide!)
theorem msg_round1 : Doubledeal_v9.full_round A0 K1 = .ok A1 := ok_of_toOption (by decide!)
theorem msg_round2 : Doubledeal_v9.full_round A1 K2 = .ok A2 := ok_of_toOption (by decide!)
theorem msg_round3 : Doubledeal_v9.full_round A2 K3 = .ok A3 := ok_of_toOption (by decide!)
theorem msg_round4 : Doubledeal_v9.full_round A3 K4 = .ok A4 := ok_of_toOption (by decide!)
theorem msg_round5 : Doubledeal_v9.full_round A4 K5 = .ok A5 := ok_of_toOption (by decide!)
theorem msg_final : Doubledeal_v9.final_round A5 K6 = .ok (embed cipher) := ok_of_toOption (by decide!)

end DoubleDealV9.Witness
