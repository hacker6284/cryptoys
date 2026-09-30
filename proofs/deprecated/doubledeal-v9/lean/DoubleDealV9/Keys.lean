/-
  VULNERABILITY PROOF (deprecated DoubleDeal v9 only).
  Kernel `decide!` facts: the emitted PassKey takes K0 = `key` to the hinted
  K1..K6, so `expand_keys key` is the hinted schedule. About 45 s and 5 GB
  per `passkey` step on the build box.
-/
import DoubleDealV9.Glue
import DoubleDealV9.WitnessData

namespace DoubleDealV9.Witness
open DoubleDealV9.Glue

set_option maxRecDepth 100000

theorem passkey1 : Doubledeal_v9.passkey (embed key) = .ok K1 := ok_of_toOption (by decide!)
theorem passkey2 : Doubledeal_v9.passkey K1 = .ok K2 := ok_of_toOption (by decide!)
theorem passkey3 : Doubledeal_v9.passkey K2 = .ok K3 := ok_of_toOption (by decide!)
theorem passkey4 : Doubledeal_v9.passkey K3 = .ok K4 := ok_of_toOption (by decide!)
theorem passkey5 : Doubledeal_v9.passkey K4 = .ok K5 := ok_of_toOption (by decide!)
theorem passkey6 : Doubledeal_v9.passkey K5 = .ok K6 := ok_of_toOption (by decide!)

/-- The emitted key schedule of the witness key. -/
theorem expand_keys_key :
    Doubledeal_v9.expand_keys (embed key) = .ok #[embed key, K1, K2, K3, K4, K5, K6] :=
  expand_keys_of_passkeys _ _ _ _ _ _ _ passkey1 passkey2 passkey3 passkey4 passkey5 passkey6

end DoubleDealV9.Witness
