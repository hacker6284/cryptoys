/-
  VULNERABILITY PROOF (deprecated DoubleDeal v9 only). Proof-only glue.

  Generic, data-free lemmas that chain per-stage facts through the emitted
  `Doubledeal_v9.encrypt` and `Doubledeal_v9.expand_keys` (their fuel loops
  unfolded by `simp`). They let the kernel check a full 6-round evaluation
  one stage at a time: a single `decide!` on the whole `encrypt` needs more
  memory than the build box has (the v8 attempt was killed at ~14 GB; one
  v9 `expand_keys` alone was killed at ~12.8 GB here).
-/
import Doubledeal_v9

namespace DoubleDealV9.Glue

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- `decide!` states facts about `Except` through `toOption` (`SudoRt.Trap` has no
    `DecidableEq`); this turns them back into `= .ok`. -/
theorem ok_of_toOption {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-- Six PassKey steps give the emitted key schedule. -/
theorem expand_keys_of_passkeys (k0 k1 k2 k3 k4 k5 k6 : Array Int)
    (h1 : Doubledeal_v9.passkey k0 = .ok k1)
    (h2 : Doubledeal_v9.passkey k1 = .ok k2)
    (h3 : Doubledeal_v9.passkey k2 = .ok k3)
    (h4 : Doubledeal_v9.passkey k3 = .ok k4)
    (h5 : Doubledeal_v9.passkey k4 = .ok k5)
    (h6 : Doubledeal_v9.passkey k5 = .ok k6) :
    Doubledeal_v9.expand_keys k0 = .ok #[k0, k1, k2, k3, k4, k5, k6] := by
  unfold Doubledeal_v9.expand_keys
  simp only [SudoRt.runLoopOn, SudoRt.natIterOn, SudoRt.natIter, SudoRt.appendL]
  have hfuel : (if (1:Int) > 6 then 1 else ((6:Int) - 1).natAbs + 1) = 6 := by decide
  rw [hfuel]
  have a0 : SudoRt.atL #[k0] (0 : Int) = .ok k0 := rfl
  have a1 : SudoRt.atL #[k0, k1] (1 : Int) = .ok k1 := rfl
  have a2 : SudoRt.atL #[k0, k1, k2] (2 : Int) = .ok k2 := rfl
  have a3 : SudoRt.atL #[k0, k1, k2, k3] (3 : Int) = .ok k3 := rfl
  have a4 : SudoRt.atL #[k0, k1, k2, k3, k4] (4 : Int) = .ok k4 := rfl
  have a5 : SudoRt.atL #[k0, k1, k2, k3, k4, k5] (5 : Int) = .ok k5 := rfl
  simp [SudoRt.natIter.go, a0, a1, a2, a3, a4, a5, h1, h2, h3, h4, h5, h6, ok_bind,
    SudoRt.addI, SudoRt.subI, SudoRt.narrowI, SudoRt.i64Min, SudoRt.i64Max]
  all_goals rfl

/-- Whitening, five full rounds and the final round give the emitted `encrypt`. -/
theorem encrypt_of_stages (m k0 k1 k2 k3 k4 k5 k6 a0 a1 a2 a3 a4 a5 a6 : Array Int)
    (hK : Doubledeal_v9.expand_keys k0 = .ok #[k0, k1, k2, k3, k4, k5, k6])
    (h0 : Doubledeal_v9.compose m k0 = .ok a0)
    (h1 : Doubledeal_v9.full_round a0 k1 = .ok a1)
    (h2 : Doubledeal_v9.full_round a1 k2 = .ok a2)
    (h3 : Doubledeal_v9.full_round a2 k3 = .ok a3)
    (h4 : Doubledeal_v9.full_round a3 k4 = .ok a4)
    (h5 : Doubledeal_v9.full_round a4 k5 = .ok a5)
    (h6 : Doubledeal_v9.final_round a5 k6 = .ok a6) :
    Doubledeal_v9.encrypt m k0 = .ok a6 := by
  unfold Doubledeal_v9.encrypt
  rw [hK]
  simp only [ok_bind]
  have a0' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (0 : Int) = .ok k0 := rfl
  have a1' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (1 : Int) = .ok k1 := rfl
  have a2' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (2 : Int) = .ok k2 := rfl
  have a3' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (3 : Int) = .ok k3 := rfl
  have a4' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (4 : Int) = .ok k4 := rfl
  have a5' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (5 : Int) = .ok k5 := rfl
  have a6' : SudoRt.atL #[k0, k1, k2, k3, k4, k5, k6] (6 : Int) = .ok k6 := rfl
  rw [a0', ok_bind, h0, ok_bind]
  simp only [SudoRt.runLoopOn, SudoRt.natIterOn, SudoRt.natIter]
  have hfuel : (if (1:Int) > 5 then 1 else ((5:Int) - 1).natAbs + 1) = 5 := by decide
  rw [hfuel]
  simp [SudoRt.natIter.go, a1', a2', a3', a4', a5', a6', h1, h2, h3, h4, h5, h6, ok_bind,
    SudoRt.addI, SudoRt.narrowI, SudoRt.i64Min, SudoRt.i64Max]

end DoubleDealV9.Glue
