/- Compiled witness check for the deprecated v8 vulnerability proof (TAP-style).
   Evaluates the emitted frozen v8 `encrypt`. Evidence, not a kernel theorem. -/
import DoubleDealV8
open DoubleDealV8.Witness
def main : IO UInt32 := do
  let checks : List (String × Bool) :=
    [ ("E_K(M) = C (witness_v8.json)", enc message key == some (embed cipher)),
      ("E_K(tau M) = tau C", enc messageTau key == some (embed cipherTau)),
      ("tau C != C", cipherTau != cipher) ]
  IO.println s!"1..{checks.length}"
  let mut ok := true
  for (i, (name, b)) in checks.enum do
    IO.println s!"{if b then "ok" else "not ok"} {i+1} - {name}"
    ok := ok && b
  return (if ok then 0 else 1)
