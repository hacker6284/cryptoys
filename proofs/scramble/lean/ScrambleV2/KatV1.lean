/-
  The v1 model against the five `scramble_v1` vectors of the SPEC (and of `scramble.sudo`'s
  tests), each checked by the kernel (`decide!`). Model only. Proof-only.
-/
import ScrambleV2.SpecV1

namespace ScrambleV2.Kat

theorem kat_v1_empty : digestV1 [] = [0, 154, 92, 23, 209, 157, 221, 190, 180] := by decide!

theorem kat_v1_a : digestV1 [97] = [0, 139, 168, 193, 110, 128, 116, 53, 77] := by decide!

theorem kat_v1_A7 : digestV1 [167] = [1, 35, 38, 254, 10, 8, 167, 108, 65] := by decide!

theorem kat_v1_hello : digestV1 [104, 101, 108, 108, 111] =
    [0, 223, 121, 2, 237, 32, 109, 248, 140] := by decide!

theorem kat_v1_cube : digestV1 [99, 117, 98, 101] =
    [0, 31, 45, 137, 218, 17, 50, 217, 69] := by decide!

end ScrambleV2.Kat
