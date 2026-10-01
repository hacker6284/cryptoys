/-
  The model against the v2 test vectors of `scramble.sudo` (the same digests as the
  SPEC's `scramble_v2` vectors), each checked by the kernel (`decide!`). These pin the
  hand-written model `Spec.lean` to the published digests; they say nothing about the
  emitted code by themselves (that is `Link2`). Proof-only.
-/
import ScrambleV2.Spec

namespace ScrambleV2.Kat

theorem kat_empty : digestV2 [] = [0, 96, 36, 233, 182, 16, 82, 244, 97] := by decide!

theorem kat_a : digestV2 [97] = [1, 88, 138, 100, 105, 207, 231, 178, 134] := by decide!

theorem kat_A7 : digestV2 [167] = [1, 85, 43, 110, 247, 218, 16, 194, 232] := by decide!

theorem kat_hello : digestV2 [104, 101, 108, 108, 111] =
    [0, 82, 163, 199, 209, 34, 145, 209, 64] := by decide!

theorem kat_cube : digestV2 [99, 117, 98, 101] =
    [1, 50, 253, 206, 11, 242, 110, 88, 152] := by decide!

end ScrambleV2.Kat
