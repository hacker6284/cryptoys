# Demo `walk_fform` hits the script-marker assert

Checked outside CI, on the Python sudoc emits from `primitives/key_exchange/ecbs/ecbs.sudo` (`proofs/sudo_py.py`, sudoc at `proofs/SUDOCODE_PIN`). No Demo KAT calls `walk_fform`. `exchange` and `walk_key` call `walk_and_finish`, and that function sends a demo tier through `walk_chord`. The same key on `walk_chord` succeeds.

## Input

Tier Demo (`script = 5`, `n = 7`). Base point `base_point_of(Demo)`:

- across `[0, 2, 1, 2, 0, 1, 1]`
- up `[2, 0, 0, 2, 2, 1, 2]`

Key cells `[1, 1]`. Fresh `new_board`, those two bands placed in `base_across` and `base_up`, then `walk_fform`.

The second cell is live and white. Its run is `x − x³ = [0, 0, 2, 2, 1, 0, 0]`. `invert_number` of that run times the run is `[1, 0, 0, 0, 0, 0, 0]`, so `walkStep` on this cell is `some (true, _)`. `is_zero` of the across after the first multiply of `fform_add` returned false, at marker 3.

## What the run did

`walk_fform` raised `AssertFailed: line 321`. That is `marker_step`'s `assert b.marker < b.t.script`.

Marker values `log_op` actually reached, in order, during this `walk_fform` only:

`-1 → 0 → 1 → 2 → 3 → 4`, then the next step wrote `5` and the assert failed (`5 < 5`).

The three cubes of `frobenius_point` are the steps that land on 0, 1, and 2. The multiplies of `fform_add` are the steps that land on 3 and 4. The following multiply is the one that traps. Nothing in that trace resets the marker. `marker_lift` at the start of the second cell is a no-op because the first cell, `start_walk`, never seats it.

## The two sides

Spec. `walkStep` (`EcbsLink2/SpecBase.lean`) cubes the live point and, for a white or red cell, returns `some (true, _)` when `chordAdd` does. `chordAdd` fails only when `specInv` of the run is `none`. Script length is not an argument. On this input the run inverts to the unit, so the spec step succeeds.

Code. `marker_step` (`ecbs.sudo` line 321) asserts `b.marker < b.t.script` after seating. Demo's script is 5. This walk reaches marker 5 and returns `AssertFailed`.

`comb_u2z` only promises a finished cell when `m + 8 < script`, and its conclusion has marker `m + 4`. That hypothesis is false here (`2 + 8 < 5`), and the emitted cell does not finish either. It stops earlier, at marker 5, rather than at a proof bound that the machine never meets.

Same board, `walk_chord` instead of `walk_fform`: result `(live, ok) = (true, true)`. Marker steps `-1 → 0 → 1 → 2 → 3 → 4`, then the closing lift sets the marker back to `-1`. That is the Demo budget in SPEC.md §3 (2 cubes + 3 multiplies, 5 script holes).
