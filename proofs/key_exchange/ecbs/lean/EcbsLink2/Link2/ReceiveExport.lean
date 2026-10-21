/-
  `receive_check` is the receiver's four verdicts. Each one names the peak,
  the move delta since the curve test, `tally_max`, and `control_highest`.
  The curve failure does not run `certificate`. The empty certificate keeps
  the empty point. Accept and mismatch rebuild that point, then clear the
  bottom and the gap. `certificate` is where an inversion happens, and only
  on its nonempty arm; this theorem leaves that call in place.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

open Ecbs

/-- The four counters `Checked` reports, taken off the board as they stand. -/
def checkedAt (v : Verdict) (rebuilt : Point) (b : Board) (moves : Int) : Checked :=
  { sudo_7Checked_7verdict := v
    sudo_7Checked_7rebuilt := rebuilt
    sudo_7Checked_4peak := b.sudo_5Board_4cost.sudo_5Costs_4peak
    sudo_7Checked_11check_moves := moves
    sudo_7Checked_9tally_max := b.sudo_5Board_4cost.sudo_5Costs_9tally_max
    sudo_7Checked_15control_highest :=
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest }

/-- The receiver's check. `moves` is `subI` of the moves since `m0`. -/
def receiveCheckCard (t : Tier) (own sent_c sent_a : Point) :
    Except SudoRt.Trap Checked :=
  do
    let recv ← new_board t
    let recv ← put recv across own.sudo_5Point_1x
    let recv ← put recv up own.sudo_5Point_1y
    let snd ← new_board t
    let snd ← put snd across sent_c.sudo_5Point_1x
    let snd ← put snd up sent_c.sudo_5Point_1y
    let recv ← call_session recv snd
    let m0 := recv.sudo_5Board_4cost.sudo_5Costs_5moves
    let rebuilt ← empty_point t
    let ⟨on, recv⟩ ← on_curve recv
    if !on then
      do
        let mv ← SudoRt.subI recv.sudo_5Board_4cost.sudo_5Costs_5moves m0
        pure (checkedAt Verdict.Sudo_7Verdict_10CurveFails rebuilt recv mv)
    else
      do
        let ⟨ok, recv⟩ ← certificate recv base_across base_up
        if !ok then
          do
            let mv ← SudoRt.subI recv.sudo_5Board_4cost.sudo_5Costs_5moves m0
            pure (checkedAt Verdict.Sudo_7Verdict_16EmptyCertificate rebuilt recv mv)
        else
          do
            let recv ← phase_drop recv
            let recv ← phase_drop recv
            let rebuilt ← point_of recv base_across base_up
            let snd ← clear snd across
            let snd ← clear snd up
            let snd ← put snd across sent_a.sudo_5Point_1x
            let snd ← put snd up sent_a.sudo_5Point_1y
            let recv ← call_session recv snd
            let matched ← certificate_matches recv
            if !matched then
              do
                let recv ← clear recv bottom
                let recv ← clear recv gap
                let mv ← SudoRt.subI recv.sudo_5Board_4cost.sudo_5Costs_5moves m0
                pure (checkedAt Verdict.Sudo_7Verdict_8Mismatch rebuilt recv mv)
            else
              do
                let recv ← clear recv bottom
                let recv ← clear recv gap
                let mv ← SudoRt.subI recv.sudo_5Board_4cost.sudo_5Costs_5moves m0
                pure (checkedAt Verdict.Sudo_7Verdict_6Accept rebuilt recv mv)

theorem receive_check_card (t : Tier) (own sent_c sent_a : Point) :
    receive_check t own sent_c sent_a = receiveCheckCard t own sent_c sent_a := by
  unfold receive_check receiveCheckCard checkedAt
  conv =>
    lhs
    zeta

end EcbsLink2.Link2
