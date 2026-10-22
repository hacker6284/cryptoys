/-
  The cofactor cell after the white copy, split the way `walk_fform` splits a
  run. A zero run makes `chord_add` return `(false, _)` and `cofactorWalk`
  return `none`. A nonzero run inverts under `FieldOk`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CofactorRed
import EcbsLink2.Link2.WalkLive
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.FieldOk
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.Link2.ChordLive
import EcbsLink2.Link2.DemoFieldOk

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The first cofactor cell copies the root. The next cell, colour 2, cubes it.
    A zero run there makes the whole cofactor walk `none`. -/
theorem cofactor_walk_zero (n k bench : Nat) (x y : List Nat)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hsub : fieldSub n x (fieldCube n k bench x) = List.replicate n 0) :
    cofactorWalk n k bench (x, y) = none := by
  have hopen : walkStep n k bench (x, y) false (whiteHole0 n, whiteHole0 n) 1 =
      some (true, (x, y)) := by
    unfold walkStep
    simp only [show (1 : Nat) = 0 ↔ False from by decide, if_false]
    simp only [show ¬ ((1 : Nat) ≠ 1 ∧ (1 : Nat) ≠ 2) from by decide, if_false]
    simp
  have hlive := walkStep_empty_run n k bench (x, y) (x, y) 2 (Or.inr rfl) hsub hn0 hnb
  unfold cofactorWalk
  simp only [cofactorCells, walkGo, hopen, hlive]

/-- The search hit this root, and the cofactor run is zero, so there is no base point. -/
theorem basePoint_zero_root (t : Spec.Tier) (x y : List Nat)
    (hroot : searchRoot t.n t.k t.benchlen t.n 1 = some (x, y))
    (hn0 : 0 < t.n) (hnb : t.n ≤ t.benchlen)
    (hsub : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) = List.replicate t.n 0) :
    basePoint t = none := by
  unfold basePoint
  rw [hroot]
  exact cofactor_walk_zero t.n t.k t.benchlen x y hn0 hnb hsub

private theorem run_trits (n : Nat) (a b : List Nat) : allTritList (fieldSub n a b) := by
  rw [fieldSub]
  exact fieldAdd_trits n a (mirrorTrits b)

private theorem inv_some (t : Spec.Tier) (hF : FieldOk t) (run : List Nat)
    (htri : allTritList run) (hlen : run.length = t.n) (hne : run ≠ zeroHome t.n) :
    ∃ g, fieldInv t.n t.k t.benchlen run = some g := by
  have hnot := hF run htri hlen hne
  revert hnot
  generalize hfi : fieldInv t.n t.k t.benchlen run = o
  clear hfi
  intro hnot
  cases o with
  | none => exact absurd rfl hnot
  | some g => exact ⟨g, rfl⟩

/-- Zero run: the emitted cell rerolls and the spec walk is `none`.
    Nonzero run: `FieldOk` supplies the inverse. `demo_run_ne` still shows Demo's
    basis pegs take the nonzero arm. -/
theorem cofactor_cell_cases (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx c3 : Nat)
    (hsh : TierShape t) (sat : TierSat t) (hF : FieldOk t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'hops3 = (c3 : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hfops : FitsLen (c3 + 1))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n))
    (hChord : FitsLen (moves + 10 * t.n + 6 * (t.benchlen - t.n)))
    (hpos : 0 < t.n) (hnb : t.n ≤ t.benchlen) (hk : t.k ≤ t.n)
    (hspan : 3 * (t.n - 1) < t.benchlen) :
    (∃ (bF bA : Board),
        frobenius_affine b = .ok bF ∧
        Ecbs.chord_add_demo bF true = .ok (false, bA) ∧
        chordStep (embed cofactorCells) (Int.ofNat 3) (Int.ofNat 1, (b, true)) =
          .ok (SudoRt.Flow.ret ((true, false),
            { bA with sudo_5Board_9marker_on := false })) ∧
        walkStep t.n t.k t.benchlen (x, y) true (x, y) 2 = none ∧
        cofactorWalk t.n t.k t.benchlen (x, y) = none) ∨
    (∃ (g : List Nat), fieldInv t.n t.k t.benchlen
        (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some g) := by
  have hlift := marker_lift_down b hmark
  obtain ⟨bF, mvF, pkF, hfrob, hmv, _hfit, hpk, hszD2, hszH2, h2o, h0o, hhome0o, h3o, hhome3,
      hopsO, hopO, hnO⟩ :=
    cofactor_cube_keep b t x y moves slides pk peakS holeN cOps ctrl mx c3 hsh sat
      hszH hszD hops hops3 hx hy hxt hyt hmk hoff hmark hc hmx hT hop1 hop3
      hfitC hfitD hfitU hheld0 hhome0 hheld1 hhome1 h2 h3t h3a hmoves hslides
      hpeak hstrict hhole hMv hSl hChord
  have haccT : allTritList (fieldCube t.n t.k t.benchlen x) :=
    fieldCube_trits t.n t.k t.benchlen x hxt hspan hk
  have hmvI : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (mvF : Int) := by
    simpa [ofNat_eq_natCast] using hmv
  have hpkI : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (pkF : Int) := by
    simpa [ofNat_eq_natCast] using hpk
  let run := fieldSub t.n x (fieldCube t.n t.k t.benchlen x)
  by_cases hzero : run = List.replicate t.n 0
  · have hzero' : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) =
        List.replicate t.n 0 := hzero
    have hcubeL : (fieldCube t.n t.k t.benchlen x).length = t.n :=
      fieldCube_length t.n t.k t.benchlen x hnb
    obtain ⟨bA, hadd, _, _, _, _, _, _⟩ :=
      chord_add_empty bF true x (fieldCube t.n t.k t.benchlen x) t.n mvF pkF c3
        hszH2 hszD2 hopsO (hopO hopsO) hfops hx hcubeL hpos hxt haccT hnO hmvI hpkI
        _hfit (h2o (by rw [hszD2]; decide))
        (h0o (by rw [hszD2]; decide)) (hhome0o (by rw [hszH2]; decide))
        (h3o (by rw [hszD2]; decide)) (hhome3 (by rw [hszH2]; decide)) hzero'
    have hbeq : SudoRt.SEq.beq (Int.ofNat 2) (2 : Int) = true := by decide
    have hstep :=
      chordStep_reroll cofactorCells 1 3 2 b b bF bA
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hlift hfrob (by simpa [hbeq] using hadd)
    have hwalk :=
      walkStep_empty_run t.n t.k t.benchlen (x, y) (x, y) 2 (Or.inr rfl) hzero' hpos hnb
    exact Or.inl ⟨bF, bA, hfrob, hadd, hstep, hwalk,
      cofactor_walk_zero t.n t.k t.benchlen x y hpos hnb hzero'⟩
  · have hlen : run.length = t.n := fieldSub_length t.n x (fieldCube t.n t.k t.benchlen x)
    have htri : allTritList run := run_trits t.n x (fieldCube t.n t.k t.benchlen x)
    have hneZ : run ≠ zeroHome t.n := by
      simpa [zeroHome, zeroPeg, run] using hzero
    exact Or.inr (inv_some t hF run htri hlen hneZ)

/-- Nonzero run on a cubed `RunFrame`. `FieldOk` gives the inverse and the
    emitted add returns the new point. -/
theorem cofactor_chord_live (b : Board) (t : Spec.Tier) (x y preY : List Nat) (c : Nat)
    (fr : RunFrame b t x (fieldCube t.n t.k t.benchlen x))
    (hF : FieldOk t) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = y) (hA : fr.y1 = fieldCube t.n t.k t.benchlen preY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : y.length = t.n) (hyA : (fieldCube t.n t.k t.benchlen preY).length = t.n)
    (htriY : allTritList y) (htriUp : allTritList (fieldCube t.n t.k t.benchlen preY))
    (hne : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) ≠ List.replicate t.n 0)
    (hMove : FitsLen (liveMoveRoom t fr.moves x (fieldCube t.n t.k t.benchlen x)))
    (hSlide : FitsLen (liveSlideRoom t fr.slides))
    (hCtrl : FitsLen (liveCtrlRoom t fr.ctrl))
    (hOps : FitsLen (liveOpsRoom t fr.opsCap))
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hholeFr : fr.hole ≤ t.benchlen) :
    ∃ (g : List Nat) (b' : Board),
      fieldInv t.n t.k t.benchlen (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some g ∧
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, preY) c = some (true,
        (chordX3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if decide (c = 2) then mirrorTrits y else y)
              (fieldCube t.n t.k t.benchlen preY)) g)
          (fieldCube t.n t.k t.benchlen x)
          (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)),
        chordY3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if decide (c = 2) then mirrorTrits y else y)
              (fieldCube t.n t.k t.benchlen preY)) g)
          (fieldSub t.n (fieldCube t.n t.k t.benchlen x)
            (chordX3 t.n t.k t.benchlen
              (fieldMul t.n t.k t.benchlen
                (fieldSub t.n (if decide (c = 2) then mirrorTrits y else y)
                  (fieldCube t.n t.k t.benchlen preY)) g)
              (fieldCube t.n t.k t.benchlen x)
              (fieldSub t.n x (fieldCube t.n t.k t.benchlen x))))
          (fieldCube t.n t.k t.benchlen preY))) := by
  let run := fieldSub t.n x (fieldCube t.n t.k t.benchlen x)
  have hlen : run.length = t.n := fieldSub_length t.n x (fieldCube t.n t.k t.benchlen x)
  have htri : allTritList run := run_trits t.n x (fieldCube t.n t.k t.benchlen x)
  have hneZ : run ≠ zeroHome t.n := by
    simpa [zeroHome, zeroPeg, run] using hne
  obtain ⟨g, hinv⟩ := inv_some t hF run htri hlen hneZ
  obtain ⟨b', hadd, _, _, hwalk, _, _, _⟩ :=
    chord_add_live b t x (fieldCube t.n t.k t.benchlen x) y
      (fieldCube t.n t.k t.benchlen preY) x preY g c fr hOk sat hR hsh hmk hc
      hY hA hf4 hf1 hyB hyA htriY htriUp rfl rfl (by simpa [run] using hinv)
      hMove hSlide hCtrl hOps hMark hMarkF hholeFr
  exact ⟨g, b', by simpa [run] using hinv, hadd, hwalk⟩

/-- Demo's case split. The nonzero arm uses the kernel check `demo_fieldOk`. -/
theorem demo_cofactor_cell_cases (b : Board) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx c3 : Nat)
    (hsh : TierShape demo) (sat : TierSat demo)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = demo.n) (hy : y.length = demo.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier demo)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'hops3 = (c3 : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hfops : FitsLen (c3 + 1))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * demo.n + 6 * (demo.benchlen - demo.n)))
    (hSl : FitsLen (slides + 4 * demo.n))
    (hChord : FitsLen (moves + 10 * demo.n + 6 * (demo.benchlen - demo.n))) :
    (∃ (bF bA : Board),
        frobenius_affine b = .ok bF ∧
        Ecbs.chord_add_demo bF true = .ok (false, bA) ∧
        chordStep (embed cofactorCells) (Int.ofNat 3) (Int.ofNat 1, (b, true)) =
          .ok (SudoRt.Flow.ret ((true, false),
            { bA with sudo_5Board_9marker_on := false })) ∧
        walkStep demo.n demo.k demo.benchlen (x, y) true (x, y) 2 = none ∧
        cofactorWalk demo.n demo.k demo.benchlen (x, y) = none) ∨
    (∃ (g : List Nat), fieldInv demo.n demo.k demo.benchlen
        (fieldSub demo.n x (fieldCube demo.n demo.k demo.benchlen x)) = some g) :=
  cofactor_cell_cases b demo x y moves slides pk peakS holeN cOps ctrl mx c3
    hsh sat demo_fieldOk hszH hszD hops hops3 hx hy hxt hyt hmk hoff hmark hc hmx hT
    hop1 hop3 hfitC hfitD hfitU hfops hheld0 hhome0 hheld1 hhome1 h2 h3t h3a
    hmoves hslides hpeak hstrict hhole hMv hSl hChord
    (by decide) (by decide) (by decide) (by decide)

/-- Demo's live cofactor cell. `demo_fieldOk` is the inverse. -/
theorem demo_cofactor_chord_live (b : Board) (x y preY : List Nat) (c : Nat)
    (fr : RunFrame b demo x (fieldCube demo.n demo.k demo.benchlen x))
    (hOk : BoardOk demo) (sat : TierSat demo) (hR : 0 < tierR demo) (hsh : TierShape demo)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = y) (hA : fr.y1 = fieldCube demo.n demo.k demo.benchlen preY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : y.length = demo.n) (hyA : (fieldCube demo.n demo.k demo.benchlen preY).length = demo.n)
    (htriY : allTritList y) (htriUp : allTritList (fieldCube demo.n demo.k demo.benchlen preY))
    (hne : fieldSub demo.n x (fieldCube demo.n demo.k demo.benchlen x) ≠ List.replicate demo.n 0)
    (hMove : FitsLen (liveMoveRoom demo fr.moves x (fieldCube demo.n demo.k demo.benchlen x)))
    (hSlide : FitsLen (liveSlideRoom demo fr.slides))
    (hCtrl : FitsLen (liveCtrlRoom demo fr.ctrl))
    (hOps : FitsLen (liveOpsRoom demo fr.opsCap))
    (hMark : fr.mark + 3 < demo.script) (hMarkF : FitsLen (fr.mark + 4))
    (hholeFr : fr.hole ≤ demo.benchlen) :
    ∃ (g : List Nat) (b' : Board),
      fieldInv demo.n demo.k demo.benchlen
        (fieldSub demo.n x (fieldCube demo.n demo.k demo.benchlen x)) = some g ∧
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep demo.n demo.k demo.benchlen (x, y) true (x, preY) c = some (true,
        (chordX3 demo.n demo.k demo.benchlen
          (fieldMul demo.n demo.k demo.benchlen
            (fieldSub demo.n (if decide (c = 2) then mirrorTrits y else y)
              (fieldCube demo.n demo.k demo.benchlen preY)) g)
          (fieldCube demo.n demo.k demo.benchlen x)
          (fieldSub demo.n x (fieldCube demo.n demo.k demo.benchlen x)),
        chordY3 demo.n demo.k demo.benchlen
          (fieldMul demo.n demo.k demo.benchlen
            (fieldSub demo.n (if decide (c = 2) then mirrorTrits y else y)
              (fieldCube demo.n demo.k demo.benchlen preY)) g)
          (fieldSub demo.n (fieldCube demo.n demo.k demo.benchlen x)
            (chordX3 demo.n demo.k demo.benchlen
              (fieldMul demo.n demo.k demo.benchlen
                (fieldSub demo.n (if decide (c = 2) then mirrorTrits y else y)
                  (fieldCube demo.n demo.k demo.benchlen preY)) g)
              (fieldCube demo.n demo.k demo.benchlen x)
              (fieldSub demo.n x (fieldCube demo.n demo.k demo.benchlen x))))
          (fieldCube demo.n demo.k demo.benchlen preY))) :=
  cofactor_chord_live b demo x y preY c fr demo_fieldOk hOk sat hR hsh hmk hc
    hY hA hf4 hf1 hyB hyA htriY htriUp hne hMove hSlide hCtrl hOps hMark hMarkF hholeFr

end EcbsLink2.Link2
