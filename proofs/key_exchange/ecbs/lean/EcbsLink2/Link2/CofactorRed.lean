/-
  The cubed cofactor root opens the next chord cell. `chord_add_open` is the
  nonempty run: the bottom becomes `x − x³`, and the tail is what the cell
  still has to run. On Demo that run is not the zero home.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CofactorCube
import EcbsLink2.Link2.ChordIf
import EcbsLink2.Link2.BasisRun

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The board the cofactor cube leaves opens `chord_add`. The run is `x − x³`. -/
theorem cofactor_chord_add (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx c3 : Nat) (red : Bool)
    (hsh : TierShape t) (sat : TierSat t)
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
    (hspan : 3 * (t.n - 1) < t.benchlen)
    (hsub : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) ≠ List.replicate t.n 0) :
    ∃ (bF bA : Board) (mvF : Nat),
      frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF ∧
      Ecbs.chord_add_demo bF red = chordAddTail bA red ∧
      (∀ h : 2 < bA.sudo_5Board_4home.size,
        bA.sudo_5Board_4home[2] =
          embed (fieldSub t.n x (fieldCube t.n t.k t.benchlen x))) ∧
      (∀ h : 2 < bA.sudo_5Board_4held.size, bA.sudo_5Board_4held[2] = true) := by
  obtain ⟨bF, mvF, pkF, hfrob, hmv, hfit, hpk, hszD2, hszH2, h2o, h0o, hhome0, h3o, hhome3,
      hopsO, hopO, hnO⟩ :=
    cofactor_cube_keep b t x y moves slides pk peakS holeN cOps ctrl mx c3 hsh sat
      hszH hszD hops hops3 hx hy hxt hyt hmk hoff hmark hc hmx hT hop1 hop3
      hfitC hfitD hfitU hheld0 hhome0 hheld1 hhome1 h2 h3t h3a hmoves hslides
      hpeak hstrict hhole hMv hSl hChord
  have haccL : (fieldCube t.n t.k t.benchlen x).length = t.n :=
    fieldCube_length t.n t.k t.benchlen x hnb
  have haccT : allTritList (fieldCube t.n t.k t.benchlen x) :=
    fieldCube_trits t.n t.k t.benchlen x hxt hspan hk
  have hmvI : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (mvF : Int) := by
    simpa [ofNat_eq_natCast] using hmv
  have hpkI : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (pkF : Int) := by
    simpa [ofNat_eq_natCast] using hpk
  obtain ⟨bA, hadd, hhome, hheld, _, _, _, _⟩ :=
    chord_add_open bF red x (fieldCube t.n t.k t.benchlen x) t.n mvF pkF c3
      hszH2 hszD2 hopsO (hopO hopsO) hfops hx haccL hpos hxt haccT hnO hmvI hpkI hfit
      (h2o (by rw [hszD2]; decide)) (h0o (by rw [hszD2]; decide))
      (hhome0 (by rw [hszH2]; decide)) (h3o (by rw [hszD2]; decide))
      (hhome3 (by rw [hszH2]; decide)) hsub
  exact ⟨bF, bA, mvF, hfrob, hmv, hadd, hhome, hheld⟩

theorem basis_trits (n j : Nat) (hj : j < n) : allTritList (basisPeg n j) := by
  intro z hz
  rcases List.mem_iff_getElem.mp hz with ⟨i, hi, rfl⟩
  have hlenB : (basisPeg n j).length = n := by
    simp [basisPeg, List.length_set, List.length_replicate]
  have hi' : i < n := by
    rwa [hlenB] at hi
  unfold basisPeg
  by_cases h : i = j
  · subst h
    rw [List.getElem_set_self]
    decide
  · rw [List.getElem_set_ne (Ne.symm h) (by simpa [List.length_replicate] using hi'),
      List.getElem_replicate]
    decide

/-- Demo discharges the nonempty run: `e_j − e_j³` is not the zero home. -/
theorem demo_cofactor_chord_add (b : Board) (y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx c3 : Nat) (red : Bool) (j : Nat)
    (hj : 0 < j) (hjn : j < 7)
    (hsh : TierShape demo) (sat : TierSat demo)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hy : y.length = demo.n)
    (hyt : allTritList y)
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
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed (basisPeg demo.n j))
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed (basisPeg demo.n j))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * demo.n + 6 * (demo.benchlen - demo.n)))
    (hSl : FitsLen (slides + 4 * demo.n))
    (hChord : FitsLen (moves + 10 * demo.n + 6 * (demo.benchlen - demo.n))) :
    ∃ (bF bA : Board),
      frobenius_affine b = .ok bF ∧
      Ecbs.chord_add_demo bF red = chordAddTail bA red := by
  have hx : (basisPeg demo.n j).length = demo.n := by
    simp [basisPeg, List.length_set, List.length_replicate, hjn]
  have hsub := demo_run_ne j hj hjn
  obtain ⟨bF, bA, _, hfrob, _, hadd, _, _⟩ :=
    cofactor_chord_add b demo (basisPeg demo.n j) y moves slides pk peakS holeN cOps ctrl mx c3
      red hsh sat hszH hszD hops hops3 hx hy (basis_trits demo.n j (by simpa [demo] using hjn))
      hyt hmk hoff hmark hc hmx hT hop1 hop3 hfitC hfitD hfitU hfops hheld0 hhome0 hheld1
      hhome1 h2 h3t h3a hmoves hslides hpeak hstrict hhole hMv hSl hChord
      (by decide) (by decide) (by decide) (by decide) hsub
  exact ⟨bF, bA, hfrob, hadd⟩

end EcbsLink2.Link2
