/-
  The cofactor cell after the white copy. The accumulator is the root, the
  marker is still `-1`, and the flag is on. `down_across` cubes that board,
  and `frobenius_affine` writes the two field cubes.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusRead
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem shape_n_pos (n w h r : Nat)
    (heq : n = w * h - 1) (hw : 0 < w) (hr : 0 < r) (hlt : r < h) : 0 < n := by
  have hh : 2 ≤ h := by omega
  have hw1 : 1 ≤ w := by omega
  have hprod : 2 ≤ w * h := Nat.mul_le_mul hw1 hh
  omega

private theorem mv2_le (mv1 pegX moves n bench spent yPeg : Nat)
    (hmv : mv1 ≤ moves + 2 * n + 3 * (bench - n))
    (hpx : pegX ≤ n) (hy : yPeg ≤ n)
    (hspent : spent ≤ mv1 + 2 * pegX + 2 * n + 3 * (bench - n)) :
    spent + 2 * yPeg ≤ moves + 8 * n + 6 * (bench - n) := by
  omega

private theorem slide_add (slides pegX yPeg n : Nat) (hpx : pegX ≤ n) (hy : yPeg ≤ n) :
    slides + 2 * pegX + 2 * yPeg ≤ slides + 4 * n := by
  omega

/-- A copied root, marker still down, flag on. Frobenius cubes both homes. -/
theorem cofactor_frobenius (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx : Nat)
    (hsh : TierShape t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n)) :
    ∃ bF,
      frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube t.n t.k t.benchlen y)) := by
  have hm : b.sudo_5Board_6marker < 0 := by rw [hmark]; decide
  have hn0 : 0 < t.n := shape_n_pos t.n t.w t.h t.r hsh.n_eq hsh.w0 hsh.r0 hsh.rlt
  have hs1 : 1 < t.script := by
    have h := hsh.script_ge
    omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have h3 : FitsLen (3 * (t.n - 1)) := FitsLen.of_le hMv (by omega)
  have hnFit : FitsLen t.n := FitsLen.of_le hMv (by omega)
  have hbenchFit : FitsLen t.benchlen := FitsLen.of_le hMv (by omega)
  have hnb : t.n ≤ t.benchlen := by
    have h := sat.cube_span
    omega
  let a := down_across b x y t.w t.h t.r t.n t.k moves slides pk peakS holeN cOps ctrl mx
      t.script hszH hszD hops hx hy hxt hyt hmk hoff hm hc hmx
      (by simp [hT, embTier]) hs1 hfitD hfitU hop1 hfitC hheld0 hhome0 hheld1 hhome1
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) hmoves hslides hpeak hstrict hhole
      hsh.w0 hsh.h0 hsh.rlt hsh.r0 hn0 hsh.n_eq hsh.k_le hsh.gap hspan
      hsh.small hsh.n_small hMv hSl
  have hpegY : pegCount ((upLane t.n t.k t.benchlen y).take t.n) ≤ t.n := by
    have htake : (upLane t.n t.k t.benchlen y).take t.n =
        fieldCube t.n t.k t.benchlen y := upLane_take t.n t.k t.benchlen y
    have hlen := fieldCube_length t.n t.k t.benchlen y hnb
    rw [htake]
    have hle := pegCount_le (fieldCube t.n t.k t.benchlen y)
    rwa [hlen] at hle
  have hpeg : FitsLen (2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) :=
    FitsLen.of_le hMv (by omega)
  have hfitM : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) := by
    have hspent := cubeMoves_le (a.mv1 + 2 * a.pegX) y t.n t.k t.benchlen
    have hle := mv2_le a.mv1 a.pegX moves t.n t.benchlen (upMv2 a)
        (pegCount ((upLane t.n t.k t.benchlen y).take t.n)) a.hmv1le a.hpegX hpegY
        (by simpa [upMv2, upMv] using hspent)
    exact FitsLen.of_le hMv hle
  have hfitS : FitsLen (upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) := by
    have hle := slide_add slides a.pegX
        (pegCount ((upLane t.n t.k t.benchlen y).take t.n)) t.n a.hpegX hpegY
    simp [upSl]
    exact FitsLen.of_le hSl (by omega)
  have hlenL : t.n ≤ a.laneX.length := by
    rw [a.hlenX]
    exact hnb
  exact frobenius_affine_marker a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit
    hlenL hnb hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsh.small hsh.n_small
    hpeg hfitM hfitS

end EcbsLink2.Link2
