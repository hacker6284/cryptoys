/-
  The zero cell's `zBench` layout, from the cubed projective point.
  The comb stays in `FformZeroAt`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellInv
import EcbsLink2.Link2.Add

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul

private theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have hxs := embed_beq xs ys
  rw [h] at hxs
  rw [embed_beq ys ys] at hxs
  exact of_decide_eq_true (by simpa using hxs)

private theorem read_cell {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : ∀ hlt : i < a.size, a[i]'hlt = v := by
  intro hlt
  have heq := Array.getElem?_eq_getElem hlt
  rw [h] at heq
  exact Option.some.inj heq.symm

/-- Homes layout: the projective coordinates are the affine homes. -/
private theorem homes_ids
    (t : Spec.Tier) (b : Ecbs.Board) (px py xP yP zP : List Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hproj : ProjOn t b px py) :
    ∃ xQ yQ zQ wInv,
      xQ = xP ∧ yQ = yP ∧ zQ = zP ∧
      allTritList zQ ∧
      xQ = fieldMul t.n t.k t.benchlen px zQ ∧
      yQ = fieldMul t.n t.k t.benchlen py zQ ∧
      wInv.length = t.n ∧ allTritList wInv ∧
      fieldMul t.n t.k t.benchlen zQ wInv = onePeg t.n := by
  rcases hproj with ⟨xQ, yQ, zQ, lay, _hxQL, _hyQL, _hzQL, _hxQT, _hyQT, hzQT,
      hxQ, hyQ, _hzne, hQ0, hlay, wInv, hwL, hwT, hinv⟩
  have hxId : xQ = xP :=
    embed_inj ((hQ0 (by rw [hszH]; decide)).symm.trans h0)
  cases lay with
  | yBench =>
    rw [hoff] at hlay
    cases hlay.1
  | zBench =>
    have hfalse := hlay.2.2.2.2.2 (by rw [hszD]; decide)
    rw [hd2] at hfalse
    cases hfalse
  | homes =>
    have hyId : yQ = yP :=
      embed_inj ((hlay.2.1 (by rw [hszH]; decide)).symm.trans h1)
    have hzId : zQ = zP :=
      embed_inj ((hlay.2.2.1 (by rw [hszH]; decide)).symm.trans h2)
    exact ⟨xQ, yQ, zQ, wInv, hxId, hyId, hzId, hzQT, hxQ, hyQ, hwL, hwT, hinv⟩

private theorem cube_home
    (n k bench : Nat) (p xP zP xQ zQ : List Nat)
    (hxId : xQ = xP) (hzId : zQ = zP)
    (hxQ : xQ = fieldMul n k bench p zQ)
    (hmul : fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zQ) =
        fieldCube n k bench (fieldMul n k bench p zQ)) :
    fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zP) =
        fieldCube n k bench xP := by
  rw [← hzId, hmul, ← hxQ, hxId]

private theorem cube_ne_cast (n k bench : Nat) (zQ zP : List Nat) (hz : zQ = zP)
    (h : fieldCube n k bench zQ ≠ List.replicate n 0) :
    fieldCube n k bench zP ≠ List.replicate n 0 := by
  rw [← hz]
  exact h

private theorem cube_inv_cast (n k bench : Nat) (zQ zP w : List Nat) (hz : zQ = zP)
    (h : fieldMul n k bench (fieldCube n k bench zQ) (fieldCube n k bench w) = onePeg n) :
    fieldMul n k bench (fieldCube n k bench zP) (fieldCube n k bench w) = onePeg n := by
  rw [← hz]
  exact h

private theorem prod_len (n k bench : Nat) (p xP zP : List Nat) (hb : n ≤ bench)
    (hmul : fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zP) =
        fieldCube n k bench xP) :
    (fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zP)).length = n := by
  rw [hmul, fieldCube_length n k bench xP hb]

private theorem prod_trits (n k bench : Nat) (p xP zP : List Nat)
    (hx : allTritList xP) (hspan : 3 * (n - 1) < bench) (hk : k ≤ n)
    (hmul : fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zP) =
        fieldCube n k bench xP) :
    allTritList (fieldMul n k bench (fieldCube n k bench p) (fieldCube n k bench zP)) := by
  rw [hmul]
  exact fieldCube_trits n k bench xP hx hspan hk

/-- Cubing a homes-layout point leaves `Z³` on the bench. -/
theorem zero_zbench
    (t : Spec.Tier) (b bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hH1 : ∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true)
    (hH2 : ∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false)
    (hbon : bZ.sudo_5Board_8bench_on = true)
    (hto : bZ.sudo_5Board_8bench_to = (2 : Int))
    (lane : List Nat)
    (hbench : bZ.sudo_5Board_5bench = embed lane)
    (htake : lane.take t.n = fieldCube t.n t.k t.benchlen zP)
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0)
    (hhome0 : bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)))
    (hhome1 : bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP))) :
    ProjOn t bZ (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) := by
  rcases hAt with ⟨_, _, _, _, hpxT, hpyT, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hproj, _⟩
  obtain ⟨xQ, yQ, zQ, wInv, hxId, hyId, hzId, hzQT, hxQ, hyQ, hwL, hwT, hinv⟩ :=
    homes_ids t b px py xP yP zP hszH hszD h0 h1 h2 hd2 hoff hproj
  have hnb : t.n ≤ t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have hk : t.k < t.n := by
    have hgap : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
    omega
  have h3span : 3 * (t.n - 1) < t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have h2span : 2 * (t.n - 1) < t.benchlen := by omega
  have hcube := cube_point_inv t.n t.k t.benchlen px py zQ wInv hOk.n_pos hk hnb
    h2span h3span hpxT hpyT hzQT hwT (by rw [hzId]; exact hzL) hwL hinv
  have hxMul := cube_home t.n t.k t.benchlen px xP zP xQ zQ hxId hzId hxQ hcube.1
  have hyMul := cube_home t.n t.k t.benchlen py yP zP yQ zQ hyId hzId hyQ hcube.2.1
  have hzNe := cube_ne_cast t.n t.k t.benchlen zQ zP hzId hcube.2.2.2.1
  have hzw := cube_inv_cast t.n t.k t.benchlen zQ zP wInv hzId hcube.2.2.1
  have hxLen := prod_len t.n t.k t.benchlen px xP zP hnb hxMul
  have hyLen := prod_len t.n t.k t.benchlen py yP zP hnb hyMul
  have hzLen := fieldCube_length t.n t.k t.benchlen zP hnb
  have hxTri := prod_trits t.n t.k t.benchlen px xP zP hxT h3span hsh.k_le hxMul
  have hyTri := prod_trits t.n t.k t.benchlen py yP zP hyT h3span hsh.k_le hyMul
  have hzTri := fieldCube_trits t.n t.k t.benchlen zP hzT h3span hsh.k_le
  have hxHome : ∀ h : 0 < bZ.sudo_5Board_4home.size,
      bZ.sudo_5Board_4home[0] = embed
        (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
          (fieldCube t.n t.k t.benchlen zP)) := by
    intro h
    exact (read_cell _ 0 _ hhome0 h).trans (congrArg embed hxMul.symm)
  have hyHome : ∀ h : 1 < bZ.sudo_5Board_4home.size,
      bZ.sudo_5Board_4home[1] = embed
        (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
          (fieldCube t.n t.k t.benchlen zP)) := by
    intro h
    exact (read_cell _ 1 _ hhome1 h).trans (congrArg embed hyMul.symm)
  have hnle : t.n ≤ lane.length := by
    have hlenT : (lane.take t.n).length = min t.n lane.length := List.length_take _ _
    rw [htake, fieldCube_length t.n t.k t.benchlen zP hnb] at hlenT
    exact hlenT.symm ▸ Nat.min_le_right t.n lane.length
  refine ⟨fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
      (fieldCube t.n t.k t.benchlen zP),
    fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
      (fieldCube t.n t.k t.benchlen zP),
    fieldCube t.n t.k t.benchlen zP, .zBench,
    hxLen, hyLen, hzLen, hxTri, hyTri, hzTri, rfl, rfl, hzNe, hxHome,
    ⟨hbon, hto, ⟨lane, hbench, hnle, htake, hzero⟩, hyHome, hH1, hH2⟩,
    fieldCube t.n t.k t.benchlen wInv, hcube.2.2.2.2.1, hcube.2.2.2.2.2, hzw⟩

end EcbsLink2.Link2
