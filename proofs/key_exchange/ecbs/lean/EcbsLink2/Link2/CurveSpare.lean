/-
  The spare multiply and its settle, on the abstract cube board. The tail
  lemma's hypotheses are the conclusion. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CurveCopy
import EcbsLink2.Link2.CurveTest

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem spareFits
    (mvC slC pegC pegX pegSq pegA pegB sch fold n bench : Nat)
    (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hmv : mvC ≤ n * (n + 1) + 6 * (bench - n) + 10 * n)
    (hsl : slC ≤ 2 * n)
    (hpc : pegC ≤ n) (hpx : pegX ≤ n) (hpsq : pegSq ≤ n)
    (hpa : pegA ≤ n) (hpb : pegB ≤ n)
    (hsch : sch ≤ n * (n + 1)) (hfold : fold ≤ 3 * (bench - n)) :
    FitsLen n ∧
    FitsLen bench ∧
    FitsLen (2 * pegC) ∧
    FitsLen (mvC + 2 * pegC) ∧
    FitsLen (slC + 2 * pegC) ∧
    FitsLen 2 ∧
    FitsLen (mvC + 2 * pegC + pegX) ∧
    FitsLen (mvC + 2 * pegC + pegX + n * (n + 1)) ∧
    FitsLen (mvC + 2 * pegC + pegX + n * (n + 1) + 3 * (bench - n)) ∧
    FitsLen (2 * (n - 1)) ∧
    FitsLen (2 * pegSq) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq) ∧
    FitsLen (slC + 2 * pegC + 2 * pegSq) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + n) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1 + pegB) ∧
    FitsLen ((mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1 + pegB + n) := by
  let cap := 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8
  have h : n ≤ cap ∧ bench ≤ cap ∧ 2 * pegC ≤ cap ∧ mvC + 2 * pegC ≤ cap ∧
      slC + 2 * pegC ≤ cap ∧ (2 : Nat) ≤ cap ∧
      mvC + 2 * pegC + pegX ≤ cap ∧
      mvC + 2 * pegC + pegX + n * (n + 1) ≤ cap ∧
      mvC + 2 * pegC + pegX + n * (n + 1) + 3 * (bench - n) ≤ cap ∧
      2 * (n - 1) ≤ cap ∧ 2 * pegSq ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq ≤ cap ∧
      slC + 2 * pegC + 2 * pegSq ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + n ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1 ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1 + pegB ≤ cap ∧
      (mvC + 2 * pegC + pegX + sch + fold) + 2 * pegSq + pegA + pegA + 1 + pegB + n ≤ cap := by
    dsimp [cap]
    omega
  exact ⟨curveLayFit n bench n hn hb h.1,
    curveLayFit n bench bench hn hb h.2.1,
    curveLayFit n bench _ hn hb h.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    curveLayFit n bench _ hn hb h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Square the across on the cube board and settle that square into the spare.
    The conjuncts are what `curve_suffix` reads. -/
theorem curve_spare_step (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (b : Ecbs.Board) (x y : List Nat)
    (pkC peakC holeC mvC slC : Nat)
    (hx : x.length = t.n) (hxt : allTritList x)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = Ecbs.bottom)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hheld2 : ∀ (h : 2 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[2] = false)
    (hhome2 : ∀ (h : 2 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[2] = (#[] : Array Int))
    (hheld3 : ∀ (h : 3 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[3] = true)
    (hhome3 : ∀ (h : 3 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[3] = embed x)
    (hheld4 : ∀ (h : 4 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[4] = true)
    (hhome4 : ∀ (h : 4 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[4] = embed y)
    (hheld5 : ∀ (h : 5 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[5] = true)
    (hhome5 : ∀ (h : 5 < b.sudo_5Board_4home.size),
      b.sudo_5Board_4home[5] = embed (fieldMul t.n t.k t.benchlen y y))
    (hheld6 : ∀ (h : 6 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[6] = false)
    (hbench : b.sudo_5Board_5bench =
      embed (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)))
    (htake : (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).take t.n =
      fieldCube t.n t.k t.benchlen x)
    (hlen : (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).length = t.benchlen)
    (hzero : ∀ i, t.n ≤ i →
      ∀ hi : i < (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).length,
        (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x))[i] = 0)
    (hmov : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slC)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkC)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakC)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC)
    (hT : b.sudo_5Board_1t = embTier t)
    (hops0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : ∀ (h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1)
    (hmv : mvC ≤ t.n * (t.n + 1) + 6 * (t.benchlen - t.n) + 10 * t.n)
    (hslC : slC ≤ 2 * t.n) :
    ∃ (bS : Ecbs.Board) (mvF : Nat)
      (h2H : 2 < bS.sudo_5Board_4home.size) (h2D : 2 < bS.sudo_5Board_4held.size)
      (h5H : 5 < bS.sudo_5Board_4home.size) (h5D : 5 < bS.sudo_5Board_4held.size)
      (h6H : 6 < bS.sudo_5Board_4home.size) (h6D : 6 < bS.sudo_5Board_4held.size),
      (Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false >>=
          Ecbs.settle) = .ok bS ∧
      bS.sudo_5Board_4held[2]'h2D = true ∧
      bS.sudo_5Board_4home[2]'h2H = embed (fieldCube t.n t.k t.benchlen x) ∧
      bS.sudo_5Board_4held[5]'h5D = true ∧
      bS.sudo_5Board_4home[5]'h5H = embed (fieldMul t.n t.k t.benchlen y y) ∧
      bS.sudo_5Board_4held[6]'h6D = true ∧
      bS.sudo_5Board_4home[6]'h6H = embed (fieldMul t.n t.k t.benchlen x x) ∧
      bS.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvF : Int) ∧
      FitsLen (mvF + t.n) ∧
      FitsLen t.n ∧
      FitsLen (mvF + pegCount (fieldMul t.n t.k t.benchlen x x) +
        pegCount (fieldMul t.n t.k t.benchlen x x)) ∧
      FitsLen (mvF + pegCount (fieldMul t.n t.k t.benchlen x x) +
        pegCount (fieldMul t.n t.k t.benchlen x x) + 1) ∧
      FitsLen (mvF + pegCount (fieldMul t.n t.k t.benchlen x x) +
        pegCount (fieldMul t.n t.k t.benchlen x x) + 1 +
        pegCount (fieldMul t.n t.k t.benchlen y y)) ∧
      FitsLen (mvF + pegCount (fieldMul t.n t.k t.benchlen x x) +
        pegCount (fieldMul t.n t.k t.benchlen x x) + 1 +
        pegCount (fieldMul t.n t.k t.benchlen y y) + t.n) := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let cLane := laneFold n (n - k) (combStrip n bench x)
  have hnb : n ≤ bench := mul_span_n n bench lay.board.n_pos lay.mul_span
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h6H : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hposC : 0 < cLane.length := by
    rw [show cLane.length = bench from by simpa [cLane, n, k, bench] using hlen]
    exact Nat.lt_of_lt_of_le lay.board.n_pos hnb
  have hnleC : n ≤ cLane.length := by
    rw [show cLane.length = bench from by simpa [cLane, n, k, bench] using hlen]
    exact hnb
  have hzeroC : ∀ i, n ≤ i → ∀ hi : i < cLane.length, cLane[i] = 0 := by
    simpa [cLane, n, k, bench] using hzero
  have hbenchC : b.sudo_5Board_5bench = embed cLane := by
    simpa [cLane, n, k, bench] using hbench
  have hpegC : pegCount (cLane.take n) ≤ n :=
    Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hpegX : pegCount x ≤ n := by simpa [n, hx] using pegCount_le x
  let sch := school n x x (List.replicate bench 0) false
  have hschL : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length x x (List.replicate bench 0) false n
  have hschB : schoolMoves x x n n ≤ n * (n + 1) := schoolMoves_bound x x n
  have hfoldB : foldCharge n (n - k) sch ≤ 3 * (bench - n) := by
    simpa [hschL] using foldCharge_bound n (n - k) sch
  let x2 := fieldMul n k bench x x
  let y2 := fieldMul n k bench y y
  have hx2L : x2.length = n := by
    simpa [x2, n, k, bench] using fieldMul_length n k bench x x hnb
  have hy2L : y2.length = n := by
    simpa [y2, n, k, bench] using fieldMul_length n k bench y y hnb
  have hpegA : pegCount x2 ≤ n := Nat.le_trans (pegCount_le x2) (by rw [hx2L]; exact Nat.le_refl _)
  have hpegB : pegCount y2 ≤ n := Nat.le_trans (pegCount_le y2) (by rw [hy2L]; exact Nat.le_refl _)
  let xLane := laneFold n (n - k) sch
  have hxl : xLane.length = bench := by
    dsimp [xLane]
    rw [laneFold_length n (n - k) sch (by rw [hschL]; exact hnb)]
    exact hschL
  have hpegSq : pegCount (xLane.take n) ≤ n :=
    Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hfits := spareFits mvC slC (pegCount (cLane.take n)) (pegCount x)
      (pegCount (xLane.take n)) (pegCount x2) (pegCount y2)
      (schoolMoves x x n n) (foldCharge n (n - k) sch) n bench
      lay.n_small lay.small.2.2.2 hmv hslC hpegC hpegX hpegSq hpegA hpegB hschB hfoldB
  obtain ⟨hfN, hfB, hf2c, hfMc, hfSc, hf2, hfC, hfM, hfFold, hfSpan, hf2s, hfSet, hfSl,
      hfTail, hfAdd, hfW, hfG, hfBot⟩ := hfits
  have hto2 : b.sudo_5Board_8bench_to = ((2 : Nat) : Int) := by rw [hto]; rfl
  have hnB : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [hT]; exact ofNat_eq_natCast _
  have hps : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakC : Int) := by
    rw [hstrict]; exact ofNat_eq_natCast _
  have hmul := curve_mul_spare b x cLane w h r n k mvC slC holeC bench pkC peakC 1
    hmk hon hto2 h2H h2D h3H h3D h6H h6D h7
    (hheld2 h2D) (hheld3 h3D) (hhome3 h3H) (hheld6 h6D)
    hbenchC hnB hposC hnleC hzeroC hfN
    (by
      rw [show cLane.length = bench from by simpa [cLane, n, k, bench] using hlen]
      exact hfB)
    hmov hsl hpk hps hf2c hfMc hfSc hops0 (hop0 hops0) hf2
    (by simpa [n] using hx) hxt
    (by rw [hT]; rfl) (by rw [hT]; rfl) (by rw [hT]; rfl) (by rw [hT]; rfl) (by rw [hT]; rfl)
    hhole lay.board.n_pos lay.mul_span hfSpan hfB hfC hfM hfFold
    lay.w_pos lay.h_pos lay.r_lt lay.r_pos lay.n_eq lay.k_le lay.gap_eq
    lay.small lay.n_small
  obtain ⟨bM, hmulOk, honM, htoM, htakeX, hhome2M, hbenchX, hhighX, hmovM, hslM, htM,
      hh6M, hh2M, _hheldFr, hhomeFr, hszHM, hszDM, hpkEx⟩ := hmul
  obtain ⟨pkM, hpkM⟩ := hpkEx
  have h6HM : 6 < bM.sudo_5Board_4home.size := by rw [hszHM, hszH]; decide
  have h6DM : 6 < bM.sudo_5Board_4held.size := by rw [hszDM, hszD]; decide
  have h7M : 7 ≤ bM.sudo_5Board_4held.size := by rw [hszDM, hszD]; decide
  have hposX : 0 < xLane.length := by
    rw [hxl]; exact Nat.lt_of_lt_of_le lay.board.n_pos hnb
  have hnleX : n ≤ xLane.length := by rw [hxl]; exact hnb
  have hzeroX : ∀ i, n ≤ i → ∀ hi : i < xLane.length, xLane[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hxl]; exact hii
    have hc := hhighX i hi hbi
    have hget := coeff_eq_get xLane i hii
    exact hget.symm.trans (by simpa [xLane, sch, n, k, bench] using hc)
  have hbenchX' : bM.sudo_5Board_5bench = embed xLane := by
    simpa [xLane, sch, n, k, bench] using hbenchX
  have htakeSq : xLane.take n = x2 := by
    simpa [xLane, sch, x2, n, k, bench] using htakeX
  have hmovMul : bM.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mvC + 2 * pegCount (cLane.take n) + pegCount x +
        schoolMoves x x n n + foldCharge n (n - k) sch) := by
    simp only [mulMoves, sch] at hmovM
    simpa [n, k, bench, cLane] using hmovM
  have hslMul : bM.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slC + 2 * pegCount (cLane.take n)) := by
    simpa [n, cLane] using hslM
  have hset := curve_settle_spare bM xLane x2 n
      (mvC + 2 * pegCount (cLane.take n) + pegCount x + schoolMoves x x n n +
        foldCharge n (n - k) sch)
      (slC + 2 * pegCount (cLane.take n)) pkM
      h6HM h6DM h7M honM
      (by rw [htoM]; rfl)
      (hh6M h6DM) hbenchX'
      (by rw [htM, hT]; exact ofNat_eq_natCast _)
      hposX hnleX hzeroX hfN
      (by rw [hxl]; exact hfB)
      hmovMul hslMul hpkM
      hf2s hfSet hfSl
      htakeSq
  obtain ⟨bS, hsetOk, _hoff, hhome6, hheld6S, hhomeK, hheldK, hmovS, htS, hszHS, hszDS⟩ := hset
  have h2HS : 2 < bS.sudo_5Board_4home.size := by rw [hszHS, hszHM, hszH]; decide
  have h2DS : 2 < bS.sudo_5Board_4held.size := by rw [hszDS, hszDM, hszD]; decide
  have h5HS : 5 < bS.sudo_5Board_4home.size := by rw [hszHS, hszHM, hszH]; decide
  have h5DS : 5 < bS.sudo_5Board_4held.size := by rw [hszDS, hszDM, hszD]; decide
  have h6HS : 6 < bS.sudo_5Board_4home.size := by rw [hszHS, hszHM, hszH]; decide
  have h6DS : 6 < bS.sudo_5Board_4held.size := by rw [hszDS, hszDM, hszD]; decide
  have h2HM : 2 < bM.sudo_5Board_4home.size := by rw [hszHM, hszH]; decide
  have h2DM : 2 < bM.sudo_5Board_4held.size := by rw [hszDM, hszD]; decide
  have h5HM : 5 < bM.sudo_5Board_4home.size := by rw [hszHM, hszH]; decide
  have h5DM : 5 < bM.sudo_5Board_4held.size := by rw [hszDM, hszD]; decide
  have h5Hb : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h5Db : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  let mvF := mvC + 2 * pegCount (cLane.take n) + pegCount x + schoolMoves x x n n +
      foldCharge n (n - k) sch + 2 * pegCount (xLane.take n)
  refine ⟨bS, mvF, h2HS, h2DS, h5HS, h5DS, h6HS, h6DS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hfN, ?_, ?_, ?_, ?_⟩
  · rw [hmulOk, ok_bind]; exact hsetOk
  · exact (hheldK 2 h2DM h2DS (by decide)).trans (hh2M h2DM)
  · have h2eq := (hhomeK 2 h2HM h2HS (by decide)).trans (hhome2M h2HM)
    simpa [cLane, n, k, bench, htake] using h2eq
  · have h5m := hheld5 h5Db
    have hfr : bM.sudo_5Board_4held[5] = b.sudo_5Board_4held[5] := by
      exact _hheldFr 5 h5Db h5DM (by decide) (by decide)
    exact (hheldK 5 h5DM h5DS (by decide)).trans (hfr.trans h5m)
  · have h5m := (hhomeFr 5 h5Hb h5HM (by decide) (by decide)).trans (hhome5 h5Hb)
    exact (hhomeK 5 h5HM h5HS (by decide)).trans h5m
  · exact hheld6S h6DS
  · simpa [x2, n, k, bench] using hhome6 h6HS
  · rw [htS, htM, hT]; exact ofNat_eq_natCast _
  · simpa [mvF, ofNat_eq_natCast] using hmovS
  · simpa [mvF, n] using hfTail
  · simpa [mvF, n, x2, htakeSq] using hfAdd
  · simpa [mvF, n, x2, htakeSq] using hfW
  · simpa [mvF, n, x2, y2, htakeSq] using hfG
  · simpa [mvF, n, x2, y2, htakeSq] using hfBot

end EcbsLink2.Link2
