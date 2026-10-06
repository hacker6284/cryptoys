import MegaDreifachV3.Link2.FaceOfFound
import MegaDreifach.Link2.FaceTurn
import MegaDreifach.Link2.InjPos
import MegaDreifach.IV
import MegaDreifachV3.Link2.RunSimp

/-
  MegaDreifach v3 Link 2: the counted run state and one card step.
  `embedRun` embeds a model `Run` (position plus five counters) as the emitted record.
  `start_run`, `turn_run`, `count_find`, `count_relook`, `count_register_looks` refine their
  model counterparts while each counter update fits in an Int64 (`FitsLen`); `counterCap`
  (2^40) is a uniform bound under which every update of one card step fits.
  `card_colour_refines` is exact on every `Nat`. `card_step_refines`: on a position with
  bijective corner and edge tables and counters ≤ `counterCap`, the emitted `card_step` returns
  the model `cardStep` for every base face, rank ≤ 12, suit amount `k ∈ 1..4` and colour.
  The piece searches inside it use the found-invariants of `Link2/FaceOfFound.lean`.
-/

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifachV3.Em

/-! ## The run record -/

/-- The emitted `Run` of a model run. -/
def embedRun (r : Run) : Megadreifach.Run where
  sudo_3Run_1g := embedPos r.g
  sudo_3Run_4last := Int.ofNat r.last.val
  sudo_3Run_5turns := Int.ofNat r.turns
  sudo_3Run_6clicks := Int.ofNat r.clicks
  sudo_3Run_5finds := Int.ofNat r.finds
  sudo_3Run_7relooks := Int.ofNat r.relooks
  sudo_3Run_14register_looks := Int.ofNat r.registerLooks

/-- All five counters are at most `m`. -/
def CountersLe (r : Run) (m : Nat) : Prop :=
  r.turns ≤ m ∧ r.clicks ≤ m ∧ r.finds ≤ m ∧ r.relooks ≤ m ∧ r.registerLooks ≤ m

/-- The counter bound under which no counter update overflows (far above any run). -/
def counterCap : Nat := 2 ^ 40

theorem fits_of_cap {n : Nat} (h : n ≤ counterCap + 16) : FitsLen n := by
  unfold FitsLen i64MaxNat; unfold counterCap at h; omega

/-! Counter projections of the run steps (the `run_proj` simp set). -/
section counters
variable (r : Run) (f : Fin 12) (a : Nat)
@[run_proj] theorem turnRun_g : (turnRun r f a).g = faceTurn r.g f a := rfl
@[run_proj] theorem turnRun_turns : (turnRun r f a).turns = r.turns + 1 := rfl
@[run_proj] theorem turnRun_clicks : (turnRun r f a).clicks = r.clicks + a := rfl
@[run_proj] theorem turnRun_finds : (turnRun r f a).finds = r.finds := rfl
@[run_proj] theorem turnRun_relooks : (turnRun r f a).relooks = r.relooks := rfl
@[run_proj] theorem turnRun_registerLooks : (turnRun r f a).registerLooks = r.registerLooks := rfl
@[run_proj] theorem countFind_g : (countFind r).g = r.g := rfl
@[run_proj] theorem countFind_turns : (countFind r).turns = r.turns := rfl
@[run_proj] theorem countFind_clicks : (countFind r).clicks = r.clicks := rfl
@[run_proj] theorem countFind_finds : (countFind r).finds = r.finds + 1 := rfl
@[run_proj] theorem countFind_relooks : (countFind r).relooks = r.relooks := rfl
@[run_proj] theorem countFind_registerLooks : (countFind r).registerLooks = r.registerLooks := rfl
@[run_proj] theorem countRelook_g : (countRelook r).g = r.g := rfl
@[run_proj] theorem countRelook_turns : (countRelook r).turns = r.turns := rfl
@[run_proj] theorem countRelook_clicks : (countRelook r).clicks = r.clicks := rfl
@[run_proj] theorem countRelook_finds : (countRelook r).finds = r.finds := rfl
@[run_proj] theorem countRelook_relooks : (countRelook r).relooks = r.relooks + 1 := rfl
@[run_proj] theorem countRelook_registerLooks : (countRelook r).registerLooks = r.registerLooks := rfl
@[run_proj] theorem countRegisterLooks_g : (countRegisterLooks r).g = r.g := rfl
@[run_proj] theorem countRegisterLooks_turns : (countRegisterLooks r).turns = r.turns := rfl
@[run_proj] theorem countRegisterLooks_clicks : (countRegisterLooks r).clicks = r.clicks := rfl
@[run_proj] theorem countRegisterLooks_finds : (countRegisterLooks r).finds = r.finds := rfl
@[run_proj] theorem countRegisterLooks_relooks : (countRegisterLooks r).relooks = r.relooks := rfl
@[run_proj] theorem countRegisterLooks_registerLooks :
    (countRegisterLooks r).registerLooks = r.registerLooks + 2 := rfl
end counters

theorem start_run_refines (h : Position) :
    Megadreifach.start_run (embedPos h) = .ok (embedRun (startRun h)) := rfl

theorem turn_run_refines (r : Run) (f : Fin 12) (amt : Nat)
    (ht : FitsLen (r.turns + 1)) (hc : FitsLen (r.clicks + amt)) :
    Megadreifach.turn_run (embedRun r) (Int.ofNat f.val) (Int.ofNat amt) =
      .ok (embedRun (turnRun r f amt)) := by
  unfold Megadreifach.turn_run
  rw [show (embedRun r).sudo_3Run_1g = embedPos r.g from rfl, face_turn_refines, ok_bind,
    show (embedRun r).sudo_3Run_5turns = Int.ofNat r.turns from rfl,
    show (1 : Int) = Int.ofNat 1 from rfl, addI_ofNat _ _ ht, ok_bind,
    show (embedRun r).sudo_3Run_6clicks = Int.ofNat r.clicks from rfl, addI_ofNat _ _ hc, ok_bind]
  rfl

theorem count_find_refines (r : Run) (h : FitsLen (r.finds + 1)) :
    Megadreifach.count_find (embedRun r) = .ok (embedRun (countFind r)) := by
  unfold Megadreifach.count_find
  rw [show (embedRun r).sudo_3Run_5finds = Int.ofNat r.finds from rfl,
    show (1 : Int) = Int.ofNat 1 from rfl, addI_ofNat _ _ h, ok_bind]
  rfl

theorem count_relook_refines (r : Run) (h : FitsLen (r.relooks + 1)) :
    Megadreifach.count_relook (embedRun r) = .ok (embedRun (countRelook r)) := by
  unfold Megadreifach.count_relook
  rw [show (embedRun r).sudo_3Run_7relooks = Int.ofNat r.relooks from rfl,
    show (1 : Int) = Int.ofNat 1 from rfl, addI_ofNat _ _ h, ok_bind]
  rfl

theorem count_register_looks_refines (r : Run) (h : FitsLen (r.registerLooks + 2)) :
    Megadreifach.count_register_looks (embedRun r) = .ok (embedRun (countRegisterLooks r)) := by
  unfold Megadreifach.count_register_looks
  rw [show (embedRun r).sudo_3Run_14register_looks = Int.ofNat r.registerLooks from rfl,
    show (2 : Int) = Int.ofNat 2 from rfl, addI_ofNat _ _ h, ok_bind]
  rfl

theorem card_colour_refines (card : Nat) :
    Megadreifach.card_colour (Int.ofNat card) = .ok (Int.ofNat (cardColour card).val) := by
  unfold Megadreifach.card_colour cardColour
  rw [show (4 : Int) = Int.ofNat 4 from rfl, divI_ofNat card (b := 4) (by decide), ok_bind]
  by_cases h : card / 4 < 12
  · have hd : decide (Int.ofNat (card / 4) < 12) = true := by
      simp; omega
    simp only [hd, if_true, dif_pos h]
    rfl
  · have hd : decide (Int.ofNat (card / 4) < 12) = false := by
      simp; omega
    simp only [hd, Bool.false_eq_true, if_false, dif_neg h]
    rfl

theorem opposites_table :
    allFin12 (fun f => isOkEq (SudoRt.atL Megadreifach.opposites (Int.ofNat f.val))
      (Int.ofNat (opp f).val)) = true := by
  decide!

theorem atL_opposites (f : Fin 12) :
    SudoRt.atL Megadreifach.opposites (Int.ofNat f.val) = .ok (Int.ofNat (opp f).val) :=
  isOkEq_spec (allFin12_spec opposites_table f)

theorem turn_run_refines1 (r : Run) (f : Fin 12)
    (ht : FitsLen (r.turns + 1)) (hc : FitsLen (r.clicks + 1)) :
    Megadreifach.turn_run (embedRun r) (Int.ofNat f.val) 1 = .ok (embedRun (turnRun r f 1)) :=
  turn_run_refines r f 1 ht hc

/-- `edge_face_of` on a run's position, for a card's edge `(c, n)` and `x ∈ {c, n}`. -/
theorem edge_face_of_run (r : Run) (hr : InjPos r.g) (c : Fin 12) (k : Nat) (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (x : Fin 12) (hx : x = c ∨ x = (suitNbrs c k).1) :
    Megadreifach.edge_face_of (embedRun r).sudo_3Run_1g (Int.ofNat c.val)
        (Int.ofNat (suitNbrs c k).1.val) (Int.ofNat x.val) =
      .ok (Int.ofNat (edgeFaceOf r.g c (suitNbrs c k).1 x).val) := by
  obtain ⟨s, hs, ⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := card_edge_found r.g hr.2 c k hk1 hk4
  rcases hx with rfl | rfl
  · rw [show edgeFaceOf r.g x (suitNbrs x k).1 x = y1 by simp [edgeFaceOf, hy1]]
    exact edge_face_of_refines r.g _ _ _ s hs y1 hy1
  · rw [show edgeFaceOf r.g c (suitNbrs c k).1 (suitNbrs c k).1 = y2 by simp [edgeFaceOf, hy2]]
    exact edge_face_of_refines r.g _ _ _ s hs y2 hy2

/-- `corner_face_of` on a run's position, for a card's corner `(c, n, n2)` and `x ∈ {c, n}`. -/
theorem corner_face_of_run (r : Run) (hr : InjPos r.g) (c : Fin 12) (k : Nat) (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (x : Fin 12) (hx : x = c ∨ x = (suitNbrs c k).1) :
    Megadreifach.corner_face_of (embedRun r).sudo_3Run_1g (Int.ofNat c.val)
        (Int.ofNat (suitNbrs c k).1.val) (Int.ofNat (suitNbrs c k).2.val) (Int.ofNat x.val) =
      .ok (Int.ofNat (cornerFaceOf r.g c (suitNbrs c k).1 (suitNbrs c k).2 x).val) := by
  obtain ⟨t, ht, ⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := card_corner_found r.g hr.1 c k hk1 hk4
  rcases hx with rfl | rfl
  · rw [show cornerFaceOf r.g x (suitNbrs x k).1 (suitNbrs x k).2 x = y1 by
      simp [cornerFaceOf, hy1]]
    exact corner_face_of_refines r.g _ _ _ _ t ht y1 hy1
  · rw [show cornerFaceOf r.g c (suitNbrs c k).1 (suitNbrs c k).2 (suitNbrs c k).1 = y2 by
      simp [cornerFaceOf, hy2]]
    exact corner_face_of_refines r.g _ _ _ _ t ht y2 hy2

/-- Side goals of the card-step rewrites: counter bounds and bijective tables. -/
macro "run_side" : tactic => `(tactic| first
  | (apply fits_of_cap; simp only [run_proj, counterCap]; omega)
  | ((repeat (first | assumption | apply injPos_faceTurn)); done))

/-- The model's `cardStep` after its face choice: the `k`-click turn of face `f` and the eight
moves that follow. `cardStep r base rank k c = cardTail r (turnedFace base rank) k c` by `rfl`. -/
def cardTail (r : Run) (f : Fin 12) (k : Nat) (c : Fin 12) : Run :=
  let r := turnRun r f k
  let n := (suitNbrs c k).1
  let n2 := (suitNbrs c k).2
  let r := countFind r
  let r := turnRun r (edgeFaceOf r.g c n c) 1
  let r := turnRun r (edgeFaceOf r.g c n n) 1
  let r := countFind r
  let r := turnRun r (cornerFaceOf r.g c n n2 c) 1
  let r := turnRun r (cornerFaceOf r.g c n n2 n) 1
  let r := countRelook r
  turnRun r (edgeFaceOf r.g c n n) 1

theorem cardStep_eq_cardTail (r : Run) (base : Fin 12) (rank k : Nat) (c : Fin 12) :
    cardStep r base rank k c = cardTail r (turnedFace base rank) k c := rfl

/-- The emitted `card_step` after its `if`: both branches of the generated body continue with this
same block, only the `turned` face differs. Restated here (as `chunkStep` in
`MegaDreifach/Link2/VHashCommon.lean` restates the emitted chunk loop) so the shared rewrite
chain is proved once, in `card_step_tail_refines`; if the emitter changes the block, the
`exact`s in `card_step_refines` fail. The emitted temporaries (`_t824` … `_t838` in the first
branch) have readable names here; binder names do not matter to the `exact`. -/
def cardStepTailE (r : Megadreifach.Run) (turned k c : Int) :
    Except SudoRt.Trap Megadreifach.Run := do
  let rTurned ← Megadreifach.turn_run r turned k
  let r := rTurned
  let nbrs ← Megadreifach.suit_nbrs c k
  let ⟨n, n2⟩ := nbrs
  let rFind1 ← Megadreifach.count_find r
  let r := rFind1
  let fEdgeC ← Megadreifach.edge_face_of (r).sudo_3Run_1g c n c
  let rEdgeC ← Megadreifach.turn_run r fEdgeC (1 : Int)
  let r := rEdgeC
  let fEdgeN ← Megadreifach.edge_face_of (r).sudo_3Run_1g c n n
  let rEdgeN ← Megadreifach.turn_run r fEdgeN (1 : Int)
  let r := rEdgeN
  let rFind2 ← Megadreifach.count_find r
  let r := rFind2
  let fCornerC ← Megadreifach.corner_face_of (r).sudo_3Run_1g c n n2 c
  let rCornerC ← Megadreifach.turn_run r fCornerC (1 : Int)
  let r := rCornerC
  let fCornerN ← Megadreifach.corner_face_of (r).sudo_3Run_1g c n n2 n
  let rCornerN ← Megadreifach.turn_run r fCornerN (1 : Int)
  let r := rCornerN
  let rRelook ← Megadreifach.count_relook r
  let r := rRelook
  let fLast ← Megadreifach.edge_face_of (r).sudo_3Run_1g c n n
  let rLast ← Megadreifach.turn_run r fLast (1 : Int)
  pure rLast

/-- The shared tail of `card_step_refines`: from any face `f`, the emitted block refines
`cardTail`. -/
theorem card_step_tail_refines (r : Run) (hg : InjPos r.g) (hb : CountersLe r counterCap)
    (f : Fin 12) (k : Nat) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (c : Fin 12) :
    cardStepTailE (embedRun r) (Int.ofNat f.val) (Int.ofNat k) (Int.ofNat c.val)
      = .ok (embedRun (cardTail r f k c)) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  unfold counterCap at b1 b2 b3 b4 b5
  unfold cardStepTailE
  rw [turn_run_refines _ _ _ ?_ ?_, ok_bind, suit_nbrs_refines c k hk1 hk4, ok_bind]
  dsimp only
  rw [count_find_refines _ ?_, ok_bind,
    edge_face_of_run _ ?_ c k hk1 hk4 c (Or.inl rfl), ok_bind, turn_run_refines1 _ _ ?_ ?_, ok_bind,
    edge_face_of_run _ ?_ c k hk1 hk4 _ (Or.inr rfl), ok_bind, turn_run_refines1 _ _ ?_ ?_, ok_bind,
    count_find_refines _ ?_, ok_bind,
    corner_face_of_run _ ?_ c k hk1 hk4 c (Or.inl rfl), ok_bind, turn_run_refines1 _ _ ?_ ?_, ok_bind,
    corner_face_of_run _ ?_ c k hk1 hk4 _ (Or.inr rfl), ok_bind, turn_run_refines1 _ _ ?_ ?_, ok_bind,
    count_relook_refines _ ?_, ok_bind,
    edge_face_of_run _ ?_ c k hk1 hk4 _ (Or.inr rfl), ok_bind, turn_run_refines1 _ _ ?_ ?_]
  · rfl
  all_goals run_side

/-- One card step. The hypotheses are sufficient, not necessary: bijective tables make the piece
    searches succeed, counters ≤ `counterCap` keep every counter update in Int64, and
    `rank ≤ 12`, `1 ≤ k ≤ 4` are the ranges a deal or an echo produces (a rank above 12 would
    also take the King branch on both sides). -/
theorem card_step_refines (r : Run) (hg : InjPos r.g) (hb : CountersLe r counterCap)
    (base : Fin 12) (rank k : Nat) (hrank : rank ≤ 12) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (c : Fin 12) :
    Megadreifach.card_step (embedRun r) (Int.ofNat base.val) (Int.ofNat rank) (Int.ofNat k)
      (Int.ofNat c.val) = .ok (embedRun (cardStep r base rank k c)) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  unfold counterCap at b1 b2 b3 b4 b5
  unfold Megadreifach.card_step
  rw [atL_opposites, ok_bind]
  by_cases hr : rank < 12
  · have hd : decide (Int.ofNat rank < 12) = true := by simp; omega
    have hfit : FitsLen (base.val + rank) := by unfold FitsLen i64MaxNat; omega
    rw [hd, if_pos rfl, addI_ofNat _ _ hfit, ok_bind, show (12 : Int) = Int.ofNat 12 from rfl,
      modI_ofNat _ (b := 12) (by decide), ok_bind,
      show Int.ofNat ((base.val + rank) % 12) = Int.ofNat (turnedFace base rank).val by
        simp [turnedFace, hr]]
    exact card_step_tail_refines r hg ⟨b1, b2, b3, b4, b5⟩ _ k hk1 hk4 c
  · have hd : decide (Int.ofNat rank < 12) = false := by simp; omega
    rw [hd, if_neg (by decide),
      show Int.ofNat (opp base).val = Int.ofNat (turnedFace base rank).val by
        simp [turnedFace, hr]]
    exact card_step_tail_refines r hg ⟨b1, b2, b3, b4, b5⟩ _ k hk1 hk4 c

end MegaDreifachV3.Link2
