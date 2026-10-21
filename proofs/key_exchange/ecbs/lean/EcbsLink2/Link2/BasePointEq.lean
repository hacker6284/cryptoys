/-
  `base_point` is the emitted search loop, then the join.
  The join is proved equal to the seat, the cofactor walk, and the move back.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Basic
import EcbsLink2.Link2.SearchCofactor
import EcbsLink2.Link2.FinishBranch

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs

/-- The join `base_point` runs after the search loop. -/
def basePointAfter (σ : Int × (Board × Int)) : Except SudoRt.Trap (Int × Board) :=
    let b := σ.2.1
    let _sp1480 := σ.2.2
    let found := _sp1480
    do
      let _as1437 ← SudoRt.sudoAssert (decide (found > (0 : Int))) 963
      let _io1438 ← clear b gap
      let b := _io1438
      let _io1439 ← clear b bottom
      let b := _io1439
      let _io1440 ← clear b across
      let b := _io1440
      let _io1441 ← move_band b base_up up
      let b := _io1441
      let _t1442 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_14key_grid_moves (4 : Int)
      let _t1443 := ({ (b).sudo_5Board_4cost with sudo_5Costs_14key_grid_moves := _t1442 } : Costs)
      let _t1444 := ({ b with sudo_5Board_4cost := _t1443 } : Board)
      let b := _t1444
      let wrwr := (#[(1 : Int), (2 : Int), (1 : Int), (2 : Int)] : Array (Int))
      if ((b).sudo_5Board_1t).sudo_4Tier_4demo then
        do
          let _io1445 ← walk_chord b wrwr
          let ⟨_ret1446, _iw01447⟩ := _io1445
          let b := _iw01447
          let _sudo_h0 := _ret1446
          let ⟨live, ok⟩ := _sudo_h0
          let _t1448 ← (if live then (do
  pure ok) else pure false)
          let _as1449 ← SudoRt.sudoAssert _t1448 972
          let _t1450 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_14key_grid_moves (4 : Int)
          let _t1451 := ({ (b).sudo_5Board_4cost with sudo_5Costs_14key_grid_moves := _t1450 } : Costs)
          let _t1452 := ({ b with sudo_5Board_4cost := _t1451 } : Board)
          let b := _t1452
          if (!( ((b).sudo_5Board_1t).sudo_4Tier_4demo )) then
            do
              let _io1453 ← finish b
              let b := _io1453
              let _io1454 ← clear b base_across
              let b := _io1454
              let _io1455 ← clear b base_up
              let b := _io1455
              let _io1456 ← move_band b base_across across
              let b := _io1456
              let _io1457 ← move_band b base_up up
              let b := _io1457
              pure (found, b)
          else
            do
              let _io1458 ← clear b base_across
              let b := _io1458
              let _io1459 ← clear b base_up
              let b := _io1459
              let _io1460 ← move_band b base_across across
              let b := _io1460
              let _io1461 ← move_band b base_up up
              let b := _io1461
              pure (found, b)
      else
        do
          let _io1462 ← walk_fform b wrwr
          let ⟨_ret1463, _iw01464⟩ := _io1462
          let b := _iw01464
          let _sudo_h1 := _ret1463
          let ⟨live, ok⟩ := _sudo_h1
          let _t1465 ← (if live then (do
  pure ok) else pure false)
          let _as1466 ← SudoRt.sudoAssert _t1465 975
          let _t1467 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_14key_grid_moves (4 : Int)
          let _t1468 := ({ (b).sudo_5Board_4cost with sudo_5Costs_14key_grid_moves := _t1467 } : Costs)
          let _t1469 := ({ b with sudo_5Board_4cost := _t1468 } : Board)
          let b := _t1469
          if (!( ((b).sudo_5Board_1t).sudo_4Tier_4demo )) then
            do
              let _io1470 ← finish b
              let b := _io1470
              let _io1471 ← clear b base_across
              let b := _io1471
              let _io1472 ← clear b base_up
              let b := _io1472
              let _io1473 ← move_band b base_across across
              let b := _io1473
              let _io1474 ← move_band b base_up up
              let b := _io1474
              pure (found, b)
          else
            do
              let _io1475 ← clear b base_across
              let b := _io1475
              let _io1476 ← clear b base_up
              let b := _io1476
              let _io1477 ← move_band b base_across across
              let b := _io1477
              let _io1478 ← move_band b base_up up
              let b := _io1478
              pure (found, b)

/-- One index of the emitted search. `n` and `toV` are the bounds
`base_point` closes over. -/
def emittedHole (n toV : Int) (σ : Int × (Board × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Board × Int)) (Int × Board)) :=
    let j := σ.1
    let b := σ.2.1
    let _sp1479 := σ.2.2
    let found := _sp1479
    do
      if j > toV then
        pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (j, (b, found)))
      else
        match ← ((do
  let _t1384 ← SudoRt.filledL n (0 : Int)
  let x := _t1384
  let _ix1385 := j
  let _t1386 ← SudoRt.putL x _ix1385 (1 : Int)
  let x := _t1386
  let _io1387 ← put b base_across x
  let b := _io1387
  let _io1388 ← curve_side b base_across bottom
  let b := _io1388
  let _io1389 ← mul b gap bottom bottom true false false
  let b := _io1389
  let _io1390 ← settle b
  let b := _io1390
  let _io1391 ← white0 b up
  let b := _io1391
  let _t1392 ← SudoRt.filledL n (0 : Int)
  let strip := _t1392
  let _t1398 ← SudoRt.subI n (2 : Int)
  let _fromV := (0 : Int)
  let toV := _t1398
  let fuel : Nat := fuelRange _fromV toV
  let _init1434 := (_fromV, strip)
  let _out ← (SudoRt.runLoopOn (ρ := (Int) × (Board)) _init1434 fuel (fun σ =>
    let i := σ.1
    let strip := σ.2
    do
      if i > toV then
        pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, strip))
      else
        match ← ((do
  let _t1394 ← SudoRt.modI i (2 : Int)
  if (SudoRt.SEq.beq _t1394 (0 : Int)) then
    do
      let _ix1396 := i
      let _t1397 ← SudoRt.putL strip _ix1396 (2 : Int)
      let strip := _t1397
      pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) strip)
  else
    do
      pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) strip)) : Except SudoRt.Trap (SudoRt.Flow _ ((Int) × (Board)))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := (Int) × (Board)) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, _fs))
        | .cont _fs => do
            if i == toV then
              pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) (i', _fs))) (fun σ =>
    let strip := σ.2
    do
      let _t1399 ← SudoRt.subI n (2 : Int)
      let _ix1400 := _t1399
      let _t1401 ← SudoRt.putL strip _ix1400 (1 : Int)
      let strip := _t1401
      let _io1402 ← put b across strip
      let b := _io1402
      let _t1403 := ({ b with sudo_5Board_9marker_on := true } : Board)
      let b := _t1403
      let _t1419 ← SudoRt.subI n (2 : Int)
      let _fromV := (0 : Int)
      let toV := _t1419
      let fuel : Nat := fuelRange _fromV toV
      let _init1433 := (_fromV, b)
      let _out ← (SudoRt.runLoopOn (ρ := (Int) × (Board)) _init1433 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > toV then
        pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, b))
      else
        match ← ((do
  let _t1405 ← SudoRt.atL strip i
  let d := _t1405
  let _io1406 ← marker_lift b
  let b := _io1406
  let _io1407 ← cube b up up
  let b := _io1407
  if (!(SudoRt.SEq.beq d (0 : Int))) then
    do
      if (SudoRt.SEq.beq d (2 : Int)) then
        do
          let _io1410 ← copy_band b spare gap false
          let b := _io1410
          let _io1411 ← mul b up up spare false false false
          let b := _io1411
          let _io1412 ← clear b up
          let b := _io1412
          let _io1413 ← settle b
          let b := _io1413
          pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) b)
      else
        do
          let _io1414 ← copy_band b spare bottom false
          let b := _io1414
          let _io1415 ← mul b up up spare false false false
          let b := _io1415
          let _io1416 ← clear b up
          let b := _io1416
          let _io1417 ← settle b
          let b := _io1417
          pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) b)
  else
    do
      let _io1418 ← settle b
      let b := _io1418
      pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) b)) : Except SudoRt.Trap (SudoRt.Flow _ ((Int) × (Board)))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := (Int) × (Board)) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, _fs))
        | .cont _fs => do
            if i == toV then
              pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) (i', _fs))) (fun σ =>
    let b := σ.2
    do
      let _io1420 ← marker_lift b
      let b := _io1420
      let _t1421 := ({ b with sudo_5Board_9marker_on := false } : Board)
      let b := _t1421
      let _io1422 ← clear b gap
      let b := _io1422
      let _io1423 ← mul b gap up up true false false
      let b := _io1423
      let _io1424 ← settle b
      let b := _io1424
      let _t1425 ← value b gap
      let _t1426 ← value b bottom
      if (SudoRt.SEq.beq _t1425 _t1426) then
        do
          let found := j
          pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (b, found))
      else
        do
          let _io1428 ← clear b gap
          let b := _io1428
          let _io1429 ← clear b bottom
          let b := _io1429
          let _io1430 ← clear b up
          let b := _io1430
          let _io1431 ← clear b across
          let b := _io1431
          let _io1432 ← clear b base_across
          let b := _io1432
          pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) (b, found))) (fun r => pure (SudoRt.Flow.ret (ρ := (Int) × (Board)) r)))
      pure _out) (fun r => pure (SudoRt.Flow.ret (ρ := (Int) × (Board)) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ ((Int) × (Board)))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := (Int) × (Board)) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (j, _fs))
        | .cont _fs => do
            if j == toV then
              pure (SudoRt.Flow.brk (ρ := (Int) × (Board)) (j, _fs))
            else do
              let i' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := (Int) × (Board)) (i', _fs))

/-- The emitted `base_point`. Fuel is `fuelRange`, the step is `emittedHole`,
    and the join is `basePointAfter`. -/
def basePointBlocks (b : Board) : Except SudoRt.Trap (Int × Board) :=
  do
    let n := ((b).sudo_5Board_1t).sudo_4Tier_1n
    let found := (0 : Int)
    let _t1435 ← SudoRt.subI n (1 : Int)
    let _fromV := (1 : Int)
    let _toV := _t1435
    let fuel : Nat := fuelRange _fromV _toV
    let _init1481 := (_fromV, (b, found))
    let _out ← (SudoRt.runLoopOn (ρ := (Int) × (Board)) _init1481 fuel (emittedHole n _toV) basePointAfter (fun r => pure r))
    pure _out

theorem base_point_eq_blocks (b : Board) :
    base_point b = basePointBlocks b := by
  unfold basePointBlocks emittedHole basePointAfter
  rfl

private theorem except_bind_assoc {α β γ : Type} (m : Except SudoRt.Trap α)
    (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  cases m <;> rfl

/-- The four clears and the band move are `cofactorSeat`. -/
private theorem seat_prefix {α : Type} (b : Board) (k : Board → Except SudoRt.Trap α) :
    (do
        let b ← clear b gap
        let b ← clear b bottom
        let b ← clear b across
        let b ← move_band b base_up up
        k b) =
      (cofactorSeat b >>= k) := by
  unfold cofactorSeat
  simp only [except_bind_assoc]

/-- Four key-grid moves, the way `base_point` counts the seat and the walk. -/
def gridAdd (b : Board) : Except SudoRt.Trap Board :=
  do
    let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves (4 : Int)
    pure ({ b with
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_14key_grid_moves := m } } : Board)

private theorem grid_prefix {α : Type} (b : Board) (k : Board → Except SudoRt.Trap α) :
    (do
        let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves (4 : Int)
        let c := ({ b.sudo_5Board_4cost with
          sudo_5Costs_14key_grid_moves := m } : Costs)
        let b2 := ({ b with sudo_5Board_4cost := c } : Board)
        let b := b2
        k b) =
      (gridAdd b >>= k) := by
  unfold gridAdd
  simp only [except_bind_assoc, pure_eq_ok, ok_bind]

private theorem grid_lets {α : Type} (b : Board) (k : Board → Except SudoRt.Trap α) :
    (do
        let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves (4 : Int)
        let c := ({ b.sudo_5Board_4cost with
          sudo_5Costs_14key_grid_moves := m } : Costs)
        let b2 := ({ b with sudo_5Board_4cost := c } : Board)
        let b := b2
        k b) =
      (do
          let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves (4 : Int)
          let c := ({ b.sudo_5Board_4cost with
            sudo_5Costs_14key_grid_moves := m } : Costs)
          let b2 := ({ b with sudo_5Board_4cost := c } : Board)
          let b := b2
          k b) := by
  rfl

/-- The clear and the two moves, with the search hole beside the board. -/
private theorem back_prefix (b : Board) (found : Int) :
    (do
        let b ← clear b base_across
        let b ← clear b base_up
        let b ← move_band b base_across across
        let b ← move_band b base_up up
        pure (found, b)) =
      pointBackPair b found := by
  unfold pointBackPair
  simp only [except_bind_assoc, pure_eq_ok, ok_bind]

private theorem finish_back_prefix (b : Board) (found : Int) :
    (do
        let b ← finish b
        let b ← clear b base_across
        let b ← clear b base_up
        let b ← move_band b base_across across
        let b ← move_band b base_up up
        pure (found, b)) =
      finishBackPair b found := by
  unfold finishBackPair
  simp only [except_bind_assoc, back_prefix]

/-- The `if` after either cofactor walk. -/
private theorem walk_back (b : Board) (found : Int) :
    (if (!(b.sudo_5Board_1t.sudo_4Tier_4demo)) then
        (do
            let b ← finish b
            let b ← clear b base_across
            let b ← clear b base_up
            let b ← move_band b base_across across
            let b ← move_band b base_up up
            pure (found, b))
      else
        (do
            let b ← clear b base_across
            let b ← clear b base_up
            let b ← move_band b base_across across
            let b ← move_band b base_up up
            pure (found, b))) =
      afterWalk b found := by
  unfold afterWalk finishBackPair
  simp only [back_prefix]

private theorem seat_lets {α : Type} (b : Board) (k : Board → Except SudoRt.Trap α) :
    (do
        let io ← clear b gap
        let b := io
        let io ← clear b bottom
        let b := io
        let io ← clear b across
        let b := io
        let io ← move_band b base_up up
        let b := io
        k b) =
      (do
          let b ← clear b gap
          let b ← clear b bottom
          let b ← clear b across
          let b ← move_band b base_up up
          k b) := by
  rfl

/-- The seat inside the join is `cofactorSeat`. -/
theorem base_point_seat {α : Type} (b : Board) (k : Board → Except SudoRt.Trap α) :
    (do
        let b ← clear b gap
        let b ← clear b bottom
        let b ← clear b across
        let b ← move_band b base_up up
        k b) =
      (cofactorSeat b >>= k) :=
  seat_prefix b k

/-- After the cofactor walk, `base_point` is `afterWalk`: `finish` on every
    tier but Demo, then the same clear and move. -/
theorem base_point_back (b : Board) (found : Int) :
    (if (!(b.sudo_5Board_1t.sudo_4Tier_4demo)) then
        (do
            let b ← finish b
            let b ← clear b base_across
            let b ← clear b base_up
            let b ← move_band b base_across across
            let b ← move_band b base_up up
            pure (found, b))
      else
        (do
            let b ← clear b base_across
            let b ← clear b base_up
            let b ← move_band b base_across across
            let b ← move_band b base_up up
            pure (found, b))) =
      afterWalk b found :=
  walk_back b found

end EcbsLink2.Link2
