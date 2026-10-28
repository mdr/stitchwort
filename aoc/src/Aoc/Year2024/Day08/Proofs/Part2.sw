-- Part 2: the grid points in line with two antennas `first` and `second`
-- are `first` plus whole steps of `first.stepToward second`
-- (`onLineOfCross`), because the gcd makes the step's parts coprime
-- (`stepFacts`, from Bézout's identity); and on the map those steps are
-- fewer than its height or width (`stepsBound`), which `harmonics` takes
-- either way (`harmonicsCorrect`).

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Int, Iff, List, Nat, Or, Set, Void)

-- Dividing a multiple of a positive number by it.
theorem divExact: (value: Int) → (below: Nat) → (times: Nat) → Int.natAbs value = times * Succ below →
    (Succ below).toInt * (value / (Succ below).toInt) = value
  | OfNat n, below, times, multiple =>
    let quotient := Nat.divUnique n (Succ below) times 0 (omega) (rewrite multiple in ring)
    rewrite quotient in Eq.cong OfNat (rewrite multiple in ring)
  | NegSucc m, below, Zero, multiple => Void.exfalso (omega [multiple])
  | NegSucc m, below, Succ times, multiple =>
    let whole: m = times * Succ below + below := omega [multiple, (ring: Succ times * Succ below = times * Succ below + Succ below)]
    let quotient := Nat.divUnique m (Succ below) times below (omega) whole
    rewrite quotient in Eq.cong NegSucc (omega [whole, (ring: times + below * Succ times = times * Succ below + below)])

-- `|x|` is `x` times its sign.
theorem natAbsSign: (x: Int) → (Int.natAbs x).toInt = Int.sign x * x
  | OfNat Zero => rfl
  | OfNat (Succ n) => Eq.cong OfNat (omega)
  | NegSucc n => Eq.cong OfNat (omega)

-- `divideBy` the gcd, with the gcd as a variable: the difference is a
-- nonzero multiple of the result, whose parts are coprime.
theorem divideByFacts (difference: Position) (goal: Prop) (rowTimes: Nat) (columnTimes: Nat) (s: Int) (t: Int)
    (nonzero: And (difference.row = 0) (difference.column = 0) → Void):
    (divisor: Nat) → Int.natAbs difference.row = rowTimes * divisor → Int.natAbs difference.column = columnTimes * divisor →
      s * (Int.natAbs difference.row).toInt + t * (Int.natAbs difference.column).toInt = divisor.toInt →
      ((scale: Int) → Not (scale = 0) → difference.row = scale * (difference.divideBy divisor).row →
        difference.column = scale * (difference.divideBy divisor).column → (s: Int) → (t: Int) →
        s * (difference.divideBy divisor).row + t * (difference.divideBy divisor).column = 1 → goal) →
      goal
  | Zero, rows, columns, bezout, use =>
    Void.exfalso (nonzero (Both (Int.natAbsZero difference.row (omega [rows])) (Int.natAbsZero difference.column (omega [columns]))))
  | Succ below, rows, columns, bezout, use =>
    let scale := (Succ below).toInt
    let step := difference.divideBy (Succ below)
    let rowLaw: scale * step.row = difference.row := divExact difference.row below rowTimes rows
    let columnLaw: scale * step.column = difference.column := divExact difference.column below columnTimes columns
    let rowSign := Int.sign difference.row
    let columnSign := Int.sign difference.column
    let scaled: scale * (s * rowSign * step.row + t * columnSign * step.column) = scale * 1 :=
      ring [bezout, s * natAbsSign difference.row, t * natAbsSign difference.column, s * rowSign * rowLaw, t * columnSign * columnLaw]
    use scale (omega) (Eq.sym rowLaw) (Eq.sym columnLaw) (s * rowSign) (t * columnSign) (mulCancel scale _ 1 (omega) scaled)

-- The step to grid points from `start` towards `end`: `end - start` is a
-- nonzero multiple of it, and its parts are coprime (some whole combination
-- of them is 1).
theorem stepFacts (start: Position) (end: Position) (distinct: Not (start = end)) (goal: Prop)
    (use: (scale: Int) → Not (scale = 0) → end.row - start.row = scale * (start.stepToward end).row →
      end.column - start.column = scale * (start.stepToward end).column → (s: Int) → (t: Int) →
      s * (start.stepToward end).row + t * (start.stepToward end).column = 1 → goal):
    goal :=
  let difference := end.minus start
  let rowSize := Int.natAbs difference.row
  let columnSize := Int.natAbs difference.column
  let nonzero := (both: And (difference.row = 0) (difference.column = 0)) =>
    distinct (positionEq start end (Eq.sym (subEqZero end.row start.row (And.left both))) (Eq.sym (subEqZero end.column start.column (And.right both))))
  match gcdDivides rowSize columnSize with
    | Both (Witness rowTimes rows) (Witness columnTimes columns) =>
      match gcdBezout rowSize columnSize with
        | Witness s (Witness t bezout) => divideByFacts difference goal rowTimes columnTimes s t nonzero (Nat.gcd rowSize columnSize) rows columns bezout use

-- Points `k` steps from `first` are in line with it and `second`.
theorem crossOnLine (fr: Int) (fc: Int) (er: Int) (ec: Int) (scale: Int) (k: Int) (pr: Int) (pc: Int) (sr: Int) (sc: Int)
    (secondRow: sr = fr + scale * er) (secondColumn: sc = fc + scale * ec) (rowAt: pr = fr + er * k) (columnAt: pc = fc + ec * k):
    (fr - pr) * (sc - pc) - (fc - pc) * (sr - pr) = 0 :=
  rewrite secondRow, secondColumn, rowAt, columnAt in ring

-- And every point in line is a whole number of steps from `first`: the
-- cross product makes the offset parallel to the step, and with the step's
-- parts coprime (`s * er + t * ec = 1`) the number of steps is
-- `s * (pr - fr) + t * (pc - fc)`.
theorem onLineOfCross (fr: Int) (fc: Int) (er: Int) (ec: Int) (scale: Int) (s: Int) (t: Int) (pr: Int) (pc: Int) (sr: Int) (sc: Int)
    (secondRow: sr = fr + scale * er) (secondColumn: sc = fc + scale * ec) (nonzero: Not (scale = 0)) (bezout: s * er + t * ec = 1)
    (cross: (fr - pr) * (sc - pc) - (fc - pc) * (sr - pr) = 0):
    And (pr = fr + er * (s * (pr - fr) + t * (pc - fc))) (pc = fc + ec * (s * (pr - fr) + t * (pc - fc))) :=
  let crossScaled: scale * ((pc - fc) * er - (pr - fr) * ec) = scale * 0 := rewrite secondRow, secondColumn at cross in ring [cross]
  let parallel := mulCancel scale ((pc - fc) * er - (pr - fr) * ec) 0 nonzero crossScaled
  Both (ring [(pr - fr) * bezout, t * parallel]) (ring [(pc - fc) * bezout, s * parallel])

-- Two numbers below `n` are less than `n` apart.
theorem natAbsFrom (p: Nat) (a: Nat) (n: Nat) (below: p < n) (aBelow: a < n): (gap: Nat) → a - p = gap → Int.natAbs (Int.subNatNatFrom p a gap) < n
  | Zero, e => omega
  | Succ gap, e => omega

theorem natAbsDiffLt (p: Nat) (a: Nat) (n: Nat) (below: p < n) (aBelow: a < n): Int.natAbs (p.toInt - a.toInt) < n :=
  rewrite Int.subOfNats p a in natAbsFrom p a n below aBelow (a - p) rfl

-- A location on the map has whole coordinates inside it.
theorem containsElim (city: City) (goal: Prop): (position: Position) → city.contains position = True →
    ((row: Nat) → (column: Nat) → position.row = OfNat row → position.column = OfNat column → row < city.height → column < city.width → goal) → goal
  | { row = OfNat row, column = OfNat column }, inside, use => use row column rfl rfl (omega) (omega)
  | { row = OfNat row, column = NegSucc column }, inside, use => Void.exfalso (omega)
  | { row = NegSucc row, column }, inside, use => Void.exfalso (Bool.falseNotTrue inside)

-- Between two locations on a map `n` high, fewer than `n` steps of a
-- nonzero size.
theorem stepsBound (fr: Int) (pr: Int) (er: Int) (k: Int) (n: Nat) (a: Nat) (p: Nat) (fromAt: fr = OfNat a) (toAt: pr = OfNat p)
    (aBelow: a < n) (pBelow: p < n) (on: pr = fr + er * k) (nonzero: Not (er = 0)):
    Int.natAbs k < n :=
  let gap: Int.natAbs (er * k) < n := rewrite (ring [on]: er * k = pr - fr), toAt, fromAt in natAbsDiffLt p a n pBelow aBelow
  let positive: Not (Int.natAbs er = 0) := z => nonzero (Int.natAbsZero er z)
  omega [Int.natAbsMul er k, Nat.leMulPos (Int.natAbs k) (Int.natAbs er) (omega)]

-- A point a whole number of steps from `start`, within the map's reach, is
-- among the harmonics.
theorem harmonicsOfSteps (city: City) (start: Position) (end: Position) (point: Position): (k: Int) →
    point.row = start.row + (start.stepToward end).row * k → point.column = start.column + (start.stepToward end).column * k →
    Int.natAbs k < Nat.max city.height city.width → point ∈ city.harmonics start end
  | OfNat count, rowAt, columnAt, bound =>
    let step := start.stepToward end
    List.memFlatMapIntro ((count: Nat) => [start.plus (step.times count.toInt), start.minus (step.times count.toInt)]) count point
      (List.range (Nat.max city.height city.width)) (List.memRangeFromIntro count (Nat.max city.height city.width) 0 (omega) (omega))
      (Inl (positionEq (start.plus (step.times count.toInt)) point (Eq.sym rowAt) (Eq.sym columnAt)))
  | NegSucc count, rowAt, columnAt, bound =>
    let step := start.stepToward end
    List.memFlatMapIntro ((count: Nat) => [start.plus (step.times count.toInt), start.minus (step.times count.toInt)]) (Succ count) point
      (List.range (Nat.max city.height city.width)) (List.memRangeFromIntro (Succ count) (Nat.max city.height city.width) 0 (omega) (omega))
      (Inr (Inl (positionEq (start.minus (step.times (Succ count).toInt)) point (ring [rowAt]) (ring [columnAt]))))

theorem harmonicsCorrect (city: City) (first: Position) (second: Position) (firstOn: city.contains first = True) (distinct: Not (first = second))
    (point: Position) (inside: city.contains point = True):
    Iff (point ∈ city.harmonics first second) (inLine point first second = True) :=
  stepFacts first second distinct _ (scale scaleNonzero rows columns s t bezout =>
    let step := first.stepToward second
    let reach := Nat.max city.height city.width
    let secondRow: second.row = first.row + scale * step.row := ring [rows]
    let secondColumn: second.column = first.column + scale * step.column := ring [columns]
    let onLine := (k: Int) (rowAt: point.row = first.row + step.row * k) (columnAt: point.column = first.column + step.column * k) =>
      let cross :=
        crossOnLine first.row first.column step.row step.column scale k point.row point.column second.row second.column secondRow secondColumn rowAt
          columnAt
      (rewrite cross in rfl: inLine point first second = True)
    {
      forward = has =>
        List.anyElim (count => point ∈ [first.plus (step.times (count: Nat).toInt), first.minus (step.times count.toInt)]) _ (List.range reach)
          (List.memFlatMapElim ((count: Nat) => [first.plus (step.times count.toInt), first.minus (step.times count.toInt)]) point (List.range reach) has)
          (count countIn pointIn =>
            match pointIn with
              | Inl e => onLine count.toInt (Eq.sym (Eq.cong Position.row e)) (Eq.sym (Eq.cong Position.column e))
              | Inr (Inl e) => onLine (0 - count.toInt) (ring [Eq.cong Position.row e]) (ring [Eq.cong Position.column e])
              | Inr (Inr none) => Void.exfalso none),
      backward = h =>
        let steps := s * (point.row - first.row) + t * (point.column - first.column)
        let both :=
          onLineOfCross first.row first.column step.row step.column scale s t point.row point.column second.row second.column secondRow secondColumn
            scaleNonzero bezout (DecEq.sound _ _ h)
        let bound: Int.natAbs steps < reach :=
          containsElim city _ point inside (pointRow pointColumn pointRowAt pointColumnAt pointRowBelow pointColumnBelow =>
            containsElim city _ first firstOn (firstRow firstColumn firstRowAt firstColumnAt firstRowBelow firstColumnBelow =>
              match still: step.row == 0 with
                | True =>
                  let rowStill := DecEq.sound step.row 0 still
                  let columnMoves: Not (step.column = 0) := z =>
                    omega [rewrite rowStill, z, Int.mulZero s, Int.mulZero t at bezout in bezout]
                  let below :=
                    stepsBound first.column point.column step.column steps city.width firstColumn pointColumn firstColumnAt pointColumnAt
                      firstColumnBelow pointColumnBelow (And.right both) columnMoves
                  omega
                | False =>
                  let below :=
                    stepsBound first.row point.row step.row steps city.height firstRow pointRow firstRowAt pointRowAt firstRowBelow pointRowBelow
                      (And.left both) (DecEq.soundFalse step.row 0 still)
                  omega))
        harmonicsOfSteps city first second point steps (And.left both) (And.right both) bound
    })

-- Part 2 counts the puzzle's antinodes, for every city whose antennas are
-- on the map.
theorem part2Correct (city: City) (onMap: (antenna: Antenna) → antenna ∈ city.antennas → city.contains antenna.position = True):
    solvePart2 city = part2 city :=
  Eq.cong Set.size
    (locationsCorrect city (((start, end)) => city.harmonics start end) (point first second => inLine point first second)
      (first second firstIn secondIn same point inside =>
        harmonicsCorrect city first.position second.position (onMap first firstIn) (Decidable.toBoolSound _ (Bool.andRight _ _ same)) point
          inside))

-- A point is in line with itself and any other.
theorem inLineSelf (point: Position) (other: Position): inLine point point other = True :=
  rewrite (ring: (point.row - point.row) * (other.column - point.column) - (point.column - point.column) * (other.row - point.row) = 0) in rfl

-- "Some of the new antinodes will occur at the position of each antenna
-- (unless that antenna is the only one of its frequency)": an antenna with
-- another of its frequency is a part 2 antinode.
theorem antennasAreAntinodes (city: City) (onMap: (antenna: Antenna) → antenna ∈ city.antennas → city.contains antenna.position = True)
    (first: Antenna) (second: Antenna) (firstIn: first ∈ city.antennas) (secondIn: second ∈ city.antennas) (same: sameFrequency first second = True):
    (antinodeLocations city (isHarmonicAntinode city)).contains first.position = True :=
  let inner :=
    List.anyOfMem city.antennas (other => sameFrequency first other && inLine first.position first.position other.position) second
      (Bool.andIntro _ _ same (inLineSelf first.position second.position)) secondIn
  rewrite Set.containsFilter (Set.fromList (positions city)) first.position (isHarmonicAntinode city),
    Set.containsFromList first.position (positions city) in
  Bool.andIntro _ _ (positionsOnMap city first.position (onMap first firstIn))
    (List.anyOfMem city.antennas
      (one => city.antennas.any (other => sameFrequency one other && inLine first.position one.position other.position)) first inner firstIn)

-- Part 2's antinodes include part 1's: in line with two antennas, one twice
-- as far as the other, is in line with two antennas.
theorem part2IncludesPart1 (city: City):
    (antinodeLocations city (isAntinode city)).isSubset (antinodeLocations city (isHarmonicAntinode city)) = True :=
  Set.isSubsetIntro _ _ (key has =>
    let both := rewrite Set.containsFilter (Set.fromList (positions city)) key (isAntinode city) at has in has
    rewrite Set.containsFilter (Set.fromList (positions city)) key (isHarmonicAntinode city) in
    Bool.andIntro _ _ (Bool.andLeft _ _ both)
      (List.anyTrueElim city.antennas (one => city.antennas.any (other => sameFrequency one other && (inLine key one.position other.position && twiceAsFar key one.position other.position))) _
        (Bool.andRight _ _ both)
        (first firstIn inner =>
          List.anyTrueElim city.antennas (other => sameFrequency first other && (inLine key first.position other.position && twiceAsFar key first.position other.position)) _
            inner
            (second secondIn pair =>
              let holds := Bool.andRight _ _ pair
              List.anyOfMem city.antennas (one => city.antennas.any (other => sameFrequency one other && inLine key one.position other.position)) first
                (List.anyOfMem city.antennas (other => sameFrequency first other && inLine key first.position other.position) second
                  (Bool.andIntro _ _ (Bool.andLeft _ _ pair) (Bool.andLeft _ _ holds)) secondIn)
                firstIn))))
