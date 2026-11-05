--| Part 2: the grid points in line with two antennas `first` and `second`
--| are `first` plus whole steps of `first.stepToward second`
--| (`onLineOfCross`), because the gcd makes the step's parts coprime
--| (`stepFacts`, from Bézout's identity); and on the map those steps are
--| fewer than its height or width (`stepsBound`), which `harmonics` takes
--| either way (`harmonicsCorrect`).

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Common (Offset, Position, positions)
import Aoc.Common.Proofs (offsetOf, offsetSome, positionExtInt)
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Int, Iff, List, Nat, Or, Set, Void)

--| Dividing a multiple of a positive number by it.
theorem divExact: (value: Int) → (below: Nat) → (times: Nat) → value.natAbs = times * Succ below →
    (Succ below).toInt * (value / (Succ below).toInt) = value
  | OfNat n, below, times, multiple =>
    let quotient := Nat.divUnique n (Succ below) times 0 (omega) (rewrite multiple in ring)
    rewrite quotient in Eq.cong OfNat (rewrite multiple in ring)
  | NegSucc m, below, Zero, multiple => Void.exfalso (omega [multiple])
  | NegSucc m, below, Succ times, multiple =>
    let whole: m = times * Succ below + below := omega [multiple, (ring: Succ times * Succ below = times * Succ below + Succ below)]
    let quotient := Nat.divUnique m (Succ below) times below (omega) whole
    rewrite quotient in Eq.cong NegSucc (omega [whole, (ring: times + below * Succ times = times * Succ below + below)])

--| `|x|` is `x` times its sign.
theorem natAbsSign: (x: Int) → x.natAbs.toInt = x.sign * x
  | OfNat Zero => rfl
  | OfNat (Succ n) => Eq.cong OfNat (omega)
  | NegSucc n => Eq.cong OfNat (omega)

--| `divideBy` the gcd, with the gcd as a variable: the difference is a
--| nonzero multiple of the result, whose parts are coprime.
theorem divideByFacts (difference: Offset) (goal: Prop) (rowTimes: Nat) (columnTimes: Nat) (s: Int) (t: Int)
    (nonzero: (difference.rows = 0) ∧ (difference.columns = 0) → Void):
    (divisor: Nat) → difference.rows.natAbs = rowTimes * divisor → difference.columns.natAbs = columnTimes * divisor →
      s * difference.rows.natAbs.toInt + t * difference.columns.natAbs.toInt = divisor.toInt →
      ((scale: Int) → scale ≠ 0 → difference.rows = scale * (divideBy difference divisor).rows →
        difference.columns = scale * (divideBy difference divisor).columns → (s: Int) → (t: Int) →
        s * (divideBy difference divisor).rows + t * (divideBy difference divisor).columns = 1 → goal) →
      goal
  | Zero, rows, columns, bezout, use =>
    Void.exfalso (nonzero (Both (Int.natAbsZero difference.rows (omega [rows])) (Int.natAbsZero difference.columns (omega [columns]))))
  | Succ below, rows, columns, bezout, use =>
    let scale := (Succ below).toInt
    let step := divideBy difference (Succ below)
    let rowLaw: scale * step.rows = difference.rows := divExact difference.rows below rowTimes rows
    let columnLaw: scale * step.columns = difference.columns := divExact difference.columns below columnTimes columns
    let rowSign := Int.sign difference.rows
    let columnSign := Int.sign difference.columns
    let scaled: scale * (s * rowSign * step.rows + t * columnSign * step.columns) = scale * 1 :=
      ring [bezout, s * natAbsSign difference.rows, t * natAbsSign difference.columns, s * rowSign * rowLaw, t * columnSign * columnLaw]
    use scale (omega) (Eq.sym rowLaw) (Eq.sym columnLaw) (s * rowSign) (t * columnSign) (Int.mulCancelLeft scale _ 1 (omega) scaled)

--| The step to grid points from `start` towards `end`: the offset between
--| them is a nonzero multiple of it, and its parts are coprime (some whole
--| combination of them is 1).
theorem stepFacts (start: Position) (end: Position) (distinct: start ≠ end) (goal: Prop)
    (use: (scale: Int) → scale ≠ 0 → end.row.toInt - start.row.toInt = scale * (start.stepToward end).rows →
      end.column.toInt - start.column.toInt = scale * (start.stepToward end).columns → (s: Int) → (t: Int) →
      s * (start.stepToward end).rows + t * (start.stepToward end).columns = 1 → goal):
    goal :=
  let difference := end.minus start
  let rowSize := Int.natAbs difference.rows
  let columnSize := Int.natAbs difference.columns
  let nonzero := (both: (difference.rows = 0) ∧ (difference.columns = 0)) =>
    distinct (positionExtInt start end (omega [And.left both]) (omega [And.right both]))
  match Nat.gcdDivides rowSize columnSize with
    | Both (Witness rowTimes rows) (Witness columnTimes columns) =>
      match Nat.gcdBezout rowSize columnSize with
        | Witness s (Witness t bezout) => divideByFacts difference goal rowTimes columnTimes s t nonzero (Nat.gcd rowSize columnSize) rows columns bezout use

--| Points `k` steps from `first` are in line with it and `second`.
theorem crossOnLine (fr: Int) (fc: Int) (er: Int) (ec: Int) (scale: Int) (k: Int) (pr: Int) (pc: Int) (sr: Int) (sc: Int)
    (secondRow: sr = fr + scale * er) (secondColumn: sc = fc + scale * ec) (rowAt: pr = fr + er * k) (columnAt: pc = fc + ec * k):
    (fr - pr) * (sc - pc) - (fc - pc) * (sr - pr) = 0 :=
  rewrite secondRow, secondColumn, rowAt, columnAt in ring

--| And every point in line is a whole number of steps from `first`: the
--| cross product makes the offset parallel to the step, and with the step's
--| parts coprime (`s * er + t * ec = 1`) the number of steps is
--| `s * (pr - fr) + t * (pc - fc)`.
theorem onLineOfCross (fr: Int) (fc: Int) (er: Int) (ec: Int) (scale: Int) (s: Int) (t: Int) (pr: Int) (pc: Int) (sr: Int) (sc: Int)
    (secondRow: sr = fr + scale * er) (secondColumn: sc = fc + scale * ec) (nonzero: scale ≠ 0) (bezout: s * er + t * ec = 1)
    (cross: (fr - pr) * (sc - pc) - (fc - pc) * (sr - pr) = 0):
    (pr = fr + er * (s * (pr - fr) + t * (pc - fc))) ∧ (pc = fc + ec * (s * (pr - fr) + t * (pc - fc))) :=
  let crossScaled: scale * ((pc - fc) * er - (pr - fr) * ec) = scale * 0 := rewrite secondRow, secondColumn at cross in ring [cross]
  let parallel := Int.mulCancelLeft scale ((pc - fc) * er - (pr - fr) * ec) 0 nonzero crossScaled
  Both (ring [(pr - fr) * bezout, t * parallel]) (ring [(pc - fc) * bezout, s * parallel])

--| Two numbers below `n` are less than `n` apart.
theorem natAbsFrom (p: Nat) (a: Nat) (n: Nat) (below: p < n) (aBelow: a < n): (gap: Nat) → a - p = gap → Int.natAbs (Int.subNatNatFrom p a gap) < n
  | Zero, e => omega
  | Succ gap, e => omega

theorem natAbsDiffLt (p: Nat) (a: Nat) (n: Nat) (below: p < n) (aBelow: a < n): Int.natAbs (p.toInt - a.toInt) < n :=
  rewrite Int.subOfNats p a in natAbsFrom p a n below aBelow (a - p) rfl

--| Between two locations on a map `n` high, fewer than `n` steps of a
--| nonzero size.
theorem stepsBound (a: Nat) (p: Nat) (er: Int) (k: Int) (n: Nat) (aBelow: a < n) (pBelow: p < n) (on: p.toInt = a.toInt + er * k)
    (nonzero: er ≠ 0):
    k.natAbs < n :=
  let gap: Int.natAbs (er * k) < n := rewrite (ring [on]: er * k = p.toInt - a.toInt) in natAbsDiffLt p a n pBelow aBelow
  let positive: Int.natAbs er ≠ 0 := z => nonzero (Int.natAbsZero er z)
  omega [Int.natAbsMul er k, Nat.leMulPos (Int.natAbs k) (Int.natAbs er) (omega)]

--| The harmonics `count` steps from `start`, either way.
def stepsFrom (start: Position) (step: Offset) (count: Nat): List Position := [step.times count.toInt, (step.times count.toInt).negate] |> .filterMap start.offset

--| A point a whole number of steps from `start`, within the map's reach, is
--| among the harmonics.
theorem harmonicsOfSteps (city: City) (start: Position) (end: Position) (point: Position): (k: Int) →
    point.row.toInt = start.row.toInt + (start.stepToward end).rows * k → point.column.toInt = start.column.toInt + (start.stepToward end).columns * k →
    k.natAbs < Nat.max city.height city.width → point ∈ city.harmonics start end
  | OfNat count, rowAt, columnAt, bound =>
    let step := start.stepToward end
    List.memFlatMapIntro (stepsFrom start step) count point (List.range 0 (Nat.max city.height city.width))
      (List.memRangeFromIntro count (Nat.max city.height city.width) 0 (omega) (omega))
      (List.memFilterMapIntro start.offset (step.times count.toInt) point [step.times count.toInt, (step.times count.toInt).negate] (Inl rfl)
        (offsetOf start (step.times count.toInt) point rowAt columnAt))
  | NegSucc count, rowAt, columnAt, bound =>
    let step := start.stepToward end
    List.memFlatMapIntro (stepsFrom start step) (Succ count) point (List.range 0 (Nat.max city.height city.width))
      (List.memRangeFromIntro (Succ count) (Nat.max city.height city.width) 0 (omega) (omega))
      (List.memFilterMapIntro start.offset (step.times (Succ count).toInt).negate point
        [step.times (Succ count).toInt, (step.times (Succ count).toInt).negate] (Inr (Inl rfl))
        (offsetOf start (step.times (Succ count).toInt).negate point (ring [rowAt]) (ring [columnAt])))

theorem harmonicsCorrect (city: City) (first: Position) (second: Position) (firstOn: city.contains first = True) (distinct: first ≠ second)
    (point: Position) (inside: city.contains point = True):
    (point ∈ city.harmonics first second) ↔ (inLine point first second = True) :=
  stepFacts first second distinct _ (scale scaleNonzero rows columns s t bezout =>
    let step := first.stepToward second
    let reach := Nat.max city.height city.width
    let fr := first.row.toInt
    let fc := first.column.toInt
    let pr := point.row.toInt
    let pc := point.column.toInt
    let secondRow: second.row.toInt = fr + scale * step.rows := ring [rows]
    let secondColumn: second.column.toInt = fc + scale * step.columns := ring [columns]
    let onLine := (k: Int) (rowAt: pr = fr + step.rows * k) (columnAt: pc = fc + step.columns * k) =>
      let cross :=
        crossOnLine fr fc step.rows step.columns scale k pr pc second.row.toInt second.column.toInt secondRow secondColumn rowAt columnAt
      (rewrite cross in rfl: inLine point first second = True)
    {
      forward = has =>
        List.anyElim (count => point ∈ stepsFrom first step count) _ (List.range 0 reach)
          (List.memFlatMapElim (stepsFrom first step) point (List.range 0 reach) has)
          (count countIn pointIn =>
            match List.memFilterMapElim first.offset point [step.times count.toInt, (step.times count.toInt).negate] pointIn with
              | Inl landed =>
                let both := offsetSome first (step.times count.toInt) point landed
                onLine count.toInt (And.left both) (And.right both)
              | Inr (Inl landed) =>
                let both := offsetSome first (step.times count.toInt).negate point landed
                onLine (0 - count.toInt) (ring [And.left both]) (ring [And.right both])
              | Inr (Inr none) => Void.exfalso none),
      backward = h =>
        let steps := s * (pr - fr) + t * (pc - fc)
        let both :=
          onLineOfCross fr fc step.rows step.columns scale s t pr pc second.row.toInt second.column.toInt secondRow secondColumn scaleNonzero bezout
            (DecEq.sound _ _ h)
        let bound: Int.natAbs steps < reach :=
          match still: step.rows == 0 with
            | True =>
              let rowStill := DecEq.sound step.rows 0 still
              let columnMoves: step.columns ≠ 0 := z => omega [rewrite rowStill, z, Int.mulZero s, Int.mulZero t at bezout in bezout]
              let below :=
                stepsBound first.column point.column step.columns steps city.width (omega [Bool.andRight _ _ firstOn])
                  (omega [Bool.andRight _ _ inside]) (And.right both) columnMoves
              omega
            | False =>
              let below :=
                stepsBound first.row point.row step.rows steps city.height (omega [Bool.andLeft _ _ firstOn]) (omega [Bool.andLeft _ _ inside])
                  (And.left both) (DecEq.soundFalse step.rows 0 still)
              omega
        harmonicsOfSteps city first second point steps (And.left both) (And.right both) bound
    })

--| Part 2 counts the puzzle's antinodes, for every city whose antennas are
--| on the map.
theorem part2Correct (city: City) (onMap: (antenna: Antenna) → antenna ∈ city.antennas → city.contains antenna.position = True):
    solvePart2 city = part2 city :=
  Eq.cong Set.size
    (locationsCorrect city (((start, end)) => city.harmonics start end) (point first second => inLine point first second)
      (first second firstIn secondIn same point inside =>
        harmonicsCorrect city first.position second.position (onMap first firstIn) (Decidable.toBoolSound _ (Bool.andRight _ _ same)) point
          inside))

--| A point is in line with itself and any other.
theorem inLineSelf (point: Position) (other: Position): inLine point point other = True :=
  rewrite (ring:
    (point.row.toInt - point.row.toInt) * (other.column.toInt - point.column.toInt)
      - (point.column.toInt - point.column.toInt) * (other.row.toInt - point.row.toInt) = 0) in rfl

--| "Some of the new antinodes will occur at the position of each antenna
--| (unless that antenna is the only one of its frequency)": an antenna with
--| another of its frequency is a part 2 antinode.
theorem antennasAreAntinodes (city: City) (onMap: (antenna: Antenna) → antenna ∈ city.antennas → city.contains antenna.position = True)
    (first: Antenna) (second: Antenna) (firstIn: first ∈ city.antennas) (secondIn: second ∈ city.antennas) (same: sameFrequency first second = True):
    (antinodeLocations city (isHarmonicAntinode city)).contains first.position = True :=
  let inner :=
    List.anyOfMem city.antennas (other => sameFrequency first other && inLine first.position first.position other.position) second
      (Bool.andIntro _ _ same (inLineSelf first.position second.position)) secondIn
  rewrite Set.containsFilter (Set.fromList (positions city.height city.width)) first.position (isHarmonicAntinode city),
    Set.containsFromList first.position (positions city.height city.width) in
  Bool.andIntro _ _ (positionsOnMap city first.position (onMap first firstIn))
    (List.anyOfMem city.antennas
      (one => city.antennas.any (other => sameFrequency one other && inLine first.position one.position other.position)) first inner firstIn)

--| Part 2's antinodes include part 1's: in line with two antennas, one twice
--| as far as the other, is in line with two antennas.
theorem part2IncludesPart1 (city: City):
    (antinodeLocations city (isAntinode city)).isSubset (antinodeLocations city (isHarmonicAntinode city)) = True :=
  Set.isSubsetIntro _ _ (key has =>
    let both := rewrite Set.containsFilter (Set.fromList (positions city.height city.width)) key (isAntinode city) at has in has
    rewrite Set.containsFilter (Set.fromList (positions city.height city.width)) key (isHarmonicAntinode city) in
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
