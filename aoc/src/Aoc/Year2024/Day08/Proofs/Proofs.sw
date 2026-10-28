-- Day 8 proved: both parts count the puzzle's antinodes (part 2 for every
-- city whose antennas are on the map), and part 2's antinodes include part
-- 1's and every antenna with a partner. Here: what both parts share, the
-- antinode locations from a list of points per pair of antennas
-- (`locationsCorrect`). Part 1's points are in Part1.sw, part 2's in
-- Part2.sw, and the integer arithmetic they need in Ints.sw.

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Int, Iff, List, Map, Nat, Set, Void)

-- The map location at a row and a column.
def place (row: Nat) (column: Nat): Position := { row = row.toInt, column = column.toInt }

-- A location on the map is in `positions`, and only those are.
theorem positionsOnMap (city: City): (position: Position) → city.contains position = True →
    (positions city).any (other => Map.Spec.sameKey position other) = True
  | { row = OfNat row, column = OfNat column }, inside =>
    let inRow := List.memMap (List.range city.width) column (List.memRangeFromIntro column city.width 0 (omega) (omega)) (place row)
    let member :=
      List.memFlatMapIntro (row => List.range city.width |> .map (place row)) row (place row column) (List.range city.height)
        (List.memRangeFromIntro row city.height 0 (omega) (omega)) inRow
    List.anyOfMem (positions city) (other => Map.Spec.sameKey (place row column) other) (place row column)
      (rewrite Map.Spec.sameKeyDecide (place row column) (place row column) in DecEq.refl (place row column)) member
  | { row = OfNat row, column = NegSucc column }, inside => omega
  | { row = NegSucc row, column }, inside => Void.exfalso (Bool.falseNotTrue inside)

theorem positionsOnlyOnMap (city: City) (position: Position) (has: (positions city).any (other => Map.Spec.sameKey position other) = True):
    city.contains position = True :=
  List.anyTrueElim (positions city) (other => Map.Spec.sameKey position other) (city.contains position = True) has (other member same =>
    rewrite Map.Spec.sameKeySound position other same in
    List.anyElim (row => other ∈ (List.range city.width |> .map (place row))) (city.contains other = True) (List.range city.height)
      (List.memFlatMapElim (row => List.range city.width |> .map (place row)) other (List.range city.height) member)
      (row rowMember inRow =>
        List.anyElim (column => place row column = other) (city.contains other = True) (List.range city.width)
          (List.memMapAny (List.range city.width) (place row) other inRow)
          (column columnMember built =>
            let rowSmall := List.memRangeFrom row city.height 0 rowMember
            let columnSmall := List.memRangeFrom column city.width 0 columnMember
            rewrite <- built in omega [rowSmall, columnSmall])))

-- Two antennas the spec pairs: of the same frequency, at different places.
def sameFrequency (first: Antenna) (second: Antenna): Bool := first.frequency == second.frequency && first.position != second.position

-- The program's pairs of the antennas that pair with `antenna`.
def partners (city: City) (antenna: Antenna): List (Position, Position) :=
  city.antennas |> .filter (sameFrequency antenna) |> .map (other => (antenna.position, other.position))

-- The program's pairs are the spec's.
theorem pairsElim (city: City) (pair: (Position, Position)) (goal: Prop) (has: pair ∈ city.antennaPairs)
    (use: (first: Antenna) → (second: Antenna) → first ∈ city.antennas → second ∈ city.antennas → sameFrequency first second = True →
      (first.position, second.position) = pair → goal):
    goal :=
  List.anyElim (antenna => pair ∈ partners city antenna) goal city.antennas (List.memFlatMapElim (partners city) pair city.antennas has)
    (first firstIn inPartners =>
      List.anyElim (other => (first.position, (other: Antenna).position) = pair) goal (city.antennas.filter (sameFrequency first))
        (List.memMapAny (city.antennas.filter (sameFrequency first)) (other => (first.position, other.position)) pair inPartners)
        (second secondIn built =>
          let both := List.memFilter city.antennas (sameFrequency first) second secondIn
          use first second firstIn (And.left both) (And.right both) built))

theorem pairsIntro (city: City) (first: Antenna) (second: Antenna) (firstIn: first ∈ city.antennas) (secondIn: second ∈ city.antennas)
    (same: sameFrequency first second = True):
    (first.position, second.position) ∈ city.antennaPairs :=
  List.memFlatMapIntro (partners city) first (first.position, second.position) city.antennas firstIn
    (List.memMap (city.antennas.filter (sameFrequency first)) second (List.memFilterIntro city.antennas (sameFrequency first) second secondIn same)
      (other => (first.position, other.position)))

-- The antinode locations, from `pick`, the points each pair of antennas
-- gives: when, for two antennas, `pick` gives exactly the points on the map
-- that `holds`, the program's locations are the spec's.
theorem locationsCorrect (city: City) (pick: (Position, Position) → List Position) (holds: Position → Position → Position → Bool)
    (agree: (first: Antenna) → (second: Antenna) → first ∈ city.antennas → second ∈ city.antennas → sameFrequency first second = True →
      (point: Position) → city.contains point = True → Iff (point ∈ pick (first.position, second.position)) (holds point first.position second.position = True)):
    city.locations (city.antennaPairs.flatMap pick) = antinodeLocations city (point => twoAntennas city (holds point)) :=
  let found := city.antennaPairs.flatMap pick
  let isSpec := (point: Position) => twoAntennas city (holds point)
  Set.ext (city.locations found) (antinodeLocations city isSpec) (key =>
    rewrite Set.containsFromList key (found.filter city.contains), Set.containsFilter (Set.fromList (positions city)) key isSpec,
      Set.containsFromList key (positions city) in
    Bool.eqOf _ _
      (has =>
        List.anyTrueElim (found.filter city.contains) (other => Map.Spec.sameKey key other) _ has (point member same =>
          let both := List.memFilter found city.contains point member
          rewrite Map.Spec.sameKeySound key point same in
          List.anyElim (pair => point ∈ pick pair) _ city.antennaPairs (List.memFlatMapElim pick point city.antennaPairs (And.left both))
            (pair pairIn picked =>
              pairsElim city pair _ pairIn (first second firstIn secondIn sameness built =>
                let holding := (agree first second firstIn secondIn sameness point (And.right both)).forward (rewrite built in picked)
                let inner := List.anyOfMem city.antennas (other => sameFrequency first other && holds point first.position other.position) second
                  (Bool.andIntro (sameFrequency first second) (holds point first.position second.position) sameness holding) secondIn
                Bool.andIntro _ _ (positionsOnMap city point (And.right both))
                  (List.anyOfMem city.antennas
                    (one => city.antennas.any (other => sameFrequency one other && holds point one.position other.position)) first inner firstIn)))))
      (has =>
        let onMap := positionsOnlyOnMap city key (Bool.andLeft _ _ has)
        List.anyTrueElim city.antennas (one => city.antennas.any (other => sameFrequency one other && holds key one.position other.position)) _
          (Bool.andRight _ _ has)
          (first firstIn inner =>
            List.anyTrueElim city.antennas (other => sameFrequency first other && holds key first.position other.position) _ inner
              (second secondIn both =>
                let sameness := Bool.andLeft _ _ both
                let picked := (agree first second firstIn secondIn sameness key onMap).backward (Bool.andRight _ _ both)
                let inFound := List.memFlatMapIntro pick (first.position, second.position) key city.antennaPairs
                  (pairsIntro city first second firstIn secondIn sameness) picked
                List.anyOfMem (found.filter city.contains) (other => Map.Spec.sameKey key other) key
                  (rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key) (List.memFilterIntro found city.contains key inFound onMap)))))
