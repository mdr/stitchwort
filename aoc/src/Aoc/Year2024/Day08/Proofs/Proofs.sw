--| Day 8 proved: both parts count the puzzle's antinodes (part 2 for every
--| city whose antennas are on the map), and part 2's antinodes include part
--| 1's and every antenna with a partner. Here: what both parts share, the
--| antinode locations from a list of points per pair of antennas
--| (`locationsCorrect`). Part 1's points are in Part1.sw, part 2's in
--| Part2.sw; the integer arithmetic they need is in std (`Int/Lemmas.sw`,
--| `Nat/Divides.sw`).

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Common (Position, positions)
import Aoc.Common.Proofs (memPositions)
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Int, Iff, List, Map, Nat, Set, Void)

--| A location on the map is in `positions`, and only those are.
theorem positionsOnMap (city: City) (position: Position) (inside: city.contains position = True):
    (positions city.height city.width).any (other => Map.Spec.sameKey position other) = True :=
  List.anyOfMem (positions city.height city.width) (other => Map.Spec.sameKey position other) position
    (rewrite Map.Spec.sameKeyDecide position position in DecEq.refl position) ((memPositions city.height city.width position).backward inside)

theorem positionsOnlyOnMap (city: City) (position: Position) (has: (positions city.height city.width).any (other => Map.Spec.sameKey position other) = True):
    city.contains position = True :=
  List.anyTrueElim (positions city.height city.width) (other => Map.Spec.sameKey position other) (city.contains position = True) has (other member same =>
    rewrite Map.Spec.sameKeySound position other same in (memPositions city.height city.width other).forward member)

--| Two antennas the spec pairs: of the same frequency, at different places.
def sameFrequency (first: Antenna) (second: Antenna): Bool := first.frequency == second.frequency && first.position != second.position

--| The program's pairs of the antennas that pair with `antenna`.
def partners (city: City) (antenna: Antenna): List (Position, Position) :=
  city.antennas |> .filter (sameFrequency antenna) |> .map (other => (antenna.position, other.position))

--| The program's pairs are the spec's.
theorem pairsElim (city: City) (pair: (Position, Position)) (goal: Prop) (has: pair ∈ city.antennaPairs)
    (use: (first: Antenna) → (second: Antenna) → first ∈ city.antennas → second ∈ city.antennas → sameFrequency first second = True →
      (first.position, second.position) = pair → goal):
    goal :=
  List.anyElim (antenna => pair ∈ partners city antenna) goal city.antennas (List.memFlatMapElim (partners city) pair city.antennas has)
    (first firstIn inPartners =>
      List.anyElim (other => (first.position, (other: Antenna).position) = pair) goal (city.antennas.filter (sameFrequency first))
        (List.memMapAny (city.antennas.filter (sameFrequency first)) (other => (first.position, other.position)) pair inPartners)
        (second secondIn built =>
          let both := List.memFilter city.antennas (sameFrequency first) secondIn
          use first second firstIn (And.left both) (And.right both) built))

theorem pairsIntro (city: City) (first: Antenna) (second: Antenna) (firstIn: first ∈ city.antennas) (secondIn: second ∈ city.antennas)
    (same: sameFrequency first second = True):
    (first.position, second.position) ∈ city.antennaPairs :=
  List.memFlatMapIntro (partners city) first (first.position, second.position) city.antennas firstIn
    (List.memMap (city.antennas.filter (sameFrequency first)) second (List.memFilterIntro city.antennas (sameFrequency first) secondIn same)
      (other => (first.position, other.position)))

--| The antinode locations, from `pick`, the points each pair of antennas
--| gives: when, for two antennas, `pick` gives exactly the points on the map
--| that `holds`, the program's locations are the spec's.
theorem locationsCorrect (city: City) (pick: (Position, Position) → List Position) (holds: Position → Position → Position → Bool)
    (agree: (first: Antenna) → (second: Antenna) → first ∈ city.antennas → second ∈ city.antennas → sameFrequency first second = True →
      (point: Position) → city.contains point = True → (point ∈ pick (first.position, second.position)) ↔ (holds point first.position second.position = True)):
    city.locations (city.antennaPairs.flatMap pick) = antinodeLocations city (point => twoAntennas city (holds point)) :=
  let found := city.antennaPairs.flatMap pick
  let isSpec := (point: Position) => twoAntennas city (holds point)
  Set.ext (city.locations found) (antinodeLocations city isSpec) (key =>
    rewrite Set.containsFromList key (found.filter city.contains), Set.containsFilter (Set.fromList (positions city.height city.width)) key isSpec,
      Set.containsFromList key (positions city.height city.width) in
    Bool.eqOf _ _
      (has =>
        List.anyTrueElim (found.filter city.contains) (other => Map.Spec.sameKey key other) _ has (point member same =>
          let both := List.memFilter found city.contains member
          rewrite Map.Spec.sameKeySound key point same in
          List.anyElim (pair => point ∈ pick pair) _ city.antennaPairs (List.memFlatMapElim pick point city.antennaPairs (And.left both))
            (pair pairIn picked =>
              pairsElim city pair _ pairIn (first second firstIn secondIn sameness built =>
                let holding := (agree first second firstIn secondIn sameness point (And.right both)).forward (rewrite built in picked)
                let inner := List.anyOfMem city.antennas (other => sameFrequency first other && holds point first.position other.position) second
                  (Bool.andIntro sameness holding) secondIn
                Bool.andIntro (positionsOnMap city point (And.right both))
                  (List.anyOfMem city.antennas
                    (one => city.antennas.any (other => sameFrequency one other && holds point one.position other.position)) first inner firstIn)))))
      (has =>
        let onMap := positionsOnlyOnMap city key (Bool.andLeft has)
        List.anyTrueElim city.antennas (one => city.antennas.any (other => sameFrequency one other && holds key one.position other.position)) _
          (Bool.andRight has)
          (first firstIn inner =>
            List.anyTrueElim city.antennas (other => sameFrequency first other && holds key first.position other.position) _ inner
              (second secondIn both =>
                let sameness := Bool.andLeft both
                let picked := (agree first second firstIn secondIn sameness key onMap).backward (Bool.andRight both)
                let inFound := List.memFlatMapIntro pick (first.position, second.position) key city.antennaPairs
                  (pairsIntro city first second firstIn secondIn sameness) picked
                List.anyOfMem (found.filter city.contains) (other => Map.Spec.sameKey key other) key
                  (rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key) (List.memFilterIntro found city.contains inFound onMap)))))
