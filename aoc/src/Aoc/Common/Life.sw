--| One generation of a Game of Life on an unbounded board, shared between
--| days. A cell is alive or not; each live cell hits all of its neighbours
--| once, and a rule decides from whether a cell is alive and how many hits
--| it took whether it is alive next. Only cells next to a live cell are
--| ever looked at, so the board needs no bounds. The rule must make a cell
--| with no live neighbours dead, as it is never counted. The proofs are in
--| `Aoc.Common.Proofs` (Proofs/Life.sw).

namespace Aoc.Common
import Std (Bool, List, Map, Nat, Ord, Set)

--| For each cell next to a live one, how many live cells it neighbours.
def lifeCounts [auto ord: Ord c] (neighbours: c → List c) (alive: Set c): Map c Nat :=
  alive.toList.flatMap neighbours |> Map.counts

--| The live cells after one generation. `survives alive count` says
--| whether a cell that is (or isn't) `alive` and has `count` live
--| neighbours is alive next.
def lifeStep [auto ord: Ord c] (neighbours: c → List c) (survives: Bool → Nat → Bool) (alive: Set c): Set c :=
  lifeCounts neighbours alive |> .filter (cell count => survives (alive.contains cell) count) |> .keySet
