-- Advent of Code 2024, day 16: a maze of walls and open tiles. A reindeer
-- starts on S facing east; moving forward one tile costs 1 point and
-- turning 90 degrees costs 1000. Part 1 is the lowest score from S to E;
-- part 2 counts the tiles on at least one path with that score.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day16.main < examples/2024/day16.txt
--
-- The proofs are in `Aoc.Year2024.Day16.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day16.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day16
import Std (Bool, DecEq, Eq, Fail, IO, List, Map, Nat, Option, Parse, Set, Text, Void)
import Std.Parse (char)

def main(): {IO, Fail} () :=
  let maze := parseMaze IO.readAll()
  IO.print "Part 1: ${solvePart1 maze}"
  IO.print "Part 2: ${solvePart2 maze}"

type Position = { row: Nat, column: Nat }

-- The open tiles (S, E and `.`), the start and the end.
type Maze = { openTiles: Set Position, start: Position, end: Position }

type Tile =
  | Wall
  | Floor
  | Start
  | End

def tile(): {Parse} Tile :=
  Parse.pick [("#", Wall), (".", Floor), ("S", Start), ("E", End)]

-- The one position holding `wanted`.
def onlyTile (tiles: List (Position, Tile)) (wanted: Tile) (name: Text): {Fail} Position :=
  match tiles.filter (entry => entry.snd == wanted) |> .map (entry => entry.fst) with
    | Cons position Nil => position
    | Nil => Fail.fail "no ${name} tile"
    | _ => Fail.fail "more than one ${name} tile"

-- One row per line, all as long as the first, with one S and one E.
def parseMaze (input: Text): {Fail} Maze :=
  let rows := Parse.all input (() => Parse.grid tile)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .forEach (((row, tiles)) =>
    Fail.ensure (tiles.length == width) "line ${row + 1}: expected ${width} tiles, as on the first line, got ${tiles.length}")
  let tiles :=
    rows.withIndex
      |> .flatMap (((row, line)) => line.withIndex |> .map (((column, kind)) => (({ row, column }: Position), kind)))
  {
    openTiles = tiles.filter (entry => entry.snd != Wall) |> .map (entry => entry.fst) |> Set.fromList,
    start = onlyTile tiles Start "S",
    end = onlyTile tiles End "E"
  }

type Direction =
  | East
  | South
  | West
  | North

def directions: List Direction := [East, South, West, North]

def Direction.clockwise: Direction → Direction
  | East => South
  | South => West
  | West => North
  | North => East

def Direction.counterclockwise: Direction → Direction
  | East => North
  | North => West
  | West => South
  | South => East

def Direction.opposite: Direction → Direction
  | East => West
  | West => East
  | North => South
  | South => North

-- The grid point one step in `direction`; none above row 0 or left of
-- column 0.
def Position.step (position: Position): Direction → Option Position
  | East => Some ({ position | column = Succ position.column })
  | South => Some ({ position | row = Succ position.row })
  | West =>
    match position.column with
      | Zero => None
      | Succ before => Some ({ position | column = before })
  | North =>
    match position.row with
      | Zero => None
      | Succ above => Some ({ position | row = above })

-- Where the reindeer is and which way it faces.
type Reindeer = { position: Position, facing: Direction }

def Maze.isOpen (maze: Maze) (position: Position): Bool := maze.openTiles.contains position

def Maze.holds (maze: Maze) (reindeer: Reindeer): Bool := maze.isOpen reindeer.position

-- Every way the reindeer can stand on an open tile.
def Maze.reindeer (maze: Maze): List Reindeer :=
  maze.openTiles.toList |> .flatMap (position => directions.map (facing => ({ position, facing }: Reindeer)))

def Reindeer.turned (reindeer: Reindeer) (facing: Direction): Reindeer := { reindeer | facing }

-- The reindeer one tile forward, if that tile is open.
def Maze.forward (maze: Maze) (reindeer: Reindeer): List Reindeer :=
  match reindeer.position.step reindeer.facing with
    | Some next => if maze.isOpen next then [{ reindeer | position = next }] else Nil
    | None => Nil

-- The reindeer one tile back, if that tile is open.
def Maze.backward (maze: Maze) (reindeer: Reindeer): List Reindeer :=
  match reindeer.position.step reindeer.facing.opposite with
    | Some previous => if maze.isOpen previous then [{ reindeer | position = previous }] else Nil
    | None => Nil

-- The two turns, each costing 1000.
def Reindeer.turns (reindeer: Reindeer): List (Reindeer, Nat) :=
  [(reindeer.turned reindeer.facing.clockwise, 1000), (reindeer.turned reindeer.facing.counterclockwise, 1000)]

-- What one move leads to, with its cost.
def Maze.after (maze: Maze) (reindeer: Reindeer): List (Reindeer, Nat) :=
  (maze.forward reindeer |> .map (next => (next, 1))) ++ reindeer.turns

-- What one move comes from, with its cost.
def Maze.before (maze: Maze) (reindeer: Reindeer): List (Reindeer, Nat) :=
  (maze.backward reindeer |> .map (previous => (previous, 1))) ++ reindeer.turns

-- The four ways to stand on the end tile.
def Maze.endReindeer (maze: Maze): List Reindeer := directions.map (facing => ({ position = maze.end, facing }: Reindeer))

def Maze.startReindeer (maze: Maze): Reindeer := { position = maze.start, facing = East }

-- A weighted graph for a shortest-path search: each state's edges with
-- their costs, and a list of the states the search can settle, with a quick
-- test for them.
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  within: s → Bool,
  states: List s,
  listed: (state: s) → within state = True → state ∈ states
}

-- The states not yet settled: one fewer each time the search settles one.
def Graph.unsettled [auto ord: Ord s] (graph: Graph s) (settled: Map s Nat): Nat := graph.states.count (state => !settled.contains state)

-- No more pass `kept` than `p` when `kept` implies `p`.
theorem countLe: (xs: List a) → (p: a → Bool) → (kept: a → Bool) → ((x: a) → kept x = True → p x = True) → xs.count kept ≤ xs.count p
  | Nil, p, kept, implies => rfl
  | Cons x rest, p, kept, implies =>
    rewrite List.countCons rest x kept, List.countCons rest x p in
      let fewer := countLe rest p kept implies
      match keeps: kept x with
        | True => rewrite implies x keeps in omega [fewer]
        | False => omega [fewer]

-- Fewer pass `kept` than `p` when `kept` implies `p` and some member passes
-- `p` but not `kept`.
theorem countFewer: (xs: List a) → (p: a → Bool) → (kept: a → Bool) → ((x: a) → kept x = True → p x = True) → (dropped: a) → dropped ∈ xs →
    p dropped = True → kept dropped = False → xs.count kept < xs.count p
  | Nil, p, kept, implies, dropped, member, passes, fails => Void.exfalso member
  | Cons x rest, p, kept, implies, dropped, Inl same, passes, fails =>
    rewrite List.countCons rest x kept, List.countCons rest x p, same, passes, fails in omega [countLe rest p kept implies]
  | Cons x rest, p, kept, implies, dropped, Inr later, passes, fails =>
    rewrite List.countCons rest x kept, List.countCons rest x p in
      let fewer := countFewer rest p kept implies dropped later passes fails
      match keeps: kept x with
        | True => rewrite implies x keeps in omega [fewer]
        | False => omega [fewer]

-- A key just inserted is there.
theorem containsInsertSame [auto ord: Ord k] (m: Map k v) (key: k) (value: v): (m.insert key value).contains key = True :=
  rewrite Map.getInsert key value m in rfl

-- Inserting keeps the keys already there.
theorem containsInsertKeeps [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (there: m.contains other = True):
    (m.insert key value).contains other = True :=
  match same: other == key with
    | True => rewrite DecEq.sound other key same in containsInsertSame m key value
    | False => rewrite Map.getInsertOther key value other (DecEq.soundFalse other key same) m in there

-- Settling a listed state not yet settled leaves fewer unsettled.
theorem unsettledInsert [auto ord: Ord s] (graph: Graph s) (settled: Map s Nat) (state: s) (cost: Nat) (listed: state ∈ graph.states)
    (fresh: settled.contains state = False): graph.unsettled (settled.insert state cost) < graph.unsettled settled :=
  countFewer graph.states (other => !settled.contains other) (other => !(settled.insert state cost).contains other)
    (other kept =>
      match there: settled.contains other with
        | True => rewrite containsInsertKeeps settled state cost other there at kept in kept
        | False => rfl)
    state listed (rewrite fresh in rfl) (rewrite containsInsertSame settled state cost in rfl)

-- The least key of a set is in it.
theorem containsMin [auto ord: Ord k] (set: Set k) (least: k) (found: set.min = Some least): set.contains least = True :=
  match entries: Map.toList set.items with
    | Nil => Void.exfalso (Option.someNotNone least (Eq.trans (Eq.sym found) (rewrite Map.minToList set.items, entries in rfl)))
    | Cons entry rest =>
      let first: set.min = Some entry.fst := rewrite Map.minToList set.items, entries in rfl
      Map.containsOfMemToList set.items least entry (rewrite entries in Inl rfl) (Option.someInjective _ _ (Eq.trans (Eq.sym first) found))

-- Taking the least key out of a set makes it smaller.
theorem sizeRemoveMin [auto ord: Ord k] (set: Set k) (least: k) (found: set.min = Some least): (set.remove least).size < set.size :=
  let there: Map.contains set.items least = True := containsMin set least found
  rewrite Map.sizeRemove set.items least, there, Map.sizeToList set.items in
    match entries: Map.toList set.items with
      | Nil => Void.exfalso (Option.someNotNone least (Eq.trans (Eq.sym found) (rewrite Map.minToList set.items, entries in rfl)))
      | Cons entry rest => omega

-- The queue with each edge's state added, at `cost` plus the edge's.
def pushEdges [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → Set (Nat, s)
  | Nil, queue => queue
  | Cons (next, weight) rest, queue => pushEdges cost rest (queue.insert (cost + weight, next))

-- Dijkstra's algorithm: `queue` holds (cost, state) pairs still to look at,
-- least first; `settled` the least cost found for each state settled so
-- far. The least pair in the queue, `popped`, settles its state, unless it
-- already is, and queues the state's neighbours.
def Graph.searchFrom [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat): (popped: Option (Nat, s)) →
    queue.min = popped → Map s Nat
    decreasing (graph.unsettled settled, queue.size)
  | None, found => settled
  | Some (cost, state), found =>
    let rest := queue.remove (cost, state)
    if fresh: settled.contains state = False then
      if within: graph.within state = True then
        let pushed := pushEdges cost (graph.edges state) rest
        Graph.searchFrom graph pushed (settled.insert state cost) pushed.min rfl
          [decreasing := Nat.LexLess.First (unsettledInsert graph settled state cost (graph.listed state within) fresh)]
      else Graph.searchFrom graph rest settled rest.min rfl [decreasing := Nat.LexLess.Second rfl (sizeRemoveMin queue (cost, state) found)]
    else Graph.searchFrom graph rest settled rest.min rfl [decreasing := Nat.LexLess.Second rfl (sizeRemoveMin queue (cost, state) found)]

def Graph.search [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat): Map s Nat :=
  Graph.searchFrom graph queue settled queue.min rfl

-- The least cost to each state reachable from one of the sources.
def Graph.distances [auto ord: Ord s] (graph: Graph s) (sources: List s): Map s Nat :=
  graph.search (sources |> .map (source => (0, source)) |> Set.fromList) Map.empty

theorem directionsComplete: (facing: Direction) → facing ∈ directions
  | East => Inl rfl
  | South => Inr (Inl rfl)
  | West => Inr (Inr (Inl rfl))
  | North => Inr (Inr (Inr (Inl rfl)))

-- A way of standing on an open tile is on the list.
theorem Maze.holdsListed (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → reindeer ∈ maze.reindeer
  | { position, facing }, holds =>
    List.memFlatMapIntro (place => directions.map (way => ({ position = place, facing = way }: Reindeer))) position
      ({ position, facing }: Reindeer) maze.openTiles.toList (Map.memKeysOfContains maze.openTiles.items position holds)
      (List.memMap directions facing (directionsComplete facing) (way => ({ position, facing = way }: Reindeer)))

-- The maze's moves forward and turns, between the ways to stand on its open
-- tiles; `backwards` follows each move the other way.
def Maze.graph (maze: Maze) (backwards: Bool): Graph Reindeer := {
  edges = reindeer => if backwards then maze.before reindeer else maze.after reindeer,
  within = maze.holds,
  states = maze.reindeer,
  listed = reindeer => maze.holdsListed reindeer
}

-- The lowest score from the start to each reachable way of standing.
def Maze.fromStart (maze: Maze): Map Reindeer Nat := (maze.graph False).distances [maze.startReindeer]

-- The lowest score from each way of standing to the end, facing any way.
def Maze.toEnd (maze: Maze): Map Reindeer Nat := (maze.graph True).distances maze.endReindeer

-- The lowest score at the end, facing any way, from the start's scores.
def Maze.lowestScore (maze: Maze) (fromStart: Map Reindeer Nat): Option Nat := maze.endReindeer.filterMap fromStart.get |> .minimum

-- The tiles where the reindeer stands, some way, with its lowest scores
-- from the start and to the end adding up to `best`.
def tilesScoring (fromStart: Map Reindeer Nat) (toEnd: Map Reindeer Nat) (best: Nat): Set Position :=
  fromStart.toList
    |> .filter (entry => toEnd.get entry.fst |> .map (rest => entry.snd + rest == best) |> .getOrElse False)
    |> .map (entry => entry.fst.position)
    |> Set.fromList

def Maze.bestTiles (maze: Maze): Set Position :=
  let fromStart := maze.fromStart
  match maze.lowestScore fromStart with
    | Some best => tilesScoring fromStart maze.toEnd best
    | None => Set.empty

def solvePart1 (maze: Maze): Nat := maze.lowestScore maze.fromStart |> .getOrElse 0

def solvePart2 (maze: Maze): Nat := maze.bestTiles.size
