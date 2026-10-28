-- Advent of Code 2024, day 23: a map of a LAN, one connection between two
-- computers per line. Part 1 counts the sets of three computers, each
-- connected to the other two, with a computer whose name starts with t.
-- Part 2 finds the largest set of computers all connected to each other and
-- prints their names, sorted and joined with commas.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day23.main < examples/2024/day23.txt
--
-- The proofs are in `Aoc.Year2024.Day23.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day23.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day23
import Std (Bool, Char, Eq, Fail, IO, List, Map, Nat, Pair, Parse, Set, Text)
import Std.Parse (lines, satisfy, text)

def main(): {IO, Fail} () :=
  let network := parseNetwork IO.readAll()
  IO.print "Part 1: ${solvePart1 network}"
  IO.print "Part 2: ${solvePart2 network}"

-- A computer, by its two-letter name.
def Computer: Type := Text

-- "Connections aren't directional": `kh-tc` and `tc-kh` are the same.
type Network = { connections: List (Computer, Computer) }

def isLowercase (char: Char): Bool := 'a' ≤ char && char ≤ 'z'

def computer(): {Parse} Computer :=
  let first := satisfy "a lowercase letter" isLowercase
  let second := satisfy "a lowercase letter" isLowercase
  Text.fromList [first, second]

-- One connection: "kh-tc".
def connection(): {Parse} (Computer, Computer) :=
  let one := computer()
  text "-"
  let other := computer()
  (one, other)

def parseNetwork (input: Text): {Fail} Network := { connections = Parse.all input (() => lines connection) }

-- Each computer's connections, both ways round.
def Links: Type := Map Computer (Set Computer)

-- Each connection, both ways round.
def Network.bothWays (network: Network): List (Computer, Computer) :=
  network.connections.flatMap (connection => [connection, (connection.snd, connection.fst)])

def Network.links (network: Network): Links :=
  network.bothWays |> Map.groupBy Pair.fst |> .map (pairs => pairs.map Pair.snd |> Set.fromList)

def neighbours (links: Links) (computer: Computer): Set Computer := links.getOr computer Set.empty

-- The sets of `first`, one of its neighbours, and a neighbour of both.
def setsWith (links: Links) (first: Computer): List (Set Computer) :=
  let firstNeighbours := neighbours links first
  firstNeighbours.toList.flatMap (second =>
    neighbours links second |> .intersect firstNeighbours |> .toList |> .map (third => Set.fromList [first, second, third]))

-- Every set of three different computers, each connected to the other two.
def setsOfThree (links: Links): Set (Set Computer) :=
  links.keySet.toList.flatMap (setsWith links) |> Set.fromList |> .filter (set => set.size == 3)

-- Whether a computer's name starts with t, as the Chief Historian's does.
def mightBeChiefs (set: Set Computer): Bool := set.any (computer => computer.startsWith "t")

def solvePart1 (network: Network): Nat := setsOfThree network.links |> .filter mightBeChiefs |> .size

-- The larger of `best` and the largest set of computers all connected to
-- each other made of `clique` and some of `candidates`, each of which is
-- connected to all of `clique`. Each candidate in turn is either in the set
-- (and then only its neighbours stay candidates) or not. A search that
-- can't beat `best`, with too few candidates left, stops.
def largestFrom (links: Links) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer): Set Computer
    decreasing candidates.size
:=
  if clique.size + candidates.size ≤ best.size then best
  else
    match candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        -- Always true (`Set.sizePopMin`); the test puts it in scope for the
        -- recursive calls.
        if fewer: others.size < candidates.size then
          let narrowed := neighbours links candidate |> .intersect others
          let withinOthers: narrowed.size ≤ others.size :=
            Set.sizeSubset others narrowed (key inside =>
              Bool.andRight _ _ (Eq.trans (Eq.sym (Set.containsIntersect (neighbours links candidate) key others)) inside))
          let withIt := largestFrom links (clique.insert candidate) narrowed best [decreasing := omega [withinOthers, fewer]]
          largestFrom links clique others withIt
        else best

-- The largest set of computers that are all connected to each other.
def largestClique (links: Links): Set Computer := largestFrom links Set.empty links.keySet Set.empty

-- "the name of every computer at the LAN party, sorted alphabetically, then
-- joined together with commas".
def password (party: Set Computer): Text := party.toList.sort.joinWith ","

def solvePart2 (network: Network): Text := largestClique network.links |> password
