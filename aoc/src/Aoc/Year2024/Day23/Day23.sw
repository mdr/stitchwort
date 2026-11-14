--| Advent of Code 2024, day 23: a map of a LAN, one connection between two
--| computers per line. Part 1 counts the sets of three computers, each
--| connected to the other two, with a computer whose name starts with t.
--| Part 2 finds the largest set of computers all connected to each other and
--| prints their names, sorted and joined with commas.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day23.main < examples/2024/day23.txt
--|
--| The proofs are in `Aoc.Year2024.Day23.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day23.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day23
import Std (Bool, Char, Eq, Fail, IO, List, Map, Nat, Parse, Set, Text)
import Std.Parse (lines, satisfy, text)

def main(): {IO, Fail} () :=
  let network := parseNetwork IO.readAll()
  IO.print "Part 1: ${solvePart1 network}"
  IO.print "Part 2: ${solvePart2 network}"

--| A computer, by its two-letter name.
type Computer = { name: Text }

--| Whether the name starts with t, as the Chief Historian's does.
def Computer.mightBeChief (computer: Computer): Bool := computer.name.startsWith "t"

--| A connection between two computers.
type Connection = { one: Computer, other: Computer }

--| The same connection read from the other end: "Connections aren't
--| directional".
def Connection.reverse (connection: Connection): Connection := { one = connection.other, other = connection.one }

--| A set of computers: a LAN party, or a set of three to count.
type Party = { members: Set Computer }

def Party.size (party: Party): Nat := party.members.size

--| Whether some member's name starts with t.
def Party.mightHaveChief (party: Party): Bool := party.members.any .mightBeChief

--| "the name of every computer at the LAN party, sorted alphabetically, then
--| joined together with commas".
def Party.password (party: Party): Text := party.members.toList |> .map .name |> .sort |> .joinWith ","

--| `kh-tc` and `tc-kh` are the same connection, so the network lists each
--| in either order, and may list one twice.
type Network = { connections: List Connection }

def computer(): {Parse} Computer :=
  let first := satisfy "a lowercase letter" Char.isAsciiLowercase
  let second := satisfy "a lowercase letter" Char.isAsciiLowercase
  { name = Text.fromList [first, second] }

--| One connection: "kh-tc".
def connection(): {Parse} Connection :=
  let one := computer()
  text "-"
  let other := computer()
  { one = one, other = other }

def parseNetwork (input: Text): {Fail} Network := { connections = Parse.all input (() => lines connection |> .toList) }

--| Each computer's neighbours.
def Links: Type := Map Computer (Set Computer)

--| Each connection, both ways round.
def Network.bothWays (network: Network): List Connection :=
  network.connections.flatMap (connection => [connection, connection.reverse])

def Network.links (network: Network): Links :=
  network.bothWays
    |> .groupBy Connection.one
    |> .map (connections => connections.map Connection.other |> .toList |> .toSet)

def Links.neighbours (links: Links) (computer: Computer): Set Computer := links.getOr computer Set.empty

--| The parties of `first`, one of its neighbours, and a neighbour of both.
def Links.setsWith (links: Links) (first: Computer): List Party :=
  let firstNeighbours := links.neighbours first
  firstNeighbours.toList.flatMap (second =>
    links.neighbours second
      |> .intersect firstNeighbours
      |> .toList
      |> .map (third => { members = [first, second, third].toSet }))

--| Every set of three different computers, each connected to the other two.
def Links.setsOfThree (links: Links): Set Party :=
  links.keySet.toList.flatMap links.setsWith |> .toSet |> .filter (.size == 3)

def solvePart1 (network: Network): Nat := network.links.setsOfThree |> .filter .mightHaveChief |> .size

--| The larger of `best` and the largest set of computers all connected to
--| each other made of `clique` and some of `candidates`, each of which is
--| connected to all of `clique`. Each candidate in turn is either in the set
--| (and then only its neighbours stay candidates) or not. A search that
--| can't beat `best`, with too few candidates left, stops.
def Links.largestFrom (links: Links) (clique candidates best: Set Computer): Set Computer
    decreasing candidates.size
:=
  if clique.size + candidates.size ≤ best.size then best
  else
    match found: candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        let fewer := Set.sizePopMin candidates candidate others found
        let narrowed := links.neighbours candidate |> .intersect others
        let withinOthers: narrowed.size ≤ others.size := Set.sizeSubset others narrowed (key inside =>
          Bool.andRight (Eq.trans (Eq.sym (Set.containsIntersect (links.neighbours candidate) key others)) inside))
        let withIt :=
          links.largestFrom (clique.insert candidate) narrowed best [decreasing := omega [withinOthers, fewer]]
        links.largestFrom clique others withIt

--| The largest set of computers that are all connected to each other.
def Links.largestClique (links: Links): Party := { members = links.largestFrom Set.empty links.keySet Set.empty }

def solvePart2 (network: Network): Text := network.links.largestClique |> .password
