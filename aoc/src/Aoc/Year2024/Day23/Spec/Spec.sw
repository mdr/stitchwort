--| Day 23 as the puzzle states it, over the list of connections. The proofs
--| (Proofs/) show the program's answers are these, for every network.
--|
--| Both parts are about sets of computers, so the spec uses a `Party`, whose
--| `members` are a `Set Computer` with a `size`, the number of computers in
--| it: a set of three is counted once, however its computers are ordered.
--| The spec states "starts with t" and the password itself rather than using
--| the program's `Computer.mightBeChief` and `Party.password`, which the
--| proofs check against these.

namespace Aoc.Year2024.Day23.Spec
import Aoc.Year2024.Day23 (Computer, Network, Party)
import Std (And, Bool, Exists, Iff, List, Nat, Not, Set, Text)

--| "the line kh-tc represents a connection between the computer named kh and
--| the computer named tc. Connections aren't directional; tc-kh would mean
--| exactly the same thing."
def connected (network: Network) (one other: Computer): Bool := network.connections.any (connection =>
  connection == { one = one, other = other } || connection == { one = other, other = one })

--| "each computer in the set is connected to the other two computers" (or,
--| in part 2, "to every other computer").
def AllConnected (network: Network) (party: Party): Prop :=
  ∀ (one other: Computer) => party.members.contains one = True
    → party.members.contains other = True
    → one ≠ other
    → connected network one other = True

--| "sets of three computers where each computer in the set is connected to
--| the other two computers".
def InterConnectedThree (network: Network) (party: Party): Prop := party.members.size = 3 ∧ AllConnected network party

--| "at least one computer with a name that starts with t".
def hasT (party: Party): Bool := party.members.any (computer => computer.name.startsWith "t")

--| "Find all the sets of three inter-connected computers. How many contain at
--| least one computer with a name that starts with t?": `count` is the number
--| of such sets, the size of the set holding exactly them.
def IsPart1 (network: Network) (count: Nat): Prop :=
  ∃ (parties: Set Party) => (∀ (party: Party) => (parties.contains party = True)
    ↔ (InterConnectedThree network party ∧ hasT party = True))
    ∧ parties.size = count

--| The computers on the network map: those in some connection.
def computers (network: Network): List Computer :=
  network.connections.flatMap (connection => [connection.one, connection.other])

--| "a set of computers that are all connected to each other": computers on
--| the map, each connected to every other one in the set.
def IsClique (network: Network) (party: Party): Prop :=
  (∀ (member: Computer) => party.members.contains member = True → member ∈ computers network)
    ∧ AllConnected network party

--| "the largest set of computers that are all connected to each other": no
--| such set has more computers. The puzzle says "the", but nothing in the
--| input rules out two of the same size; this is any one of them.
def IsLargest (network: Network) (party: Party): Prop :=
  IsClique network party ∧ (∀ (other: Party) => IsClique network other → other.members.size ≤ party.members.size)

--| "the password to get into the LAN party is the name of every computer at
--| the LAN party, sorted alphabetically, then joined together with commas".
def password (party: Party): Text := party.members.toList |> .map .name |> .sort |> .joinWith ","

--| "What is the password to get into the LAN party?": the password of a
--| largest set.
def IsPart2 (network: Network) (answer: Text): Prop :=
  ∃ (party: Party) => IsLargest network party ∧ answer = password party
