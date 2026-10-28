-- Day 23 as the puzzle states it, over the list of connections. The proofs
-- (Proofs/) show the program's answers are these, for every network.
--
-- Both parts are about sets of computers, so the spec uses `Set Computer`,
-- whose `size` is the number of computers in it: a set of three is counted
-- once, however its computers are ordered.

namespace Aoc.Year2024.Day23.Spec
import Aoc.Year2024.Day23 (Computer, Network)
import Std (And, Bool, Exists, Iff, List, Nat, Not, Set, Text)

-- "the line kh-tc represents a connection between the computer named kh and
-- the computer named tc. Connections aren't directional; tc-kh would mean
-- exactly the same thing."
def connected (network: Network) (one: Computer) (other: Computer): Bool :=
  network.connections.any (connection => connection == (one, other) || connection == (other, one))

-- "each computer in the set is connected to the other two computers" (or,
-- in part 2, "to every other computer").
def AllConnected (network: Network) (set: Set Computer): Prop :=
  (one: Computer) → (other: Computer) → set.contains one = True → set.contains other = True → Not (one = other) →
    connected network one other = True

-- "sets of three computers where each computer in the set is connected to
-- the other two computers".
def InterConnectedThree (network: Network) (set: Set Computer): Prop := set.size = 3 ∧ AllConnected network set

-- "at least one computer with a name that starts with t".
def hasT (set: Set Computer): Bool := set.any (computer => computer.startsWith "t")

-- "Find all the sets of three inter-connected computers. How many contain at
-- least one computer with a name that starts with t?": `count` is the
-- number of such sets, the size of the set holding exactly them.
def IsPart1 (network: Network) (count: Nat): Prop :=
  ∃ (sets: Set (Set Computer)) =>
    ((set: Set Computer) → Iff (sets.contains set = True) (InterConnectedThree network set ∧ hasT set = True)) ∧ sets.size = count

-- The computers on the network map: those in some connection.
def computers (network: Network): List Computer := network.connections.flatMap (connection => [connection.fst, connection.snd])

-- "a set of computers that are all connected to each other": computers on
-- the map, each connected to every other one in the set.
def IsClique (network: Network) (set: Set Computer): Prop :=
  ((member: Computer) → set.contains member = True → member ∈ computers network) ∧ AllConnected network set

-- "the largest set of computers that are all connected to each other": no
-- such set has more computers. The puzzle says "the", but nothing in the
-- input rules out two of the same size; this is any one of them.
def IsLargest (network: Network) (set: Set Computer): Prop :=
  IsClique network set ∧ ((other: Set Computer) → IsClique network other → other.size ≤ set.size)

-- "the password to get into the LAN party is the name of every computer at
-- the LAN party, sorted alphabetically, then joined together with commas".
def password (party: Set Computer): Text := party.toList.sort.joinWith ","

-- "What is the password to get into the LAN party?": the password of a
-- largest set.
def IsPart2 (network: Network) (answer: Text): Prop := ∃ (party: Set Computer) => IsLargest network party ∧ answer = password party
