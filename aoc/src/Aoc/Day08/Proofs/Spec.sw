-- Day 8 as the puzzle states it, over the parsed boxes, for the proofs in
-- Proofs/Part1.sw and Proofs/Part2.sw.
--
-- In plain words:
--   - The boxes are numbered by their place in the input, from 0.
--   - "Connect together the 1000 pairs of junction boxes which are closest
--     together": the pairs are every box i with every box j, i < j, in
--     order of straight-line distance, closest first. The puzzle doesn't
--     say what comes first at equal distances; here it is the pair with the
--     lower first box, then the lower second box (`connectionOrder`). Pairs
--     already in one circuit count too: connecting them, "nothing happens".
--   - "Electricity can pass between those two junction boxes", and on
--     along every string of lights: two boxes are in the same circuit when
--     a chain of connections links them (`Joined`).
--   - Part 1: after the first k connections (1,000 for the input), "multiply
--     together the sizes of the three largest circuits".
--   - Part 2: "continue connecting the closest unconnected pairs of junction
--     boxes together until they're all in the same circuit", and multiply
--     the X coordinates of the last two boxes connected: those of the
--     connection after which, for the first time, all the boxes are in one
--     circuit (`LastNeeded`).

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Aoc.Day08.Tests (example)
import Std (List, Nat, Ord, Ordering)

-- Box number i.
def boxAt (points: List Point) (i: Nat): Point := points.getOr origin i

-- Every pair of the boxes 0 to n - 1: box i with box j, for i < j.
def allPairs (n: Nat): List (Nat, Nat) := (List.range n).pairs

-- What decides the order of the pairs: the squared distance between the
-- two boxes (in the same order as the distance), then the first box, then
-- the second.
def connectionKey (points: List Point) (pair: (Nat, Nat)): (Nat, Nat, Nat) :=
  ((boxAt points pair.fst).squaredDistance (boxAt points pair.snd), pair.fst, pair.snd)

-- Every pair of boxes, in the order they are connected.
def connectionOrder (points: List Point): List (Nat, Nat) :=
  allPairs points.length |> .sortBy (a b => Ord.compare (connectionKey points a) (connectionKey points b))

-- The first k connections.
def firstConnections (k: Nat) (points: List Point): List (Nat, Nat) := (connectionOrder points).take k

-- `Joined connections a b`: box a and box b are in the same circuit, linked
-- by a chain of the connections.
type Joined (connections: List (Nat, Nat)): Nat -> Nat -> Prop =
  | Itself (box: Nat): Joined connections box box
  | Connected [a b: Nat] (connection: List.Mem (a, b) connections): Joined connections a b
  | Backwards [a b: Nat] (joined: Joined connections a b): Joined connections b a
  | Chain [a b c: Nat] (first: Joined connections a b) (next: Joined connections b c): Joined connections a c

-- Each of p and q follows from the other.
def Iff (p: Prop) (q: Prop): Prop := And (p -> q) (q -> p)

-- `sameCircuit` tells, for any two of the boxes 0 to n - 1, whether they
-- are in the same circuit. (`Joined` is a proposition, so the sizes below,
-- which count boxes, are written with such a test; any two tests that tell
-- give the same sizes.)
def Tells (n: Nat) (connections: List (Nat, Nat)) (sameCircuit: Nat -> Nat -> Bool): Prop :=
  (a: Nat) -> (b: Nat) -> a < n -> b < n -> Iff (sameCircuit a b = True) (Joined connections a b)

-- The size of each circuit of the boxes 0 to n - 1: a circuit is counted
-- once, at its first box (no lower box is in it), and its size is the
-- number of boxes in it.
def circuitSizes (n: Nat) (sameCircuit: Nat -> Nat -> Bool): List Nat :=
  List.range n
    |> .filter (box => !(List.range box |> .any (other => sameCircuit other box)))
    |> .map (box => List.range n |> .count (other => sameCircuit other box))

-- The three largest sizes (or all, if there are fewer), multiplied.
def threeLargestProduct (sizes: List Nat): Nat := sizes.sortBy (a b => Nat.compare b a) |> .take 3 |> .product

-- All the boxes 0 to n - 1 are in one circuit.
def OneCircuit (n: Nat) (connections: List (Nat, Nat)): Prop :=
  (a: Nat) -> (b: Nat) -> a < n -> b < n -> Joined connections a b

-- Connection number k (counting from 0) is the last one needed: after it
-- all the boxes are in one circuit, and before it they weren't.
def LastNeeded (points: List Point) (k: Nat): Prop :=
  And (OneCircuit points.length (firstConnections (Succ k) points)) (Not (OneCircuit points.length (firstConnections k points)))

-- Connection number k.
def connectionAt (points: List Point) (k: Nat): (Nat, Nat) := (connectionOrder points).getOr (0, 0) k

-- The product of the X coordinates of a pair's two boxes.
def xProduct (points: List Point) (pair: (Nat, Nat)): Nat := (boxAt points pair.fst).x * (boxAt points pair.snd).x

test "the example's first connections" :=
  firstConnections 4 example.points == [(0, 19), (0, 7), (2, 13), (7, 19)]
test "pairs at equal distances come in box order" :=
  connectionOrder [{ x = 0, y = 0, z = 0 }, { x = 1, y = 0, z = 0 }, { x = 2, y = 0, z = 0 }] == [(0, 1), (1, 2), (0, 2)]
