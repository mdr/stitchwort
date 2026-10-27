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

namespace Aoc.Year2025.Day08.Spec
import Aoc.Year2025.Day08 (..)
import Std (Iff, List, Nat, Ord, Ordering)

-- Box number i.
def boxAt (points: List Point) (i: Nat): Point := points.getOr i origin

-- Every pair of the boxes 0 to n - 1: box i with box j, for i < j.
def allPairs (n: Nat): List (Nat, Nat) := List.range n |> .pairs

-- What decides the order of the pairs: the squared distance between the
-- two boxes (in the same order as the distance), then the first box, then
-- the second. (A `Connection` is ordered by its fields in turn.)
def connectionKey (points: List Point) (pair: (Nat, Nat)): Connection :=
  { distance = (boxAt points pair.fst).squaredDistance (boxAt points pair.snd), first = pair.fst, second = pair.snd }

-- Every pair of boxes, in the order they are connected.
def connectionOrder (points: List Point): List (Nat, Nat) := allPairs points.length |> .sortOn (connectionKey points)

-- The first k connections.
def firstConnections (k: Nat) (points: List Point): List (Nat, Nat) := connectionOrder points |> .take k

-- `Joined connections a b`: box a and box b are in the same circuit, linked
-- by a chain of the connections.
type Joined (connections: List (Nat, Nat)): Nat → Nat → Prop =
  | Itself (box: Nat): Joined connections box box
  | Connected [a b: Nat] (connection: List.Mem (a, b) connections): Joined connections a b
  | Backwards [a b: Nat] (joined: Joined connections a b): Joined connections b a
  | Chain [a b c: Nat] (first: Joined connections a b) (next: Joined connections b c): Joined connections a c

-- `sameCircuit` tells, for any two of the boxes 0 to n - 1, whether they
-- are in the same circuit. (`Joined` is a proposition, so the sizes below,
-- which count boxes, are written with such a test; any two tests that tell
-- give the same sizes.)
def Tells (n: Nat) (connections: List (Nat, Nat)) (sameCircuit: Nat → Nat → Bool): Prop :=
  (a: Nat) → (b: Nat) → a < n → b < n → Iff (sameCircuit a b = True) (Joined connections a b)

-- The size of each circuit of the boxes 0 to n - 1: a circuit is counted
-- once, at its first box (no lower box is in it), and its size is the
-- number of boxes in it.
def circuitSizes (n: Nat) (sameCircuit: Nat → Nat → Bool): List Nat :=
  List.range n
    |> .filter (box => ¬(List.range box |> .any (other => sameCircuit other box)))
    |> .map (box => List.range n |> .count (other => sameCircuit other box))

-- The three largest sizes (or all, if there are fewer), multiplied.
def threeLargestProduct (sizes: List Nat): Nat := sizes.sortBy (a b => Nat.compare b a) |> .take 3 |> .product

-- All the boxes 0 to n - 1 are in one circuit.
def OneCircuit (n: Nat) (connections: List (Nat, Nat)): Prop :=
  (a: Nat) → (b: Nat) → a < n → b < n → Joined connections a b

-- Connection number k (counting from 0) is the last one needed: after it
-- all the boxes are in one circuit, and before it they weren't.
def LastNeeded (points: List Point) (k: Nat): Prop :=
  And (OneCircuit points.length (firstConnections (Succ k) points)) (Not (OneCircuit points.length (firstConnections k points)))

-- Connection number k.
def connectionAt (points: List Point) (k: Nat): (Nat, Nat) := connectionOrder points |> .getOr k (0, 0)

-- The product of the X coordinates of a pair's two boxes.
def xProduct (points: List Point) (pair: (Nat, Nat)): Nat := (boxAt points pair.fst).x * (boxAt points pair.snd).x
