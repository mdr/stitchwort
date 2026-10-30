-- expect-error: E-UNKNOWN-NAME
-- True statements with broken proofs about trees that hold a `List` or a
-- `Vec` of themselves: the search finds no counterexample, says nothing,
-- and finishes quickly. A random list's elements share its size (SW-900);
-- when each was drawn at the whole size, a random rose tree grew faster
-- than exponentially, and checking `rose` used 3 GB within a second.
import Std (List, Nat, Vec)

type Rose: Type =
  | Leaf
  | Node (kids: List Rose)

theorem rose (q: Rose): q = q := nope

-- The program SW-900 was found with.
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

theorem smaller (items: List Packet) (q: Packet) (h: List.Mem q items): q = q := nope

type Wide: Type =
  | WLeaf
  | WNode (kids: Vec Wide 2)

-- Trees in a `Vec`, whose elements share its size too. `Vec` has `DecEq`
-- (`Wide` hasn't: none is derived through a `Vec`), so these are searched.
theorem pair (v: Vec Rose 2): v = v := nope

type Grid: Type =
  | Done
  | Row (cells: Vec Rose 3) (rest: Grid)

theorem grid (g: Grid): g = g := nope
