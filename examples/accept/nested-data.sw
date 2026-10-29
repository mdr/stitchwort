-- Nested data types (docs/proposals/nested-data-types.md): a data type may
-- hold itself inside an earlier data type, such as `List`, at a parameter
-- that the earlier type only stores. Pairs with soundness/nested-negative.sw
-- (a type inside `Neg`, which takes its parameter as a function's input),
-- soundness/nested-in-quotient.sw and soundness/partial-nested.sw. More
-- shapes are in accept/nested-data-shapes.sw; derived `==`, `<` and `${…}`
-- in accept/nested-data-derived.sw.
--
--   $ stitchwort run examples/accept/nested-data.sw
--   size: 6

import Std (Eq, IO, List, Nat, Void)
import Std.IO (print)

-- A packet is a number or a list of packets (Advent of Code 2022, day 13).
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

-- Structural recursion: `items` is part of the packet `size` matched, and a
-- packet matched out of `items` is part of `items`, so part of the packet
-- too. A function and its helper for the list are defined together.
def size: Packet → Nat
  | Number n => 1
  | Packets items => Succ (sizeList items)

def sizeList: List Packet → Nat
  | Nil => 0
  | Cons p rest => size p + sizeList rest

def example: Packet := Packets [Number 1, Packets [Number 2, Number 3], Packets []]

test "size" := size example == 6
theorem sizeExample: size example = 6 := rfl

-- `List`'s own functions and theorems apply to the list inside.
test "length" := match example with
  | Number _ => False
  | Packets items => items.length == 3

-- A packet in a list is no bigger than the list, so it's smaller than the
-- packet that holds the list.
theorem sizeListMem (q: Packet): (items: List Packet) → List.Mem q items → size q ≤ sizeList items
  | Nil, member => Void.exfalso member
  | Cons p rest, Inl same => rewrite same in Nat.leAddRight (size q) (sizeList rest)
  | Cons p rest, Inr member =>
    Nat.leTrans (size q) (sizeList rest) (size p + sizeList rest)
      (sizeListMem q rest member) (Nat.leAddLeft (size p) (sizeList rest))

theorem sizeMem (q: Packet) (items: List Packet) (member: List.Mem q items): size q < size (Packets items) :=
  sizeListMem q items member

def main(): {IO} () := print "size: ${size example}"
