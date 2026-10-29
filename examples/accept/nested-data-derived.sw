-- Derived `==`, `<` and `${…}` for nested data types
-- (docs/proposals/nested-data-types.md §10, stage 2). A type inside `List`,
-- `Option` or a pair (or those inside each other) gets them as any other
-- type does: `==` structural, `Ord` constructors first and then fields,
-- with lists compared as `List`'s own `Ord` compares them, and `Show`
-- printing a list and a pair as their own instances print them. Each
-- container gets a helper defined together with the type's own function
-- (`Packet.%decEq` with one for `List Packet`), so every call is on a part
-- of the argument. Nesting through another container (`Vec`, a type of the
-- program) gets none: reject/nested-data-derived-vec.sw.
--
--   $ stitchwort run examples/accept/nested-data-derived.sw
--   compare [[1], [2, [3]]] [[1], [2, [4]]]: Less
--   sorted: [Number 0, Number 3, Packets [], Packets [Number 1]]
--   Node 'a' [Node 'b' [], Node 'c' [Node 'd' []]]

import Std (IO, List, Map, Nat, Option, Ordering, Text)
import Std.IO (print)

-- A packet is a number or a list of packets (Advent of Code 2022, day 13).
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

def example: Packet := Packets [Packets [Number 1], Packets [Number 2, Packets [Number 3]]]

test "equal" := example == Packets [Packets [Number 1], Packets [Number 2, Packets [Number 3]]]
test "unequal deep down" := example != Packets [Packets [Number 1], Packets [Number 2, Packets [Number 4]]]
test "unequal lengths" := Packets [Number 1] != Packets [Number 1, Number 1]
test "unequal constructors" := Number 0 != Packets []

-- Constructors in the order they're declared, then the fields; the lists
-- inside compare as lists do: element by element, a shorter prefix first.
test "constructors first" := Number 100 < Packets []
test "element by element" := Packets [Number 1, Number 9] < Packets [Number 2]
test "prefix first" := Packets [Number 1] < Packets [Number 1, Number 0]
test "compare" := Ord.compare example (Packets [Packets [Number 1], Packets [Number 2]]) == Greater
test "compare equal" := Ord.compare example example == Equal
test "as lists do" :=
  Ord.compare (Packets [Number 1, Number 9]) (Packets [Number 2]) == Ord.compare [1, 9] [2]

-- As a list of numbers would print, with the constructors.
test "show" := "${example}" == "Packets [Packets [Number 1], Packets [Number 2, Packets [Number 3]]]"
test "show empty" := "${Packets []}" == "Packets []"
test "show in a list" := "${[Number 1, Packets []]}" == "[Number 1, Packets []]"

-- What `==` and `Ord` give the library: sorting, `contains`, maps.
test "sort" :=
  List.sort [Packets [Number 1], Number 3, Packets [], Number 0] ==
    [Number 0, Number 3, Packets [], Packets [Number 1]]
test "contains" := [Number 1, example].contains example
test "map keys" := (Map.fromList [(example, 1), (Number 2, 2)]).get example == Some 1

-- `auto`, `if h:` and a proposition where a `Bool` is expected decide an
-- equation between packets with the derived instance, which also computes
-- in proofs.
def needsSame (p: Packet) (q: Packet) [auto same: p = q]: Nat := 1
test "auto" := needsSame (Packets [Number 1]) (Packets [Number 1]) == 1
test "if" := (if h: example = example then 1 else 0) == 1
def isEmpty (p: Packet): Bool := p = Packets []
test "as a Bool" := isEmpty (Packets []) && !isEmpty (Packets [Packets []])
theorem computes: (Packets [Number 1, Packets []] == Packets [Number 1, Packets []]) = True := rfl
theorem comparesInProofs: Ord.compare (Number 7) (Packets []) = Less := rfl

-- A rose tree: a parameter, and the list of trees.
type Rose (a: Type): Type =
  | Node (label: a) (kids: List (Rose a))

def rose: Rose Char := Node 'a' [Node 'b' [], Node 'c' [Node 'd' []]]

test "rose equal" := rose == Node 'a' [Node 'b' [], Node 'c' [Node 'd' []]]
test "rose unequal" := rose != Node 'a' [Node 'b' [], Node 'c' [Node 'e' []]]
test "rose order" := Node 1 [Node 2 []] < Node 1 [Node 2 [Node 0 []]]
test "rose label first" := Node 1 [Node 9 []] < Node 2 []
test "rose show" := "${rose}" == "Node 'a' [Node 'b' [], Node 'c' [Node 'd' []]]"

-- A list of lists: a helper for each list type.
type Table: Type =
  | Cell (n: Nat)
  | Rows (rows: List (List Table))

test "table equal" := Rows [[Cell 1], [Cell 2, Rows []]] == Rows [[Cell 1], [Cell 2, Rows []]]
test "table unequal" := Rows [[Cell 1], [Cell 2, Rows []]] != Rows [[Cell 1], [Cell 2, Rows [[]]]]
test "table order" := Rows [[Cell 1], []] < Rows [[Cell 1], [Cell 0]]
test "table show" := "${Rows [[Cell 1], [], [Rows [[]]]]}" == "Rows [[Cell 1], [], [Rows [[]]]]"

-- An option of a pair: `None` first, then the pair's parts in order.
type Chain: Type =
  | Stop
  | Link (next: Option (Chain, Nat)) (name: Text)

def chain: Chain := Link (Some (Link None "b", 3)) "a"

test "chain equal" := chain == Link (Some (Link None "b", 3)) "a"
test "chain unequal" := chain != Link (Some (Link None "b", 4)) "a"
test "chain none first" := Link None "z" < Link (Some (Stop, 0)) "a"
test "chain pair in order" := Link (Some (Stop, 9)) "a" < Link (Some (Link None "", 0)) "a"
test "chain show" := "${chain}" == "Link (Some (Link None \"b\", 3)) \"a\""

-- A few thousand nodes.
def wide (n: Nat): Packet := Packets (List.range n |> .map (k => Packets [Number k, Packets []]))

test "big" := wide 3000 == wide 3000 && wide 3000 < Packets [wide 3000]

def main(): {IO} () :=
  let left := Packets [Packets [Number 1], Packets [Number 2, Packets [Number 3]]]
  let right := Packets [Packets [Number 1], Packets [Number 2, Packets [Number 4]]]
  print "compare [[1], [2, [3]]] [[1], [2, [4]]]: ${Ord.compare left right}"
  print "sorted: ${List.sort [Packets [Number 1], Number 3, Packets [], Number 0]}"
  print "${rose}"
