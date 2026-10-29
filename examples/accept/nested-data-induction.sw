-- Induction and recursion over nested data types
-- (docs/proposals/nested-data-types.md §9, §10 stage 3). A type that holds
-- itself inside `List`, `Option`, a pair, or a container of the program
-- gets, generated:
--
-- - `T.size`, the number of constructors in a value, the lists' cells
--   included; a recursive call on an element of a list in a node, brought
--   into scope by `attach`, is then smaller under `decreasing T.size x`
--   with nothing to prove by hand;
-- - `T.induct`, one case per constructor, where a field that holds the type
--   inside a container has that container's `All` of the motive as its
--   hypothesis (`List.All motive items`, `List.All (Option.All motive)
--   xs`);
-- - `T.inductMem`, for a field that's a `List T` or an `Option T` itself:
--   the hypothesis for every member, `(q: T) → List.Mem q items → motive q`;
-- - `D.All` for a container `D` of the program the type is in.
--
-- accept/nested-data.sw has the hand-written versions to compare.
--
--   $ stitchwort run examples/accept/nested-data-induction.sw
--   depth: 3
--   numbers: 4
--   labels: [1, 2, 3, 4]
--   ranked: 3
--   weight: 7

import Std (Eq, IO, List, Nat, Option, Pair, Unit, Vec, Void)
import Std.IO (print)

-- A packet is a number or a list of packets (Advent of Code 2022, day 13).
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

def example: Packet := Packets [Number 1, Packets [Number 2, Packets [Number 3]], Packets [], Number 4]

-- `Packet.size` counts constructors: `Packets [Number 1]` is a `Packets`, a
-- `Cons`, a `Number` and a `Nil`.
theorem sizeOne: Packet.size (Packets [Number 1]) = 4 := rfl

-- Recursion through `map` on the attached list: `e.isIn` says that
-- `e.value` is in `items`, and the generated lemma that an element of the
-- list is smaller than the packet proves the call smaller. No `size`, no
-- lemma, no `let` written here.
def Packet.depth (p: Packet): Nat
    decreasing Packet.size p
:=
  match p with
    | Number n => 0
    | Packets items => 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max)

test "depth" := Packet.depth example == 3

-- Structural recursion with a helper for the list, as before.
def numbers: Packet → Nat
  | Number _ => 1
  | Packets items => numbersIn items

def numbersIn: List Packet → Nat
  | Nil => 0
  | Cons p rest => numbers p + numbersIn rest

-- A proof by `Packet.induct`: the `Packets` case gets `List.All` of the
-- claim for its items, which a lemma over the list takes apart. Each step
-- is closed by `omega`. `Packet.size (Packets items)` computes as far as the
-- list is known, so the lemma can state its bound with it.
theorem numbersInLe: (items: List Packet) → List.All (q => numbers q ≤ Packet.size q) items →
    numbersIn items ≤ Packet.size (Packets items)
  | Nil, all => rfl
  | Cons p rest, Both here others =>
    let ih := numbersInLe rest others
    omega

theorem numbersLe (p: Packet): numbers p ≤ Packet.size p :=
  Packet.induct (q => numbers q ≤ Packet.size q) (value => rfl) (items all => numbersInLe items all) p

-- The same claim's other half, by `Packet.inductMem`: every member of the
-- list is assumed to have it. Here: every packet has a positive size.
theorem sizePositive (p: Packet): 0 < Packet.size p :=
  Packet.inductMem (q => 0 < Packet.size q) (value => rfl) (items each => rfl) p

-- A rose tree with a parameter: `Rose.induct` takes the motive over `Rose a`.
type Rose (a: Type): Type =
  | Bloom (label: a) (kids: List (Rose a))

def Rose.labels (t: Rose a): List a
    decreasing Rose.size t
:=
  match t with
    | Bloom x kids => Cons x (kids.attach.map (e => Rose.labels e.value) |> .foldLeft [] List.append)

test "labels" := Rose.labels (Bloom 1 [Bloom 2 [], Bloom 3 [Bloom 4 []]]) == [1, 2, 3, 4]

-- A label count is at least one, by `Rose.inductMem` on any `Rose a`.
theorem labelsNonEmpty (t: Rose a): 0 < Rose.size t :=
  Rose.inductMem (s => 0 < Rose.size s) (label kids each => rfl) t

-- Nested twice, and in an `Option` of a pair: the hypotheses compose.
type Nest: Type =
  | Leaf
  | Deep (rows: List (List Nest))
  | Maybe (next: Option (Pair Nest Nat))

-- The statement of `Nest.induct`, written out.
theorem nestInduct (motive: Nest → Prop) (leaf: motive Leaf)
    (deep: (rows: List (List Nest)) → List.All (List.All motive) rows → motive (Deep rows))
    (maybe: (next: Option (Pair Nest Nat)) → Option.All (Pair.All motive (x => Unit)) next → motive (Maybe next))
    (t: Nest): motive t :=
  Nest.induct motive leaf deep maybe t

-- `List (Option T)`: `List.All (Option.All motive)`.
type Sparse: Type =
  | Dense (n: Nat)
  | Holes (slots: List (Option Sparse))

theorem sparseInduct (motive: Sparse → Prop) (dense: (n: Nat) → motive (Dense n))
    (holes: (slots: List (Option Sparse)) → List.All (Option.All motive) slots → motive (Holes slots))
    (t: Sparse): motive t :=
  Sparse.induct motive dense holes t

-- A container of the program: `Bag a` gets `Bag.All`, one predicate for
-- its parameter, true of every value in it.
type Bag (a: Type): Type =
  | Single (x: a)
  | Many (first: a) (rest: List a)

theorem bagAll (p: a → Prop) (x: a) (y: a) (px: p x) (py: p y): Bag.All p (Many x [y]) := Both px (Both py ())

type Crate: Type =
  | Empty
  | Packed (bag: Bag Crate)

theorem crateInduct (motive: Crate → Prop) (empty: motive Empty)
    (packed: (bag: Bag Crate) → Bag.All motive bag → motive (Packed bag))
    (t: Crate): motive t :=
  Crate.induct motive empty packed t

-- An indexed family: the motive takes the index too.
type Ranked: Nat → Type =
  | RLeaf: Ranked 0
  | RNode (n: Nat) (kids: List (Ranked n)): Ranked (Succ n)

def Ranked.count (r: Ranked k): Nat
    decreasing Ranked.size r
:=
  match r with
    | RLeaf => 1
    | RNode n kids => 1 + (kids.attach.map (e => Ranked.count e.value) |> .foldLeft 0 Nat.add)

theorem rankedPositive (r: Ranked k): 0 < Ranked.size r :=
  Ranked.induct (n s => 0 < Ranked.size s) rfl (n kids all => rfl) r

-- A record, with a weight on each node.
type Node = { weight: Nat, children: List Node }

def Node.total (node: Node): Nat
    decreasing Node.size node
:=
  match node with
    | { weight, children } => weight + (children.attach.map (e => Node.total e.value) |> .foldLeft 0 Nat.add)

test "total" := Node.total { weight = 1, children = [{ weight = 2, children = [] }, { weight = 4, children = [] }] } == 7

def main(): {IO} () :=
  print "depth: ${Packet.depth example}"
  print "numbers: ${numbers example}"
  print "labels: ${Rose.labels (Bloom 1 [Bloom 2 [], Bloom 3 [Bloom 4 []]])}"
  print "ranked: ${Ranked.count (RNode 1 [RNode 0 [], RNode 0 []])}"
  print "weight: ${Node.total { weight = 1, children = [{ weight = 2, children = [] }, { weight = 4, children = [] }] }}"
