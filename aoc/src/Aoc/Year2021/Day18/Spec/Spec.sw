--| Day 18 as the puzzle states it. The puzzle's rules say "the first regular
--| number to the left" and "the leftmost such pair": they are about reading
--| order. So the spec reads a number as its regular numbers from left to
--| right, each with how many pairs it is inside (`leaves`), and states
--| exploding and splitting on that list, where "to the left" is "earlier in
--| the list". The number type is the program's; nothing else is shared with
--| it. The proofs (Proofs/) show the program's steps on the tree are these
--| steps on its leaves.

namespace Aoc.Year2021.Day18.Spec
import Aoc.Year2021.Day18 (Number)
import Std (List, Nat, Option)

--| A regular number, and how many pairs it is inside.
type Leaf = { value: Nat, depth: Nat }

--| A number's regular numbers in reading order, for a number inside `depth`
--| pairs.
def leaves (depth: Nat): Number → List Leaf
  | Regular value => [{ value, depth }]
  | Pair left right => leaves (depth + 1) left ++ leaves (depth + 1) right

--| Where the leftmost pair nested inside four pairs is: the regular numbers
--| before it, its two values, and the regular numbers after it.
type Exploding = { before: List Leaf, left: Leaf, right: Leaf, after: List Leaf }

--| The first regular number inside more than four pairs, and the next one.
--| In a number with nothing inside more than five pairs (the only numbers
--| the puzzle explodes), these are the leftmost pair nested inside four
--| pairs: that pair's elements can't be pairs, so they are its two values.
def firstDeep: List Leaf → Option Exploding
  | [] => None
  | [leaf, ..rest] =>
    if 4 < leaf.depth then
      match rest with
        | [next, ..after] => Some { before = [], left = leaf, right = next, after }
        | [] => None
    else
      match firstDeep rest with
        | Some found => Some { found | before = [leaf, ..found.before] }
        | None => None

--| `amount` added to the first regular number, if there is one.
def addToFirst (amount: Nat): List Leaf → List Leaf
  | [] => []
  | [leaf, ..rest] => [{ value = leaf.value + amount, depth = leaf.depth }, ..rest]

--| `amount` added to the last regular number, if there is one.
def addToLast (amount: Nat): List Leaf → List Leaf
  | [] => []
  | [leaf] => [{ value = leaf.value + amount, depth = leaf.depth }]
  | [leaf, ..rest] => [leaf, ..addToLast amount rest]

--| Exploding: the pair's left value is added to the first regular number to
--| its left (the last one before it), its right value to the first regular
--| number to its right, and the pair becomes the regular number 0, inside
--| one pair fewer than its values were.
def explodeLeaves (leaves: List Leaf): Option (List Leaf) := match firstDeep leaves with
  | Some found =>
    Some
      (addToLast found.left.value found.before
        ++ [{ value = 0, depth = found.left.depth - 1 }, ..addToFirst found.right.value found.after])
  | None => None

--| Splitting: the leftmost regular number of 10 or more becomes a pair of
--| its half rounded down and its half rounded up.
def splitLeaves: List Leaf → Option (List Leaf)
  | [] => None
  | [leaf, ..rest] =>
    if 10 ≤ leaf.value then
      Some [
        { value = leaf.value / 2, depth = leaf.depth + 1 },
        { value = (leaf.value + 1) / 2, depth = leaf.depth + 1 },
        ..rest
      ]
    else
      match splitLeaves rest with
        | Some after => Some [leaf, ..after]
        | None => None

--| One step of reducing: explode if a pair can, else split if a number can.
def reduceStep (leaves: List Leaf): Option (List Leaf) := match explodeLeaves leaves with
  | Some after => Some after
  | None => splitLeaves leaves

--| Reducing `start` ends at `final`: step until no step applies.
type ReducesTo: List Leaf → List Leaf → Prop =
  | Reduced (done: reduceStep final = None): ReducesTo final final
  | Steps (step: reduceStep start = Some next) (rest: ReducesTo next final): ReducesTo start final

--| A reduced number: no pair is nested inside four pairs (no regular number
--| is inside more than four), and no regular number is 10 or more. The
--| puzzle's numbers are all reduced.
def IsReduced (number: Number): Prop := List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves 0 number)

--| `x + y` is `sum`: the pair of `x` and `y`, reduced, has `sum`'s leaves.
def IsSum (x y sum: Number): Prop := ReducesTo (leaves 0 (Pair x y)) (leaves 0 sum)

--| `total`, then each of `numbers` added to it in turn, is `final`.
type AddsUpTo: Number → List Number → Number → Prop =
  | NothingAdded (total: Number): AddsUpTo total [] total
  | AddNext (sum: IsSum total next total2) (rest: AddsUpTo total2 numbers final): AddsUpTo total [next, ..numbers] final

def magnitude: Number → Nat
  | Regular value => value
  | Pair left right => 3 * magnitude left + 2 * magnitude right

--| Part 1: the magnitude of the numbers added up in order.
def Part1 (numbers: List Number) (answer: Nat): Prop :=
  ∃ (first: Number) (rest: List Number) (final: Number) => numbers = [first, ..rest]
    ∧ AddsUpTo first rest final
    ∧ magnitude final = answer

--| Part 2: the largest magnitude of `x + y` for numbers `x` and `y` on
--| different lines.
def Part2 (numbers: List Number) (answer: Nat): Prop :=
  (∃ (i: Nat) (j: Nat) (x: Number) (y: Number) (sum: Number) => i ≠ j
    ∧ numbers.get i = Some x
    ∧ numbers.get j = Some y
    ∧ IsSum x y sum
    ∧ magnitude sum = answer)
    ∧ (∀ (i j: Nat) (x y sum: Number) => i ≠ j
      → numbers.get i = Some x
      → numbers.get j = Some y
      → IsSum x y sum
      → magnitude sum ≤ answer)
