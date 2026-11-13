--| The puzzle's worked examples, by the program and by the spec.

namespace Aoc.Year2021.Day18.Tests
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (explodeLeaves, leaves, splitLeaves)
import Aoc.Year2021.Day18.Proofs (explodeSome, height, reduceExplodes, reduceSplits, splitHeight, splitSome, splitSomeLeaves)
import Std (Fail, List, Option, Parse, Result, Text)

--| One number from its text, or `Regular 0` if it doesn't parse.
def numberOf (text: Text): Number := match Fail.toResult (() => Parse.line text (() => number text.length)) with
  | Ok read => read
  | Err _ => Regular 0

def numberResult (text: Text): Result Number Text := Fail.toResult (() => Parse.line text (() => number text.length))

def exploded (text: Text): Option Number := explode 0 (numberOf text) |> .map .number

test "explode, nothing to the left" := exploded "[[[[[9,8],1],2],3],4]" == Some (numberOf "[[[[0,9],2],3],4]")
test "explode, nothing to the right" := exploded "[7,[6,[5,[4,[3,2]]]]]" == Some (numberOf "[7,[6,[5,[7,0]]]]")
test "explode, both sides" := exploded "[[6,[5,[4,[3,2]]]],1]" == Some (numberOf "[[6,[5,[7,0]]],3]")
test "explode, the leftmost pair first" :=
  exploded "[[3,[2,[1,[7,3]]]],[6,[5,[4,[3,2]]]]]" == Some (numberOf "[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]")
test "explode, then the next" := exploded "[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]" == Some (numberOf "[[3,[2,[8,0]]],[9,[5,[7,0]]]]")
test "nothing to explode" := numberResult "[[3,[2,[8,0]]],[9,[5,[7,0]]]]" |> .map (number => explode 0 number |> .map .number) == Ok None

test "split 15" := split (numberOf "[[[[0,7],4],[15,[0,13]]],[1,1]]") == Some (numberOf "[[[[0,7],4],[[7,8],[0,13]]],[1,1]]")
test "split 13" := split (numberOf "[[[[0,7],4],[[7,8],[0,13]]],[1,1]]") == Some (numberOf "[[[[0,7],4],[[7,8],[0,[6,7]]]],[1,1]]")

--| The spec's steps on the leaves give the same numbers' leaves.
test "spec explode" :=
  explodeLeaves (leaves 0 (numberOf "[[6,[5,[4,[3,2]]]],1]")) == Some (leaves 0 (numberOf "[[6,[5,[7,0]]],3]"))
test "spec split" :=
  splitLeaves (leaves 0 (numberOf "[[[[0,7],4],[15,[0,13]]],[1,1]]")) == Some (leaves 0 (numberOf "[[[[0,7],4],[[7,8],[0,13]]],[1,1]]"))

test "a sum" := add (numberOf "[[[[4,3],4],4],[7,[[8,4],9]]]") (numberOf "[1,1]") == Some (numberOf "[[[[0,7],4],[[7,8],[6,0]]],[8,1]]")
test "a magnitude" := magnitude (numberOf "[[[[8,7],[7,7]],[[8,6],[7,7]]],[[[0,7],[6,6]],[8,7]]]") == 3488
test "small magnitudes" := magnitude (numberOf "[[1,2],[[3,4],5]]") == 143 ∧ magnitude (numberOf "[9,1]") == 29

def homework: Text :=
  Text.join
    [
      "[[[0,[5,8]],[[1,7],[9,6]]],[[4,[1,2]],[[1,4],2]]]",
      "[[[5,[2,8]],4],[5,[[9,9],0]]]",
      "[6,[[[6,2],[5,6]],[[7,6],[4,7]]]]",
      "[[[6,[0,7]],[0,9]],[4,[9,[9,0]]]]",
      "[[[7,[6,4]],[3,[1,3]]],[[[5,5],1],9]]",
      "[[6,[[7,3],[3,2]]],[[[3,8],[5,7]],4]]",
      "[[[[5,4],[7,7]],8],[[8,3],8]]",
      "[[9,3],[[9,9],[6,[4,9]]]]",
      "[[2,[[7,7],7]],[[5,8],[[9,3],[0,2]]]]",
      "[[[[5,2],5],[8,[3,7]]],[[5,[7,5]],[4,4]]]"
    ]
    '\n'

def homeworkNumbers: List Number := Fail.orElse [] (() => parseNumbers homework)

test "the homework parses" := homeworkNumbers.length == 10
test "the homework's total" := solvePart1 homeworkNumbers == Some 4140
test "the homework's largest sum" := solvePart2 homeworkNumbers == Some 3993

--| The parser refuses a number that isn't reduced, and anything else that
--| isn't a number.
def refuses (input: Text): Bool :=
  Fail.toResult (() => parseNumbers input) |> matches | Err _

test "the parser refuses a deep pair" := refuses "[[[[[9,8],1],2],3],4]"
test "the parser refuses a number above 9" := refuses "[10,1]"
test "the parser refuses junk" := refuses "[1,2" ∧ refuses "[1;2]" ∧ refuses "[1,2]x"
test "the parser takes reduced numbers" := not (refuses """
  [1,2]
  [[[[1,2],3],4],5]""")

--| The hypotheses of `splitSome`, `splitSomeLeaves`, `splitHeight`,
--| `reduceSplits`, `explodeSome` and `reduceExplodes` can hold: two of
--| the puzzle's first examples.
-- (the audit's random numbers never split or explode to the random
-- number it picks)
def tenAndOne: Number := Pair (Regular 10) (Regular 1)

def tenSplit: Number := Pair (Pair (Regular 5) (Regular 5)) (Regular 1)

theorem exampleSplits: splitLeaves (leaves 0 tenAndOne) = Some (leaves 0 tenSplit) := splitSome tenAndOne tenSplit rfl

theorem exampleSplitsAfter: splitLeaves (leaves 0 tenAndOne ++ []) = Some (leaves 0 tenSplit ++ []) := splitSomeLeaves 0 tenAndOne tenSplit rfl []

theorem exampleSplitHeight: height tenSplit ≤ height tenAndOne + 1 := splitHeight tenAndOne tenSplit rfl

def deepLeft: Number := Pair (Pair (Pair (Pair (Pair (Regular 9) (Regular 8)) (Regular 1)) (Regular 2)) (Regular 3)) (Regular 4)

def deepLeftExploded: Explosion :=
  { toLeft = 9, number = Pair (Pair (Pair (Pair (Regular 0) (Regular 9)) (Regular 2)) (Regular 3)) (Regular 4), toRight = 0 }

theorem exampleExplodes: explodeLeaves (leaves 0 deepLeft) = Some (leaves 0 deepLeftExploded.number) :=
  explodeSome deepLeft deepLeftExploded rfl omega

theorem exampleReduceSplits: reduce 1 tenAndOne = reduce 0 tenSplit := reduceSplits 0 tenAndOne tenSplit rfl rfl

theorem exampleReduceExplodes: reduce 1 deepLeft = reduce 0 deepLeftExploded.number := reduceExplodes 0 deepLeft deepLeftExploded rfl
