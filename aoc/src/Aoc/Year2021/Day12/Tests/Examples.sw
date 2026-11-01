-- Day 12's tests: the puzzle's example and unit tests. Kept apart from the
-- program, so `stitchwort run Aoc.Year2021.Day12.main` doesn't check them.

namespace Aoc.Year2021.Day12.Tests
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (startToEnd)
import Std (Fail, List, Text)

def parsed (input: Text): Result (List (Text, Text)) Text := Fail.toResult (() => parsePassages input)

def passagesOf (input: Text): List (Text, Text) := Fail.orElse [] (() => parsePassages input)

def example: List (Text, Text) := passagesOf "start-A\nstart-b\nA-c\nA-b\nb-d\nA-end\nb-end\n"

-- The hypotheses of `parseNoBigNeighbours` and `endsVisited` can hold
-- (the audit's random inputs never parse, nor start at `start`).
theorem smallParses: Fail.toResult (() => parsePassages "start-A\nA-end\n") = Ok [("start", "A"), ("A", "end")] := rfl

theorem shortPath: startToEnd ["start", "A", "end"] = True := rfl

test "parse the example" :=
  example == [("start", "A"), ("start", "b"), ("A", "c"), ("A", "b"), ("b", "d"), ("A", "end"), ("b", "end")]
test "two big caves joined" := parsed "start-A\nA-BC\nb-end\n" == Err "line 2: A-BC joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
test "no dash" := parsed "start-A\nAb\n" == Err "line 2, column 3: expected '-', got the end of the line"
test "big and small" := isBig "A" ∧ isBig "HN" ∧ ¬isBig "start" ∧ ¬isBig "end" ∧ ¬isBig "dc" ∧ ¬isBig ""

test "the example's ten paths" :=
  ((paths example False).map (path => Text.join path ',') |> .sort)
    == [
      "start,A,b,A,c,A,end",
      "start,A,b,A,end",
      "start,A,b,end",
      "start,A,c,A,b,A,end",
      "start,A,c,A,b,end",
      "start,A,c,A,end",
      "start,A,end",
      "start,b,A,c,A,end",
      "start,b,A,end",
      "start,b,end"
    ]
test "example, part 1" := solvePart1 example == 10
test "example, part 2" := solvePart2 example == 36
test "only start-end" := solvePart1 [("start", "end")] == 1 ∧ solvePart2 [("end", "start")] == 1
test "no passages" := solvePart1 [] == 0 ∧ solvePart2 [] == 0
test "neighbours, each once" := neighboursOf [("a", "b"), ("b", "a"), ("a", "a")] "a" == ["b", "a"]
