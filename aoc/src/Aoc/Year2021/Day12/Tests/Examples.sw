--| Day 12's tests: the puzzle's example and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day12.main`
-- doesn't check them.

namespace Aoc.Year2021.Day12.Tests
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Fail, List, Text)

def parsed (input: Text): Result (List Passage) Text := Fail.toResult (() => parsePassages input)

def passagesOf (input: Text): List Passage := Fail.orElse [] (() => parsePassages input)

--| The passage `a-b`.
def link (a b: Text): Passage := { from = { name = a }, to = { name = b } }

def example: List Passage := passagesOf """
  start-A
  start-b
  A-c
  A-b
  b-d
  A-end
  b-end
  """

--| The hypotheses of `parseNoBigNeighbours` and `endsVisited` can hold.
-- (the audit's random inputs never parse, nor start at `start`)
theorem smallParses: Fail.toResult (() => parsePassages """
  start-A
  A-end
  """) = Ok [link "start" "A", link "A" "end"] := rfl

theorem shortPath: ({ caves = [{ name = "start" }, { name = "A" }, { name = "end" }] }: Path).startToEnd = True := rfl

test "parse the example" :=
  example
    == [link "start" "A", link "start" "b", link "A" "c", link "A" "b", link "b" "d", link "A" "end", link "b" "end"]
test "two big caves joined" :=
  parsed "start-A\nA-BC\nb-end\n"
    == Err
        "line 2: A-BC joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
test "no dash" := parsed "start-A\nAb\n" == Err "line 2, column 3: expected '-', got the end of the line"
test "big and small" :=
  Cave.isBig { name = "A" }
    ∧ Cave.isBig { name = "HN" }
    ∧ Cave.isSmall { name = "start" }
    ∧ Cave.isSmall { name = "end" }
    ∧ Cave.isSmall { name = "dc" }
    ∧ Cave.isSmall { name = "" }

test "the example's ten paths" :=
  ((paths example (spare := False)).map (path => Text.join (path.caves.map .name) ',') |> .sort)
    == ["start,A,b,A,c,A,end", "start,A,b,A,end", "start,A,b,end", "start,A,c,A,b,A,end", "start,A,c,A,b,end",
      "start,A,c,A,end", "start,A,end", "start,b,A,c,A,end", "start,b,A,end", "start,b,end"]
test "example, part 1" := solvePart1 example == 10
test "example, part 2" := solvePart2 example == 36
test "only start-end" := solvePart1 [link "start" "end"] == 1 ∧ solvePart2 [link "end" "start"] == 1
test "no passages" := solvePart1 [] == 0 ∧ solvePart2 [] == 0
test "neighbours, each once" :=
  neighboursOf [link "a" "b", link "b" "a", link "a" "a"] { name = "a" } == [{ name = "b" }, { name = "a" }]
