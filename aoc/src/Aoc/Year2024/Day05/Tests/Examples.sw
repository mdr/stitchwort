-- Day 5's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day05.main` doesn't check them.

namespace Aoc.Year2024.Day05.Tests
import Aoc.Year2024.Day05 (..)
import Std (Fail, List, Nat, Result, Text)

def example: Text := """
  47|53
  97|13
  97|61
  97|47
  75|29
  61|13
  75|53
  29|13
  97|29
  53|29
  61|53
  97|53
  61|29
  47|13
  75|47
  97|75
  47|61
  75|61
  47|29
  75|13
  53|13

  75,47,61,53,29
  97,61,53,29,13
  75,29,13
  75,97,47,61,53
  61,13,29
  97,13,75,29,47
  """

def parsed (input: Text): Result PrintQueue Text := Fail.toResult (() => parsePrintQueue input)

def exampleQueue: PrintQueue := Fail.orElse { rules = [], updates = [] } (() => parsePrintQueue example)

def examplePrecedes: Nat → Nat → Bool := mustPrecede (ruleSet exampleQueue.rules)

test "example, part 1" := solvePart1 exampleQueue == 143
test "example, part 2" := solvePart2 exampleQueue == 123
test "example, which updates are in order" :=
  exampleQueue.updates.map (update => inOrder examplePrecedes update.pages) == [True, True, True, False, False, False]
test "example, reordered" :=
  exampleQueue.updates.map (update => (update.reorder examplePrecedes).pages) |> .drop 3 ==
    [[97, 75, 47, 61, 53], [61, 29, 13], [97, 75, 47, 29, 13]]
test "example, middle pages" := exampleQueue.updates.map .middlePage == [61, 53, 29, 47, 13, 75]

test "parse" := parsed "1|2\n3|4\n\n1,2,3\n4\n" ==
  Ok ({ rules = [{ before = 1, after = 2 }, { before = 3, after = 4 }], updates = [{ pages = [1, 2, 3] }, { pages = [4] }] }: PrintQueue)
test "parse without a final line break" := parsed "1|2\n\n1,2,3" ==
  Ok ({ rules = [{ before = 1, after = 2 }], updates = [{ pages = [1, 2, 3] }] }: PrintQueue)
test "a bad rule" := parsed "1|2\n3x4\n\n1,2\n" == Err "line 2, column 2: expected '|' or a blank line before this line, got 'x'"
test "a rule with no second page" := parsed "1|2\n3|\n\n1,2\n" == Err "line 2, column 3: expected a number or a blank line before this line, got the end of the line"
test "a bad update" := parsed "1|2\n\n1,2\n3,x\n" == Err "line 4, column 3: expected a number, got 'x'"
test "a bad separator in an update" := parsed "1|2\n\n1,2\n3;4\n" == Err "line 4, column 2: expected ',' or the end of the line, got ';'"
test "a rule among the updates" := parsed "1|2\n\n1,2\n3|4\n" == Err "line 4, column 2: expected ',' or the end of the line, got '|'"
test "no blank line" := parsed "1|2\n1,2\n" == Err "line 2, column 2: expected '|' or a blank line before this line, got ','"
test "no updates" := parsed "1|2\n\n" == Err "line 3, column 1: expected a number, got the end of the input"
test "two blank lines" := parsed "1|2\n\n\n1,2\n" == Err "line 3, column 1: expected a number, got the end of the line"
test "blank lines at the end" := parsed "1|2\n\n1,2\n\n\n" == Ok ({ rules = [{ before = 1, after = 2 }], updates = [{ pages = [1, 2] }] }: PrintQueue)

def precedesIn (rules: List Rule): Nat → Nat → Bool := mustPrecede (ruleSet rules)

test "no rules: any order" := inOrder (precedesIn []) [3, 1, 2]
test "a rule broken" := !(inOrder (precedesIn [{ before = 1, after = 2 }]) [2, 1])
test "a rule kept" := inOrder (precedesIn [{ before = 1, after = 2 }]) [1, 2]
test "a rule kept with pages between" := inOrder (precedesIn [{ before = 1, after = 2 }]) [1, 5, 2]
test "a rule broken with pages between" := !(inOrder (precedesIn [{ before = 1, after = 2 }]) [2, 5, 1])
test "a rule about a missing page" := inOrder (precedesIn [{ before = 1, after = 9 }]) [2, 1]
test "one page" := inOrder (precedesIn [{ before = 1, after = 1 }]) [1]
test "no pages" := inOrder (precedesIn [{ before = 1, after = 2 }]) []
test "reorder: a chain" :=
  (Update.reorder { pages = [1, 2, 3] } (precedesIn [{ before = 3, after = 2 }, { before = 2, after = 1 }, { before = 3, after = 1 }])).pages == [3, 2, 1]
test "reorder: pages no rule mentions keep their order" := (Update.reorder { pages = [5, 4, 6] } (precedesIn [])).pages == [5, 4, 6]
test "middle of one page" := Update.middlePage { pages = [7] } == 7
test "middle of three" := Update.middlePage { pages = [1, 2, 3] } == 2
